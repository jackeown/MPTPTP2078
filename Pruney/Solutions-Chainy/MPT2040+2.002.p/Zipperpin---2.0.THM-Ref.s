%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Qa1F2G7EIq

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:36 EST 2020

% Result     : Theorem 20.41s
% Output     : Refutation 20.45s
% Verified   : 
% Statistics : Number of formulae       :  607 (30755 expanded)
%              Number of leaves         :   59 (9293 expanded)
%              Depth                    :  100
%              Number of atoms          : 10072 (948422 expanded)
%              Number of equality atoms :   94 (2571 expanded)
%              Maximal formula depth    :   29 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(r2_waybel_9_type,type,(
    r2_waybel_9: $i > $i > $o )).

thf(l1_waybel_9_type,type,(
    l1_waybel_9: $i > $o )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(r3_waybel_9_type,type,(
    r3_waybel_9: $i > $i > $i > $o )).

thf(k4_waybel_1_type,type,(
    k4_waybel_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k2_yellow_0_type,type,(
    k2_yellow_0: $i > $i > $i )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(u1_waybel_0_type,type,(
    u1_waybel_0: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v11_waybel_0_type,type,(
    v11_waybel_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(k1_waybel_9_type,type,(
    k1_waybel_9: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i )).

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
    ! [X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X29 )
      | ~ ( v4_orders_2 @ X29 )
      | ~ ( v7_waybel_0 @ X29 )
      | ~ ( l1_waybel_0 @ X29 @ X30 )
      | ( r3_waybel_9 @ X30 @ X29 @ ( sk_C @ X29 @ X30 ) )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v1_compts_1 @ X30 )
      | ~ ( v8_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
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
    ! [X19: $i] :
      ( ( l1_pre_topc @ X19 )
      | ~ ( l1_waybel_9 @ X19 ) ) ),
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
    ! [X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X29 )
      | ~ ( v4_orders_2 @ X29 )
      | ~ ( v7_waybel_0 @ X29 )
      | ~ ( l1_waybel_0 @ X29 @ X30 )
      | ( m1_subset_1 @ ( sk_C @ X29 @ X30 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v1_compts_1 @ X30 )
      | ~ ( v8_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
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

thf('28',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X35 ) )
      | ( m1_subset_1 @ ( sk_D_2 @ X35 ) @ ( u1_struct_0 @ X35 ) )
      | ~ ( v11_waybel_0 @ X36 @ X35 )
      | ~ ( r3_waybel_9 @ X35 @ X36 @ X34 )
      | ( X34
        = ( k1_waybel_9 @ X35 @ X36 ) )
      | ~ ( l1_waybel_0 @ X36 @ X35 )
      | ~ ( v7_waybel_0 @ X36 )
      | ~ ( v4_orders_2 @ X36 )
      | ( v2_struct_0 @ X36 )
      | ~ ( l1_waybel_9 @ X35 )
      | ~ ( v1_compts_1 @ X35 )
      | ~ ( v2_lattice3 @ X35 )
      | ~ ( v1_lattice3 @ X35 )
      | ~ ( v5_orders_2 @ X35 )
      | ~ ( v4_orders_2 @ X35 )
      | ~ ( v3_orders_2 @ X35 )
      | ~ ( v8_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t36_waybel_9])).

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
        = ( k1_waybel_9 @ sk_A @ X0 ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( v11_waybel_0 @ X0 @ sk_A )
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
        = ( k1_waybel_9 @ sk_A @ X0 ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( v11_waybel_0 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30','31','32','33','34','35','36','37','38'])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v11_waybel_0 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','39'])).

thf('41',plain,(
    v11_waybel_0 @ sk_B @ sk_A ),
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
      = ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41','42','43','44'])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X37: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X37 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_D_2 @ sk_A ) ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X35 ) )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X35 @ ( sk_D_2 @ X35 ) ) @ X35 @ X35 )
      | ~ ( v11_waybel_0 @ X36 @ X35 )
      | ~ ( r3_waybel_9 @ X35 @ X36 @ X34 )
      | ( X34
        = ( k1_waybel_9 @ X35 @ X36 ) )
      | ~ ( l1_waybel_0 @ X36 @ X35 )
      | ~ ( v7_waybel_0 @ X36 )
      | ~ ( v4_orders_2 @ X36 )
      | ( v2_struct_0 @ X36 )
      | ~ ( l1_waybel_9 @ X35 )
      | ~ ( v1_compts_1 @ X35 )
      | ~ ( v2_lattice3 @ X35 )
      | ~ ( v1_lattice3 @ X35 )
      | ~ ( v5_orders_2 @ X35 )
      | ~ ( v4_orders_2 @ X35 )
      | ~ ( v3_orders_2 @ X35 )
      | ~ ( v8_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t36_waybel_9])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( sk_C @ sk_B @ sk_A )
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
    inference(demod,[status(thm)],['50','51','52','53','54','55','56','57','58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v11_waybel_0 @ X0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( ( sk_C @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ X0 ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_C @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( sk_C @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( ( sk_C @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ X0 ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( v11_waybel_0 @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v11_waybel_0 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','62'])).

thf('64',plain,(
    v11_waybel_0 @ sk_B @ sk_A ),
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
      = ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['63','64','65','66','67'])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('73',plain,
    ( ( r3_waybel_9 @ sk_A @ sk_B @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('76',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('77',plain,
    ( ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('80',plain,
    ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('81',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

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

thf('82',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v7_waybel_0 @ X20 )
      | ~ ( l1_waybel_0 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ( r1_lattice3 @ X21 @ ( k2_relset_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X21 ) @ ( u1_waybel_0 @ X21 @ X20 ) ) @ X22 )
      | ( X23 != X22 )
      | ~ ( r3_waybel_9 @ X21 @ X20 @ X23 )
      | ~ ( v11_waybel_0 @ X20 @ X21 )
      | ( m1_subset_1 @ ( sk_E @ X21 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_waybel_9 @ X21 )
      | ~ ( v1_compts_1 @ X21 )
      | ~ ( v2_lattice3 @ X21 )
      | ~ ( v1_lattice3 @ X21 )
      | ~ ( v5_orders_2 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v3_orders_2 @ X21 )
      | ~ ( v8_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[l51_waybel_9])).

thf('83',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v2_pre_topc @ X21 )
      | ~ ( v8_pre_topc @ X21 )
      | ~ ( v3_orders_2 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v5_orders_2 @ X21 )
      | ~ ( v1_lattice3 @ X21 )
      | ~ ( v2_lattice3 @ X21 )
      | ~ ( v1_compts_1 @ X21 )
      | ~ ( l1_waybel_9 @ X21 )
      | ( m1_subset_1 @ ( sk_E @ X21 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( v11_waybel_0 @ X20 @ X21 )
      | ~ ( r3_waybel_9 @ X21 @ X20 @ X22 )
      | ( r1_lattice3 @ X21 @ ( k2_relset_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X21 ) @ ( u1_waybel_0 @ X21 @ X20 ) ) @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_waybel_0 @ X20 @ X21 )
      | ~ ( v7_waybel_0 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ X0 ) ) @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C @ sk_B @ sk_A ) )
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
      | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ X0 ) ) @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( v11_waybel_0 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['84','85','86','87','88','89','90','91','92','93'])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v11_waybel_0 @ sk_B @ sk_A )
    | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['80','94'])).

thf('96',plain,(
    v11_waybel_0 @ sk_B @ sk_A ),
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
    | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['95','96','97','98','99'])).

thf('101',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( sk_C @ sk_B @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,
    ( ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['79','101'])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('105',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf(t31_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ( l1_orders_2 @ A )
        & ( v5_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ( ( r2_yellow_0 @ A @ C )
                  & ( B
                    = ( k2_yellow_0 @ A @ C ) ) )
               => ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r1_lattice3 @ A @ C @ D )
                       => ( r1_orders_2 @ A @ D @ B ) ) )
                  & ( r1_lattice3 @ A @ C @ B ) ) )
              & ( ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r1_lattice3 @ A @ C @ D )
                       => ( r1_orders_2 @ A @ D @ B ) ) )
                  & ( r1_lattice3 @ A @ C @ B ) )
               => ( ( r2_yellow_0 @ A @ C )
                  & ( B
                    = ( k2_yellow_0 @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
       => ( zip_tseitin_0 @ D @ C @ B @ A ) )
     => ( zip_tseitin_1 @ D @ C @ B @ A ) ) )).

thf('108',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( zip_tseitin_1 @ X5 @ X6 @ X7 @ X8 )
      | ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf(zf_stmt_2,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( r1_lattice3 @ A @ C @ D )
       => ( r1_orders_2 @ A @ D @ B ) )
     => ( zip_tseitin_0 @ D @ C @ B @ A ) ) )).

thf('111',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X4 )
      | ( r1_lattice3 @ X4 @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

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

thf('112',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ~ ( v7_waybel_0 @ X24 )
      | ~ ( l1_waybel_0 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X25 ) )
      | ~ ( r1_lattice3 @ X25 @ ( k2_relset_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X25 ) @ ( u1_waybel_0 @ X25 @ X24 ) ) @ X27 )
      | ( r1_orders_2 @ X25 @ X27 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X25 ) )
      | ( X28 != X26 )
      | ~ ( r3_waybel_9 @ X25 @ X24 @ X28 )
      | ( m1_subset_1 @ ( sk_E_1 @ X25 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_waybel_9 @ X25 )
      | ~ ( v1_compts_1 @ X25 )
      | ~ ( v2_lattice3 @ X25 )
      | ~ ( v1_lattice3 @ X25 )
      | ~ ( v5_orders_2 @ X25 )
      | ~ ( v4_orders_2 @ X25 )
      | ~ ( v3_orders_2 @ X25 )
      | ~ ( v8_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[l52_waybel_9])).

thf('113',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( v2_pre_topc @ X25 )
      | ~ ( v8_pre_topc @ X25 )
      | ~ ( v3_orders_2 @ X25 )
      | ~ ( v4_orders_2 @ X25 )
      | ~ ( v5_orders_2 @ X25 )
      | ~ ( v1_lattice3 @ X25 )
      | ~ ( v2_lattice3 @ X25 )
      | ~ ( v1_compts_1 @ X25 )
      | ~ ( l1_waybel_9 @ X25 )
      | ( m1_subset_1 @ ( sk_E_1 @ X25 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( r3_waybel_9 @ X25 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X25 ) )
      | ( r1_orders_2 @ X25 @ X27 @ X26 )
      | ~ ( r1_lattice3 @ X25 @ ( k2_relset_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X25 ) @ ( u1_waybel_0 @ X25 @ X24 ) ) @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_waybel_0 @ X24 @ X25 )
      | ~ ( v7_waybel_0 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X0 @ ( k2_relset_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X2 ) @ ( u1_waybel_0 @ X2 @ X1 ) ) @ X4 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v7_waybel_0 @ X1 )
      | ~ ( l1_waybel_0 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( r1_orders_2 @ X2 @ X0 @ X3 )
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
    inference('sup-',[status(thm)],['111','113'])).

thf('115',plain,(
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
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X1 @ ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( zip_tseitin_0 @ X1 @ ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ X0 ) ) @ X2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['110','114'])).

thf('116',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X1 @ ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( zip_tseitin_0 @ X1 @ ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ X0 ) ) @ X2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['115','116','117','118','119','120','121','122','123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ X1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ( r1_orders_2 @ sk_A @ X1 @ ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['109','125'])).

thf('127',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ X1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_orders_2 @ sk_A @ X1 @ ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['126','127','128','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X1 @ ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( zip_tseitin_0 @ X1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_1 @ X0 @ X3 @ X2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ X0 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ X1 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_orders_2 @ sk_A @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['108','131'])).

thf('133',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( zip_tseitin_1 @ X5 @ X6 @ X7 @ X8 )
      | ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('134',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X1 @ ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_1 @ X1 @ X3 @ X2 @ sk_A )
      | ( zip_tseitin_1 @ X1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ X1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_orders_2 @ sk_A @ X1 @ ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(eq_fact,[status(thm)],['134'])).

thf('136',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf(zf_stmt_3,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( B
          = ( k2_yellow_0 @ A @ C ) )
        & ( r2_yellow_0 @ A @ C ) ) ) )).

thf(zf_stmt_5,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_6,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ( ( r1_lattice3 @ A @ C @ B )
                  & ! [D: $i] :
                      ( zip_tseitin_1 @ D @ C @ B @ A ) )
               => ( zip_tseitin_2 @ C @ B @ A ) )
              & ( ( ( B
                    = ( k2_yellow_0 @ A @ C ) )
                  & ( r2_yellow_0 @ A @ C ) )
               => ( ( r1_lattice3 @ A @ C @ B )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r1_lattice3 @ A @ C @ D )
                       => ( r1_orders_2 @ A @ D @ B ) ) ) ) ) ) ) ) )).

thf('137',plain,(
    ! [X12: $i,X13: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r1_lattice3 @ X13 @ X16 @ X12 )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X16 @ X12 @ X13 ) @ X16 @ X12 @ X13 )
      | ( zip_tseitin_2 @ X16 @ X12 @ X13 )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( v5_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( zip_tseitin_2 @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X19: $i] :
      ( ( l1_orders_2 @ X19 )
      | ~ ( l1_waybel_9 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('142',plain,(
    l1_orders_2 @ sk_A ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_2 @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['138','139','142'])).

thf('144',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['135','143'])).

thf('145',plain,
    ( ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['107','145'])).

thf('147',plain,
    ( ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X4 )
      | ~ ( r1_orders_2 @ X4 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( zip_tseitin_1 @ X5 @ X6 @ X7 @ X8 )
      | ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_1 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_2 @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['138','139','142'])).

thf('153',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,
    ( ~ ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['106','154'])).

thf('156',plain,
    ( ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_yellow_0 @ X9 @ X10 )
      | ~ ( zip_tseitin_2 @ X10 @ X11 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('158',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf(d4_waybel_9,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ( ( r2_waybel_9 @ A @ B )
          <=> ( r2_yellow_0 @ A @ ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_waybel_0 @ A @ B ) ) ) ) ) ) )).

thf('159',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_waybel_0 @ X17 @ X18 )
      | ~ ( r2_yellow_0 @ X18 @ ( k2_relset_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X18 ) @ ( u1_waybel_0 @ X18 @ X17 ) ) )
      | ( r2_waybel_9 @ X18 @ X17 )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_waybel_9])).

thf('160',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    l1_orders_2 @ sk_A ),
    inference('sup-',[status(thm)],['140','141'])).

thf('162',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_waybel_9 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['160','161','162'])).

thf('164',plain,(
    ! [X37: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X37 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('167',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( zip_tseitin_1 @ X5 @ X6 @ X7 @ X8 )
      | ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_2 @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['138','139','142'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( zip_tseitin_2 @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['166','169'])).

thf('171',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('173',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X4 )
      | ( r1_lattice3 @ X4 @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('174',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( zip_tseitin_1 @ X5 @ X6 @ X7 @ X8 )
      | ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('175',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_lattice3 @ X0 @ X2 @ X3 )
      | ( zip_tseitin_1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_2 @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['138','139','142'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( zip_tseitin_2 @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
    | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['172','177'])).

thf('179',plain,
    ( ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['178'])).

thf('180',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ~ ( v7_waybel_0 @ X24 )
      | ~ ( l1_waybel_0 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X25 ) )
      | ~ ( r1_lattice3 @ X25 @ ( k2_relset_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X25 ) @ ( u1_waybel_0 @ X25 @ X24 ) ) @ X27 )
      | ( r1_orders_2 @ X25 @ X27 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X25 ) )
      | ( X28 != X26 )
      | ~ ( r3_waybel_9 @ X25 @ X24 @ X28 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X25 @ ( sk_E_1 @ X25 ) ) @ X25 @ X25 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_waybel_9 @ X25 )
      | ~ ( v1_compts_1 @ X25 )
      | ~ ( v2_lattice3 @ X25 )
      | ~ ( v1_lattice3 @ X25 )
      | ~ ( v5_orders_2 @ X25 )
      | ~ ( v4_orders_2 @ X25 )
      | ~ ( v3_orders_2 @ X25 )
      | ~ ( v8_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[l52_waybel_9])).

thf('181',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( v2_pre_topc @ X25 )
      | ~ ( v8_pre_topc @ X25 )
      | ~ ( v3_orders_2 @ X25 )
      | ~ ( v4_orders_2 @ X25 )
      | ~ ( v5_orders_2 @ X25 )
      | ~ ( v1_lattice3 @ X25 )
      | ~ ( v2_lattice3 @ X25 )
      | ~ ( v1_compts_1 @ X25 )
      | ~ ( l1_waybel_9 @ X25 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X25 @ ( sk_E_1 @ X25 ) ) @ X25 @ X25 )
      | ~ ( r3_waybel_9 @ X25 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X25 ) )
      | ( r1_orders_2 @ X25 @ X27 @ X26 )
      | ~ ( r1_lattice3 @ X25 @ ( k2_relset_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X25 ) @ ( u1_waybel_0 @ X25 @ X24 ) ) @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_waybel_0 @ X24 @ X25 )
      | ~ ( v7_waybel_0 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(simplify,[status(thm)],['180'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
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
    inference('sup-',[status(thm)],['179','181'])).

thf('183',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['182','183','184','185','186','187','188','189','190','191','192','193','194'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['195'])).

thf('197',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ X0 )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['171','196'])).

thf('198',plain,(
    ! [X0: $i] :
      ( ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['197'])).

thf('199',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_waybel_9 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ X0 )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['165','198'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ( r2_waybel_9 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['105','200'])).

thf('202',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['201'])).

thf('203',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['104','202'])).

thf('204',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['203'])).

thf('205',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X4 )
      | ~ ( r1_orders_2 @ X4 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('206',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_waybel_9 @ sk_A @ sk_B )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( zip_tseitin_1 @ X5 @ X6 @ X7 @ X8 )
      | ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('208',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ( r2_waybel_9 @ sk_A @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_1 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_2 @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['138','139','142'])).

thf('210',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['208','209'])).

thf('211',plain,
    ( ~ ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['210'])).

thf('212',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['103','211'])).

thf('213',plain,
    ( ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['212'])).

thf('214',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_yellow_0 @ X9 @ X10 )
      | ~ ( zip_tseitin_2 @ X10 @ X11 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('215',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_waybel_0 @ X17 @ X18 )
      | ~ ( r2_yellow_0 @ X18 @ ( k2_relset_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X18 ) @ ( u1_waybel_0 @ X18 @ X17 ) ) )
      | ( r2_waybel_9 @ X18 @ X17 )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_waybel_9])).

thf('217',plain,
    ( ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['215','216'])).

thf('218',plain,(
    l1_orders_2 @ sk_A ),
    inference('sup-',[status(thm)],['140','141'])).

thf('219',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,
    ( ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_waybel_9 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['217','218','219'])).

thf('221',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['220'])).

thf('222',plain,(
    ! [X37: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X37 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,
    ( ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E @ sk_A ) ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['221','222'])).

thf('224',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v7_waybel_0 @ X20 )
      | ~ ( l1_waybel_0 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ( r1_lattice3 @ X21 @ ( k2_relset_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X21 ) @ ( u1_waybel_0 @ X21 @ X20 ) ) @ X22 )
      | ( X23 != X22 )
      | ~ ( r3_waybel_9 @ X21 @ X20 @ X23 )
      | ~ ( v11_waybel_0 @ X20 @ X21 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X21 @ ( sk_E @ X21 ) ) @ X21 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_waybel_9 @ X21 )
      | ~ ( v1_compts_1 @ X21 )
      | ~ ( v2_lattice3 @ X21 )
      | ~ ( v1_lattice3 @ X21 )
      | ~ ( v5_orders_2 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v3_orders_2 @ X21 )
      | ~ ( v8_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[l51_waybel_9])).

thf('225',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v2_pre_topc @ X21 )
      | ~ ( v8_pre_topc @ X21 )
      | ~ ( v3_orders_2 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v5_orders_2 @ X21 )
      | ~ ( v1_lattice3 @ X21 )
      | ~ ( v2_lattice3 @ X21 )
      | ~ ( v1_compts_1 @ X21 )
      | ~ ( l1_waybel_9 @ X21 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X21 @ ( sk_E @ X21 ) ) @ X21 @ X21 )
      | ~ ( v11_waybel_0 @ X20 @ X21 )
      | ~ ( r3_waybel_9 @ X21 @ X20 @ X22 )
      | ( r1_lattice3 @ X21 @ ( k2_relset_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X21 ) @ ( u1_waybel_0 @ X21 @ X20 ) ) @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_waybel_0 @ X20 @ X21 )
      | ~ ( v7_waybel_0 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(simplify,[status(thm)],['224'])).

thf('226',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r2_waybel_9 @ sk_A @ sk_B )
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
    inference('sup-',[status(thm)],['223','225'])).

thf('227',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r2_waybel_9 @ sk_A @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ X0 ) ) @ X1 )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ X1 )
      | ~ ( v11_waybel_0 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['226','227','228','229','230','231','232','233','234','235'])).

thf('237',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v11_waybel_0 @ X0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ X0 ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r2_waybel_9 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','236'])).

thf('238',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r2_waybel_9 @ sk_A @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ X0 ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ~ ( v11_waybel_0 @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['237'])).

thf('239',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v11_waybel_0 @ sk_B @ sk_A )
    | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['74','238'])).

thf('240',plain,(
    v11_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['239','240','241','242','243'])).

thf('245',plain,
    ( ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['244'])).

thf('246',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('247',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('248',plain,
    ( ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['244'])).

thf('249',plain,
    ( ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['244'])).

thf('250',plain,
    ( ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('251',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['249','250'])).

thf('252',plain,
    ( ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['251'])).

thf('253',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X4 )
      | ~ ( r1_orders_2 @ X4 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('254',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r2_waybel_9 @ sk_A @ sk_B )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['252','253'])).

thf('255',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( zip_tseitin_1 @ X5 @ X6 @ X7 @ X8 )
      | ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('256',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_waybel_9 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_1 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['254','255'])).

thf('257',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_2 @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['138','139','142'])).

thf('258',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['256','257'])).

thf('259',plain,
    ( ~ ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['258'])).

thf('260',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['248','259'])).

thf('261',plain,
    ( ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['260'])).

thf('262',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_yellow_0 @ X9 @ X10 )
      | ~ ( zip_tseitin_2 @ X10 @ X11 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('263',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['261','262'])).

thf('264',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_waybel_0 @ X17 @ X18 )
      | ~ ( r2_yellow_0 @ X18 @ ( k2_relset_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X18 ) @ ( u1_waybel_0 @ X18 @ X17 ) ) )
      | ( r2_waybel_9 @ X18 @ X17 )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_waybel_9])).

thf('265',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['263','264'])).

thf('266',plain,(
    l1_orders_2 @ sk_A ),
    inference('sup-',[status(thm)],['140','141'])).

thf('267',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('268',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_waybel_9 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['265','266','267'])).

thf('269',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['268'])).

thf('270',plain,(
    ! [X37: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X37 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('271',plain,
    ( ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['269','270'])).

thf('272',plain,
    ( ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['244'])).

thf('273',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( zip_tseitin_2 @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('274',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['272','273'])).

thf('275',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['274'])).

thf('276',plain,
    ( ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['244'])).

thf('277',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( zip_tseitin_2 @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('278',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
    | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['276','277'])).

thf('279',plain,
    ( ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['278'])).

thf('280',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( v2_pre_topc @ X25 )
      | ~ ( v8_pre_topc @ X25 )
      | ~ ( v3_orders_2 @ X25 )
      | ~ ( v4_orders_2 @ X25 )
      | ~ ( v5_orders_2 @ X25 )
      | ~ ( v1_lattice3 @ X25 )
      | ~ ( v2_lattice3 @ X25 )
      | ~ ( v1_compts_1 @ X25 )
      | ~ ( l1_waybel_9 @ X25 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X25 @ ( sk_E_1 @ X25 ) ) @ X25 @ X25 )
      | ~ ( r3_waybel_9 @ X25 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X25 ) )
      | ( r1_orders_2 @ X25 @ X27 @ X26 )
      | ~ ( r1_lattice3 @ X25 @ ( k2_relset_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X25 ) @ ( u1_waybel_0 @ X25 @ X24 ) ) @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_waybel_0 @ X24 @ X25 )
      | ~ ( v7_waybel_0 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(simplify,[status(thm)],['180'])).

thf('281',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r2_waybel_9 @ sk_A @ sk_B )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
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
    inference('sup-',[status(thm)],['279','280'])).

thf('282',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('283',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('284',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('285',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('286',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('287',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('288',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('289',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('290',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('291',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('292',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('293',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('294',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r2_waybel_9 @ sk_A @ sk_B )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['281','282','283','284','285','286','287','288','289','290','291','292','293'])).

thf('295',plain,(
    ! [X0: $i] :
      ( ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ( r2_waybel_9 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['294'])).

thf('296',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r2_waybel_9 @ sk_A @ sk_B )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r2_waybel_9 @ sk_A @ sk_B )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ X0 )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['275','295'])).

thf('297',plain,(
    ! [X0: $i] :
      ( ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ( r2_waybel_9 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['296'])).

thf('298',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r2_waybel_9 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r2_waybel_9 @ sk_A @ sk_B )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ X0 )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['271','297'])).

thf('299',plain,(
    ! [X0: $i] :
      ( ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ( r2_waybel_9 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['298'])).

thf('300',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['247','299'])).

thf('301',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['300'])).

thf('302',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['246','301'])).

thf('303',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['302'])).

thf('304',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X4 )
      | ~ ( r1_orders_2 @ X4 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('305',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r2_waybel_9 @ sk_A @ sk_B )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['303','304'])).

thf('306',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( zip_tseitin_1 @ X5 @ X6 @ X7 @ X8 )
      | ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('307',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ( r2_waybel_9 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_1 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['305','306'])).

thf('308',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_2 @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['138','139','142'])).

thf('309',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['307','308'])).

thf('310',plain,
    ( ~ ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['309'])).

thf('311',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['245','310'])).

thf('312',plain,
    ( ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) @ sk_A )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['311'])).

thf('313',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_yellow_0 @ X9 @ X10 )
      | ~ ( zip_tseitin_2 @ X10 @ X11 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('314',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['312','313'])).

thf('315',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_waybel_0 @ X17 @ X18 )
      | ~ ( r2_yellow_0 @ X18 @ ( k2_relset_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X18 ) @ ( u1_waybel_0 @ X18 @ X17 ) ) )
      | ( r2_waybel_9 @ X18 @ X17 )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_waybel_9])).

thf('316',plain,
    ( ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['314','315'])).

thf('317',plain,(
    l1_orders_2 @ sk_A ),
    inference('sup-',[status(thm)],['140','141'])).

thf('318',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('319',plain,
    ( ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_waybel_9 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['316','317','318'])).

thf('320',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['319'])).

thf('321',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('322',plain,
    ( ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['320','321'])).

thf('323',plain,
    ( ~ ( r2_waybel_9 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('324',plain,
    ( ~ ( r2_waybel_9 @ sk_A @ sk_B )
   <= ~ ( r2_waybel_9 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['323'])).

thf('325',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('326',plain,
    ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('327',plain,
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

thf('328',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( v4_orders_2 @ X31 )
      | ~ ( v7_waybel_0 @ X31 )
      | ~ ( l1_waybel_0 @ X31 @ X32 )
      | ~ ( r3_waybel_9 @ X32 @ X31 @ X33 )
      | ( r2_hidden @ X33 @ ( k10_yellow_6 @ X32 @ X31 ) )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X32 ) )
      | ( r3_waybel_9 @ X32 @ X31 @ ( sk_C_1 @ X31 @ X32 ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v1_compts_1 @ X32 )
      | ~ ( v8_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t33_waybel_9])).

thf('329',plain,(
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
    inference('sup-',[status(thm)],['327','328'])).

thf('330',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('331',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('332',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('333',plain,(
    l1_pre_topc @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('334',plain,(
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
    inference(demod,[status(thm)],['329','330','331','332','333'])).

thf('335',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_1 @ X0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['334'])).

thf('336',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['326','335'])).

thf('337',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('338',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('339',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('340',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['336','337','338','339'])).

thf('341',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['340'])).

thf('342',plain,
    ( ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['325','341'])).

thf('343',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['342'])).

thf('344',plain,
    ( ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['323'])).

thf('345',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['343','344'])).

thf('346',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('347',plain,
    ( ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['345','346'])).

thf('348',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('349',plain,
    ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('350',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('351',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( v4_orders_2 @ X31 )
      | ~ ( v7_waybel_0 @ X31 )
      | ~ ( l1_waybel_0 @ X31 @ X32 )
      | ~ ( r3_waybel_9 @ X32 @ X31 @ X33 )
      | ( r2_hidden @ X33 @ ( k10_yellow_6 @ X32 @ X31 ) )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X32 ) )
      | ( m1_subset_1 @ ( sk_C_1 @ X31 @ X32 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v1_compts_1 @ X32 )
      | ~ ( v8_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t33_waybel_9])).

thf('352',plain,(
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
    inference('sup-',[status(thm)],['350','351'])).

thf('353',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('354',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('355',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('356',plain,(
    l1_pre_topc @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('357',plain,(
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
    inference(demod,[status(thm)],['352','353','354','355','356'])).

thf('358',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_C_1 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['357'])).

thf('359',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['349','358'])).

thf('360',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('361',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('362',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('363',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['359','360','361','362'])).

thf('364',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['363'])).

thf('365',plain,
    ( ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['348','364'])).

thf('366',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['365'])).

thf('367',plain,
    ( ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['323'])).

thf('368',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['366','367'])).

thf('369',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('370',plain,
    ( ( ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['368','369'])).

thf('371',plain,
    ( ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['345','346'])).

thf('372',plain,
    ( ( ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['368','369'])).

thf('373',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X35 ) )
      | ( m1_subset_1 @ ( sk_D_2 @ X35 ) @ ( u1_struct_0 @ X35 ) )
      | ~ ( v11_waybel_0 @ X36 @ X35 )
      | ~ ( r3_waybel_9 @ X35 @ X36 @ X34 )
      | ( X34
        = ( k1_waybel_9 @ X35 @ X36 ) )
      | ~ ( l1_waybel_0 @ X36 @ X35 )
      | ~ ( v7_waybel_0 @ X36 )
      | ~ ( v4_orders_2 @ X36 )
      | ( v2_struct_0 @ X36 )
      | ~ ( l1_waybel_9 @ X35 )
      | ~ ( v1_compts_1 @ X35 )
      | ~ ( v2_lattice3 @ X35 )
      | ~ ( v1_lattice3 @ X35 )
      | ~ ( v5_orders_2 @ X35 )
      | ~ ( v4_orders_2 @ X35 )
      | ~ ( v3_orders_2 @ X35 )
      | ~ ( v8_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t36_waybel_9])).

thf('374',plain,
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
          = ( k1_waybel_9 @ sk_A @ X0 ) )
        | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
        | ~ ( v11_waybel_0 @ X0 @ sk_A )
        | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['372','373'])).

thf('375',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('376',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('377',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('378',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('379',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('380',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('381',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('382',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('383',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('384',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ( ( sk_C_1 @ sk_B @ sk_A )
          = ( k1_waybel_9 @ sk_A @ X0 ) )
        | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
        | ~ ( v11_waybel_0 @ X0 @ sk_A )
        | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['374','375','376','377','378','379','380','381','382','383'])).

thf('385',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v11_waybel_0 @ sk_B @ sk_A )
      | ( ( sk_C_1 @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['371','384'])).

thf('386',plain,(
    v11_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('387',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('388',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('389',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('390',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( sk_C_1 @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['385','386','387','388','389'])).

thf('391',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( ( sk_C_1 @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['390'])).

thf('392',plain,(
    ! [X37: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X37 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('393',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( sk_C_1 @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_D_2 @ sk_A ) ) @ sk_A @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['391','392'])).

thf('394',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X35 ) )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X35 @ ( sk_D_2 @ X35 ) ) @ X35 @ X35 )
      | ~ ( v11_waybel_0 @ X36 @ X35 )
      | ~ ( r3_waybel_9 @ X35 @ X36 @ X34 )
      | ( X34
        = ( k1_waybel_9 @ X35 @ X36 ) )
      | ~ ( l1_waybel_0 @ X36 @ X35 )
      | ~ ( v7_waybel_0 @ X36 )
      | ~ ( v4_orders_2 @ X36 )
      | ( v2_struct_0 @ X36 )
      | ~ ( l1_waybel_9 @ X35 )
      | ~ ( v1_compts_1 @ X35 )
      | ~ ( v2_lattice3 @ X35 )
      | ~ ( v1_lattice3 @ X35 )
      | ~ ( v5_orders_2 @ X35 )
      | ~ ( v4_orders_2 @ X35 )
      | ~ ( v3_orders_2 @ X35 )
      | ~ ( v8_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t36_waybel_9])).

thf('395',plain,
    ( ! [X0: $i,X1: $i] :
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
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['393','394'])).

thf('396',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('397',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('398',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('399',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('400',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('401',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('402',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('403',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('404',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('405',plain,
    ( ! [X0: $i,X1: $i] :
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
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['395','396','397','398','399','400','401','402','403','404'])).

thf('406',plain,
    ( ! [X0: $i] :
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
        | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['370','405'])).

thf('407',plain,
    ( ! [X0: $i] :
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
        | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['406'])).

thf('408',plain,
    ( ( ( v2_struct_0 @ sk_A )
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
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['347','407'])).

thf('409',plain,(
    v11_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('410',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('411',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('412',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('413',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_C_1 @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( ( sk_C_1 @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['408','409','410','411','412'])).

thf('414',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( ( sk_C_1 @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['413'])).

thf('415',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('416',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( sk_C_1 @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ sk_B ) ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['414','415'])).

thf('417',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('418',plain,
    ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('419',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('420',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( v4_orders_2 @ X31 )
      | ~ ( v7_waybel_0 @ X31 )
      | ~ ( l1_waybel_0 @ X31 @ X32 )
      | ~ ( r3_waybel_9 @ X32 @ X31 @ X33 )
      | ( r2_hidden @ X33 @ ( k10_yellow_6 @ X32 @ X31 ) )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X32 ) )
      | ( r3_waybel_9 @ X32 @ X31 @ ( sk_D_1 @ X31 @ X32 ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v1_compts_1 @ X32 )
      | ~ ( v8_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t33_waybel_9])).

thf('421',plain,(
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
    inference('sup-',[status(thm)],['419','420'])).

thf('422',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('423',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('424',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('425',plain,(
    l1_pre_topc @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('426',plain,(
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
    inference(demod,[status(thm)],['421','422','423','424','425'])).

thf('427',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_D_1 @ X0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['426'])).

thf('428',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['418','427'])).

thf('429',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('430',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('431',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('432',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['428','429','430','431'])).

thf('433',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['432'])).

thf('434',plain,
    ( ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['417','433'])).

thf('435',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['434'])).

thf('436',plain,
    ( ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['323'])).

thf('437',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['435','436'])).

thf('438',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('439',plain,
    ( ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['437','438'])).

thf('440',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('441',plain,
    ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('442',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('443',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( v4_orders_2 @ X31 )
      | ~ ( v7_waybel_0 @ X31 )
      | ~ ( l1_waybel_0 @ X31 @ X32 )
      | ~ ( r3_waybel_9 @ X32 @ X31 @ X33 )
      | ( r2_hidden @ X33 @ ( k10_yellow_6 @ X32 @ X31 ) )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X32 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X31 @ X32 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v1_compts_1 @ X32 )
      | ~ ( v8_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t33_waybel_9])).

thf('444',plain,(
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
    inference('sup-',[status(thm)],['442','443'])).

thf('445',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('446',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('447',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('448',plain,(
    l1_pre_topc @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('449',plain,(
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
    inference(demod,[status(thm)],['444','445','446','447','448'])).

thf('450',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['449'])).

thf('451',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['441','450'])).

thf('452',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('453',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('454',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('455',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['451','452','453','454'])).

thf('456',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['455'])).

thf('457',plain,
    ( ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['440','456'])).

thf('458',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['457'])).

thf('459',plain,
    ( ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['323'])).

thf('460',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['458','459'])).

thf('461',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('462',plain,
    ( ( ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['460','461'])).

thf('463',plain,
    ( ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['437','438'])).

thf('464',plain,
    ( ( ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['460','461'])).

thf('465',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X35 ) )
      | ( m1_subset_1 @ ( sk_D_2 @ X35 ) @ ( u1_struct_0 @ X35 ) )
      | ~ ( v11_waybel_0 @ X36 @ X35 )
      | ~ ( r3_waybel_9 @ X35 @ X36 @ X34 )
      | ( X34
        = ( k1_waybel_9 @ X35 @ X36 ) )
      | ~ ( l1_waybel_0 @ X36 @ X35 )
      | ~ ( v7_waybel_0 @ X36 )
      | ~ ( v4_orders_2 @ X36 )
      | ( v2_struct_0 @ X36 )
      | ~ ( l1_waybel_9 @ X35 )
      | ~ ( v1_compts_1 @ X35 )
      | ~ ( v2_lattice3 @ X35 )
      | ~ ( v1_lattice3 @ X35 )
      | ~ ( v5_orders_2 @ X35 )
      | ~ ( v4_orders_2 @ X35 )
      | ~ ( v3_orders_2 @ X35 )
      | ~ ( v8_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t36_waybel_9])).

thf('466',plain,
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
    inference('sup-',[status(thm)],['464','465'])).

thf('467',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('468',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('469',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('470',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('471',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('472',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('473',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('474',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('475',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('476',plain,
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
    inference(demod,[status(thm)],['466','467','468','469','470','471','472','473','474','475'])).

thf('477',plain,
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
    inference('sup-',[status(thm)],['463','476'])).

thf('478',plain,(
    v11_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('479',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('480',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('481',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('482',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( sk_D_1 @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['477','478','479','480','481'])).

thf('483',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( ( sk_D_1 @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['482'])).

thf('484',plain,(
    ! [X37: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X37 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('485',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( sk_D_1 @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_D_2 @ sk_A ) ) @ sk_A @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['483','484'])).

thf('486',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X35 ) )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X35 @ ( sk_D_2 @ X35 ) ) @ X35 @ X35 )
      | ~ ( v11_waybel_0 @ X36 @ X35 )
      | ~ ( r3_waybel_9 @ X35 @ X36 @ X34 )
      | ( X34
        = ( k1_waybel_9 @ X35 @ X36 ) )
      | ~ ( l1_waybel_0 @ X36 @ X35 )
      | ~ ( v7_waybel_0 @ X36 )
      | ~ ( v4_orders_2 @ X36 )
      | ( v2_struct_0 @ X36 )
      | ~ ( l1_waybel_9 @ X35 )
      | ~ ( v1_compts_1 @ X35 )
      | ~ ( v2_lattice3 @ X35 )
      | ~ ( v1_lattice3 @ X35 )
      | ~ ( v5_orders_2 @ X35 )
      | ~ ( v4_orders_2 @ X35 )
      | ~ ( v3_orders_2 @ X35 )
      | ~ ( v8_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t36_waybel_9])).

thf('487',plain,
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
    inference('sup-',[status(thm)],['485','486'])).

thf('488',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('489',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('490',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('491',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('492',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('493',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('494',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('495',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('496',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('497',plain,
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
    inference(demod,[status(thm)],['487','488','489','490','491','492','493','494','495','496'])).

thf('498',plain,
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
    inference('sup-',[status(thm)],['462','497'])).

thf('499',plain,
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
    inference(simplify,[status(thm)],['498'])).

thf('500',plain,
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
    inference('sup-',[status(thm)],['439','499'])).

thf('501',plain,(
    v11_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('502',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('503',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('504',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('505',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_1 @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( ( sk_D_1 @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['500','501','502','503','504'])).

thf('506',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( ( sk_D_1 @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['505'])).

thf('507',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('508',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( sk_D_1 @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ sk_B ) ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['506','507'])).

thf('509',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('510',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('511',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( v4_orders_2 @ X31 )
      | ~ ( v7_waybel_0 @ X31 )
      | ~ ( l1_waybel_0 @ X31 @ X32 )
      | ~ ( r3_waybel_9 @ X32 @ X31 @ X33 )
      | ( r2_hidden @ X33 @ ( k10_yellow_6 @ X32 @ X31 ) )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X32 ) )
      | ( ( sk_C_1 @ X31 @ X32 )
       != ( sk_D_1 @ X31 @ X32 ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v1_compts_1 @ X32 )
      | ~ ( v8_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t33_waybel_9])).

thf('512',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v8_pre_topc @ sk_A )
      | ~ ( v1_compts_1 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( ( sk_C_1 @ X0 @ sk_A )
       != ( sk_D_1 @ X0 @ sk_A ) )
      | ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['510','511'])).

thf('513',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('514',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('515',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('516',plain,(
    l1_pre_topc @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('517',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_C_1 @ X0 @ sk_A )
       != ( sk_D_1 @ X0 @ sk_A ) )
      | ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['512','513','514','515','516'])).

thf('518',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ( ( sk_C_1 @ X0 @ sk_A )
       != ( sk_D_1 @ X0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['517'])).

thf('519',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_C_1 @ sk_B @ sk_A )
     != ( sk_D_1 @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['509','518'])).

thf('520',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('521',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('522',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('523',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_C_1 @ sk_B @ sk_A )
     != ( sk_D_1 @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['519','520','521','522'])).

thf('524',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( ( sk_C_1 @ sk_B @ sk_A )
     != ( sk_D_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['523'])).

thf('525',plain,
    ( ( ( ( sk_C_1 @ sk_B @ sk_A )
       != ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['508','524'])).

thf('526',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_C_1 @ sk_B @ sk_A )
       != ( k1_waybel_9 @ sk_A @ sk_B ) ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['525'])).

thf('527',plain,
    ( ( ( ( k1_waybel_9 @ sk_A @ sk_B )
       != ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['416','526'])).

thf('528',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['527'])).

thf('529',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('530',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['528','529'])).

thf('531',plain,
    ( ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['323'])).

thf('532',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['530','531'])).

thf(cc1_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('533',plain,(
    ! [X0: $i] :
      ( ~ ( v1_lattice3 @ X0 )
      | ~ ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattice3])).

thf('534',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['532','533'])).

thf('535',plain,(
    l1_orders_2 @ sk_A ),
    inference('sup-',[status(thm)],['140','141'])).

thf('536',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('537',plain,(
    r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['534','535','536'])).

thf('538',plain,
    ( ~ ( r2_waybel_9 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['323'])).

thf('539',plain,(
    ~ ( r2_waybel_9 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['537','538'])).

thf('540',plain,(
    ~ ( r2_waybel_9 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['324','539'])).

thf('541',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['322','540'])).

thf('542',plain,(
    ! [X0: $i] :
      ( ~ ( v1_lattice3 @ X0 )
      | ~ ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattice3])).

thf('543',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A ) ),
    inference('sup-',[status(thm)],['541','542'])).

thf('544',plain,(
    l1_orders_2 @ sk_A ),
    inference('sup-',[status(thm)],['140','141'])).

thf('545',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('546',plain,(
    $false ),
    inference(demod,[status(thm)],['543','544','545'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Qa1F2G7EIq
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:58:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 20.41/20.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 20.41/20.61  % Solved by: fo/fo7.sh
% 20.41/20.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 20.41/20.61  % done 4885 iterations in 20.134s
% 20.41/20.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 20.41/20.61  % SZS output start Refutation
% 20.41/20.61  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 20.41/20.61  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 20.41/20.61  thf(r2_waybel_9_type, type, r2_waybel_9: $i > $i > $o).
% 20.41/20.61  thf(l1_waybel_9_type, type, l1_waybel_9: $i > $o).
% 20.41/20.61  thf(r2_yellow_0_type, type, r2_yellow_0: $i > $i > $o).
% 20.41/20.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 20.41/20.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 20.41/20.61  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 20.41/20.61  thf(sk_E_type, type, sk_E: $i > $i).
% 20.41/20.61  thf(r3_waybel_9_type, type, r3_waybel_9: $i > $i > $i > $o).
% 20.41/20.61  thf(k4_waybel_1_type, type, k4_waybel_1: $i > $i > $i).
% 20.41/20.61  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 20.41/20.61  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 20.41/20.61  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 20.41/20.61  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 20.41/20.61  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 20.41/20.61  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 20.41/20.61  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 20.41/20.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 20.41/20.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 20.41/20.61  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 20.41/20.61  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 20.41/20.61  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 20.41/20.61  thf(k2_yellow_0_type, type, k2_yellow_0: $i > $i > $i).
% 20.41/20.61  thf(k10_yellow_6_type, type, k10_yellow_6: $i > $i > $i).
% 20.41/20.61  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 20.41/20.61  thf(u1_waybel_0_type, type, u1_waybel_0: $i > $i > $i).
% 20.41/20.61  thf(sk_E_1_type, type, sk_E_1: $i > $i).
% 20.41/20.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 20.41/20.61  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 20.41/20.61  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 20.41/20.61  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 20.41/20.61  thf(sk_B_type, type, sk_B: $i).
% 20.41/20.61  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 20.41/20.61  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 20.41/20.61  thf(v11_waybel_0_type, type, v11_waybel_0: $i > $i > $o).
% 20.41/20.61  thf(sk_A_type, type, sk_A: $i).
% 20.41/20.61  thf(v1_compts_1_type, type, v1_compts_1: $i > $o).
% 20.41/20.61  thf(k1_waybel_9_type, type, k1_waybel_9: $i > $i > $i).
% 20.41/20.61  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 20.41/20.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 20.41/20.61  thf(sk_D_2_type, type, sk_D_2: $i > $i).
% 20.41/20.61  thf(t39_waybel_9, conjecture,
% 20.41/20.61    (![A:$i]:
% 20.41/20.61     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 20.41/20.61         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 20.41/20.61         ( v2_lattice3 @ A ) & ( v1_compts_1 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 20.41/20.61       ( ( ![B:$i]:
% 20.41/20.61           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 20.41/20.61             ( v5_pre_topc @ ( k4_waybel_1 @ A @ B ) @ A @ A ) ) ) =>
% 20.41/20.61         ( ![B:$i]:
% 20.41/20.61           ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 20.41/20.61               ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 20.41/20.61             ( ( v11_waybel_0 @ B @ A ) =>
% 20.41/20.61               ( ( r2_waybel_9 @ A @ B ) & 
% 20.41/20.61                 ( r2_hidden @
% 20.41/20.61                   ( k1_waybel_9 @ A @ B ) @ ( k10_yellow_6 @ A @ B ) ) ) ) ) ) ) ))).
% 20.41/20.61  thf(zf_stmt_0, negated_conjecture,
% 20.41/20.61    (~( ![A:$i]:
% 20.41/20.61        ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 20.41/20.61            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 20.41/20.61            ( v2_lattice3 @ A ) & ( v1_compts_1 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 20.41/20.61          ( ( ![B:$i]:
% 20.41/20.61              ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 20.41/20.61                ( v5_pre_topc @ ( k4_waybel_1 @ A @ B ) @ A @ A ) ) ) =>
% 20.41/20.61            ( ![B:$i]:
% 20.41/20.61              ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 20.41/20.61                  ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 20.41/20.61                ( ( v11_waybel_0 @ B @ A ) =>
% 20.41/20.61                  ( ( r2_waybel_9 @ A @ B ) & 
% 20.41/20.61                    ( r2_hidden @
% 20.41/20.61                      ( k1_waybel_9 @ A @ B ) @ ( k10_yellow_6 @ A @ B ) ) ) ) ) ) ) ) )),
% 20.41/20.61    inference('cnf.neg', [status(esa)], [t39_waybel_9])).
% 20.41/20.61  thf('0', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf(t30_waybel_9, axiom,
% 20.41/20.61    (![A:$i]:
% 20.41/20.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 20.41/20.61         ( v8_pre_topc @ A ) & ( v1_compts_1 @ A ) & ( l1_pre_topc @ A ) ) =>
% 20.41/20.61       ( ![B:$i]:
% 20.41/20.61         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 20.41/20.61             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 20.41/20.61           ( ?[C:$i]:
% 20.41/20.61             ( ( r3_waybel_9 @ A @ B @ C ) & 
% 20.41/20.61               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 20.41/20.61  thf('1', plain,
% 20.41/20.61      (![X29 : $i, X30 : $i]:
% 20.41/20.61         ((v2_struct_0 @ X29)
% 20.41/20.61          | ~ (v4_orders_2 @ X29)
% 20.41/20.61          | ~ (v7_waybel_0 @ X29)
% 20.41/20.61          | ~ (l1_waybel_0 @ X29 @ X30)
% 20.41/20.61          | (r3_waybel_9 @ X30 @ X29 @ (sk_C @ X29 @ X30))
% 20.41/20.61          | ~ (l1_pre_topc @ X30)
% 20.41/20.61          | ~ (v1_compts_1 @ X30)
% 20.41/20.61          | ~ (v8_pre_topc @ X30)
% 20.41/20.61          | ~ (v2_pre_topc @ X30)
% 20.41/20.61          | (v2_struct_0 @ X30))),
% 20.41/20.61      inference('cnf', [status(esa)], [t30_waybel_9])).
% 20.41/20.61  thf('2', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_A)
% 20.41/20.61        | ~ (v2_pre_topc @ sk_A)
% 20.41/20.61        | ~ (v8_pre_topc @ sk_A)
% 20.41/20.61        | ~ (v1_compts_1 @ sk_A)
% 20.41/20.61        | ~ (l1_pre_topc @ sk_A)
% 20.41/20.61        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 20.41/20.61        | ~ (v7_waybel_0 @ sk_B)
% 20.41/20.61        | ~ (v4_orders_2 @ sk_B)
% 20.41/20.61        | (v2_struct_0 @ sk_B))),
% 20.41/20.61      inference('sup-', [status(thm)], ['0', '1'])).
% 20.41/20.61  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('4', plain, ((v8_pre_topc @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('5', plain, ((v1_compts_1 @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('6', plain, ((l1_waybel_9 @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf(dt_l1_waybel_9, axiom,
% 20.41/20.61    (![A:$i]:
% 20.41/20.61     ( ( l1_waybel_9 @ A ) => ( ( l1_pre_topc @ A ) & ( l1_orders_2 @ A ) ) ))).
% 20.41/20.61  thf('7', plain, (![X19 : $i]: ((l1_pre_topc @ X19) | ~ (l1_waybel_9 @ X19))),
% 20.41/20.61      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 20.41/20.61  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 20.41/20.61      inference('sup-', [status(thm)], ['6', '7'])).
% 20.41/20.61  thf('9', plain, ((v7_waybel_0 @ sk_B)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('10', plain, ((v4_orders_2 @ sk_B)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('11', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_A)
% 20.41/20.61        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 20.41/20.61        | (v2_struct_0 @ sk_B))),
% 20.41/20.61      inference('demod', [status(thm)], ['2', '3', '4', '5', '8', '9', '10'])).
% 20.41/20.61  thf('12', plain, (~ (v2_struct_0 @ sk_B)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('13', plain,
% 20.41/20.61      (((r3_waybel_9 @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 20.41/20.61        | (v2_struct_0 @ sk_A))),
% 20.41/20.61      inference('clc', [status(thm)], ['11', '12'])).
% 20.41/20.61  thf('14', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('15', plain,
% 20.41/20.61      (![X29 : $i, X30 : $i]:
% 20.41/20.61         ((v2_struct_0 @ X29)
% 20.41/20.61          | ~ (v4_orders_2 @ X29)
% 20.41/20.61          | ~ (v7_waybel_0 @ X29)
% 20.41/20.61          | ~ (l1_waybel_0 @ X29 @ X30)
% 20.41/20.61          | (m1_subset_1 @ (sk_C @ X29 @ X30) @ (u1_struct_0 @ X30))
% 20.41/20.61          | ~ (l1_pre_topc @ X30)
% 20.41/20.61          | ~ (v1_compts_1 @ X30)
% 20.41/20.61          | ~ (v8_pre_topc @ X30)
% 20.41/20.61          | ~ (v2_pre_topc @ X30)
% 20.41/20.61          | (v2_struct_0 @ X30))),
% 20.41/20.61      inference('cnf', [status(esa)], [t30_waybel_9])).
% 20.41/20.61  thf('16', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_A)
% 20.41/20.61        | ~ (v2_pre_topc @ sk_A)
% 20.41/20.61        | ~ (v8_pre_topc @ sk_A)
% 20.41/20.61        | ~ (v1_compts_1 @ sk_A)
% 20.41/20.61        | ~ (l1_pre_topc @ sk_A)
% 20.41/20.61        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61        | ~ (v7_waybel_0 @ sk_B)
% 20.41/20.61        | ~ (v4_orders_2 @ sk_B)
% 20.41/20.61        | (v2_struct_0 @ sk_B))),
% 20.41/20.61      inference('sup-', [status(thm)], ['14', '15'])).
% 20.41/20.61  thf('17', plain, ((v2_pre_topc @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('18', plain, ((v8_pre_topc @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('19', plain, ((v1_compts_1 @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 20.41/20.61      inference('sup-', [status(thm)], ['6', '7'])).
% 20.41/20.61  thf('21', plain, ((v7_waybel_0 @ sk_B)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('22', plain, ((v4_orders_2 @ sk_B)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('23', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_A)
% 20.41/20.61        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61        | (v2_struct_0 @ sk_B))),
% 20.41/20.61      inference('demod', [status(thm)],
% 20.41/20.61                ['16', '17', '18', '19', '20', '21', '22'])).
% 20.41/20.61  thf('24', plain, (~ (v2_struct_0 @ sk_B)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('25', plain,
% 20.41/20.61      (((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61        | (v2_struct_0 @ sk_A))),
% 20.41/20.61      inference('clc', [status(thm)], ['23', '24'])).
% 20.41/20.61  thf('26', plain,
% 20.41/20.61      (((r3_waybel_9 @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 20.41/20.61        | (v2_struct_0 @ sk_A))),
% 20.41/20.61      inference('clc', [status(thm)], ['11', '12'])).
% 20.41/20.61  thf('27', plain,
% 20.41/20.61      (((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61        | (v2_struct_0 @ sk_A))),
% 20.41/20.61      inference('clc', [status(thm)], ['23', '24'])).
% 20.41/20.61  thf(t36_waybel_9, axiom,
% 20.41/20.61    (![A:$i]:
% 20.41/20.61     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 20.41/20.61         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 20.41/20.61         ( v2_lattice3 @ A ) & ( v1_compts_1 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 20.41/20.61       ( ![B:$i]:
% 20.41/20.61         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 20.41/20.61           ( ![C:$i]:
% 20.41/20.61             ( ( ( ~( v2_struct_0 @ C ) ) & ( v4_orders_2 @ C ) & 
% 20.41/20.61                 ( v7_waybel_0 @ C ) & ( l1_waybel_0 @ C @ A ) ) =>
% 20.41/20.61               ( ( ( ![D:$i]:
% 20.41/20.61                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 20.41/20.61                       ( v5_pre_topc @ ( k4_waybel_1 @ A @ D ) @ A @ A ) ) ) & 
% 20.41/20.61                   ( v11_waybel_0 @ C @ A ) & ( r3_waybel_9 @ A @ C @ B ) ) =>
% 20.41/20.61                 ( ( B ) = ( k1_waybel_9 @ A @ C ) ) ) ) ) ) ) ))).
% 20.41/20.61  thf('28', plain,
% 20.41/20.61      (![X34 : $i, X35 : $i, X36 : $i]:
% 20.41/20.61         (~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X35))
% 20.41/20.61          | (m1_subset_1 @ (sk_D_2 @ X35) @ (u1_struct_0 @ X35))
% 20.41/20.61          | ~ (v11_waybel_0 @ X36 @ X35)
% 20.41/20.61          | ~ (r3_waybel_9 @ X35 @ X36 @ X34)
% 20.41/20.61          | ((X34) = (k1_waybel_9 @ X35 @ X36))
% 20.41/20.61          | ~ (l1_waybel_0 @ X36 @ X35)
% 20.41/20.61          | ~ (v7_waybel_0 @ X36)
% 20.41/20.61          | ~ (v4_orders_2 @ X36)
% 20.41/20.61          | (v2_struct_0 @ X36)
% 20.41/20.61          | ~ (l1_waybel_9 @ X35)
% 20.41/20.61          | ~ (v1_compts_1 @ X35)
% 20.41/20.61          | ~ (v2_lattice3 @ X35)
% 20.41/20.61          | ~ (v1_lattice3 @ X35)
% 20.41/20.61          | ~ (v5_orders_2 @ X35)
% 20.41/20.61          | ~ (v4_orders_2 @ X35)
% 20.41/20.61          | ~ (v3_orders_2 @ X35)
% 20.41/20.61          | ~ (v8_pre_topc @ X35)
% 20.41/20.61          | ~ (v2_pre_topc @ X35))),
% 20.41/20.61      inference('cnf', [status(esa)], [t36_waybel_9])).
% 20.41/20.61  thf('29', plain,
% 20.41/20.61      (![X0 : $i]:
% 20.41/20.61         ((v2_struct_0 @ sk_A)
% 20.41/20.61          | ~ (v2_pre_topc @ sk_A)
% 20.41/20.61          | ~ (v8_pre_topc @ sk_A)
% 20.41/20.61          | ~ (v3_orders_2 @ sk_A)
% 20.41/20.61          | ~ (v4_orders_2 @ sk_A)
% 20.41/20.61          | ~ (v5_orders_2 @ sk_A)
% 20.41/20.61          | ~ (v1_lattice3 @ sk_A)
% 20.41/20.61          | ~ (v2_lattice3 @ sk_A)
% 20.41/20.61          | ~ (v1_compts_1 @ sk_A)
% 20.41/20.61          | ~ (l1_waybel_9 @ sk_A)
% 20.41/20.61          | (v2_struct_0 @ X0)
% 20.41/20.61          | ~ (v4_orders_2 @ X0)
% 20.41/20.61          | ~ (v7_waybel_0 @ X0)
% 20.41/20.61          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 20.41/20.61          | ((sk_C @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ X0))
% 20.41/20.61          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B @ sk_A))
% 20.41/20.61          | ~ (v11_waybel_0 @ X0 @ sk_A)
% 20.41/20.61          | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 20.41/20.61      inference('sup-', [status(thm)], ['27', '28'])).
% 20.41/20.61  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('31', plain, ((v8_pre_topc @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('32', plain, ((v3_orders_2 @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('33', plain, ((v4_orders_2 @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('34', plain, ((v5_orders_2 @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('35', plain, ((v1_lattice3 @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('36', plain, ((v2_lattice3 @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('37', plain, ((v1_compts_1 @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('38', plain, ((l1_waybel_9 @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('39', plain,
% 20.41/20.61      (![X0 : $i]:
% 20.41/20.61         ((v2_struct_0 @ sk_A)
% 20.41/20.61          | (v2_struct_0 @ X0)
% 20.41/20.61          | ~ (v4_orders_2 @ X0)
% 20.41/20.61          | ~ (v7_waybel_0 @ X0)
% 20.41/20.61          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 20.41/20.61          | ((sk_C @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ X0))
% 20.41/20.61          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B @ sk_A))
% 20.41/20.61          | ~ (v11_waybel_0 @ X0 @ sk_A)
% 20.41/20.61          | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 20.41/20.61      inference('demod', [status(thm)],
% 20.41/20.61                ['29', '30', '31', '32', '33', '34', '35', '36', '37', '38'])).
% 20.41/20.61  thf('40', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_A)
% 20.41/20.61        | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61        | ~ (v11_waybel_0 @ sk_B @ sk_A)
% 20.41/20.61        | ((sk_C @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.61        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 20.41/20.61        | ~ (v7_waybel_0 @ sk_B)
% 20.41/20.61        | ~ (v4_orders_2 @ sk_B)
% 20.41/20.61        | (v2_struct_0 @ sk_B)
% 20.41/20.61        | (v2_struct_0 @ sk_A))),
% 20.41/20.61      inference('sup-', [status(thm)], ['26', '39'])).
% 20.41/20.61  thf('41', plain, ((v11_waybel_0 @ sk_B @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('42', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('43', plain, ((v7_waybel_0 @ sk_B)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('44', plain, ((v4_orders_2 @ sk_B)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('45', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_A)
% 20.41/20.61        | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61        | ((sk_C @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.61        | (v2_struct_0 @ sk_B)
% 20.41/20.61        | (v2_struct_0 @ sk_A))),
% 20.41/20.61      inference('demod', [status(thm)], ['40', '41', '42', '43', '44'])).
% 20.41/20.61  thf('46', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_B)
% 20.41/20.61        | ((sk_C @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.61        | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61        | (v2_struct_0 @ sk_A))),
% 20.41/20.61      inference('simplify', [status(thm)], ['45'])).
% 20.41/20.61  thf('47', plain,
% 20.41/20.61      (![X37 : $i]:
% 20.41/20.61         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X37) @ sk_A @ sk_A)
% 20.41/20.61          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A)))),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('48', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_A)
% 20.41/20.61        | ((sk_C @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.61        | (v2_struct_0 @ sk_B)
% 20.41/20.61        | (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_D_2 @ sk_A)) @ sk_A @ sk_A))),
% 20.41/20.61      inference('sup-', [status(thm)], ['46', '47'])).
% 20.41/20.61  thf('49', plain,
% 20.41/20.61      (![X34 : $i, X35 : $i, X36 : $i]:
% 20.41/20.61         (~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X35))
% 20.41/20.61          | ~ (v5_pre_topc @ (k4_waybel_1 @ X35 @ (sk_D_2 @ X35)) @ X35 @ X35)
% 20.41/20.61          | ~ (v11_waybel_0 @ X36 @ X35)
% 20.41/20.61          | ~ (r3_waybel_9 @ X35 @ X36 @ X34)
% 20.41/20.61          | ((X34) = (k1_waybel_9 @ X35 @ X36))
% 20.41/20.61          | ~ (l1_waybel_0 @ X36 @ X35)
% 20.41/20.61          | ~ (v7_waybel_0 @ X36)
% 20.41/20.61          | ~ (v4_orders_2 @ X36)
% 20.41/20.61          | (v2_struct_0 @ X36)
% 20.41/20.61          | ~ (l1_waybel_9 @ X35)
% 20.41/20.61          | ~ (v1_compts_1 @ X35)
% 20.41/20.61          | ~ (v2_lattice3 @ X35)
% 20.41/20.61          | ~ (v1_lattice3 @ X35)
% 20.41/20.61          | ~ (v5_orders_2 @ X35)
% 20.41/20.61          | ~ (v4_orders_2 @ X35)
% 20.41/20.61          | ~ (v3_orders_2 @ X35)
% 20.41/20.61          | ~ (v8_pre_topc @ X35)
% 20.41/20.61          | ~ (v2_pre_topc @ X35))),
% 20.41/20.61      inference('cnf', [status(esa)], [t36_waybel_9])).
% 20.41/20.61  thf('50', plain,
% 20.41/20.61      (![X0 : $i, X1 : $i]:
% 20.41/20.61         ((v2_struct_0 @ sk_B)
% 20.41/20.61          | ((sk_C @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.61          | (v2_struct_0 @ sk_A)
% 20.41/20.61          | ~ (v2_pre_topc @ sk_A)
% 20.41/20.61          | ~ (v8_pre_topc @ sk_A)
% 20.41/20.61          | ~ (v3_orders_2 @ sk_A)
% 20.41/20.61          | ~ (v4_orders_2 @ sk_A)
% 20.41/20.61          | ~ (v5_orders_2 @ sk_A)
% 20.41/20.61          | ~ (v1_lattice3 @ sk_A)
% 20.41/20.61          | ~ (v2_lattice3 @ sk_A)
% 20.41/20.61          | ~ (v1_compts_1 @ sk_A)
% 20.41/20.61          | ~ (l1_waybel_9 @ sk_A)
% 20.41/20.61          | (v2_struct_0 @ X0)
% 20.41/20.61          | ~ (v4_orders_2 @ X0)
% 20.41/20.61          | ~ (v7_waybel_0 @ X0)
% 20.41/20.61          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 20.41/20.61          | ((X1) = (k1_waybel_9 @ sk_A @ X0))
% 20.41/20.61          | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 20.41/20.61          | ~ (v11_waybel_0 @ X0 @ sk_A)
% 20.41/20.61          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 20.41/20.61      inference('sup-', [status(thm)], ['48', '49'])).
% 20.41/20.61  thf('51', plain, ((v2_pre_topc @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('52', plain, ((v8_pre_topc @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('53', plain, ((v3_orders_2 @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('54', plain, ((v4_orders_2 @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('55', plain, ((v5_orders_2 @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('56', plain, ((v1_lattice3 @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('57', plain, ((v2_lattice3 @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('58', plain, ((v1_compts_1 @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('59', plain, ((l1_waybel_9 @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('60', plain,
% 20.41/20.61      (![X0 : $i, X1 : $i]:
% 20.41/20.61         ((v2_struct_0 @ sk_B)
% 20.41/20.61          | ((sk_C @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.61          | (v2_struct_0 @ sk_A)
% 20.41/20.61          | (v2_struct_0 @ X0)
% 20.41/20.61          | ~ (v4_orders_2 @ X0)
% 20.41/20.61          | ~ (v7_waybel_0 @ X0)
% 20.41/20.61          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 20.41/20.61          | ((X1) = (k1_waybel_9 @ sk_A @ X0))
% 20.41/20.61          | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 20.41/20.61          | ~ (v11_waybel_0 @ X0 @ sk_A)
% 20.41/20.61          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 20.41/20.61      inference('demod', [status(thm)],
% 20.41/20.61                ['50', '51', '52', '53', '54', '55', '56', '57', '58', '59'])).
% 20.41/20.61  thf('61', plain,
% 20.41/20.61      (![X0 : $i]:
% 20.41/20.61         ((v2_struct_0 @ sk_A)
% 20.41/20.61          | ~ (v11_waybel_0 @ X0 @ sk_A)
% 20.41/20.61          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B @ sk_A))
% 20.41/20.61          | ((sk_C @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ X0))
% 20.41/20.61          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 20.41/20.61          | ~ (v7_waybel_0 @ X0)
% 20.41/20.61          | ~ (v4_orders_2 @ X0)
% 20.41/20.61          | (v2_struct_0 @ X0)
% 20.41/20.61          | (v2_struct_0 @ sk_A)
% 20.41/20.61          | ((sk_C @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.61          | (v2_struct_0 @ sk_B))),
% 20.41/20.61      inference('sup-', [status(thm)], ['25', '60'])).
% 20.41/20.61  thf('62', plain,
% 20.41/20.61      (![X0 : $i]:
% 20.41/20.61         ((v2_struct_0 @ sk_B)
% 20.41/20.61          | ((sk_C @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.61          | (v2_struct_0 @ X0)
% 20.41/20.61          | ~ (v4_orders_2 @ X0)
% 20.41/20.61          | ~ (v7_waybel_0 @ X0)
% 20.41/20.61          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 20.41/20.61          | ((sk_C @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ X0))
% 20.41/20.61          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B @ sk_A))
% 20.41/20.61          | ~ (v11_waybel_0 @ X0 @ sk_A)
% 20.41/20.61          | (v2_struct_0 @ sk_A))),
% 20.41/20.61      inference('simplify', [status(thm)], ['61'])).
% 20.41/20.61  thf('63', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_A)
% 20.41/20.61        | (v2_struct_0 @ sk_A)
% 20.41/20.61        | ~ (v11_waybel_0 @ sk_B @ sk_A)
% 20.41/20.61        | ((sk_C @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.61        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 20.41/20.61        | ~ (v7_waybel_0 @ sk_B)
% 20.41/20.61        | ~ (v4_orders_2 @ sk_B)
% 20.41/20.61        | (v2_struct_0 @ sk_B)
% 20.41/20.61        | ((sk_C @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.61        | (v2_struct_0 @ sk_B))),
% 20.41/20.61      inference('sup-', [status(thm)], ['13', '62'])).
% 20.41/20.61  thf('64', plain, ((v11_waybel_0 @ sk_B @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('65', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('66', plain, ((v7_waybel_0 @ sk_B)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('67', plain, ((v4_orders_2 @ sk_B)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('68', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_A)
% 20.41/20.61        | (v2_struct_0 @ sk_A)
% 20.41/20.61        | ((sk_C @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.61        | (v2_struct_0 @ sk_B)
% 20.41/20.61        | ((sk_C @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.61        | (v2_struct_0 @ sk_B))),
% 20.41/20.61      inference('demod', [status(thm)], ['63', '64', '65', '66', '67'])).
% 20.41/20.61  thf('69', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_B)
% 20.41/20.61        | ((sk_C @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.61        | (v2_struct_0 @ sk_A))),
% 20.41/20.61      inference('simplify', [status(thm)], ['68'])).
% 20.41/20.61  thf('70', plain, (~ (v2_struct_0 @ sk_B)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('71', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_A)
% 20.41/20.61        | ((sk_C @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B)))),
% 20.41/20.61      inference('clc', [status(thm)], ['69', '70'])).
% 20.41/20.61  thf('72', plain,
% 20.41/20.61      (((r3_waybel_9 @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 20.41/20.61        | (v2_struct_0 @ sk_A))),
% 20.41/20.61      inference('clc', [status(thm)], ['11', '12'])).
% 20.41/20.61  thf('73', plain,
% 20.41/20.61      (((r3_waybel_9 @ sk_A @ sk_B @ (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.61        | (v2_struct_0 @ sk_A)
% 20.41/20.61        | (v2_struct_0 @ sk_A))),
% 20.41/20.61      inference('sup+', [status(thm)], ['71', '72'])).
% 20.41/20.61  thf('74', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_A)
% 20.41/20.61        | (r3_waybel_9 @ sk_A @ sk_B @ (k1_waybel_9 @ sk_A @ sk_B)))),
% 20.41/20.61      inference('simplify', [status(thm)], ['73'])).
% 20.41/20.61  thf('75', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_A)
% 20.41/20.61        | ((sk_C @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B)))),
% 20.41/20.61      inference('clc', [status(thm)], ['69', '70'])).
% 20.41/20.61  thf('76', plain,
% 20.41/20.61      (((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61        | (v2_struct_0 @ sk_A))),
% 20.41/20.61      inference('clc', [status(thm)], ['23', '24'])).
% 20.41/20.61  thf('77', plain,
% 20.41/20.61      (((m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 20.41/20.61        | (v2_struct_0 @ sk_A)
% 20.41/20.61        | (v2_struct_0 @ sk_A))),
% 20.41/20.61      inference('sup+', [status(thm)], ['75', '76'])).
% 20.41/20.61  thf('78', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_A)
% 20.41/20.61        | (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 20.41/20.61      inference('simplify', [status(thm)], ['77'])).
% 20.41/20.61  thf('79', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_A)
% 20.41/20.61        | ((sk_C @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B)))),
% 20.41/20.61      inference('clc', [status(thm)], ['69', '70'])).
% 20.41/20.61  thf('80', plain,
% 20.41/20.61      (((r3_waybel_9 @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 20.41/20.61        | (v2_struct_0 @ sk_A))),
% 20.41/20.61      inference('clc', [status(thm)], ['11', '12'])).
% 20.41/20.61  thf('81', plain,
% 20.41/20.61      (((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61        | (v2_struct_0 @ sk_A))),
% 20.41/20.61      inference('clc', [status(thm)], ['23', '24'])).
% 20.41/20.61  thf(l51_waybel_9, axiom,
% 20.41/20.61    (![A:$i]:
% 20.41/20.61     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 20.41/20.61         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 20.41/20.61         ( v2_lattice3 @ A ) & ( v1_compts_1 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 20.41/20.61       ( ![B:$i]:
% 20.41/20.61         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 20.41/20.61             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 20.41/20.61           ( ![C:$i]:
% 20.41/20.61             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 20.41/20.61               ( ![D:$i]:
% 20.41/20.61                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 20.41/20.61                   ( ( ( ( C ) = ( D ) ) & 
% 20.41/20.61                       ( ![E:$i]:
% 20.41/20.61                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 20.41/20.61                           ( v5_pre_topc @ ( k4_waybel_1 @ A @ E ) @ A @ A ) ) ) & 
% 20.41/20.61                       ( v11_waybel_0 @ B @ A ) & ( r3_waybel_9 @ A @ B @ C ) ) =>
% 20.41/20.61                     ( r1_lattice3 @
% 20.41/20.61                       A @ 
% 20.41/20.61                       ( k2_relset_1 @
% 20.41/20.61                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 20.41/20.61                         ( u1_waybel_0 @ A @ B ) ) @ 
% 20.41/20.61                       D ) ) ) ) ) ) ) ) ))).
% 20.41/20.61  thf('82', plain,
% 20.41/20.61      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 20.41/20.61         ((v2_struct_0 @ X20)
% 20.41/20.61          | ~ (v4_orders_2 @ X20)
% 20.41/20.61          | ~ (v7_waybel_0 @ X20)
% 20.41/20.61          | ~ (l1_waybel_0 @ X20 @ X21)
% 20.41/20.61          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 20.41/20.61          | (r1_lattice3 @ X21 @ 
% 20.41/20.61             (k2_relset_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X21) @ 
% 20.41/20.61              (u1_waybel_0 @ X21 @ X20)) @ 
% 20.41/20.61             X22)
% 20.41/20.61          | ((X23) != (X22))
% 20.41/20.61          | ~ (r3_waybel_9 @ X21 @ X20 @ X23)
% 20.41/20.61          | ~ (v11_waybel_0 @ X20 @ X21)
% 20.41/20.61          | (m1_subset_1 @ (sk_E @ X21) @ (u1_struct_0 @ X21))
% 20.41/20.61          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X21))
% 20.41/20.61          | ~ (l1_waybel_9 @ X21)
% 20.41/20.61          | ~ (v1_compts_1 @ X21)
% 20.41/20.61          | ~ (v2_lattice3 @ X21)
% 20.41/20.61          | ~ (v1_lattice3 @ X21)
% 20.41/20.61          | ~ (v5_orders_2 @ X21)
% 20.41/20.61          | ~ (v4_orders_2 @ X21)
% 20.41/20.61          | ~ (v3_orders_2 @ X21)
% 20.41/20.61          | ~ (v8_pre_topc @ X21)
% 20.41/20.61          | ~ (v2_pre_topc @ X21))),
% 20.41/20.61      inference('cnf', [status(esa)], [l51_waybel_9])).
% 20.41/20.61  thf('83', plain,
% 20.41/20.61      (![X20 : $i, X21 : $i, X22 : $i]:
% 20.41/20.61         (~ (v2_pre_topc @ X21)
% 20.41/20.61          | ~ (v8_pre_topc @ X21)
% 20.41/20.61          | ~ (v3_orders_2 @ X21)
% 20.41/20.61          | ~ (v4_orders_2 @ X21)
% 20.41/20.61          | ~ (v5_orders_2 @ X21)
% 20.41/20.61          | ~ (v1_lattice3 @ X21)
% 20.41/20.61          | ~ (v2_lattice3 @ X21)
% 20.41/20.61          | ~ (v1_compts_1 @ X21)
% 20.41/20.61          | ~ (l1_waybel_9 @ X21)
% 20.41/20.61          | (m1_subset_1 @ (sk_E @ X21) @ (u1_struct_0 @ X21))
% 20.41/20.61          | ~ (v11_waybel_0 @ X20 @ X21)
% 20.41/20.61          | ~ (r3_waybel_9 @ X21 @ X20 @ X22)
% 20.41/20.61          | (r1_lattice3 @ X21 @ 
% 20.41/20.61             (k2_relset_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X21) @ 
% 20.41/20.61              (u1_waybel_0 @ X21 @ X20)) @ 
% 20.41/20.61             X22)
% 20.41/20.61          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 20.41/20.61          | ~ (l1_waybel_0 @ X20 @ X21)
% 20.41/20.61          | ~ (v7_waybel_0 @ X20)
% 20.41/20.61          | ~ (v4_orders_2 @ X20)
% 20.41/20.61          | (v2_struct_0 @ X20))),
% 20.41/20.61      inference('simplify', [status(thm)], ['82'])).
% 20.41/20.61  thf('84', plain,
% 20.41/20.61      (![X0 : $i]:
% 20.41/20.61         ((v2_struct_0 @ sk_A)
% 20.41/20.61          | (v2_struct_0 @ X0)
% 20.41/20.61          | ~ (v4_orders_2 @ X0)
% 20.41/20.61          | ~ (v7_waybel_0 @ X0)
% 20.41/20.61          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 20.41/20.61          | (r1_lattice3 @ sk_A @ 
% 20.41/20.61             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.61              (u1_waybel_0 @ sk_A @ X0)) @ 
% 20.41/20.61             (sk_C @ sk_B @ sk_A))
% 20.41/20.61          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B @ sk_A))
% 20.41/20.61          | ~ (v11_waybel_0 @ X0 @ sk_A)
% 20.41/20.61          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61          | ~ (l1_waybel_9 @ sk_A)
% 20.41/20.61          | ~ (v1_compts_1 @ sk_A)
% 20.41/20.61          | ~ (v2_lattice3 @ sk_A)
% 20.41/20.61          | ~ (v1_lattice3 @ sk_A)
% 20.41/20.61          | ~ (v5_orders_2 @ sk_A)
% 20.41/20.61          | ~ (v4_orders_2 @ sk_A)
% 20.41/20.61          | ~ (v3_orders_2 @ sk_A)
% 20.41/20.61          | ~ (v8_pre_topc @ sk_A)
% 20.41/20.61          | ~ (v2_pre_topc @ sk_A))),
% 20.41/20.61      inference('sup-', [status(thm)], ['81', '83'])).
% 20.41/20.61  thf('85', plain, ((l1_waybel_9 @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('86', plain, ((v1_compts_1 @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('87', plain, ((v2_lattice3 @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('88', plain, ((v1_lattice3 @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('89', plain, ((v5_orders_2 @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('90', plain, ((v4_orders_2 @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('91', plain, ((v3_orders_2 @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('92', plain, ((v8_pre_topc @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('93', plain, ((v2_pre_topc @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('94', plain,
% 20.41/20.61      (![X0 : $i]:
% 20.41/20.61         ((v2_struct_0 @ sk_A)
% 20.41/20.61          | (v2_struct_0 @ X0)
% 20.41/20.61          | ~ (v4_orders_2 @ X0)
% 20.41/20.61          | ~ (v7_waybel_0 @ X0)
% 20.41/20.61          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 20.41/20.61          | (r1_lattice3 @ sk_A @ 
% 20.41/20.61             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.61              (u1_waybel_0 @ sk_A @ X0)) @ 
% 20.41/20.61             (sk_C @ sk_B @ sk_A))
% 20.41/20.61          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B @ sk_A))
% 20.41/20.61          | ~ (v11_waybel_0 @ X0 @ sk_A)
% 20.41/20.61          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 20.41/20.61      inference('demod', [status(thm)],
% 20.41/20.61                ['84', '85', '86', '87', '88', '89', '90', '91', '92', '93'])).
% 20.41/20.61  thf('95', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_A)
% 20.41/20.61        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61        | ~ (v11_waybel_0 @ sk_B @ sk_A)
% 20.41/20.61        | (r1_lattice3 @ sk_A @ 
% 20.41/20.61           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.61            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.61           (sk_C @ sk_B @ sk_A))
% 20.41/20.61        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 20.41/20.61        | ~ (v7_waybel_0 @ sk_B)
% 20.41/20.61        | ~ (v4_orders_2 @ sk_B)
% 20.41/20.61        | (v2_struct_0 @ sk_B)
% 20.41/20.61        | (v2_struct_0 @ sk_A))),
% 20.41/20.61      inference('sup-', [status(thm)], ['80', '94'])).
% 20.41/20.61  thf('96', plain, ((v11_waybel_0 @ sk_B @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('97', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('98', plain, ((v7_waybel_0 @ sk_B)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('99', plain, ((v4_orders_2 @ sk_B)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('100', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_A)
% 20.41/20.61        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61        | (r1_lattice3 @ sk_A @ 
% 20.41/20.61           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.61            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.61           (sk_C @ sk_B @ sk_A))
% 20.41/20.61        | (v2_struct_0 @ sk_B)
% 20.41/20.61        | (v2_struct_0 @ sk_A))),
% 20.41/20.61      inference('demod', [status(thm)], ['95', '96', '97', '98', '99'])).
% 20.41/20.61  thf('101', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_B)
% 20.41/20.61        | (r1_lattice3 @ sk_A @ 
% 20.41/20.61           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.61            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.61           (sk_C @ sk_B @ sk_A))
% 20.41/20.61        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61        | (v2_struct_0 @ sk_A))),
% 20.41/20.61      inference('simplify', [status(thm)], ['100'])).
% 20.41/20.61  thf('102', plain,
% 20.41/20.61      (((r1_lattice3 @ sk_A @ 
% 20.41/20.61         (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.61          (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.61         (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.61        | (v2_struct_0 @ sk_A)
% 20.41/20.61        | (v2_struct_0 @ sk_A)
% 20.41/20.61        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61        | (v2_struct_0 @ sk_B))),
% 20.41/20.61      inference('sup+', [status(thm)], ['79', '101'])).
% 20.41/20.61  thf('103', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_B)
% 20.41/20.61        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61        | (v2_struct_0 @ sk_A)
% 20.41/20.61        | (r1_lattice3 @ sk_A @ 
% 20.41/20.61           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.61            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.61           (k1_waybel_9 @ sk_A @ sk_B)))),
% 20.41/20.61      inference('simplify', [status(thm)], ['102'])).
% 20.41/20.61  thf('104', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_A)
% 20.41/20.61        | (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 20.41/20.61      inference('simplify', [status(thm)], ['77'])).
% 20.41/20.61  thf('105', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_A)
% 20.41/20.61        | (r3_waybel_9 @ sk_A @ sk_B @ (k1_waybel_9 @ sk_A @ sk_B)))),
% 20.41/20.61      inference('simplify', [status(thm)], ['73'])).
% 20.41/20.61  thf('106', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_B)
% 20.41/20.61        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61        | (v2_struct_0 @ sk_A)
% 20.41/20.61        | (r1_lattice3 @ sk_A @ 
% 20.41/20.61           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.61            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.61           (k1_waybel_9 @ sk_A @ sk_B)))),
% 20.41/20.61      inference('simplify', [status(thm)], ['102'])).
% 20.41/20.61  thf('107', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_B)
% 20.41/20.61        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61        | (v2_struct_0 @ sk_A)
% 20.41/20.61        | (r1_lattice3 @ sk_A @ 
% 20.41/20.61           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.61            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.61           (k1_waybel_9 @ sk_A @ sk_B)))),
% 20.41/20.61      inference('simplify', [status(thm)], ['102'])).
% 20.41/20.61  thf(t31_yellow_0, axiom,
% 20.41/20.61    (![A:$i]:
% 20.41/20.61     ( ( ( l1_orders_2 @ A ) & ( v5_orders_2 @ A ) ) =>
% 20.41/20.61       ( ![B:$i]:
% 20.41/20.61         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 20.41/20.61           ( ![C:$i]:
% 20.41/20.61             ( ( ( ( r2_yellow_0 @ A @ C ) & 
% 20.41/20.61                   ( ( B ) = ( k2_yellow_0 @ A @ C ) ) ) =>
% 20.41/20.61                 ( ( ![D:$i]:
% 20.41/20.61                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 20.41/20.61                       ( ( r1_lattice3 @ A @ C @ D ) =>
% 20.41/20.61                         ( r1_orders_2 @ A @ D @ B ) ) ) ) & 
% 20.41/20.61                   ( r1_lattice3 @ A @ C @ B ) ) ) & 
% 20.41/20.61               ( ( ( ![D:$i]:
% 20.41/20.61                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 20.41/20.61                       ( ( r1_lattice3 @ A @ C @ D ) =>
% 20.41/20.61                         ( r1_orders_2 @ A @ D @ B ) ) ) ) & 
% 20.41/20.61                   ( r1_lattice3 @ A @ C @ B ) ) =>
% 20.41/20.61                 ( ( r2_yellow_0 @ A @ C ) & 
% 20.41/20.61                   ( ( B ) = ( k2_yellow_0 @ A @ C ) ) ) ) ) ) ) ) ))).
% 20.41/20.61  thf(zf_stmt_1, axiom,
% 20.41/20.61    (![D:$i,C:$i,B:$i,A:$i]:
% 20.41/20.61     ( ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 20.41/20.61         ( zip_tseitin_0 @ D @ C @ B @ A ) ) =>
% 20.41/20.61       ( zip_tseitin_1 @ D @ C @ B @ A ) ))).
% 20.41/20.61  thf('108', plain,
% 20.41/20.61      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 20.41/20.61         ((zip_tseitin_1 @ X5 @ X6 @ X7 @ X8)
% 20.41/20.61          | (m1_subset_1 @ X5 @ (u1_struct_0 @ X8)))),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 20.41/20.61  thf('109', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_A)
% 20.41/20.61        | (r3_waybel_9 @ sk_A @ sk_B @ (k1_waybel_9 @ sk_A @ sk_B)))),
% 20.41/20.61      inference('simplify', [status(thm)], ['73'])).
% 20.41/20.61  thf('110', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_A)
% 20.41/20.61        | (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 20.41/20.61      inference('simplify', [status(thm)], ['77'])).
% 20.41/20.61  thf(zf_stmt_2, axiom,
% 20.41/20.61    (![D:$i,C:$i,B:$i,A:$i]:
% 20.41/20.61     ( ( ( r1_lattice3 @ A @ C @ D ) => ( r1_orders_2 @ A @ D @ B ) ) =>
% 20.41/20.61       ( zip_tseitin_0 @ D @ C @ B @ A ) ))).
% 20.41/20.61  thf('111', plain,
% 20.41/20.61      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 20.41/20.61         ((zip_tseitin_0 @ X1 @ X2 @ X3 @ X4) | (r1_lattice3 @ X4 @ X2 @ X1))),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 20.41/20.61  thf(l52_waybel_9, axiom,
% 20.41/20.61    (![A:$i]:
% 20.41/20.61     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 20.41/20.61         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 20.41/20.61         ( v2_lattice3 @ A ) & ( v1_compts_1 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 20.41/20.61       ( ![B:$i]:
% 20.41/20.61         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 20.41/20.61             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 20.41/20.61           ( ![C:$i]:
% 20.41/20.61             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 20.41/20.61               ( ![D:$i]:
% 20.41/20.61                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 20.41/20.61                   ( ( ( ( C ) = ( D ) ) & 
% 20.41/20.61                       ( ![E:$i]:
% 20.41/20.61                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 20.41/20.61                           ( v5_pre_topc @ ( k4_waybel_1 @ A @ E ) @ A @ A ) ) ) & 
% 20.41/20.61                       ( r3_waybel_9 @ A @ B @ C ) ) =>
% 20.41/20.61                     ( ![E:$i]:
% 20.41/20.61                       ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 20.41/20.61                         ( ( r1_lattice3 @
% 20.41/20.61                             A @ 
% 20.41/20.61                             ( k2_relset_1 @
% 20.41/20.61                               ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 20.41/20.61                               ( u1_waybel_0 @ A @ B ) ) @ 
% 20.41/20.61                             E ) =>
% 20.41/20.61                           ( r1_orders_2 @ A @ E @ D ) ) ) ) ) ) ) ) ) ) ) ))).
% 20.41/20.61  thf('112', plain,
% 20.41/20.61      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 20.41/20.61         ((v2_struct_0 @ X24)
% 20.41/20.61          | ~ (v4_orders_2 @ X24)
% 20.41/20.61          | ~ (v7_waybel_0 @ X24)
% 20.41/20.61          | ~ (l1_waybel_0 @ X24 @ X25)
% 20.41/20.61          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X25))
% 20.41/20.61          | ~ (r1_lattice3 @ X25 @ 
% 20.41/20.61               (k2_relset_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X25) @ 
% 20.41/20.61                (u1_waybel_0 @ X25 @ X24)) @ 
% 20.41/20.61               X27)
% 20.41/20.61          | (r1_orders_2 @ X25 @ X27 @ X26)
% 20.41/20.61          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X25))
% 20.41/20.61          | ((X28) != (X26))
% 20.41/20.61          | ~ (r3_waybel_9 @ X25 @ X24 @ X28)
% 20.41/20.61          | (m1_subset_1 @ (sk_E_1 @ X25) @ (u1_struct_0 @ X25))
% 20.41/20.61          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X25))
% 20.41/20.61          | ~ (l1_waybel_9 @ X25)
% 20.41/20.61          | ~ (v1_compts_1 @ X25)
% 20.41/20.61          | ~ (v2_lattice3 @ X25)
% 20.41/20.61          | ~ (v1_lattice3 @ X25)
% 20.41/20.61          | ~ (v5_orders_2 @ X25)
% 20.41/20.61          | ~ (v4_orders_2 @ X25)
% 20.41/20.61          | ~ (v3_orders_2 @ X25)
% 20.41/20.61          | ~ (v8_pre_topc @ X25)
% 20.41/20.61          | ~ (v2_pre_topc @ X25))),
% 20.41/20.61      inference('cnf', [status(esa)], [l52_waybel_9])).
% 20.41/20.61  thf('113', plain,
% 20.41/20.61      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 20.41/20.61         (~ (v2_pre_topc @ X25)
% 20.41/20.61          | ~ (v8_pre_topc @ X25)
% 20.41/20.61          | ~ (v3_orders_2 @ X25)
% 20.41/20.61          | ~ (v4_orders_2 @ X25)
% 20.41/20.61          | ~ (v5_orders_2 @ X25)
% 20.41/20.61          | ~ (v1_lattice3 @ X25)
% 20.41/20.61          | ~ (v2_lattice3 @ X25)
% 20.41/20.61          | ~ (v1_compts_1 @ X25)
% 20.41/20.61          | ~ (l1_waybel_9 @ X25)
% 20.41/20.61          | (m1_subset_1 @ (sk_E_1 @ X25) @ (u1_struct_0 @ X25))
% 20.41/20.61          | ~ (r3_waybel_9 @ X25 @ X24 @ X26)
% 20.41/20.61          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X25))
% 20.41/20.61          | (r1_orders_2 @ X25 @ X27 @ X26)
% 20.41/20.61          | ~ (r1_lattice3 @ X25 @ 
% 20.41/20.61               (k2_relset_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X25) @ 
% 20.41/20.61                (u1_waybel_0 @ X25 @ X24)) @ 
% 20.41/20.61               X27)
% 20.41/20.61          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X25))
% 20.41/20.61          | ~ (l1_waybel_0 @ X24 @ X25)
% 20.41/20.61          | ~ (v7_waybel_0 @ X24)
% 20.41/20.61          | ~ (v4_orders_2 @ X24)
% 20.41/20.61          | (v2_struct_0 @ X24))),
% 20.41/20.61      inference('simplify', [status(thm)], ['112'])).
% 20.41/20.61  thf('114', plain,
% 20.41/20.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 20.41/20.61         ((zip_tseitin_0 @ X0 @ 
% 20.41/20.61           (k2_relset_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X2) @ 
% 20.41/20.61            (u1_waybel_0 @ X2 @ X1)) @ 
% 20.41/20.61           X4 @ X2)
% 20.41/20.61          | (v2_struct_0 @ X1)
% 20.41/20.61          | ~ (v4_orders_2 @ X1)
% 20.41/20.61          | ~ (v7_waybel_0 @ X1)
% 20.41/20.61          | ~ (l1_waybel_0 @ X1 @ X2)
% 20.41/20.61          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 20.41/20.61          | (r1_orders_2 @ X2 @ X0 @ X3)
% 20.41/20.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X2))
% 20.41/20.61          | ~ (r3_waybel_9 @ X2 @ X1 @ X3)
% 20.41/20.61          | (m1_subset_1 @ (sk_E_1 @ X2) @ (u1_struct_0 @ X2))
% 20.41/20.61          | ~ (l1_waybel_9 @ X2)
% 20.41/20.61          | ~ (v1_compts_1 @ X2)
% 20.41/20.61          | ~ (v2_lattice3 @ X2)
% 20.41/20.61          | ~ (v1_lattice3 @ X2)
% 20.41/20.61          | ~ (v5_orders_2 @ X2)
% 20.41/20.61          | ~ (v4_orders_2 @ X2)
% 20.41/20.61          | ~ (v3_orders_2 @ X2)
% 20.41/20.61          | ~ (v8_pre_topc @ X2)
% 20.41/20.61          | ~ (v2_pre_topc @ X2))),
% 20.41/20.61      inference('sup-', [status(thm)], ['111', '113'])).
% 20.41/20.61  thf('115', plain,
% 20.41/20.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 20.41/20.61         ((v2_struct_0 @ sk_A)
% 20.41/20.61          | ~ (v2_pre_topc @ sk_A)
% 20.41/20.61          | ~ (v8_pre_topc @ sk_A)
% 20.41/20.61          | ~ (v3_orders_2 @ sk_A)
% 20.41/20.61          | ~ (v4_orders_2 @ sk_A)
% 20.41/20.61          | ~ (v5_orders_2 @ sk_A)
% 20.41/20.61          | ~ (v1_lattice3 @ sk_A)
% 20.41/20.61          | ~ (v2_lattice3 @ sk_A)
% 20.41/20.61          | ~ (v1_compts_1 @ sk_A)
% 20.41/20.61          | ~ (l1_waybel_9 @ sk_A)
% 20.41/20.61          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61          | ~ (r3_waybel_9 @ sk_A @ X0 @ (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.61          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 20.41/20.61          | (r1_orders_2 @ sk_A @ X1 @ (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.61          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 20.41/20.61          | ~ (v7_waybel_0 @ X0)
% 20.41/20.61          | ~ (v4_orders_2 @ X0)
% 20.41/20.61          | (v2_struct_0 @ X0)
% 20.41/20.61          | (zip_tseitin_0 @ X1 @ 
% 20.41/20.61             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.61              (u1_waybel_0 @ sk_A @ X0)) @ 
% 20.41/20.61             X2 @ sk_A))),
% 20.41/20.61      inference('sup-', [status(thm)], ['110', '114'])).
% 20.41/20.61  thf('116', plain, ((v2_pre_topc @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('117', plain, ((v8_pre_topc @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('118', plain, ((v3_orders_2 @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('119', plain, ((v4_orders_2 @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('120', plain, ((v5_orders_2 @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('121', plain, ((v1_lattice3 @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('122', plain, ((v2_lattice3 @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('123', plain, ((v1_compts_1 @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('124', plain, ((l1_waybel_9 @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('125', plain,
% 20.41/20.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 20.41/20.61         ((v2_struct_0 @ sk_A)
% 20.41/20.61          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61          | ~ (r3_waybel_9 @ sk_A @ X0 @ (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.61          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 20.41/20.61          | (r1_orders_2 @ sk_A @ X1 @ (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.61          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 20.41/20.61          | ~ (v7_waybel_0 @ X0)
% 20.41/20.61          | ~ (v4_orders_2 @ X0)
% 20.41/20.61          | (v2_struct_0 @ X0)
% 20.41/20.61          | (zip_tseitin_0 @ X1 @ 
% 20.41/20.61             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.61              (u1_waybel_0 @ sk_A @ X0)) @ 
% 20.41/20.61             X2 @ sk_A))),
% 20.41/20.61      inference('demod', [status(thm)],
% 20.41/20.61                ['115', '116', '117', '118', '119', '120', '121', '122', 
% 20.41/20.61                 '123', '124'])).
% 20.41/20.61  thf('126', plain,
% 20.41/20.61      (![X0 : $i, X1 : $i]:
% 20.41/20.61         ((v2_struct_0 @ sk_A)
% 20.41/20.61          | (zip_tseitin_0 @ X1 @ 
% 20.41/20.61             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.61              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.61             X0 @ sk_A)
% 20.41/20.61          | (v2_struct_0 @ sk_B)
% 20.41/20.61          | ~ (v4_orders_2 @ sk_B)
% 20.41/20.61          | ~ (v7_waybel_0 @ sk_B)
% 20.41/20.61          | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 20.41/20.61          | (r1_orders_2 @ sk_A @ X1 @ (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.61          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 20.41/20.61          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61          | (v2_struct_0 @ sk_A))),
% 20.41/20.61      inference('sup-', [status(thm)], ['109', '125'])).
% 20.41/20.61  thf('127', plain, ((v4_orders_2 @ sk_B)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('128', plain, ((v7_waybel_0 @ sk_B)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('129', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('130', plain,
% 20.41/20.61      (![X0 : $i, X1 : $i]:
% 20.41/20.61         ((v2_struct_0 @ sk_A)
% 20.41/20.61          | (zip_tseitin_0 @ X1 @ 
% 20.41/20.61             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.61              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.61             X0 @ sk_A)
% 20.41/20.61          | (v2_struct_0 @ sk_B)
% 20.41/20.61          | (r1_orders_2 @ sk_A @ X1 @ (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.61          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 20.41/20.61          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61          | (v2_struct_0 @ sk_A))),
% 20.41/20.61      inference('demod', [status(thm)], ['126', '127', '128', '129'])).
% 20.41/20.61  thf('131', plain,
% 20.41/20.61      (![X0 : $i, X1 : $i]:
% 20.41/20.61         ((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 20.41/20.61          | (r1_orders_2 @ sk_A @ X1 @ (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.61          | (v2_struct_0 @ sk_B)
% 20.41/20.61          | (zip_tseitin_0 @ X1 @ 
% 20.41/20.61             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.61              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.61             X0 @ sk_A)
% 20.41/20.61          | (v2_struct_0 @ sk_A))),
% 20.41/20.61      inference('simplify', [status(thm)], ['130'])).
% 20.41/20.61  thf('132', plain,
% 20.41/20.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 20.41/20.61         ((zip_tseitin_1 @ X0 @ X3 @ X2 @ sk_A)
% 20.41/20.61          | (v2_struct_0 @ sk_A)
% 20.41/20.61          | (zip_tseitin_0 @ X0 @ 
% 20.41/20.61             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.61              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.61             X1 @ sk_A)
% 20.41/20.61          | (v2_struct_0 @ sk_B)
% 20.41/20.61          | (r1_orders_2 @ sk_A @ X0 @ (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.61          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 20.41/20.61      inference('sup-', [status(thm)], ['108', '131'])).
% 20.41/20.61  thf('133', plain,
% 20.41/20.61      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 20.41/20.61         ((zip_tseitin_1 @ X5 @ X6 @ X7 @ X8)
% 20.41/20.61          | ~ (zip_tseitin_0 @ X5 @ X6 @ X7 @ X8))),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 20.41/20.61  thf('134', plain,
% 20.41/20.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 20.41/20.61         ((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61          | (r1_orders_2 @ sk_A @ X1 @ (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.61          | (v2_struct_0 @ sk_B)
% 20.41/20.61          | (v2_struct_0 @ sk_A)
% 20.41/20.61          | (zip_tseitin_1 @ X1 @ X3 @ X2 @ sk_A)
% 20.41/20.61          | (zip_tseitin_1 @ X1 @ 
% 20.41/20.61             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.61              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.61             X0 @ sk_A))),
% 20.41/20.61      inference('sup-', [status(thm)], ['132', '133'])).
% 20.41/20.61  thf('135', plain,
% 20.41/20.61      (![X0 : $i, X1 : $i]:
% 20.41/20.61         ((zip_tseitin_1 @ X1 @ 
% 20.41/20.61           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.61            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.61           X0 @ sk_A)
% 20.41/20.61          | (v2_struct_0 @ sk_A)
% 20.41/20.61          | (v2_struct_0 @ sk_B)
% 20.41/20.61          | (r1_orders_2 @ sk_A @ X1 @ (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.61          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 20.41/20.61      inference('eq_fact', [status(thm)], ['134'])).
% 20.41/20.61  thf('136', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_A)
% 20.41/20.61        | (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 20.41/20.61      inference('simplify', [status(thm)], ['77'])).
% 20.41/20.61  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 20.41/20.61  thf(zf_stmt_4, axiom,
% 20.41/20.61    (![C:$i,B:$i,A:$i]:
% 20.41/20.61     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 20.41/20.61       ( ( ( B ) = ( k2_yellow_0 @ A @ C ) ) & ( r2_yellow_0 @ A @ C ) ) ))).
% 20.41/20.61  thf(zf_stmt_5, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 20.41/20.61  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 20.41/20.61  thf(zf_stmt_7, axiom,
% 20.41/20.61    (![A:$i]:
% 20.41/20.61     ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 20.41/20.61       ( ![B:$i]:
% 20.41/20.61         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 20.41/20.61           ( ![C:$i]:
% 20.41/20.61             ( ( ( ( r1_lattice3 @ A @ C @ B ) & 
% 20.41/20.61                   ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) =>
% 20.41/20.61                 ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 20.41/20.61               ( ( ( ( B ) = ( k2_yellow_0 @ A @ C ) ) & 
% 20.41/20.61                   ( r2_yellow_0 @ A @ C ) ) =>
% 20.41/20.61                 ( ( r1_lattice3 @ A @ C @ B ) & 
% 20.41/20.61                   ( ![D:$i]:
% 20.41/20.61                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 20.41/20.61                       ( ( r1_lattice3 @ A @ C @ D ) =>
% 20.41/20.61                         ( r1_orders_2 @ A @ D @ B ) ) ) ) ) ) ) ) ) ) ))).
% 20.41/20.61  thf('137', plain,
% 20.41/20.61      (![X12 : $i, X13 : $i, X16 : $i]:
% 20.41/20.61         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 20.41/20.61          | ~ (r1_lattice3 @ X13 @ X16 @ X12)
% 20.41/20.61          | ~ (zip_tseitin_1 @ (sk_D @ X16 @ X12 @ X13) @ X16 @ X12 @ X13)
% 20.41/20.61          | (zip_tseitin_2 @ X16 @ X12 @ X13)
% 20.41/20.61          | ~ (l1_orders_2 @ X13)
% 20.41/20.61          | ~ (v5_orders_2 @ X13))),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_7])).
% 20.41/20.61  thf('138', plain,
% 20.41/20.61      (![X0 : $i]:
% 20.41/20.61         ((v2_struct_0 @ sk_A)
% 20.41/20.61          | ~ (v5_orders_2 @ sk_A)
% 20.41/20.61          | ~ (l1_orders_2 @ sk_A)
% 20.41/20.61          | (zip_tseitin_2 @ X0 @ (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.61          | ~ (zip_tseitin_1 @ 
% 20.41/20.61               (sk_D @ X0 @ (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ X0 @ 
% 20.41/20.61               (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.61          | ~ (r1_lattice3 @ sk_A @ X0 @ (k1_waybel_9 @ sk_A @ sk_B)))),
% 20.41/20.61      inference('sup-', [status(thm)], ['136', '137'])).
% 20.41/20.61  thf('139', plain, ((v5_orders_2 @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('140', plain, ((l1_waybel_9 @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('141', plain,
% 20.41/20.61      (![X19 : $i]: ((l1_orders_2 @ X19) | ~ (l1_waybel_9 @ X19))),
% 20.41/20.61      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 20.41/20.61  thf('142', plain, ((l1_orders_2 @ sk_A)),
% 20.41/20.61      inference('sup-', [status(thm)], ['140', '141'])).
% 20.41/20.61  thf('143', plain,
% 20.41/20.61      (![X0 : $i]:
% 20.41/20.61         ((v2_struct_0 @ sk_A)
% 20.41/20.61          | (zip_tseitin_2 @ X0 @ (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.61          | ~ (zip_tseitin_1 @ 
% 20.41/20.61               (sk_D @ X0 @ (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ X0 @ 
% 20.41/20.61               (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.61          | ~ (r1_lattice3 @ sk_A @ X0 @ (k1_waybel_9 @ sk_A @ sk_B)))),
% 20.41/20.61      inference('demod', [status(thm)], ['138', '139', '142'])).
% 20.41/20.61  thf('144', plain,
% 20.41/20.61      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61        | (r1_orders_2 @ sk_A @ 
% 20.41/20.61           (sk_D @ 
% 20.41/20.61            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.61             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.61            (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.61           (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.61        | (v2_struct_0 @ sk_B)
% 20.41/20.61        | (v2_struct_0 @ sk_A)
% 20.41/20.61        | ~ (r1_lattice3 @ sk_A @ 
% 20.41/20.61             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.61              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.61             (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.61        | (zip_tseitin_2 @ 
% 20.41/20.61           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.61            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.61           (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.61        | (v2_struct_0 @ sk_A))),
% 20.41/20.61      inference('sup-', [status(thm)], ['135', '143'])).
% 20.41/20.61  thf('145', plain,
% 20.41/20.61      (((zip_tseitin_2 @ 
% 20.41/20.61         (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.61          (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.61         (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.61        | ~ (r1_lattice3 @ sk_A @ 
% 20.41/20.61             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.61              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.61             (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.61        | (v2_struct_0 @ sk_A)
% 20.41/20.61        | (v2_struct_0 @ sk_B)
% 20.41/20.61        | (r1_orders_2 @ sk_A @ 
% 20.41/20.61           (sk_D @ 
% 20.41/20.61            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.61             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.61            (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.61           (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.61        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 20.41/20.61      inference('simplify', [status(thm)], ['144'])).
% 20.41/20.61  thf('146', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_A)
% 20.41/20.61        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61        | (v2_struct_0 @ sk_B)
% 20.41/20.61        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61        | (r1_orders_2 @ sk_A @ 
% 20.41/20.61           (sk_D @ 
% 20.41/20.61            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.61             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.61            (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.61           (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.61        | (v2_struct_0 @ sk_B)
% 20.41/20.61        | (v2_struct_0 @ sk_A)
% 20.41/20.61        | (zip_tseitin_2 @ 
% 20.41/20.61           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.61            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.61           (k1_waybel_9 @ sk_A @ sk_B) @ sk_A))),
% 20.41/20.61      inference('sup-', [status(thm)], ['107', '145'])).
% 20.41/20.61  thf('147', plain,
% 20.41/20.61      (((zip_tseitin_2 @ 
% 20.41/20.61         (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.61          (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.61         (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.61        | (r1_orders_2 @ sk_A @ 
% 20.41/20.61           (sk_D @ 
% 20.41/20.61            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.61             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.61            (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.61           (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.61        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61        | (v2_struct_0 @ sk_B)
% 20.41/20.61        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61        | (v2_struct_0 @ sk_A))),
% 20.41/20.61      inference('simplify', [status(thm)], ['146'])).
% 20.41/20.61  thf('148', plain,
% 20.41/20.61      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 20.41/20.61         ((zip_tseitin_0 @ X1 @ X2 @ X3 @ X4) | ~ (r1_orders_2 @ X4 @ X1 @ X3))),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 20.41/20.61  thf('149', plain,
% 20.41/20.61      (![X0 : $i]:
% 20.41/20.61         ((v2_struct_0 @ sk_A)
% 20.41/20.61          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61          | (v2_struct_0 @ sk_B)
% 20.41/20.61          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61          | (zip_tseitin_2 @ 
% 20.41/20.61             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.61              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.61             (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.61          | (zip_tseitin_0 @ 
% 20.41/20.61             (sk_D @ 
% 20.41/20.61              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.61               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.61              (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.61             X0 @ (k1_waybel_9 @ sk_A @ sk_B) @ sk_A))),
% 20.41/20.61      inference('sup-', [status(thm)], ['147', '148'])).
% 20.41/20.61  thf('150', plain,
% 20.41/20.61      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 20.41/20.61         ((zip_tseitin_1 @ X5 @ X6 @ X7 @ X8)
% 20.41/20.61          | ~ (zip_tseitin_0 @ X5 @ X6 @ X7 @ X8))),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 20.41/20.61  thf('151', plain,
% 20.41/20.61      (![X0 : $i]:
% 20.41/20.61         ((zip_tseitin_2 @ 
% 20.41/20.61           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.61            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.61           (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.61          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61          | (v2_struct_0 @ sk_B)
% 20.41/20.61          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61          | (v2_struct_0 @ sk_A)
% 20.41/20.61          | (zip_tseitin_1 @ 
% 20.41/20.61             (sk_D @ 
% 20.41/20.61              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.61               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.61              (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.61             X0 @ (k1_waybel_9 @ sk_A @ sk_B) @ sk_A))),
% 20.41/20.61      inference('sup-', [status(thm)], ['149', '150'])).
% 20.41/20.61  thf('152', plain,
% 20.41/20.61      (![X0 : $i]:
% 20.41/20.61         ((v2_struct_0 @ sk_A)
% 20.41/20.61          | (zip_tseitin_2 @ X0 @ (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.61          | ~ (zip_tseitin_1 @ 
% 20.41/20.61               (sk_D @ X0 @ (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ X0 @ 
% 20.41/20.61               (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.61          | ~ (r1_lattice3 @ sk_A @ X0 @ (k1_waybel_9 @ sk_A @ sk_B)))),
% 20.41/20.61      inference('demod', [status(thm)], ['138', '139', '142'])).
% 20.41/20.61  thf('153', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_A)
% 20.41/20.61        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61        | (v2_struct_0 @ sk_B)
% 20.41/20.61        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61        | (zip_tseitin_2 @ 
% 20.41/20.61           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.61            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.61           (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.61        | ~ (r1_lattice3 @ sk_A @ 
% 20.41/20.61             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.61              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.61             (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.61        | (zip_tseitin_2 @ 
% 20.41/20.61           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.61            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.61           (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.61        | (v2_struct_0 @ sk_A))),
% 20.41/20.61      inference('sup-', [status(thm)], ['151', '152'])).
% 20.41/20.61  thf('154', plain,
% 20.41/20.61      ((~ (r1_lattice3 @ sk_A @ 
% 20.41/20.61           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.61            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.61           (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.61        | (zip_tseitin_2 @ 
% 20.41/20.61           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.61            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.61           (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.61        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61        | (v2_struct_0 @ sk_B)
% 20.41/20.61        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61        | (v2_struct_0 @ sk_A))),
% 20.41/20.61      inference('simplify', [status(thm)], ['153'])).
% 20.41/20.61  thf('155', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_A)
% 20.41/20.61        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61        | (v2_struct_0 @ sk_B)
% 20.41/20.61        | (v2_struct_0 @ sk_A)
% 20.41/20.61        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61        | (v2_struct_0 @ sk_B)
% 20.41/20.61        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61        | (zip_tseitin_2 @ 
% 20.41/20.61           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.61            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.61           (k1_waybel_9 @ sk_A @ sk_B) @ sk_A))),
% 20.41/20.61      inference('sup-', [status(thm)], ['106', '154'])).
% 20.41/20.61  thf('156', plain,
% 20.41/20.61      (((zip_tseitin_2 @ 
% 20.41/20.61         (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.61          (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.61         (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.61        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61        | (v2_struct_0 @ sk_B)
% 20.41/20.61        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61        | (v2_struct_0 @ sk_A))),
% 20.41/20.61      inference('simplify', [status(thm)], ['155'])).
% 20.41/20.61  thf('157', plain,
% 20.41/20.61      (![X9 : $i, X10 : $i, X11 : $i]:
% 20.41/20.61         ((r2_yellow_0 @ X9 @ X10) | ~ (zip_tseitin_2 @ X10 @ X11 @ X9))),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_4])).
% 20.41/20.61  thf('158', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_A)
% 20.41/20.61        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61        | (v2_struct_0 @ sk_B)
% 20.41/20.61        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61        | (r2_yellow_0 @ sk_A @ 
% 20.41/20.61           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.61            (u1_waybel_0 @ sk_A @ sk_B))))),
% 20.41/20.61      inference('sup-', [status(thm)], ['156', '157'])).
% 20.41/20.61  thf(d4_waybel_9, axiom,
% 20.41/20.61    (![A:$i]:
% 20.41/20.61     ( ( l1_orders_2 @ A ) =>
% 20.41/20.61       ( ![B:$i]:
% 20.41/20.61         ( ( l1_waybel_0 @ B @ A ) =>
% 20.41/20.61           ( ( r2_waybel_9 @ A @ B ) <=>
% 20.41/20.61             ( r2_yellow_0 @
% 20.41/20.61               A @ 
% 20.41/20.61               ( k2_relset_1 @
% 20.41/20.61                 ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 20.41/20.61                 ( u1_waybel_0 @ A @ B ) ) ) ) ) ) ))).
% 20.41/20.61  thf('159', plain,
% 20.41/20.61      (![X17 : $i, X18 : $i]:
% 20.41/20.61         (~ (l1_waybel_0 @ X17 @ X18)
% 20.41/20.61          | ~ (r2_yellow_0 @ X18 @ 
% 20.41/20.61               (k2_relset_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X18) @ 
% 20.41/20.61                (u1_waybel_0 @ X18 @ X17)))
% 20.41/20.61          | (r2_waybel_9 @ X18 @ X17)
% 20.41/20.61          | ~ (l1_orders_2 @ X18))),
% 20.41/20.61      inference('cnf', [status(esa)], [d4_waybel_9])).
% 20.41/20.61  thf('160', plain,
% 20.41/20.61      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61        | (v2_struct_0 @ sk_B)
% 20.41/20.61        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61        | (v2_struct_0 @ sk_A)
% 20.41/20.61        | ~ (l1_orders_2 @ sk_A)
% 20.41/20.61        | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.61        | ~ (l1_waybel_0 @ sk_B @ sk_A))),
% 20.41/20.61      inference('sup-', [status(thm)], ['158', '159'])).
% 20.41/20.61  thf('161', plain, ((l1_orders_2 @ sk_A)),
% 20.41/20.61      inference('sup-', [status(thm)], ['140', '141'])).
% 20.41/20.61  thf('162', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('163', plain,
% 20.41/20.61      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61        | (v2_struct_0 @ sk_B)
% 20.41/20.61        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61        | (v2_struct_0 @ sk_A)
% 20.41/20.61        | (r2_waybel_9 @ sk_A @ sk_B))),
% 20.41/20.61      inference('demod', [status(thm)], ['160', '161', '162'])).
% 20.41/20.61  thf('164', plain,
% 20.41/20.61      (![X37 : $i]:
% 20.41/20.61         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X37) @ sk_A @ sk_A)
% 20.41/20.61          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A)))),
% 20.41/20.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.61  thf('165', plain,
% 20.41/20.61      (((r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.61        | (v2_struct_0 @ sk_A)
% 20.41/20.61        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61        | (v2_struct_0 @ sk_B)
% 20.41/20.61        | (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ sk_A))),
% 20.41/20.61      inference('sup-', [status(thm)], ['163', '164'])).
% 20.41/20.61  thf('166', plain,
% 20.41/20.61      (((v2_struct_0 @ sk_B)
% 20.41/20.61        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.61        | (v2_struct_0 @ sk_A)
% 20.41/20.61        | (r1_lattice3 @ sk_A @ 
% 20.41/20.61           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.61            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.61           (k1_waybel_9 @ sk_A @ sk_B)))),
% 20.41/20.62      inference('simplify', [status(thm)], ['102'])).
% 20.41/20.62  thf('167', plain,
% 20.41/20.62      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 20.41/20.62         ((zip_tseitin_1 @ X5 @ X6 @ X7 @ X8)
% 20.41/20.62          | (m1_subset_1 @ X5 @ (u1_struct_0 @ X8)))),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 20.41/20.62  thf('168', plain,
% 20.41/20.62      (![X0 : $i]:
% 20.41/20.62         ((v2_struct_0 @ sk_A)
% 20.41/20.62          | (zip_tseitin_2 @ X0 @ (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62          | ~ (zip_tseitin_1 @ 
% 20.41/20.62               (sk_D @ X0 @ (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ X0 @ 
% 20.41/20.62               (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62          | ~ (r1_lattice3 @ sk_A @ X0 @ (k1_waybel_9 @ sk_A @ sk_B)))),
% 20.41/20.62      inference('demod', [status(thm)], ['138', '139', '142'])).
% 20.41/20.62  thf('169', plain,
% 20.41/20.62      (![X0 : $i]:
% 20.41/20.62         ((m1_subset_1 @ (sk_D @ X0 @ (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62           (u1_struct_0 @ sk_A))
% 20.41/20.62          | ~ (r1_lattice3 @ sk_A @ X0 @ (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.62          | (zip_tseitin_2 @ X0 @ (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62          | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('sup-', [status(thm)], ['167', '168'])).
% 20.41/20.62  thf('170', plain,
% 20.41/20.62      (((v2_struct_0 @ sk_A)
% 20.41/20.62        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_A)
% 20.41/20.62        | (zip_tseitin_2 @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62        | (m1_subset_1 @ 
% 20.41/20.62           (sk_D @ 
% 20.41/20.62            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62            (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62           (u1_struct_0 @ sk_A)))),
% 20.41/20.62      inference('sup-', [status(thm)], ['166', '169'])).
% 20.41/20.62  thf('171', plain,
% 20.41/20.62      (((m1_subset_1 @ 
% 20.41/20.62         (sk_D @ 
% 20.41/20.62          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62          (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62         (u1_struct_0 @ sk_A))
% 20.41/20.62        | (zip_tseitin_2 @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62        | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('simplify', [status(thm)], ['170'])).
% 20.41/20.62  thf('172', plain,
% 20.41/20.62      (((v2_struct_0 @ sk_B)
% 20.41/20.62        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62        | (v2_struct_0 @ sk_A)
% 20.41/20.62        | (r1_lattice3 @ sk_A @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B)))),
% 20.41/20.62      inference('simplify', [status(thm)], ['102'])).
% 20.41/20.62  thf('173', plain,
% 20.41/20.62      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 20.41/20.62         ((zip_tseitin_0 @ X1 @ X2 @ X3 @ X4) | (r1_lattice3 @ X4 @ X2 @ X1))),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 20.41/20.62  thf('174', plain,
% 20.41/20.62      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 20.41/20.62         ((zip_tseitin_1 @ X5 @ X6 @ X7 @ X8)
% 20.41/20.62          | ~ (zip_tseitin_0 @ X5 @ X6 @ X7 @ X8))),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 20.41/20.62  thf('175', plain,
% 20.41/20.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 20.41/20.62         ((r1_lattice3 @ X0 @ X2 @ X3) | (zip_tseitin_1 @ X3 @ X2 @ X1 @ X0))),
% 20.41/20.62      inference('sup-', [status(thm)], ['173', '174'])).
% 20.41/20.62  thf('176', plain,
% 20.41/20.62      (![X0 : $i]:
% 20.41/20.62         ((v2_struct_0 @ sk_A)
% 20.41/20.62          | (zip_tseitin_2 @ X0 @ (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62          | ~ (zip_tseitin_1 @ 
% 20.41/20.62               (sk_D @ X0 @ (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ X0 @ 
% 20.41/20.62               (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62          | ~ (r1_lattice3 @ sk_A @ X0 @ (k1_waybel_9 @ sk_A @ sk_B)))),
% 20.41/20.62      inference('demod', [status(thm)], ['138', '139', '142'])).
% 20.41/20.62  thf('177', plain,
% 20.41/20.62      (![X0 : $i]:
% 20.41/20.62         ((r1_lattice3 @ sk_A @ X0 @ 
% 20.41/20.62           (sk_D @ X0 @ (k1_waybel_9 @ sk_A @ sk_B) @ sk_A))
% 20.41/20.62          | ~ (r1_lattice3 @ sk_A @ X0 @ (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.62          | (zip_tseitin_2 @ X0 @ (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62          | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('sup-', [status(thm)], ['175', '176'])).
% 20.41/20.62  thf('178', plain,
% 20.41/20.62      (((v2_struct_0 @ sk_A)
% 20.41/20.62        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_A)
% 20.41/20.62        | (zip_tseitin_2 @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62        | (r1_lattice3 @ sk_A @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (sk_D @ 
% 20.41/20.62            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62            (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)))),
% 20.41/20.62      inference('sup-', [status(thm)], ['172', '177'])).
% 20.41/20.62  thf('179', plain,
% 20.41/20.62      (((r1_lattice3 @ sk_A @ 
% 20.41/20.62         (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62          (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62         (sk_D @ 
% 20.41/20.62          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62          (k1_waybel_9 @ sk_A @ sk_B) @ sk_A))
% 20.41/20.62        | (zip_tseitin_2 @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62        | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('simplify', [status(thm)], ['178'])).
% 20.41/20.62  thf('180', plain,
% 20.41/20.62      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 20.41/20.62         ((v2_struct_0 @ X24)
% 20.41/20.62          | ~ (v4_orders_2 @ X24)
% 20.41/20.62          | ~ (v7_waybel_0 @ X24)
% 20.41/20.62          | ~ (l1_waybel_0 @ X24 @ X25)
% 20.41/20.62          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X25))
% 20.41/20.62          | ~ (r1_lattice3 @ X25 @ 
% 20.41/20.62               (k2_relset_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X25) @ 
% 20.41/20.62                (u1_waybel_0 @ X25 @ X24)) @ 
% 20.41/20.62               X27)
% 20.41/20.62          | (r1_orders_2 @ X25 @ X27 @ X26)
% 20.41/20.62          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X25))
% 20.41/20.62          | ((X28) != (X26))
% 20.41/20.62          | ~ (r3_waybel_9 @ X25 @ X24 @ X28)
% 20.41/20.62          | ~ (v5_pre_topc @ (k4_waybel_1 @ X25 @ (sk_E_1 @ X25)) @ X25 @ X25)
% 20.41/20.62          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X25))
% 20.41/20.62          | ~ (l1_waybel_9 @ X25)
% 20.41/20.62          | ~ (v1_compts_1 @ X25)
% 20.41/20.62          | ~ (v2_lattice3 @ X25)
% 20.41/20.62          | ~ (v1_lattice3 @ X25)
% 20.41/20.62          | ~ (v5_orders_2 @ X25)
% 20.41/20.62          | ~ (v4_orders_2 @ X25)
% 20.41/20.62          | ~ (v3_orders_2 @ X25)
% 20.41/20.62          | ~ (v8_pre_topc @ X25)
% 20.41/20.62          | ~ (v2_pre_topc @ X25))),
% 20.41/20.62      inference('cnf', [status(esa)], [l52_waybel_9])).
% 20.41/20.62  thf('181', plain,
% 20.41/20.62      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 20.41/20.62         (~ (v2_pre_topc @ X25)
% 20.41/20.62          | ~ (v8_pre_topc @ X25)
% 20.41/20.62          | ~ (v3_orders_2 @ X25)
% 20.41/20.62          | ~ (v4_orders_2 @ X25)
% 20.41/20.62          | ~ (v5_orders_2 @ X25)
% 20.41/20.62          | ~ (v1_lattice3 @ X25)
% 20.41/20.62          | ~ (v2_lattice3 @ X25)
% 20.41/20.62          | ~ (v1_compts_1 @ X25)
% 20.41/20.62          | ~ (l1_waybel_9 @ X25)
% 20.41/20.62          | ~ (v5_pre_topc @ (k4_waybel_1 @ X25 @ (sk_E_1 @ X25)) @ X25 @ X25)
% 20.41/20.62          | ~ (r3_waybel_9 @ X25 @ X24 @ X26)
% 20.41/20.62          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X25))
% 20.41/20.62          | (r1_orders_2 @ X25 @ X27 @ X26)
% 20.41/20.62          | ~ (r1_lattice3 @ X25 @ 
% 20.41/20.62               (k2_relset_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X25) @ 
% 20.41/20.62                (u1_waybel_0 @ X25 @ X24)) @ 
% 20.41/20.62               X27)
% 20.41/20.62          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X25))
% 20.41/20.62          | ~ (l1_waybel_0 @ X24 @ X25)
% 20.41/20.62          | ~ (v7_waybel_0 @ X24)
% 20.41/20.62          | ~ (v4_orders_2 @ X24)
% 20.41/20.62          | (v2_struct_0 @ X24))),
% 20.41/20.62      inference('simplify', [status(thm)], ['180'])).
% 20.41/20.62  thf('182', plain,
% 20.41/20.62      (![X0 : $i]:
% 20.41/20.62         ((v2_struct_0 @ sk_A)
% 20.41/20.62          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62          | (v2_struct_0 @ sk_B)
% 20.41/20.62          | (zip_tseitin_2 @ 
% 20.41/20.62             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62             (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62          | (v2_struct_0 @ sk_B)
% 20.41/20.62          | ~ (v4_orders_2 @ sk_B)
% 20.41/20.62          | ~ (v7_waybel_0 @ sk_B)
% 20.41/20.62          | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 20.41/20.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 20.41/20.62          | (r1_orders_2 @ sk_A @ 
% 20.41/20.62             (sk_D @ 
% 20.41/20.62              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62              (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62             X0)
% 20.41/20.62          | ~ (m1_subset_1 @ 
% 20.41/20.62               (sk_D @ 
% 20.41/20.62                (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62                 (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62                (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62               (u1_struct_0 @ sk_A))
% 20.41/20.62          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 20.41/20.62          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ 
% 20.41/20.62               sk_A)
% 20.41/20.62          | ~ (l1_waybel_9 @ sk_A)
% 20.41/20.62          | ~ (v1_compts_1 @ sk_A)
% 20.41/20.62          | ~ (v2_lattice3 @ sk_A)
% 20.41/20.62          | ~ (v1_lattice3 @ sk_A)
% 20.41/20.62          | ~ (v5_orders_2 @ sk_A)
% 20.41/20.62          | ~ (v4_orders_2 @ sk_A)
% 20.41/20.62          | ~ (v3_orders_2 @ sk_A)
% 20.41/20.62          | ~ (v8_pre_topc @ sk_A)
% 20.41/20.62          | ~ (v2_pre_topc @ sk_A))),
% 20.41/20.62      inference('sup-', [status(thm)], ['179', '181'])).
% 20.41/20.62  thf('183', plain, ((v4_orders_2 @ sk_B)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('184', plain, ((v7_waybel_0 @ sk_B)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('185', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('186', plain, ((l1_waybel_9 @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('187', plain, ((v1_compts_1 @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('188', plain, ((v2_lattice3 @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('189', plain, ((v1_lattice3 @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('190', plain, ((v5_orders_2 @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('191', plain, ((v4_orders_2 @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('192', plain, ((v3_orders_2 @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('193', plain, ((v8_pre_topc @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('194', plain, ((v2_pre_topc @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('195', plain,
% 20.41/20.62      (![X0 : $i]:
% 20.41/20.62         ((v2_struct_0 @ sk_A)
% 20.41/20.62          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62          | (v2_struct_0 @ sk_B)
% 20.41/20.62          | (zip_tseitin_2 @ 
% 20.41/20.62             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62             (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62          | (v2_struct_0 @ sk_B)
% 20.41/20.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 20.41/20.62          | (r1_orders_2 @ sk_A @ 
% 20.41/20.62             (sk_D @ 
% 20.41/20.62              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62              (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62             X0)
% 20.41/20.62          | ~ (m1_subset_1 @ 
% 20.41/20.62               (sk_D @ 
% 20.41/20.62                (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62                 (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62                (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62               (u1_struct_0 @ sk_A))
% 20.41/20.62          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 20.41/20.62          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ 
% 20.41/20.62               sk_A))),
% 20.41/20.62      inference('demod', [status(thm)],
% 20.41/20.62                ['182', '183', '184', '185', '186', '187', '188', '189', 
% 20.41/20.62                 '190', '191', '192', '193', '194'])).
% 20.41/20.62  thf('196', plain,
% 20.41/20.62      (![X0 : $i]:
% 20.41/20.62         (~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ sk_A)
% 20.41/20.62          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 20.41/20.62          | ~ (m1_subset_1 @ 
% 20.41/20.62               (sk_D @ 
% 20.41/20.62                (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62                 (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62                (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62               (u1_struct_0 @ sk_A))
% 20.41/20.62          | (r1_orders_2 @ sk_A @ 
% 20.41/20.62             (sk_D @ 
% 20.41/20.62              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62              (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62             X0)
% 20.41/20.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 20.41/20.62          | (zip_tseitin_2 @ 
% 20.41/20.62             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62             (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62          | (v2_struct_0 @ sk_B)
% 20.41/20.62          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62          | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('simplify', [status(thm)], ['195'])).
% 20.41/20.62  thf('197', plain,
% 20.41/20.62      (![X0 : $i]:
% 20.41/20.62         ((v2_struct_0 @ sk_A)
% 20.41/20.62          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62          | (v2_struct_0 @ sk_B)
% 20.41/20.62          | (zip_tseitin_2 @ 
% 20.41/20.62             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62             (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62          | (v2_struct_0 @ sk_A)
% 20.41/20.62          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62          | (v2_struct_0 @ sk_B)
% 20.41/20.62          | (zip_tseitin_2 @ 
% 20.41/20.62             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62             (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 20.41/20.62          | (r1_orders_2 @ sk_A @ 
% 20.41/20.62             (sk_D @ 
% 20.41/20.62              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62              (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62             X0)
% 20.41/20.62          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 20.41/20.62          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ 
% 20.41/20.62               sk_A))),
% 20.41/20.62      inference('sup-', [status(thm)], ['171', '196'])).
% 20.41/20.62  thf('198', plain,
% 20.41/20.62      (![X0 : $i]:
% 20.41/20.62         (~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ sk_A)
% 20.41/20.62          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 20.41/20.62          | (r1_orders_2 @ sk_A @ 
% 20.41/20.62             (sk_D @ 
% 20.41/20.62              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62              (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62             X0)
% 20.41/20.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 20.41/20.62          | (zip_tseitin_2 @ 
% 20.41/20.62             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62             (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62          | (v2_struct_0 @ sk_B)
% 20.41/20.62          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62          | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('simplify', [status(thm)], ['197'])).
% 20.41/20.62  thf('199', plain,
% 20.41/20.62      (![X0 : $i]:
% 20.41/20.62         ((v2_struct_0 @ sk_B)
% 20.41/20.62          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62          | (v2_struct_0 @ sk_A)
% 20.41/20.62          | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62          | (v2_struct_0 @ sk_A)
% 20.41/20.62          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62          | (v2_struct_0 @ sk_B)
% 20.41/20.62          | (zip_tseitin_2 @ 
% 20.41/20.62             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62             (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 20.41/20.62          | (r1_orders_2 @ sk_A @ 
% 20.41/20.62             (sk_D @ 
% 20.41/20.62              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62              (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62             X0)
% 20.41/20.62          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0))),
% 20.41/20.62      inference('sup-', [status(thm)], ['165', '198'])).
% 20.41/20.62  thf('200', plain,
% 20.41/20.62      (![X0 : $i]:
% 20.41/20.62         (~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 20.41/20.62          | (r1_orders_2 @ sk_A @ 
% 20.41/20.62             (sk_D @ 
% 20.41/20.62              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62              (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62             X0)
% 20.41/20.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 20.41/20.62          | (zip_tseitin_2 @ 
% 20.41/20.62             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62             (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62          | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62          | (v2_struct_0 @ sk_A)
% 20.41/20.62          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62          | (v2_struct_0 @ sk_B))),
% 20.41/20.62      inference('simplify', [status(thm)], ['199'])).
% 20.41/20.62  thf('201', plain,
% 20.41/20.62      (((v2_struct_0 @ sk_A)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62        | (v2_struct_0 @ sk_A)
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (zip_tseitin_2 @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62        | ~ (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 20.41/20.62        | (r1_orders_2 @ sk_A @ 
% 20.41/20.62           (sk_D @ 
% 20.41/20.62            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62            (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B)))),
% 20.41/20.62      inference('sup-', [status(thm)], ['105', '200'])).
% 20.41/20.62  thf('202', plain,
% 20.41/20.62      (((r1_orders_2 @ sk_A @ 
% 20.41/20.62         (sk_D @ 
% 20.41/20.62          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62          (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62         (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.62        | ~ (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 20.41/20.62        | (zip_tseitin_2 @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('simplify', [status(thm)], ['201'])).
% 20.41/20.62  thf('203', plain,
% 20.41/20.62      (((v2_struct_0 @ sk_A)
% 20.41/20.62        | (v2_struct_0 @ sk_A)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (zip_tseitin_2 @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62        | (r1_orders_2 @ sk_A @ 
% 20.41/20.62           (sk_D @ 
% 20.41/20.62            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62            (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B)))),
% 20.41/20.62      inference('sup-', [status(thm)], ['104', '202'])).
% 20.41/20.62  thf('204', plain,
% 20.41/20.62      (((r1_orders_2 @ sk_A @ 
% 20.41/20.62         (sk_D @ 
% 20.41/20.62          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62          (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62         (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.62        | (zip_tseitin_2 @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('simplify', [status(thm)], ['203'])).
% 20.41/20.62  thf('205', plain,
% 20.41/20.62      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 20.41/20.62         ((zip_tseitin_0 @ X1 @ X2 @ X3 @ X4) | ~ (r1_orders_2 @ X4 @ X1 @ X3))),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 20.41/20.62  thf('206', plain,
% 20.41/20.62      (![X0 : $i]:
% 20.41/20.62         ((v2_struct_0 @ sk_A)
% 20.41/20.62          | (v2_struct_0 @ sk_B)
% 20.41/20.62          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62          | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62          | (zip_tseitin_2 @ 
% 20.41/20.62             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62             (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62          | (zip_tseitin_0 @ 
% 20.41/20.62             (sk_D @ 
% 20.41/20.62              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62              (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62             X0 @ (k1_waybel_9 @ sk_A @ sk_B) @ sk_A))),
% 20.41/20.62      inference('sup-', [status(thm)], ['204', '205'])).
% 20.41/20.62  thf('207', plain,
% 20.41/20.62      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 20.41/20.62         ((zip_tseitin_1 @ X5 @ X6 @ X7 @ X8)
% 20.41/20.62          | ~ (zip_tseitin_0 @ X5 @ X6 @ X7 @ X8))),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 20.41/20.62  thf('208', plain,
% 20.41/20.62      (![X0 : $i]:
% 20.41/20.62         ((zip_tseitin_2 @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62          | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62          | (v2_struct_0 @ sk_B)
% 20.41/20.62          | (v2_struct_0 @ sk_A)
% 20.41/20.62          | (zip_tseitin_1 @ 
% 20.41/20.62             (sk_D @ 
% 20.41/20.62              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62              (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62             X0 @ (k1_waybel_9 @ sk_A @ sk_B) @ sk_A))),
% 20.41/20.62      inference('sup-', [status(thm)], ['206', '207'])).
% 20.41/20.62  thf('209', plain,
% 20.41/20.62      (![X0 : $i]:
% 20.41/20.62         ((v2_struct_0 @ sk_A)
% 20.41/20.62          | (zip_tseitin_2 @ X0 @ (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62          | ~ (zip_tseitin_1 @ 
% 20.41/20.62               (sk_D @ X0 @ (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ X0 @ 
% 20.41/20.62               (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62          | ~ (r1_lattice3 @ sk_A @ X0 @ (k1_waybel_9 @ sk_A @ sk_B)))),
% 20.41/20.62      inference('demod', [status(thm)], ['138', '139', '142'])).
% 20.41/20.62  thf('210', plain,
% 20.41/20.62      (((v2_struct_0 @ sk_A)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (zip_tseitin_2 @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62        | ~ (r1_lattice3 @ sk_A @ 
% 20.41/20.62             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62             (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.62        | (zip_tseitin_2 @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62        | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('sup-', [status(thm)], ['208', '209'])).
% 20.41/20.62  thf('211', plain,
% 20.41/20.62      ((~ (r1_lattice3 @ sk_A @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.62        | (zip_tseitin_2 @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('simplify', [status(thm)], ['210'])).
% 20.41/20.62  thf('212', plain,
% 20.41/20.62      (((v2_struct_0 @ sk_A)
% 20.41/20.62        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_A)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (zip_tseitin_2 @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B) @ sk_A))),
% 20.41/20.62      inference('sup-', [status(thm)], ['103', '211'])).
% 20.41/20.62  thf('213', plain,
% 20.41/20.62      (((zip_tseitin_2 @ 
% 20.41/20.62         (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62          (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62         (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62        | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('simplify', [status(thm)], ['212'])).
% 20.41/20.62  thf('214', plain,
% 20.41/20.62      (![X9 : $i, X10 : $i, X11 : $i]:
% 20.41/20.62         ((r2_yellow_0 @ X9 @ X10) | ~ (zip_tseitin_2 @ X10 @ X11 @ X9))),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_4])).
% 20.41/20.62  thf('215', plain,
% 20.41/20.62      (((v2_struct_0 @ sk_A)
% 20.41/20.62        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (r2_yellow_0 @ sk_A @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B))))),
% 20.41/20.62      inference('sup-', [status(thm)], ['213', '214'])).
% 20.41/20.62  thf('216', plain,
% 20.41/20.62      (![X17 : $i, X18 : $i]:
% 20.41/20.62         (~ (l1_waybel_0 @ X17 @ X18)
% 20.41/20.62          | ~ (r2_yellow_0 @ X18 @ 
% 20.41/20.62               (k2_relset_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X18) @ 
% 20.41/20.62                (u1_waybel_0 @ X18 @ X17)))
% 20.41/20.62          | (r2_waybel_9 @ X18 @ X17)
% 20.41/20.62          | ~ (l1_orders_2 @ X18))),
% 20.41/20.62      inference('cnf', [status(esa)], [d4_waybel_9])).
% 20.41/20.62  thf('217', plain,
% 20.41/20.62      (((r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62        | (v2_struct_0 @ sk_A)
% 20.41/20.62        | ~ (l1_orders_2 @ sk_A)
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | ~ (l1_waybel_0 @ sk_B @ sk_A))),
% 20.41/20.62      inference('sup-', [status(thm)], ['215', '216'])).
% 20.41/20.62  thf('218', plain, ((l1_orders_2 @ sk_A)),
% 20.41/20.62      inference('sup-', [status(thm)], ['140', '141'])).
% 20.41/20.62  thf('219', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('220', plain,
% 20.41/20.62      (((r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62        | (v2_struct_0 @ sk_A)
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B))),
% 20.41/20.62      inference('demod', [status(thm)], ['217', '218', '219'])).
% 20.41/20.62  thf('221', plain,
% 20.41/20.62      (((v2_struct_0 @ sk_A)
% 20.41/20.62        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B))),
% 20.41/20.62      inference('simplify', [status(thm)], ['220'])).
% 20.41/20.62  thf('222', plain,
% 20.41/20.62      (![X37 : $i]:
% 20.41/20.62         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X37) @ sk_A @ sk_A)
% 20.41/20.62          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A)))),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('223', plain,
% 20.41/20.62      (((r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_A)
% 20.41/20.62        | (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E @ sk_A)) @ sk_A @ sk_A))),
% 20.41/20.62      inference('sup-', [status(thm)], ['221', '222'])).
% 20.41/20.62  thf('224', plain,
% 20.41/20.62      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 20.41/20.62         ((v2_struct_0 @ X20)
% 20.41/20.62          | ~ (v4_orders_2 @ X20)
% 20.41/20.62          | ~ (v7_waybel_0 @ X20)
% 20.41/20.62          | ~ (l1_waybel_0 @ X20 @ X21)
% 20.41/20.62          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 20.41/20.62          | (r1_lattice3 @ X21 @ 
% 20.41/20.62             (k2_relset_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X21) @ 
% 20.41/20.62              (u1_waybel_0 @ X21 @ X20)) @ 
% 20.41/20.62             X22)
% 20.41/20.62          | ((X23) != (X22))
% 20.41/20.62          | ~ (r3_waybel_9 @ X21 @ X20 @ X23)
% 20.41/20.62          | ~ (v11_waybel_0 @ X20 @ X21)
% 20.41/20.62          | ~ (v5_pre_topc @ (k4_waybel_1 @ X21 @ (sk_E @ X21)) @ X21 @ X21)
% 20.41/20.62          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X21))
% 20.41/20.62          | ~ (l1_waybel_9 @ X21)
% 20.41/20.62          | ~ (v1_compts_1 @ X21)
% 20.41/20.62          | ~ (v2_lattice3 @ X21)
% 20.41/20.62          | ~ (v1_lattice3 @ X21)
% 20.41/20.62          | ~ (v5_orders_2 @ X21)
% 20.41/20.62          | ~ (v4_orders_2 @ X21)
% 20.41/20.62          | ~ (v3_orders_2 @ X21)
% 20.41/20.62          | ~ (v8_pre_topc @ X21)
% 20.41/20.62          | ~ (v2_pre_topc @ X21))),
% 20.41/20.62      inference('cnf', [status(esa)], [l51_waybel_9])).
% 20.41/20.62  thf('225', plain,
% 20.41/20.62      (![X20 : $i, X21 : $i, X22 : $i]:
% 20.41/20.62         (~ (v2_pre_topc @ X21)
% 20.41/20.62          | ~ (v8_pre_topc @ X21)
% 20.41/20.62          | ~ (v3_orders_2 @ X21)
% 20.41/20.62          | ~ (v4_orders_2 @ X21)
% 20.41/20.62          | ~ (v5_orders_2 @ X21)
% 20.41/20.62          | ~ (v1_lattice3 @ X21)
% 20.41/20.62          | ~ (v2_lattice3 @ X21)
% 20.41/20.62          | ~ (v1_compts_1 @ X21)
% 20.41/20.62          | ~ (l1_waybel_9 @ X21)
% 20.41/20.62          | ~ (v5_pre_topc @ (k4_waybel_1 @ X21 @ (sk_E @ X21)) @ X21 @ X21)
% 20.41/20.62          | ~ (v11_waybel_0 @ X20 @ X21)
% 20.41/20.62          | ~ (r3_waybel_9 @ X21 @ X20 @ X22)
% 20.41/20.62          | (r1_lattice3 @ X21 @ 
% 20.41/20.62             (k2_relset_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X21) @ 
% 20.41/20.62              (u1_waybel_0 @ X21 @ X20)) @ 
% 20.41/20.62             X22)
% 20.41/20.62          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 20.41/20.62          | ~ (l1_waybel_0 @ X20 @ X21)
% 20.41/20.62          | ~ (v7_waybel_0 @ X20)
% 20.41/20.62          | ~ (v4_orders_2 @ X20)
% 20.41/20.62          | (v2_struct_0 @ X20))),
% 20.41/20.62      inference('simplify', [status(thm)], ['224'])).
% 20.41/20.62  thf('226', plain,
% 20.41/20.62      (![X0 : $i, X1 : $i]:
% 20.41/20.62         ((v2_struct_0 @ sk_A)
% 20.41/20.62          | (v2_struct_0 @ sk_B)
% 20.41/20.62          | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62          | (v2_struct_0 @ X0)
% 20.41/20.62          | ~ (v4_orders_2 @ X0)
% 20.41/20.62          | ~ (v7_waybel_0 @ X0)
% 20.41/20.62          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 20.41/20.62          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 20.41/20.62          | (r1_lattice3 @ sk_A @ 
% 20.41/20.62             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62              (u1_waybel_0 @ sk_A @ X0)) @ 
% 20.41/20.62             X1)
% 20.41/20.62          | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 20.41/20.62          | ~ (v11_waybel_0 @ X0 @ sk_A)
% 20.41/20.62          | ~ (l1_waybel_9 @ sk_A)
% 20.41/20.62          | ~ (v1_compts_1 @ sk_A)
% 20.41/20.62          | ~ (v2_lattice3 @ sk_A)
% 20.41/20.62          | ~ (v1_lattice3 @ sk_A)
% 20.41/20.62          | ~ (v5_orders_2 @ sk_A)
% 20.41/20.62          | ~ (v4_orders_2 @ sk_A)
% 20.41/20.62          | ~ (v3_orders_2 @ sk_A)
% 20.41/20.62          | ~ (v8_pre_topc @ sk_A)
% 20.41/20.62          | ~ (v2_pre_topc @ sk_A))),
% 20.41/20.62      inference('sup-', [status(thm)], ['223', '225'])).
% 20.41/20.62  thf('227', plain, ((l1_waybel_9 @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('228', plain, ((v1_compts_1 @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('229', plain, ((v2_lattice3 @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('230', plain, ((v1_lattice3 @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('231', plain, ((v5_orders_2 @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('232', plain, ((v4_orders_2 @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('233', plain, ((v3_orders_2 @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('234', plain, ((v8_pre_topc @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('235', plain, ((v2_pre_topc @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('236', plain,
% 20.41/20.62      (![X0 : $i, X1 : $i]:
% 20.41/20.62         ((v2_struct_0 @ sk_A)
% 20.41/20.62          | (v2_struct_0 @ sk_B)
% 20.41/20.62          | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62          | (v2_struct_0 @ X0)
% 20.41/20.62          | ~ (v4_orders_2 @ X0)
% 20.41/20.62          | ~ (v7_waybel_0 @ X0)
% 20.41/20.62          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 20.41/20.62          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 20.41/20.62          | (r1_lattice3 @ sk_A @ 
% 20.41/20.62             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62              (u1_waybel_0 @ sk_A @ X0)) @ 
% 20.41/20.62             X1)
% 20.41/20.62          | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 20.41/20.62          | ~ (v11_waybel_0 @ X0 @ sk_A))),
% 20.41/20.62      inference('demod', [status(thm)],
% 20.41/20.62                ['226', '227', '228', '229', '230', '231', '232', '233', 
% 20.41/20.62                 '234', '235'])).
% 20.41/20.62  thf('237', plain,
% 20.41/20.62      (![X0 : $i]:
% 20.41/20.62         ((v2_struct_0 @ sk_A)
% 20.41/20.62          | ~ (v11_waybel_0 @ X0 @ sk_A)
% 20.41/20.62          | ~ (r3_waybel_9 @ sk_A @ X0 @ (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.62          | (r1_lattice3 @ sk_A @ 
% 20.41/20.62             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62              (u1_waybel_0 @ sk_A @ X0)) @ 
% 20.41/20.62             (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.62          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 20.41/20.62          | ~ (v7_waybel_0 @ X0)
% 20.41/20.62          | ~ (v4_orders_2 @ X0)
% 20.41/20.62          | (v2_struct_0 @ X0)
% 20.41/20.62          | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62          | (v2_struct_0 @ sk_B)
% 20.41/20.62          | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('sup-', [status(thm)], ['78', '236'])).
% 20.41/20.62  thf('238', plain,
% 20.41/20.62      (![X0 : $i]:
% 20.41/20.62         ((v2_struct_0 @ sk_B)
% 20.41/20.62          | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62          | (v2_struct_0 @ X0)
% 20.41/20.62          | ~ (v4_orders_2 @ X0)
% 20.41/20.62          | ~ (v7_waybel_0 @ X0)
% 20.41/20.62          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 20.41/20.62          | (r1_lattice3 @ sk_A @ 
% 20.41/20.62             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62              (u1_waybel_0 @ sk_A @ X0)) @ 
% 20.41/20.62             (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.62          | ~ (r3_waybel_9 @ sk_A @ X0 @ (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.62          | ~ (v11_waybel_0 @ X0 @ sk_A)
% 20.41/20.62          | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('simplify', [status(thm)], ['237'])).
% 20.41/20.62  thf('239', plain,
% 20.41/20.62      (((v2_struct_0 @ sk_A)
% 20.41/20.62        | (v2_struct_0 @ sk_A)
% 20.41/20.62        | ~ (v11_waybel_0 @ sk_B @ sk_A)
% 20.41/20.62        | (r1_lattice3 @ sk_A @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.62        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 20.41/20.62        | ~ (v7_waybel_0 @ sk_B)
% 20.41/20.62        | ~ (v4_orders_2 @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_B))),
% 20.41/20.62      inference('sup-', [status(thm)], ['74', '238'])).
% 20.41/20.62  thf('240', plain, ((v11_waybel_0 @ sk_B @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('241', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('242', plain, ((v7_waybel_0 @ sk_B)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('243', plain, ((v4_orders_2 @ sk_B)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('244', plain,
% 20.41/20.62      (((v2_struct_0 @ sk_A)
% 20.41/20.62        | (v2_struct_0 @ sk_A)
% 20.41/20.62        | (r1_lattice3 @ sk_A @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_B))),
% 20.41/20.62      inference('demod', [status(thm)], ['239', '240', '241', '242', '243'])).
% 20.41/20.62  thf('245', plain,
% 20.41/20.62      (((r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (r1_lattice3 @ sk_A @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.62        | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('simplify', [status(thm)], ['244'])).
% 20.41/20.62  thf('246', plain,
% 20.41/20.62      (((v2_struct_0 @ sk_A)
% 20.41/20.62        | (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 20.41/20.62      inference('simplify', [status(thm)], ['77'])).
% 20.41/20.62  thf('247', plain,
% 20.41/20.62      (((v2_struct_0 @ sk_A)
% 20.41/20.62        | (r3_waybel_9 @ sk_A @ sk_B @ (k1_waybel_9 @ sk_A @ sk_B)))),
% 20.41/20.62      inference('simplify', [status(thm)], ['73'])).
% 20.41/20.62  thf('248', plain,
% 20.41/20.62      (((r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (r1_lattice3 @ sk_A @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.62        | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('simplify', [status(thm)], ['244'])).
% 20.41/20.62  thf('249', plain,
% 20.41/20.62      (((r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (r1_lattice3 @ sk_A @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.62        | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('simplify', [status(thm)], ['244'])).
% 20.41/20.62  thf('250', plain,
% 20.41/20.62      (((zip_tseitin_2 @ 
% 20.41/20.62         (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62          (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62         (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62        | ~ (r1_lattice3 @ sk_A @ 
% 20.41/20.62             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62             (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.62        | (v2_struct_0 @ sk_A)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (r1_orders_2 @ sk_A @ 
% 20.41/20.62           (sk_D @ 
% 20.41/20.62            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62            (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.62        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 20.41/20.62      inference('simplify', [status(thm)], ['144'])).
% 20.41/20.62  thf('251', plain,
% 20.41/20.62      (((v2_struct_0 @ sk_A)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62        | (r1_orders_2 @ sk_A @ 
% 20.41/20.62           (sk_D @ 
% 20.41/20.62            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62            (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_A)
% 20.41/20.62        | (zip_tseitin_2 @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B) @ sk_A))),
% 20.41/20.62      inference('sup-', [status(thm)], ['249', '250'])).
% 20.41/20.62  thf('252', plain,
% 20.41/20.62      (((zip_tseitin_2 @ 
% 20.41/20.62         (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62          (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62         (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62        | (r1_orders_2 @ sk_A @ 
% 20.41/20.62           (sk_D @ 
% 20.41/20.62            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62            (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.62        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('simplify', [status(thm)], ['251'])).
% 20.41/20.62  thf('253', plain,
% 20.41/20.62      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 20.41/20.62         ((zip_tseitin_0 @ X1 @ X2 @ X3 @ X4) | ~ (r1_orders_2 @ X4 @ X1 @ X3))),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 20.41/20.62  thf('254', plain,
% 20.41/20.62      (![X0 : $i]:
% 20.41/20.62         ((v2_struct_0 @ sk_A)
% 20.41/20.62          | (v2_struct_0 @ sk_B)
% 20.41/20.62          | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62          | (zip_tseitin_2 @ 
% 20.41/20.62             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62             (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62          | (zip_tseitin_0 @ 
% 20.41/20.62             (sk_D @ 
% 20.41/20.62              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62              (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62             X0 @ (k1_waybel_9 @ sk_A @ sk_B) @ sk_A))),
% 20.41/20.62      inference('sup-', [status(thm)], ['252', '253'])).
% 20.41/20.62  thf('255', plain,
% 20.41/20.62      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 20.41/20.62         ((zip_tseitin_1 @ X5 @ X6 @ X7 @ X8)
% 20.41/20.62          | ~ (zip_tseitin_0 @ X5 @ X6 @ X7 @ X8))),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 20.41/20.62  thf('256', plain,
% 20.41/20.62      (![X0 : $i]:
% 20.41/20.62         ((zip_tseitin_2 @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62          | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62          | (v2_struct_0 @ sk_B)
% 20.41/20.62          | (v2_struct_0 @ sk_A)
% 20.41/20.62          | (zip_tseitin_1 @ 
% 20.41/20.62             (sk_D @ 
% 20.41/20.62              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62              (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62             X0 @ (k1_waybel_9 @ sk_A @ sk_B) @ sk_A))),
% 20.41/20.62      inference('sup-', [status(thm)], ['254', '255'])).
% 20.41/20.62  thf('257', plain,
% 20.41/20.62      (![X0 : $i]:
% 20.41/20.62         ((v2_struct_0 @ sk_A)
% 20.41/20.62          | (zip_tseitin_2 @ X0 @ (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62          | ~ (zip_tseitin_1 @ 
% 20.41/20.62               (sk_D @ X0 @ (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ X0 @ 
% 20.41/20.62               (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62          | ~ (r1_lattice3 @ sk_A @ X0 @ (k1_waybel_9 @ sk_A @ sk_B)))),
% 20.41/20.62      inference('demod', [status(thm)], ['138', '139', '142'])).
% 20.41/20.62  thf('258', plain,
% 20.41/20.62      (((v2_struct_0 @ sk_A)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62        | (zip_tseitin_2 @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62        | ~ (r1_lattice3 @ sk_A @ 
% 20.41/20.62             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62             (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.62        | (zip_tseitin_2 @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62        | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('sup-', [status(thm)], ['256', '257'])).
% 20.41/20.62  thf('259', plain,
% 20.41/20.62      ((~ (r1_lattice3 @ sk_A @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.62        | (zip_tseitin_2 @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('simplify', [status(thm)], ['258'])).
% 20.41/20.62  thf('260', plain,
% 20.41/20.62      (((v2_struct_0 @ sk_A)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_A)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62        | (zip_tseitin_2 @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B) @ sk_A))),
% 20.41/20.62      inference('sup-', [status(thm)], ['248', '259'])).
% 20.41/20.62  thf('261', plain,
% 20.41/20.62      (((zip_tseitin_2 @ 
% 20.41/20.62         (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62          (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62         (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('simplify', [status(thm)], ['260'])).
% 20.41/20.62  thf('262', plain,
% 20.41/20.62      (![X9 : $i, X10 : $i, X11 : $i]:
% 20.41/20.62         ((r2_yellow_0 @ X9 @ X10) | ~ (zip_tseitin_2 @ X10 @ X11 @ X9))),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_4])).
% 20.41/20.62  thf('263', plain,
% 20.41/20.62      (((v2_struct_0 @ sk_A)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62        | (r2_yellow_0 @ sk_A @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B))))),
% 20.41/20.62      inference('sup-', [status(thm)], ['261', '262'])).
% 20.41/20.62  thf('264', plain,
% 20.41/20.62      (![X17 : $i, X18 : $i]:
% 20.41/20.62         (~ (l1_waybel_0 @ X17 @ X18)
% 20.41/20.62          | ~ (r2_yellow_0 @ X18 @ 
% 20.41/20.62               (k2_relset_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X18) @ 
% 20.41/20.62                (u1_waybel_0 @ X18 @ X17)))
% 20.41/20.62          | (r2_waybel_9 @ X18 @ X17)
% 20.41/20.62          | ~ (l1_orders_2 @ X18))),
% 20.41/20.62      inference('cnf', [status(esa)], [d4_waybel_9])).
% 20.41/20.62  thf('265', plain,
% 20.41/20.62      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_A)
% 20.41/20.62        | ~ (l1_orders_2 @ sk_A)
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | ~ (l1_waybel_0 @ sk_B @ sk_A))),
% 20.41/20.62      inference('sup-', [status(thm)], ['263', '264'])).
% 20.41/20.62  thf('266', plain, ((l1_orders_2 @ sk_A)),
% 20.41/20.62      inference('sup-', [status(thm)], ['140', '141'])).
% 20.41/20.62  thf('267', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('268', plain,
% 20.41/20.62      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_A)
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B))),
% 20.41/20.62      inference('demod', [status(thm)], ['265', '266', '267'])).
% 20.41/20.62  thf('269', plain,
% 20.41/20.62      (((v2_struct_0 @ sk_A)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 20.41/20.62      inference('simplify', [status(thm)], ['268'])).
% 20.41/20.62  thf('270', plain,
% 20.41/20.62      (![X37 : $i]:
% 20.41/20.62         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X37) @ sk_A @ sk_A)
% 20.41/20.62          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A)))),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('271', plain,
% 20.41/20.62      (((r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_A)
% 20.41/20.62        | (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ sk_A))),
% 20.41/20.62      inference('sup-', [status(thm)], ['269', '270'])).
% 20.41/20.62  thf('272', plain,
% 20.41/20.62      (((r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (r1_lattice3 @ sk_A @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.62        | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('simplify', [status(thm)], ['244'])).
% 20.41/20.62  thf('273', plain,
% 20.41/20.62      (![X0 : $i]:
% 20.41/20.62         ((m1_subset_1 @ (sk_D @ X0 @ (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62           (u1_struct_0 @ sk_A))
% 20.41/20.62          | ~ (r1_lattice3 @ sk_A @ X0 @ (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.62          | (zip_tseitin_2 @ X0 @ (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62          | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('sup-', [status(thm)], ['167', '168'])).
% 20.41/20.62  thf('274', plain,
% 20.41/20.62      (((v2_struct_0 @ sk_A)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_A)
% 20.41/20.62        | (zip_tseitin_2 @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62        | (m1_subset_1 @ 
% 20.41/20.62           (sk_D @ 
% 20.41/20.62            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62            (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62           (u1_struct_0 @ sk_A)))),
% 20.41/20.62      inference('sup-', [status(thm)], ['272', '273'])).
% 20.41/20.62  thf('275', plain,
% 20.41/20.62      (((m1_subset_1 @ 
% 20.41/20.62         (sk_D @ 
% 20.41/20.62          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62          (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62         (u1_struct_0 @ sk_A))
% 20.41/20.62        | (zip_tseitin_2 @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('simplify', [status(thm)], ['274'])).
% 20.41/20.62  thf('276', plain,
% 20.41/20.62      (((r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (r1_lattice3 @ sk_A @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.62        | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('simplify', [status(thm)], ['244'])).
% 20.41/20.62  thf('277', plain,
% 20.41/20.62      (![X0 : $i]:
% 20.41/20.62         ((r1_lattice3 @ sk_A @ X0 @ 
% 20.41/20.62           (sk_D @ X0 @ (k1_waybel_9 @ sk_A @ sk_B) @ sk_A))
% 20.41/20.62          | ~ (r1_lattice3 @ sk_A @ X0 @ (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.62          | (zip_tseitin_2 @ X0 @ (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62          | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('sup-', [status(thm)], ['175', '176'])).
% 20.41/20.62  thf('278', plain,
% 20.41/20.62      (((v2_struct_0 @ sk_A)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_A)
% 20.41/20.62        | (zip_tseitin_2 @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62        | (r1_lattice3 @ sk_A @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (sk_D @ 
% 20.41/20.62            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62            (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)))),
% 20.41/20.62      inference('sup-', [status(thm)], ['276', '277'])).
% 20.41/20.62  thf('279', plain,
% 20.41/20.62      (((r1_lattice3 @ sk_A @ 
% 20.41/20.62         (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62          (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62         (sk_D @ 
% 20.41/20.62          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62          (k1_waybel_9 @ sk_A @ sk_B) @ sk_A))
% 20.41/20.62        | (zip_tseitin_2 @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('simplify', [status(thm)], ['278'])).
% 20.41/20.62  thf('280', plain,
% 20.41/20.62      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 20.41/20.62         (~ (v2_pre_topc @ X25)
% 20.41/20.62          | ~ (v8_pre_topc @ X25)
% 20.41/20.62          | ~ (v3_orders_2 @ X25)
% 20.41/20.62          | ~ (v4_orders_2 @ X25)
% 20.41/20.62          | ~ (v5_orders_2 @ X25)
% 20.41/20.62          | ~ (v1_lattice3 @ X25)
% 20.41/20.62          | ~ (v2_lattice3 @ X25)
% 20.41/20.62          | ~ (v1_compts_1 @ X25)
% 20.41/20.62          | ~ (l1_waybel_9 @ X25)
% 20.41/20.62          | ~ (v5_pre_topc @ (k4_waybel_1 @ X25 @ (sk_E_1 @ X25)) @ X25 @ X25)
% 20.41/20.62          | ~ (r3_waybel_9 @ X25 @ X24 @ X26)
% 20.41/20.62          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X25))
% 20.41/20.62          | (r1_orders_2 @ X25 @ X27 @ X26)
% 20.41/20.62          | ~ (r1_lattice3 @ X25 @ 
% 20.41/20.62               (k2_relset_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X25) @ 
% 20.41/20.62                (u1_waybel_0 @ X25 @ X24)) @ 
% 20.41/20.62               X27)
% 20.41/20.62          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X25))
% 20.41/20.62          | ~ (l1_waybel_0 @ X24 @ X25)
% 20.41/20.62          | ~ (v7_waybel_0 @ X24)
% 20.41/20.62          | ~ (v4_orders_2 @ X24)
% 20.41/20.62          | (v2_struct_0 @ X24))),
% 20.41/20.62      inference('simplify', [status(thm)], ['180'])).
% 20.41/20.62  thf('281', plain,
% 20.41/20.62      (![X0 : $i]:
% 20.41/20.62         ((v2_struct_0 @ sk_A)
% 20.41/20.62          | (v2_struct_0 @ sk_B)
% 20.41/20.62          | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62          | (zip_tseitin_2 @ 
% 20.41/20.62             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62             (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62          | (v2_struct_0 @ sk_B)
% 20.41/20.62          | ~ (v4_orders_2 @ sk_B)
% 20.41/20.62          | ~ (v7_waybel_0 @ sk_B)
% 20.41/20.62          | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 20.41/20.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 20.41/20.62          | (r1_orders_2 @ sk_A @ 
% 20.41/20.62             (sk_D @ 
% 20.41/20.62              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62              (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62             X0)
% 20.41/20.62          | ~ (m1_subset_1 @ 
% 20.41/20.62               (sk_D @ 
% 20.41/20.62                (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62                 (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62                (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62               (u1_struct_0 @ sk_A))
% 20.41/20.62          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 20.41/20.62          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ 
% 20.41/20.62               sk_A)
% 20.41/20.62          | ~ (l1_waybel_9 @ sk_A)
% 20.41/20.62          | ~ (v1_compts_1 @ sk_A)
% 20.41/20.62          | ~ (v2_lattice3 @ sk_A)
% 20.41/20.62          | ~ (v1_lattice3 @ sk_A)
% 20.41/20.62          | ~ (v5_orders_2 @ sk_A)
% 20.41/20.62          | ~ (v4_orders_2 @ sk_A)
% 20.41/20.62          | ~ (v3_orders_2 @ sk_A)
% 20.41/20.62          | ~ (v8_pre_topc @ sk_A)
% 20.41/20.62          | ~ (v2_pre_topc @ sk_A))),
% 20.41/20.62      inference('sup-', [status(thm)], ['279', '280'])).
% 20.41/20.62  thf('282', plain, ((v4_orders_2 @ sk_B)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('283', plain, ((v7_waybel_0 @ sk_B)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('284', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('285', plain, ((l1_waybel_9 @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('286', plain, ((v1_compts_1 @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('287', plain, ((v2_lattice3 @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('288', plain, ((v1_lattice3 @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('289', plain, ((v5_orders_2 @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('290', plain, ((v4_orders_2 @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('291', plain, ((v3_orders_2 @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('292', plain, ((v8_pre_topc @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('293', plain, ((v2_pre_topc @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('294', plain,
% 20.41/20.62      (![X0 : $i]:
% 20.41/20.62         ((v2_struct_0 @ sk_A)
% 20.41/20.62          | (v2_struct_0 @ sk_B)
% 20.41/20.62          | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62          | (zip_tseitin_2 @ 
% 20.41/20.62             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62             (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62          | (v2_struct_0 @ sk_B)
% 20.41/20.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 20.41/20.62          | (r1_orders_2 @ sk_A @ 
% 20.41/20.62             (sk_D @ 
% 20.41/20.62              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62              (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62             X0)
% 20.41/20.62          | ~ (m1_subset_1 @ 
% 20.41/20.62               (sk_D @ 
% 20.41/20.62                (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62                 (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62                (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62               (u1_struct_0 @ sk_A))
% 20.41/20.62          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 20.41/20.62          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ 
% 20.41/20.62               sk_A))),
% 20.41/20.62      inference('demod', [status(thm)],
% 20.41/20.62                ['281', '282', '283', '284', '285', '286', '287', '288', 
% 20.41/20.62                 '289', '290', '291', '292', '293'])).
% 20.41/20.62  thf('295', plain,
% 20.41/20.62      (![X0 : $i]:
% 20.41/20.62         (~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ sk_A)
% 20.41/20.62          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 20.41/20.62          | ~ (m1_subset_1 @ 
% 20.41/20.62               (sk_D @ 
% 20.41/20.62                (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62                 (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62                (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62               (u1_struct_0 @ sk_A))
% 20.41/20.62          | (r1_orders_2 @ sk_A @ 
% 20.41/20.62             (sk_D @ 
% 20.41/20.62              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62              (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62             X0)
% 20.41/20.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 20.41/20.62          | (zip_tseitin_2 @ 
% 20.41/20.62             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62             (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62          | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62          | (v2_struct_0 @ sk_B)
% 20.41/20.62          | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('simplify', [status(thm)], ['294'])).
% 20.41/20.62  thf('296', plain,
% 20.41/20.62      (![X0 : $i]:
% 20.41/20.62         ((v2_struct_0 @ sk_A)
% 20.41/20.62          | (v2_struct_0 @ sk_B)
% 20.41/20.62          | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62          | (zip_tseitin_2 @ 
% 20.41/20.62             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62             (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62          | (v2_struct_0 @ sk_A)
% 20.41/20.62          | (v2_struct_0 @ sk_B)
% 20.41/20.62          | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62          | (zip_tseitin_2 @ 
% 20.41/20.62             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62             (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 20.41/20.62          | (r1_orders_2 @ sk_A @ 
% 20.41/20.62             (sk_D @ 
% 20.41/20.62              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62              (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62             X0)
% 20.41/20.62          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 20.41/20.62          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ 
% 20.41/20.62               sk_A))),
% 20.41/20.62      inference('sup-', [status(thm)], ['275', '295'])).
% 20.41/20.62  thf('297', plain,
% 20.41/20.62      (![X0 : $i]:
% 20.41/20.62         (~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ sk_A)
% 20.41/20.62          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 20.41/20.62          | (r1_orders_2 @ sk_A @ 
% 20.41/20.62             (sk_D @ 
% 20.41/20.62              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62              (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62             X0)
% 20.41/20.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 20.41/20.62          | (zip_tseitin_2 @ 
% 20.41/20.62             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62             (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62          | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62          | (v2_struct_0 @ sk_B)
% 20.41/20.62          | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('simplify', [status(thm)], ['296'])).
% 20.41/20.62  thf('298', plain,
% 20.41/20.62      (![X0 : $i]:
% 20.41/20.62         ((v2_struct_0 @ sk_A)
% 20.41/20.62          | (v2_struct_0 @ sk_B)
% 20.41/20.62          | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62          | (v2_struct_0 @ sk_A)
% 20.41/20.62          | (v2_struct_0 @ sk_B)
% 20.41/20.62          | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62          | (zip_tseitin_2 @ 
% 20.41/20.62             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62             (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 20.41/20.62          | (r1_orders_2 @ sk_A @ 
% 20.41/20.62             (sk_D @ 
% 20.41/20.62              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62              (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62             X0)
% 20.41/20.62          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0))),
% 20.41/20.62      inference('sup-', [status(thm)], ['271', '297'])).
% 20.41/20.62  thf('299', plain,
% 20.41/20.62      (![X0 : $i]:
% 20.41/20.62         (~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 20.41/20.62          | (r1_orders_2 @ sk_A @ 
% 20.41/20.62             (sk_D @ 
% 20.41/20.62              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62              (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62             X0)
% 20.41/20.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 20.41/20.62          | (zip_tseitin_2 @ 
% 20.41/20.62             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62             (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62          | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62          | (v2_struct_0 @ sk_B)
% 20.41/20.62          | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('simplify', [status(thm)], ['298'])).
% 20.41/20.62  thf('300', plain,
% 20.41/20.62      (((v2_struct_0 @ sk_A)
% 20.41/20.62        | (v2_struct_0 @ sk_A)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (zip_tseitin_2 @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62        | ~ (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 20.41/20.62        | (r1_orders_2 @ sk_A @ 
% 20.41/20.62           (sk_D @ 
% 20.41/20.62            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62            (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B)))),
% 20.41/20.62      inference('sup-', [status(thm)], ['247', '299'])).
% 20.41/20.62  thf('301', plain,
% 20.41/20.62      (((r1_orders_2 @ sk_A @ 
% 20.41/20.62         (sk_D @ 
% 20.41/20.62          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62          (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62         (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.62        | ~ (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 20.41/20.62        | (zip_tseitin_2 @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('simplify', [status(thm)], ['300'])).
% 20.41/20.62  thf('302', plain,
% 20.41/20.62      (((v2_struct_0 @ sk_A)
% 20.41/20.62        | (v2_struct_0 @ sk_A)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (zip_tseitin_2 @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62        | (r1_orders_2 @ sk_A @ 
% 20.41/20.62           (sk_D @ 
% 20.41/20.62            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62            (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B)))),
% 20.41/20.62      inference('sup-', [status(thm)], ['246', '301'])).
% 20.41/20.62  thf('303', plain,
% 20.41/20.62      (((r1_orders_2 @ sk_A @ 
% 20.41/20.62         (sk_D @ 
% 20.41/20.62          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62          (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62         (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.62        | (zip_tseitin_2 @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('simplify', [status(thm)], ['302'])).
% 20.41/20.62  thf('304', plain,
% 20.41/20.62      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 20.41/20.62         ((zip_tseitin_0 @ X1 @ X2 @ X3 @ X4) | ~ (r1_orders_2 @ X4 @ X1 @ X3))),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 20.41/20.62  thf('305', plain,
% 20.41/20.62      (![X0 : $i]:
% 20.41/20.62         ((v2_struct_0 @ sk_A)
% 20.41/20.62          | (v2_struct_0 @ sk_B)
% 20.41/20.62          | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62          | (zip_tseitin_2 @ 
% 20.41/20.62             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62             (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62          | (zip_tseitin_0 @ 
% 20.41/20.62             (sk_D @ 
% 20.41/20.62              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62              (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62             X0 @ (k1_waybel_9 @ sk_A @ sk_B) @ sk_A))),
% 20.41/20.62      inference('sup-', [status(thm)], ['303', '304'])).
% 20.41/20.62  thf('306', plain,
% 20.41/20.62      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 20.41/20.62         ((zip_tseitin_1 @ X5 @ X6 @ X7 @ X8)
% 20.41/20.62          | ~ (zip_tseitin_0 @ X5 @ X6 @ X7 @ X8))),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 20.41/20.62  thf('307', plain,
% 20.41/20.62      (![X0 : $i]:
% 20.41/20.62         ((zip_tseitin_2 @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62          | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62          | (v2_struct_0 @ sk_B)
% 20.41/20.62          | (v2_struct_0 @ sk_A)
% 20.41/20.62          | (zip_tseitin_1 @ 
% 20.41/20.62             (sk_D @ 
% 20.41/20.62              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62              (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ 
% 20.41/20.62             X0 @ (k1_waybel_9 @ sk_A @ sk_B) @ sk_A))),
% 20.41/20.62      inference('sup-', [status(thm)], ['305', '306'])).
% 20.41/20.62  thf('308', plain,
% 20.41/20.62      (![X0 : $i]:
% 20.41/20.62         ((v2_struct_0 @ sk_A)
% 20.41/20.62          | (zip_tseitin_2 @ X0 @ (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62          | ~ (zip_tseitin_1 @ 
% 20.41/20.62               (sk_D @ X0 @ (k1_waybel_9 @ sk_A @ sk_B) @ sk_A) @ X0 @ 
% 20.41/20.62               (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62          | ~ (r1_lattice3 @ sk_A @ X0 @ (k1_waybel_9 @ sk_A @ sk_B)))),
% 20.41/20.62      inference('demod', [status(thm)], ['138', '139', '142'])).
% 20.41/20.62  thf('309', plain,
% 20.41/20.62      (((v2_struct_0 @ sk_A)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (zip_tseitin_2 @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62        | ~ (r1_lattice3 @ sk_A @ 
% 20.41/20.62             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62             (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.62        | (zip_tseitin_2 @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62        | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('sup-', [status(thm)], ['307', '308'])).
% 20.41/20.62  thf('310', plain,
% 20.41/20.62      ((~ (r1_lattice3 @ sk_A @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.62        | (zip_tseitin_2 @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('simplify', [status(thm)], ['309'])).
% 20.41/20.62  thf('311', plain,
% 20.41/20.62      (((v2_struct_0 @ sk_A)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_A)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (zip_tseitin_2 @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62           (k1_waybel_9 @ sk_A @ sk_B) @ sk_A))),
% 20.41/20.62      inference('sup-', [status(thm)], ['245', '310'])).
% 20.41/20.62  thf('312', plain,
% 20.41/20.62      (((zip_tseitin_2 @ 
% 20.41/20.62         (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62          (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 20.41/20.62         (k1_waybel_9 @ sk_A @ sk_B) @ sk_A)
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('simplify', [status(thm)], ['311'])).
% 20.41/20.62  thf('313', plain,
% 20.41/20.62      (![X9 : $i, X10 : $i, X11 : $i]:
% 20.41/20.62         ((r2_yellow_0 @ X9 @ X10) | ~ (zip_tseitin_2 @ X10 @ X11 @ X9))),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_4])).
% 20.41/20.62  thf('314', plain,
% 20.41/20.62      (((v2_struct_0 @ sk_A)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (r2_yellow_0 @ sk_A @ 
% 20.41/20.62           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 20.41/20.62            (u1_waybel_0 @ sk_A @ sk_B))))),
% 20.41/20.62      inference('sup-', [status(thm)], ['312', '313'])).
% 20.41/20.62  thf('315', plain,
% 20.41/20.62      (![X17 : $i, X18 : $i]:
% 20.41/20.62         (~ (l1_waybel_0 @ X17 @ X18)
% 20.41/20.62          | ~ (r2_yellow_0 @ X18 @ 
% 20.41/20.62               (k2_relset_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X18) @ 
% 20.41/20.62                (u1_waybel_0 @ X18 @ X17)))
% 20.41/20.62          | (r2_waybel_9 @ X18 @ X17)
% 20.41/20.62          | ~ (l1_orders_2 @ X18))),
% 20.41/20.62      inference('cnf', [status(esa)], [d4_waybel_9])).
% 20.41/20.62  thf('316', plain,
% 20.41/20.62      (((r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_A)
% 20.41/20.62        | ~ (l1_orders_2 @ sk_A)
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | ~ (l1_waybel_0 @ sk_B @ sk_A))),
% 20.41/20.62      inference('sup-', [status(thm)], ['314', '315'])).
% 20.41/20.62  thf('317', plain, ((l1_orders_2 @ sk_A)),
% 20.41/20.62      inference('sup-', [status(thm)], ['140', '141'])).
% 20.41/20.62  thf('318', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('319', plain,
% 20.41/20.62      (((r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_A)
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B))),
% 20.41/20.62      inference('demod', [status(thm)], ['316', '317', '318'])).
% 20.41/20.62  thf('320', plain,
% 20.41/20.62      (((v2_struct_0 @ sk_A)
% 20.41/20.62        | (v2_struct_0 @ sk_B)
% 20.41/20.62        | (r2_waybel_9 @ sk_A @ sk_B))),
% 20.41/20.62      inference('simplify', [status(thm)], ['319'])).
% 20.41/20.62  thf('321', plain, (~ (v2_struct_0 @ sk_B)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('322', plain, (((r2_waybel_9 @ sk_A @ sk_B) | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('clc', [status(thm)], ['320', '321'])).
% 20.41/20.62  thf('323', plain,
% 20.41/20.62      ((~ (r2_waybel_9 @ sk_A @ sk_B)
% 20.41/20.62        | ~ (r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.41/20.62             (k10_yellow_6 @ sk_A @ sk_B)))),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('324', plain,
% 20.41/20.62      ((~ (r2_waybel_9 @ sk_A @ sk_B)) <= (~ ((r2_waybel_9 @ sk_A @ sk_B)))),
% 20.41/20.62      inference('split', [status(esa)], ['323'])).
% 20.41/20.62  thf('325', plain,
% 20.41/20.62      (((v2_struct_0 @ sk_A)
% 20.41/20.62        | ((sk_C @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B)))),
% 20.41/20.62      inference('clc', [status(thm)], ['69', '70'])).
% 20.41/20.62  thf('326', plain,
% 20.41/20.62      (((r3_waybel_9 @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 20.41/20.62        | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('clc', [status(thm)], ['11', '12'])).
% 20.41/20.62  thf('327', plain,
% 20.41/20.62      (((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62        | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('clc', [status(thm)], ['23', '24'])).
% 20.41/20.62  thf(t33_waybel_9, axiom,
% 20.41/20.62    (![A:$i]:
% 20.41/20.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 20.41/20.62         ( v8_pre_topc @ A ) & ( v1_compts_1 @ A ) & ( l1_pre_topc @ A ) ) =>
% 20.41/20.62       ( ![B:$i]:
% 20.41/20.62         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 20.41/20.62             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 20.41/20.62           ( ( ![C:$i]:
% 20.41/20.62               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 20.41/20.62                 ( ![D:$i]:
% 20.41/20.62                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 20.41/20.62                     ( ( ( r3_waybel_9 @ A @ B @ C ) & 
% 20.41/20.62                         ( r3_waybel_9 @ A @ B @ D ) ) =>
% 20.41/20.62                       ( ( C ) = ( D ) ) ) ) ) ) ) =>
% 20.41/20.62             ( ![C:$i]:
% 20.41/20.62               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 20.41/20.62                 ( ( r3_waybel_9 @ A @ B @ C ) =>
% 20.41/20.62                   ( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) ) ) ) ) ) ) ) ))).
% 20.41/20.62  thf('328', plain,
% 20.41/20.62      (![X31 : $i, X32 : $i, X33 : $i]:
% 20.41/20.62         ((v2_struct_0 @ X31)
% 20.41/20.62          | ~ (v4_orders_2 @ X31)
% 20.41/20.62          | ~ (v7_waybel_0 @ X31)
% 20.41/20.62          | ~ (l1_waybel_0 @ X31 @ X32)
% 20.41/20.62          | ~ (r3_waybel_9 @ X32 @ X31 @ X33)
% 20.41/20.62          | (r2_hidden @ X33 @ (k10_yellow_6 @ X32 @ X31))
% 20.41/20.62          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 20.41/20.62          | (r3_waybel_9 @ X32 @ X31 @ (sk_C_1 @ X31 @ X32))
% 20.41/20.62          | ~ (l1_pre_topc @ X32)
% 20.41/20.62          | ~ (v1_compts_1 @ X32)
% 20.41/20.62          | ~ (v8_pre_topc @ X32)
% 20.41/20.62          | ~ (v2_pre_topc @ X32)
% 20.41/20.62          | (v2_struct_0 @ X32))),
% 20.41/20.62      inference('cnf', [status(esa)], [t33_waybel_9])).
% 20.41/20.62  thf('329', plain,
% 20.41/20.62      (![X0 : $i]:
% 20.41/20.62         ((v2_struct_0 @ sk_A)
% 20.41/20.62          | (v2_struct_0 @ sk_A)
% 20.41/20.62          | ~ (v2_pre_topc @ sk_A)
% 20.41/20.62          | ~ (v8_pre_topc @ sk_A)
% 20.41/20.62          | ~ (v1_compts_1 @ sk_A)
% 20.41/20.62          | ~ (l1_pre_topc @ sk_A)
% 20.41/20.62          | (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ X0 @ sk_A))
% 20.41/20.62          | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 20.41/20.62          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B @ sk_A))
% 20.41/20.62          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 20.41/20.62          | ~ (v7_waybel_0 @ X0)
% 20.41/20.62          | ~ (v4_orders_2 @ X0)
% 20.41/20.62          | (v2_struct_0 @ X0))),
% 20.41/20.62      inference('sup-', [status(thm)], ['327', '328'])).
% 20.41/20.62  thf('330', plain, ((v2_pre_topc @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('331', plain, ((v8_pre_topc @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('332', plain, ((v1_compts_1 @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('333', plain, ((l1_pre_topc @ sk_A)),
% 20.41/20.62      inference('sup-', [status(thm)], ['6', '7'])).
% 20.41/20.62  thf('334', plain,
% 20.41/20.62      (![X0 : $i]:
% 20.41/20.62         ((v2_struct_0 @ sk_A)
% 20.41/20.62          | (v2_struct_0 @ sk_A)
% 20.41/20.62          | (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ X0 @ sk_A))
% 20.41/20.62          | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 20.41/20.62          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B @ sk_A))
% 20.41/20.62          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 20.41/20.62          | ~ (v7_waybel_0 @ X0)
% 20.41/20.62          | ~ (v4_orders_2 @ X0)
% 20.41/20.62          | (v2_struct_0 @ X0))),
% 20.41/20.62      inference('demod', [status(thm)], ['329', '330', '331', '332', '333'])).
% 20.41/20.62  thf('335', plain,
% 20.41/20.62      (![X0 : $i]:
% 20.41/20.62         ((v2_struct_0 @ X0)
% 20.41/20.62          | ~ (v4_orders_2 @ X0)
% 20.41/20.62          | ~ (v7_waybel_0 @ X0)
% 20.41/20.62          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 20.41/20.62          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B @ sk_A))
% 20.41/20.62          | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 20.41/20.62          | (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ X0 @ sk_A))
% 20.41/20.62          | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('simplify', [status(thm)], ['334'])).
% 20.41/20.62  thf('336', plain,
% 20.41/20.62      (((v2_struct_0 @ sk_A)
% 20.41/20.62        | (v2_struct_0 @ sk_A)
% 20.41/20.62        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_C_1 @ sk_B @ sk_A))
% 20.41/20.62        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 20.41/20.62        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 20.41/20.62        | ~ (v7_waybel_0 @ sk_B)
% 20.41/20.62        | ~ (v4_orders_2 @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_B))),
% 20.41/20.62      inference('sup-', [status(thm)], ['326', '335'])).
% 20.41/20.62  thf('337', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('338', plain, ((v7_waybel_0 @ sk_B)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('339', plain, ((v4_orders_2 @ sk_B)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('340', plain,
% 20.41/20.62      (((v2_struct_0 @ sk_A)
% 20.41/20.62        | (v2_struct_0 @ sk_A)
% 20.41/20.62        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_C_1 @ sk_B @ sk_A))
% 20.41/20.62        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 20.41/20.62        | (v2_struct_0 @ sk_B))),
% 20.41/20.62      inference('demod', [status(thm)], ['336', '337', '338', '339'])).
% 20.41/20.62  thf('341', plain,
% 20.41/20.62      (((v2_struct_0 @ sk_B)
% 20.41/20.62        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 20.41/20.62        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_C_1 @ sk_B @ sk_A))
% 20.41/20.62        | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('simplify', [status(thm)], ['340'])).
% 20.41/20.62  thf('342', plain,
% 20.41/20.62      (((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ (k10_yellow_6 @ sk_A @ sk_B))
% 20.41/20.62        | (v2_struct_0 @ sk_A)
% 20.41/20.62        | (v2_struct_0 @ sk_A)
% 20.41/20.62        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_C_1 @ sk_B @ sk_A))
% 20.41/20.62        | (v2_struct_0 @ sk_B))),
% 20.41/20.62      inference('sup+', [status(thm)], ['325', '341'])).
% 20.41/20.62  thf('343', plain,
% 20.41/20.62      (((v2_struct_0 @ sk_B)
% 20.41/20.62        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_C_1 @ sk_B @ sk_A))
% 20.41/20.62        | (v2_struct_0 @ sk_A)
% 20.41/20.62        | (r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.41/20.62           (k10_yellow_6 @ sk_A @ sk_B)))),
% 20.41/20.62      inference('simplify', [status(thm)], ['342'])).
% 20.41/20.62  thf('344', plain,
% 20.41/20.62      ((~ (r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.41/20.62           (k10_yellow_6 @ sk_A @ sk_B)))
% 20.41/20.62         <= (~
% 20.41/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.41/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.41/20.62      inference('split', [status(esa)], ['323'])).
% 20.41/20.62  thf('345', plain,
% 20.41/20.62      ((((v2_struct_0 @ sk_A)
% 20.41/20.62         | (r3_waybel_9 @ sk_A @ sk_B @ (sk_C_1 @ sk_B @ sk_A))
% 20.41/20.62         | (v2_struct_0 @ sk_B)))
% 20.41/20.62         <= (~
% 20.41/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.41/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.41/20.62      inference('sup-', [status(thm)], ['343', '344'])).
% 20.41/20.62  thf('346', plain, (~ (v2_struct_0 @ sk_B)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('347', plain,
% 20.41/20.62      ((((r3_waybel_9 @ sk_A @ sk_B @ (sk_C_1 @ sk_B @ sk_A))
% 20.41/20.62         | (v2_struct_0 @ sk_A)))
% 20.41/20.62         <= (~
% 20.41/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.41/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.41/20.62      inference('clc', [status(thm)], ['345', '346'])).
% 20.41/20.62  thf('348', plain,
% 20.41/20.62      (((v2_struct_0 @ sk_A)
% 20.41/20.62        | ((sk_C @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B)))),
% 20.41/20.62      inference('clc', [status(thm)], ['69', '70'])).
% 20.41/20.62  thf('349', plain,
% 20.41/20.62      (((r3_waybel_9 @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 20.41/20.62        | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('clc', [status(thm)], ['11', '12'])).
% 20.41/20.62  thf('350', plain,
% 20.41/20.62      (((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62        | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('clc', [status(thm)], ['23', '24'])).
% 20.41/20.62  thf('351', plain,
% 20.41/20.62      (![X31 : $i, X32 : $i, X33 : $i]:
% 20.41/20.62         ((v2_struct_0 @ X31)
% 20.41/20.62          | ~ (v4_orders_2 @ X31)
% 20.41/20.62          | ~ (v7_waybel_0 @ X31)
% 20.41/20.62          | ~ (l1_waybel_0 @ X31 @ X32)
% 20.41/20.62          | ~ (r3_waybel_9 @ X32 @ X31 @ X33)
% 20.41/20.62          | (r2_hidden @ X33 @ (k10_yellow_6 @ X32 @ X31))
% 20.41/20.62          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 20.41/20.62          | (m1_subset_1 @ (sk_C_1 @ X31 @ X32) @ (u1_struct_0 @ X32))
% 20.41/20.62          | ~ (l1_pre_topc @ X32)
% 20.41/20.62          | ~ (v1_compts_1 @ X32)
% 20.41/20.62          | ~ (v8_pre_topc @ X32)
% 20.41/20.62          | ~ (v2_pre_topc @ X32)
% 20.41/20.62          | (v2_struct_0 @ X32))),
% 20.41/20.62      inference('cnf', [status(esa)], [t33_waybel_9])).
% 20.41/20.62  thf('352', plain,
% 20.41/20.62      (![X0 : $i]:
% 20.41/20.62         ((v2_struct_0 @ sk_A)
% 20.41/20.62          | (v2_struct_0 @ sk_A)
% 20.41/20.62          | ~ (v2_pre_topc @ sk_A)
% 20.41/20.62          | ~ (v8_pre_topc @ sk_A)
% 20.41/20.62          | ~ (v1_compts_1 @ sk_A)
% 20.41/20.62          | ~ (l1_pre_topc @ sk_A)
% 20.41/20.62          | (m1_subset_1 @ (sk_C_1 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62          | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 20.41/20.62          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B @ sk_A))
% 20.41/20.62          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 20.41/20.62          | ~ (v7_waybel_0 @ X0)
% 20.41/20.62          | ~ (v4_orders_2 @ X0)
% 20.41/20.62          | (v2_struct_0 @ X0))),
% 20.41/20.62      inference('sup-', [status(thm)], ['350', '351'])).
% 20.41/20.62  thf('353', plain, ((v2_pre_topc @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('354', plain, ((v8_pre_topc @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('355', plain, ((v1_compts_1 @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('356', plain, ((l1_pre_topc @ sk_A)),
% 20.41/20.62      inference('sup-', [status(thm)], ['6', '7'])).
% 20.41/20.62  thf('357', plain,
% 20.41/20.62      (![X0 : $i]:
% 20.41/20.62         ((v2_struct_0 @ sk_A)
% 20.41/20.62          | (v2_struct_0 @ sk_A)
% 20.41/20.62          | (m1_subset_1 @ (sk_C_1 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62          | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 20.41/20.62          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B @ sk_A))
% 20.41/20.62          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 20.41/20.62          | ~ (v7_waybel_0 @ X0)
% 20.41/20.62          | ~ (v4_orders_2 @ X0)
% 20.41/20.62          | (v2_struct_0 @ X0))),
% 20.41/20.62      inference('demod', [status(thm)], ['352', '353', '354', '355', '356'])).
% 20.41/20.62  thf('358', plain,
% 20.41/20.62      (![X0 : $i]:
% 20.41/20.62         ((v2_struct_0 @ X0)
% 20.41/20.62          | ~ (v4_orders_2 @ X0)
% 20.41/20.62          | ~ (v7_waybel_0 @ X0)
% 20.41/20.62          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 20.41/20.62          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B @ sk_A))
% 20.41/20.62          | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 20.41/20.62          | (m1_subset_1 @ (sk_C_1 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62          | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('simplify', [status(thm)], ['357'])).
% 20.41/20.62  thf('359', plain,
% 20.41/20.62      (((v2_struct_0 @ sk_A)
% 20.41/20.62        | (v2_struct_0 @ sk_A)
% 20.41/20.62        | (m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 20.41/20.62        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 20.41/20.62        | ~ (v7_waybel_0 @ sk_B)
% 20.41/20.62        | ~ (v4_orders_2 @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_B))),
% 20.41/20.62      inference('sup-', [status(thm)], ['349', '358'])).
% 20.41/20.62  thf('360', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('361', plain, ((v7_waybel_0 @ sk_B)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('362', plain, ((v4_orders_2 @ sk_B)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('363', plain,
% 20.41/20.62      (((v2_struct_0 @ sk_A)
% 20.41/20.62        | (v2_struct_0 @ sk_A)
% 20.41/20.62        | (m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 20.41/20.62        | (v2_struct_0 @ sk_B))),
% 20.41/20.62      inference('demod', [status(thm)], ['359', '360', '361', '362'])).
% 20.41/20.62  thf('364', plain,
% 20.41/20.62      (((v2_struct_0 @ sk_B)
% 20.41/20.62        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 20.41/20.62        | (m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62        | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('simplify', [status(thm)], ['363'])).
% 20.41/20.62  thf('365', plain,
% 20.41/20.62      (((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ (k10_yellow_6 @ sk_A @ sk_B))
% 20.41/20.62        | (v2_struct_0 @ sk_A)
% 20.41/20.62        | (v2_struct_0 @ sk_A)
% 20.41/20.62        | (m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62        | (v2_struct_0 @ sk_B))),
% 20.41/20.62      inference('sup+', [status(thm)], ['348', '364'])).
% 20.41/20.62  thf('366', plain,
% 20.41/20.62      (((v2_struct_0 @ sk_B)
% 20.41/20.62        | (m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62        | (v2_struct_0 @ sk_A)
% 20.41/20.62        | (r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.41/20.62           (k10_yellow_6 @ sk_A @ sk_B)))),
% 20.41/20.62      inference('simplify', [status(thm)], ['365'])).
% 20.41/20.62  thf('367', plain,
% 20.41/20.62      ((~ (r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.41/20.62           (k10_yellow_6 @ sk_A @ sk_B)))
% 20.41/20.62         <= (~
% 20.41/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.41/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.41/20.62      inference('split', [status(esa)], ['323'])).
% 20.41/20.62  thf('368', plain,
% 20.41/20.62      ((((v2_struct_0 @ sk_A)
% 20.41/20.62         | (m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62         | (v2_struct_0 @ sk_B)))
% 20.41/20.62         <= (~
% 20.41/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.41/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.41/20.62      inference('sup-', [status(thm)], ['366', '367'])).
% 20.41/20.62  thf('369', plain, (~ (v2_struct_0 @ sk_B)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('370', plain,
% 20.41/20.62      ((((m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62         | (v2_struct_0 @ sk_A)))
% 20.41/20.62         <= (~
% 20.41/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.41/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.41/20.62      inference('clc', [status(thm)], ['368', '369'])).
% 20.41/20.62  thf('371', plain,
% 20.41/20.62      ((((r3_waybel_9 @ sk_A @ sk_B @ (sk_C_1 @ sk_B @ sk_A))
% 20.41/20.62         | (v2_struct_0 @ sk_A)))
% 20.41/20.62         <= (~
% 20.41/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.41/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.41/20.62      inference('clc', [status(thm)], ['345', '346'])).
% 20.41/20.62  thf('372', plain,
% 20.41/20.62      ((((m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62         | (v2_struct_0 @ sk_A)))
% 20.41/20.62         <= (~
% 20.41/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.41/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.41/20.62      inference('clc', [status(thm)], ['368', '369'])).
% 20.41/20.62  thf('373', plain,
% 20.41/20.62      (![X34 : $i, X35 : $i, X36 : $i]:
% 20.41/20.62         (~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X35))
% 20.41/20.62          | (m1_subset_1 @ (sk_D_2 @ X35) @ (u1_struct_0 @ X35))
% 20.41/20.62          | ~ (v11_waybel_0 @ X36 @ X35)
% 20.41/20.62          | ~ (r3_waybel_9 @ X35 @ X36 @ X34)
% 20.41/20.62          | ((X34) = (k1_waybel_9 @ X35 @ X36))
% 20.41/20.62          | ~ (l1_waybel_0 @ X36 @ X35)
% 20.41/20.62          | ~ (v7_waybel_0 @ X36)
% 20.41/20.62          | ~ (v4_orders_2 @ X36)
% 20.41/20.62          | (v2_struct_0 @ X36)
% 20.41/20.62          | ~ (l1_waybel_9 @ X35)
% 20.41/20.62          | ~ (v1_compts_1 @ X35)
% 20.41/20.62          | ~ (v2_lattice3 @ X35)
% 20.41/20.62          | ~ (v1_lattice3 @ X35)
% 20.41/20.62          | ~ (v5_orders_2 @ X35)
% 20.41/20.62          | ~ (v4_orders_2 @ X35)
% 20.41/20.62          | ~ (v3_orders_2 @ X35)
% 20.41/20.62          | ~ (v8_pre_topc @ X35)
% 20.41/20.62          | ~ (v2_pre_topc @ X35))),
% 20.41/20.62      inference('cnf', [status(esa)], [t36_waybel_9])).
% 20.41/20.62  thf('374', plain,
% 20.41/20.62      ((![X0 : $i]:
% 20.41/20.62          ((v2_struct_0 @ sk_A)
% 20.41/20.62           | ~ (v2_pre_topc @ sk_A)
% 20.41/20.62           | ~ (v8_pre_topc @ sk_A)
% 20.41/20.62           | ~ (v3_orders_2 @ sk_A)
% 20.41/20.62           | ~ (v4_orders_2 @ sk_A)
% 20.41/20.62           | ~ (v5_orders_2 @ sk_A)
% 20.41/20.62           | ~ (v1_lattice3 @ sk_A)
% 20.41/20.62           | ~ (v2_lattice3 @ sk_A)
% 20.41/20.62           | ~ (v1_compts_1 @ sk_A)
% 20.41/20.62           | ~ (l1_waybel_9 @ sk_A)
% 20.41/20.62           | (v2_struct_0 @ X0)
% 20.41/20.62           | ~ (v4_orders_2 @ X0)
% 20.41/20.62           | ~ (v7_waybel_0 @ X0)
% 20.41/20.62           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 20.41/20.62           | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ X0))
% 20.41/20.62           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 20.41/20.62           | ~ (v11_waybel_0 @ X0 @ sk_A)
% 20.41/20.62           | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 20.41/20.62         <= (~
% 20.41/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.41/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.41/20.62      inference('sup-', [status(thm)], ['372', '373'])).
% 20.41/20.62  thf('375', plain, ((v2_pre_topc @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('376', plain, ((v8_pre_topc @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('377', plain, ((v3_orders_2 @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('378', plain, ((v4_orders_2 @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('379', plain, ((v5_orders_2 @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('380', plain, ((v1_lattice3 @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('381', plain, ((v2_lattice3 @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('382', plain, ((v1_compts_1 @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('383', plain, ((l1_waybel_9 @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('384', plain,
% 20.41/20.62      ((![X0 : $i]:
% 20.41/20.62          ((v2_struct_0 @ sk_A)
% 20.41/20.62           | (v2_struct_0 @ X0)
% 20.41/20.62           | ~ (v4_orders_2 @ X0)
% 20.41/20.62           | ~ (v7_waybel_0 @ X0)
% 20.41/20.62           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 20.41/20.62           | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ X0))
% 20.41/20.62           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 20.41/20.62           | ~ (v11_waybel_0 @ X0 @ sk_A)
% 20.41/20.62           | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 20.41/20.62         <= (~
% 20.41/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.41/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.41/20.62      inference('demod', [status(thm)],
% 20.41/20.62                ['374', '375', '376', '377', '378', '379', '380', '381', 
% 20.41/20.62                 '382', '383'])).
% 20.41/20.62  thf('385', plain,
% 20.41/20.62      ((((v2_struct_0 @ sk_A)
% 20.41/20.62         | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62         | ~ (v11_waybel_0 @ sk_B @ sk_A)
% 20.41/20.62         | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.62         | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 20.41/20.62         | ~ (v7_waybel_0 @ sk_B)
% 20.41/20.62         | ~ (v4_orders_2 @ sk_B)
% 20.41/20.62         | (v2_struct_0 @ sk_B)
% 20.41/20.62         | (v2_struct_0 @ sk_A)))
% 20.41/20.62         <= (~
% 20.41/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.41/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.41/20.62      inference('sup-', [status(thm)], ['371', '384'])).
% 20.41/20.62  thf('386', plain, ((v11_waybel_0 @ sk_B @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('387', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('388', plain, ((v7_waybel_0 @ sk_B)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('389', plain, ((v4_orders_2 @ sk_B)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('390', plain,
% 20.41/20.62      ((((v2_struct_0 @ sk_A)
% 20.41/20.62         | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62         | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.62         | (v2_struct_0 @ sk_B)
% 20.41/20.62         | (v2_struct_0 @ sk_A)))
% 20.41/20.62         <= (~
% 20.41/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.41/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.41/20.62      inference('demod', [status(thm)], ['385', '386', '387', '388', '389'])).
% 20.41/20.62  thf('391', plain,
% 20.41/20.62      ((((v2_struct_0 @ sk_B)
% 20.41/20.62         | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.62         | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62         | (v2_struct_0 @ sk_A)))
% 20.41/20.62         <= (~
% 20.41/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.41/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.41/20.62      inference('simplify', [status(thm)], ['390'])).
% 20.41/20.62  thf('392', plain,
% 20.41/20.62      (![X37 : $i]:
% 20.41/20.62         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X37) @ sk_A @ sk_A)
% 20.41/20.62          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A)))),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('393', plain,
% 20.41/20.62      ((((v2_struct_0 @ sk_A)
% 20.41/20.62         | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.62         | (v2_struct_0 @ sk_B)
% 20.41/20.62         | (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_D_2 @ sk_A)) @ sk_A @ sk_A)))
% 20.41/20.62         <= (~
% 20.41/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.41/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.41/20.62      inference('sup-', [status(thm)], ['391', '392'])).
% 20.41/20.62  thf('394', plain,
% 20.41/20.62      (![X34 : $i, X35 : $i, X36 : $i]:
% 20.41/20.62         (~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X35))
% 20.41/20.62          | ~ (v5_pre_topc @ (k4_waybel_1 @ X35 @ (sk_D_2 @ X35)) @ X35 @ X35)
% 20.41/20.62          | ~ (v11_waybel_0 @ X36 @ X35)
% 20.41/20.62          | ~ (r3_waybel_9 @ X35 @ X36 @ X34)
% 20.41/20.62          | ((X34) = (k1_waybel_9 @ X35 @ X36))
% 20.41/20.62          | ~ (l1_waybel_0 @ X36 @ X35)
% 20.41/20.62          | ~ (v7_waybel_0 @ X36)
% 20.41/20.62          | ~ (v4_orders_2 @ X36)
% 20.41/20.62          | (v2_struct_0 @ X36)
% 20.41/20.62          | ~ (l1_waybel_9 @ X35)
% 20.41/20.62          | ~ (v1_compts_1 @ X35)
% 20.41/20.62          | ~ (v2_lattice3 @ X35)
% 20.41/20.62          | ~ (v1_lattice3 @ X35)
% 20.41/20.62          | ~ (v5_orders_2 @ X35)
% 20.41/20.62          | ~ (v4_orders_2 @ X35)
% 20.41/20.62          | ~ (v3_orders_2 @ X35)
% 20.41/20.62          | ~ (v8_pre_topc @ X35)
% 20.41/20.62          | ~ (v2_pre_topc @ X35))),
% 20.41/20.62      inference('cnf', [status(esa)], [t36_waybel_9])).
% 20.41/20.62  thf('395', plain,
% 20.41/20.62      ((![X0 : $i, X1 : $i]:
% 20.41/20.62          ((v2_struct_0 @ sk_B)
% 20.41/20.62           | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.62           | (v2_struct_0 @ sk_A)
% 20.41/20.62           | ~ (v2_pre_topc @ sk_A)
% 20.41/20.62           | ~ (v8_pre_topc @ sk_A)
% 20.41/20.62           | ~ (v3_orders_2 @ sk_A)
% 20.41/20.62           | ~ (v4_orders_2 @ sk_A)
% 20.41/20.62           | ~ (v5_orders_2 @ sk_A)
% 20.41/20.62           | ~ (v1_lattice3 @ sk_A)
% 20.41/20.62           | ~ (v2_lattice3 @ sk_A)
% 20.41/20.62           | ~ (v1_compts_1 @ sk_A)
% 20.41/20.62           | ~ (l1_waybel_9 @ sk_A)
% 20.41/20.62           | (v2_struct_0 @ X0)
% 20.41/20.62           | ~ (v4_orders_2 @ X0)
% 20.41/20.62           | ~ (v7_waybel_0 @ X0)
% 20.41/20.62           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 20.41/20.62           | ((X1) = (k1_waybel_9 @ sk_A @ X0))
% 20.41/20.62           | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 20.41/20.62           | ~ (v11_waybel_0 @ X0 @ sk_A)
% 20.41/20.62           | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))))
% 20.41/20.62         <= (~
% 20.41/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.41/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.41/20.62      inference('sup-', [status(thm)], ['393', '394'])).
% 20.41/20.62  thf('396', plain, ((v2_pre_topc @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('397', plain, ((v8_pre_topc @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('398', plain, ((v3_orders_2 @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('399', plain, ((v4_orders_2 @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('400', plain, ((v5_orders_2 @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('401', plain, ((v1_lattice3 @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('402', plain, ((v2_lattice3 @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('403', plain, ((v1_compts_1 @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('404', plain, ((l1_waybel_9 @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('405', plain,
% 20.41/20.62      ((![X0 : $i, X1 : $i]:
% 20.41/20.62          ((v2_struct_0 @ sk_B)
% 20.41/20.62           | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.62           | (v2_struct_0 @ sk_A)
% 20.41/20.62           | (v2_struct_0 @ X0)
% 20.41/20.62           | ~ (v4_orders_2 @ X0)
% 20.41/20.62           | ~ (v7_waybel_0 @ X0)
% 20.41/20.62           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 20.41/20.62           | ((X1) = (k1_waybel_9 @ sk_A @ X0))
% 20.41/20.62           | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 20.41/20.62           | ~ (v11_waybel_0 @ X0 @ sk_A)
% 20.41/20.62           | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))))
% 20.41/20.62         <= (~
% 20.41/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.41/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.41/20.62      inference('demod', [status(thm)],
% 20.41/20.62                ['395', '396', '397', '398', '399', '400', '401', '402', 
% 20.41/20.62                 '403', '404'])).
% 20.41/20.62  thf('406', plain,
% 20.41/20.62      ((![X0 : $i]:
% 20.41/20.62          ((v2_struct_0 @ sk_A)
% 20.41/20.62           | ~ (v11_waybel_0 @ X0 @ sk_A)
% 20.41/20.62           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 20.41/20.62           | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ X0))
% 20.41/20.62           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 20.41/20.62           | ~ (v7_waybel_0 @ X0)
% 20.41/20.62           | ~ (v4_orders_2 @ X0)
% 20.41/20.62           | (v2_struct_0 @ X0)
% 20.41/20.62           | (v2_struct_0 @ sk_A)
% 20.41/20.62           | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.62           | (v2_struct_0 @ sk_B)))
% 20.41/20.62         <= (~
% 20.41/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.41/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.41/20.62      inference('sup-', [status(thm)], ['370', '405'])).
% 20.41/20.62  thf('407', plain,
% 20.41/20.62      ((![X0 : $i]:
% 20.41/20.62          ((v2_struct_0 @ sk_B)
% 20.41/20.62           | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.62           | (v2_struct_0 @ X0)
% 20.41/20.62           | ~ (v4_orders_2 @ X0)
% 20.41/20.62           | ~ (v7_waybel_0 @ X0)
% 20.41/20.62           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 20.41/20.62           | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ X0))
% 20.41/20.62           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 20.41/20.62           | ~ (v11_waybel_0 @ X0 @ sk_A)
% 20.41/20.62           | (v2_struct_0 @ sk_A)))
% 20.41/20.62         <= (~
% 20.41/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.41/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.41/20.62      inference('simplify', [status(thm)], ['406'])).
% 20.41/20.62  thf('408', plain,
% 20.41/20.62      ((((v2_struct_0 @ sk_A)
% 20.41/20.62         | (v2_struct_0 @ sk_A)
% 20.41/20.62         | ~ (v11_waybel_0 @ sk_B @ sk_A)
% 20.41/20.62         | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.62         | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 20.41/20.62         | ~ (v7_waybel_0 @ sk_B)
% 20.41/20.62         | ~ (v4_orders_2 @ sk_B)
% 20.41/20.62         | (v2_struct_0 @ sk_B)
% 20.41/20.62         | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.62         | (v2_struct_0 @ sk_B)))
% 20.41/20.62         <= (~
% 20.41/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.41/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.41/20.62      inference('sup-', [status(thm)], ['347', '407'])).
% 20.41/20.62  thf('409', plain, ((v11_waybel_0 @ sk_B @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('410', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('411', plain, ((v7_waybel_0 @ sk_B)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('412', plain, ((v4_orders_2 @ sk_B)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('413', plain,
% 20.41/20.62      ((((v2_struct_0 @ sk_A)
% 20.41/20.62         | (v2_struct_0 @ sk_A)
% 20.41/20.62         | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.62         | (v2_struct_0 @ sk_B)
% 20.41/20.62         | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.62         | (v2_struct_0 @ sk_B)))
% 20.41/20.62         <= (~
% 20.41/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.41/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.41/20.62      inference('demod', [status(thm)], ['408', '409', '410', '411', '412'])).
% 20.41/20.62  thf('414', plain,
% 20.41/20.62      ((((v2_struct_0 @ sk_B)
% 20.41/20.62         | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 20.41/20.62         | (v2_struct_0 @ sk_A)))
% 20.41/20.62         <= (~
% 20.41/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.41/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.41/20.62      inference('simplify', [status(thm)], ['413'])).
% 20.41/20.62  thf('415', plain, (~ (v2_struct_0 @ sk_B)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('416', plain,
% 20.41/20.62      ((((v2_struct_0 @ sk_A)
% 20.41/20.62         | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))))
% 20.41/20.62         <= (~
% 20.41/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.41/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.41/20.62      inference('clc', [status(thm)], ['414', '415'])).
% 20.41/20.62  thf('417', plain,
% 20.41/20.62      (((v2_struct_0 @ sk_A)
% 20.41/20.62        | ((sk_C @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B)))),
% 20.41/20.62      inference('clc', [status(thm)], ['69', '70'])).
% 20.41/20.62  thf('418', plain,
% 20.41/20.62      (((r3_waybel_9 @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 20.41/20.62        | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('clc', [status(thm)], ['11', '12'])).
% 20.41/20.62  thf('419', plain,
% 20.41/20.62      (((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.41/20.62        | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('clc', [status(thm)], ['23', '24'])).
% 20.41/20.62  thf('420', plain,
% 20.41/20.62      (![X31 : $i, X32 : $i, X33 : $i]:
% 20.41/20.62         ((v2_struct_0 @ X31)
% 20.41/20.62          | ~ (v4_orders_2 @ X31)
% 20.41/20.62          | ~ (v7_waybel_0 @ X31)
% 20.41/20.62          | ~ (l1_waybel_0 @ X31 @ X32)
% 20.41/20.62          | ~ (r3_waybel_9 @ X32 @ X31 @ X33)
% 20.41/20.62          | (r2_hidden @ X33 @ (k10_yellow_6 @ X32 @ X31))
% 20.41/20.62          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 20.41/20.62          | (r3_waybel_9 @ X32 @ X31 @ (sk_D_1 @ X31 @ X32))
% 20.41/20.62          | ~ (l1_pre_topc @ X32)
% 20.41/20.62          | ~ (v1_compts_1 @ X32)
% 20.41/20.62          | ~ (v8_pre_topc @ X32)
% 20.41/20.62          | ~ (v2_pre_topc @ X32)
% 20.41/20.62          | (v2_struct_0 @ X32))),
% 20.41/20.62      inference('cnf', [status(esa)], [t33_waybel_9])).
% 20.41/20.62  thf('421', plain,
% 20.41/20.62      (![X0 : $i]:
% 20.41/20.62         ((v2_struct_0 @ sk_A)
% 20.41/20.62          | (v2_struct_0 @ sk_A)
% 20.41/20.62          | ~ (v2_pre_topc @ sk_A)
% 20.41/20.62          | ~ (v8_pre_topc @ sk_A)
% 20.41/20.62          | ~ (v1_compts_1 @ sk_A)
% 20.41/20.62          | ~ (l1_pre_topc @ sk_A)
% 20.41/20.62          | (r3_waybel_9 @ sk_A @ X0 @ (sk_D_1 @ X0 @ sk_A))
% 20.41/20.62          | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 20.41/20.62          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B @ sk_A))
% 20.41/20.62          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 20.41/20.62          | ~ (v7_waybel_0 @ X0)
% 20.41/20.62          | ~ (v4_orders_2 @ X0)
% 20.41/20.62          | (v2_struct_0 @ X0))),
% 20.41/20.62      inference('sup-', [status(thm)], ['419', '420'])).
% 20.41/20.62  thf('422', plain, ((v2_pre_topc @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('423', plain, ((v8_pre_topc @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('424', plain, ((v1_compts_1 @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('425', plain, ((l1_pre_topc @ sk_A)),
% 20.41/20.62      inference('sup-', [status(thm)], ['6', '7'])).
% 20.41/20.62  thf('426', plain,
% 20.41/20.62      (![X0 : $i]:
% 20.41/20.62         ((v2_struct_0 @ sk_A)
% 20.41/20.62          | (v2_struct_0 @ sk_A)
% 20.41/20.62          | (r3_waybel_9 @ sk_A @ X0 @ (sk_D_1 @ X0 @ sk_A))
% 20.41/20.62          | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 20.41/20.62          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B @ sk_A))
% 20.41/20.62          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 20.41/20.62          | ~ (v7_waybel_0 @ X0)
% 20.41/20.62          | ~ (v4_orders_2 @ X0)
% 20.41/20.62          | (v2_struct_0 @ X0))),
% 20.41/20.62      inference('demod', [status(thm)], ['421', '422', '423', '424', '425'])).
% 20.41/20.62  thf('427', plain,
% 20.41/20.62      (![X0 : $i]:
% 20.41/20.62         ((v2_struct_0 @ X0)
% 20.41/20.62          | ~ (v4_orders_2 @ X0)
% 20.41/20.62          | ~ (v7_waybel_0 @ X0)
% 20.41/20.62          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 20.41/20.62          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B @ sk_A))
% 20.41/20.62          | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 20.41/20.62          | (r3_waybel_9 @ sk_A @ X0 @ (sk_D_1 @ X0 @ sk_A))
% 20.41/20.62          | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('simplify', [status(thm)], ['426'])).
% 20.41/20.62  thf('428', plain,
% 20.41/20.62      (((v2_struct_0 @ sk_A)
% 20.41/20.62        | (v2_struct_0 @ sk_A)
% 20.41/20.62        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_D_1 @ sk_B @ sk_A))
% 20.41/20.62        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 20.41/20.62        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 20.41/20.62        | ~ (v7_waybel_0 @ sk_B)
% 20.41/20.62        | ~ (v4_orders_2 @ sk_B)
% 20.41/20.62        | (v2_struct_0 @ sk_B))),
% 20.41/20.62      inference('sup-', [status(thm)], ['418', '427'])).
% 20.41/20.62  thf('429', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('430', plain, ((v7_waybel_0 @ sk_B)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('431', plain, ((v4_orders_2 @ sk_B)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('432', plain,
% 20.41/20.62      (((v2_struct_0 @ sk_A)
% 20.41/20.62        | (v2_struct_0 @ sk_A)
% 20.41/20.62        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_D_1 @ sk_B @ sk_A))
% 20.41/20.62        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 20.41/20.62        | (v2_struct_0 @ sk_B))),
% 20.41/20.62      inference('demod', [status(thm)], ['428', '429', '430', '431'])).
% 20.41/20.62  thf('433', plain,
% 20.41/20.62      (((v2_struct_0 @ sk_B)
% 20.41/20.62        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 20.41/20.62        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_D_1 @ sk_B @ sk_A))
% 20.41/20.62        | (v2_struct_0 @ sk_A))),
% 20.41/20.62      inference('simplify', [status(thm)], ['432'])).
% 20.41/20.62  thf('434', plain,
% 20.41/20.62      (((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ (k10_yellow_6 @ sk_A @ sk_B))
% 20.41/20.62        | (v2_struct_0 @ sk_A)
% 20.41/20.62        | (v2_struct_0 @ sk_A)
% 20.41/20.62        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_D_1 @ sk_B @ sk_A))
% 20.41/20.62        | (v2_struct_0 @ sk_B))),
% 20.41/20.62      inference('sup+', [status(thm)], ['417', '433'])).
% 20.41/20.62  thf('435', plain,
% 20.41/20.62      (((v2_struct_0 @ sk_B)
% 20.41/20.62        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_D_1 @ sk_B @ sk_A))
% 20.41/20.62        | (v2_struct_0 @ sk_A)
% 20.41/20.62        | (r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.41/20.62           (k10_yellow_6 @ sk_A @ sk_B)))),
% 20.41/20.62      inference('simplify', [status(thm)], ['434'])).
% 20.41/20.62  thf('436', plain,
% 20.41/20.62      ((~ (r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.41/20.62           (k10_yellow_6 @ sk_A @ sk_B)))
% 20.41/20.62         <= (~
% 20.41/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.41/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.41/20.62      inference('split', [status(esa)], ['323'])).
% 20.41/20.62  thf('437', plain,
% 20.41/20.62      ((((v2_struct_0 @ sk_A)
% 20.41/20.62         | (r3_waybel_9 @ sk_A @ sk_B @ (sk_D_1 @ sk_B @ sk_A))
% 20.41/20.62         | (v2_struct_0 @ sk_B)))
% 20.41/20.62         <= (~
% 20.41/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.41/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.41/20.62      inference('sup-', [status(thm)], ['435', '436'])).
% 20.41/20.62  thf('438', plain, (~ (v2_struct_0 @ sk_B)),
% 20.41/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.62  thf('439', plain,
% 20.41/20.62      ((((r3_waybel_9 @ sk_A @ sk_B @ (sk_D_1 @ sk_B @ sk_A))
% 20.41/20.62         | (v2_struct_0 @ sk_A)))
% 20.41/20.62         <= (~
% 20.41/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.41/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.41/20.62      inference('clc', [status(thm)], ['437', '438'])).
% 20.41/20.62  thf('440', plain,
% 20.41/20.62      (((v2_struct_0 @ sk_A)
% 20.41/20.62        | ((sk_C @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B)))),
% 20.45/20.62      inference('clc', [status(thm)], ['69', '70'])).
% 20.45/20.62  thf('441', plain,
% 20.45/20.62      (((r3_waybel_9 @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 20.45/20.62        | (v2_struct_0 @ sk_A))),
% 20.45/20.62      inference('clc', [status(thm)], ['11', '12'])).
% 20.45/20.62  thf('442', plain,
% 20.45/20.62      (((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.45/20.62        | (v2_struct_0 @ sk_A))),
% 20.45/20.62      inference('clc', [status(thm)], ['23', '24'])).
% 20.45/20.62  thf('443', plain,
% 20.45/20.62      (![X31 : $i, X32 : $i, X33 : $i]:
% 20.45/20.62         ((v2_struct_0 @ X31)
% 20.45/20.62          | ~ (v4_orders_2 @ X31)
% 20.45/20.62          | ~ (v7_waybel_0 @ X31)
% 20.45/20.62          | ~ (l1_waybel_0 @ X31 @ X32)
% 20.45/20.62          | ~ (r3_waybel_9 @ X32 @ X31 @ X33)
% 20.45/20.62          | (r2_hidden @ X33 @ (k10_yellow_6 @ X32 @ X31))
% 20.45/20.62          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 20.45/20.62          | (m1_subset_1 @ (sk_D_1 @ X31 @ X32) @ (u1_struct_0 @ X32))
% 20.45/20.62          | ~ (l1_pre_topc @ X32)
% 20.45/20.62          | ~ (v1_compts_1 @ X32)
% 20.45/20.62          | ~ (v8_pre_topc @ X32)
% 20.45/20.62          | ~ (v2_pre_topc @ X32)
% 20.45/20.62          | (v2_struct_0 @ X32))),
% 20.45/20.62      inference('cnf', [status(esa)], [t33_waybel_9])).
% 20.45/20.62  thf('444', plain,
% 20.45/20.62      (![X0 : $i]:
% 20.45/20.62         ((v2_struct_0 @ sk_A)
% 20.45/20.62          | (v2_struct_0 @ sk_A)
% 20.45/20.62          | ~ (v2_pre_topc @ sk_A)
% 20.45/20.62          | ~ (v8_pre_topc @ sk_A)
% 20.45/20.62          | ~ (v1_compts_1 @ sk_A)
% 20.45/20.62          | ~ (l1_pre_topc @ sk_A)
% 20.45/20.62          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.45/20.62          | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 20.45/20.62          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B @ sk_A))
% 20.45/20.62          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 20.45/20.62          | ~ (v7_waybel_0 @ X0)
% 20.45/20.62          | ~ (v4_orders_2 @ X0)
% 20.45/20.62          | (v2_struct_0 @ X0))),
% 20.45/20.62      inference('sup-', [status(thm)], ['442', '443'])).
% 20.45/20.62  thf('445', plain, ((v2_pre_topc @ sk_A)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('446', plain, ((v8_pre_topc @ sk_A)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('447', plain, ((v1_compts_1 @ sk_A)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('448', plain, ((l1_pre_topc @ sk_A)),
% 20.45/20.62      inference('sup-', [status(thm)], ['6', '7'])).
% 20.45/20.62  thf('449', plain,
% 20.45/20.62      (![X0 : $i]:
% 20.45/20.62         ((v2_struct_0 @ sk_A)
% 20.45/20.62          | (v2_struct_0 @ sk_A)
% 20.45/20.62          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.45/20.62          | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 20.45/20.62          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B @ sk_A))
% 20.45/20.62          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 20.45/20.62          | ~ (v7_waybel_0 @ X0)
% 20.45/20.62          | ~ (v4_orders_2 @ X0)
% 20.45/20.62          | (v2_struct_0 @ X0))),
% 20.45/20.62      inference('demod', [status(thm)], ['444', '445', '446', '447', '448'])).
% 20.45/20.62  thf('450', plain,
% 20.45/20.62      (![X0 : $i]:
% 20.45/20.62         ((v2_struct_0 @ X0)
% 20.45/20.62          | ~ (v4_orders_2 @ X0)
% 20.45/20.62          | ~ (v7_waybel_0 @ X0)
% 20.45/20.62          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 20.45/20.62          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B @ sk_A))
% 20.45/20.62          | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 20.45/20.62          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.45/20.62          | (v2_struct_0 @ sk_A))),
% 20.45/20.62      inference('simplify', [status(thm)], ['449'])).
% 20.45/20.62  thf('451', plain,
% 20.45/20.62      (((v2_struct_0 @ sk_A)
% 20.45/20.62        | (v2_struct_0 @ sk_A)
% 20.45/20.62        | (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.45/20.62        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 20.45/20.62        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 20.45/20.62        | ~ (v7_waybel_0 @ sk_B)
% 20.45/20.62        | ~ (v4_orders_2 @ sk_B)
% 20.45/20.62        | (v2_struct_0 @ sk_B))),
% 20.45/20.62      inference('sup-', [status(thm)], ['441', '450'])).
% 20.45/20.62  thf('452', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('453', plain, ((v7_waybel_0 @ sk_B)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('454', plain, ((v4_orders_2 @ sk_B)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('455', plain,
% 20.45/20.62      (((v2_struct_0 @ sk_A)
% 20.45/20.62        | (v2_struct_0 @ sk_A)
% 20.45/20.62        | (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.45/20.62        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 20.45/20.62        | (v2_struct_0 @ sk_B))),
% 20.45/20.62      inference('demod', [status(thm)], ['451', '452', '453', '454'])).
% 20.45/20.62  thf('456', plain,
% 20.45/20.62      (((v2_struct_0 @ sk_B)
% 20.45/20.62        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 20.45/20.62        | (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.45/20.62        | (v2_struct_0 @ sk_A))),
% 20.45/20.62      inference('simplify', [status(thm)], ['455'])).
% 20.45/20.62  thf('457', plain,
% 20.45/20.62      (((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ (k10_yellow_6 @ sk_A @ sk_B))
% 20.45/20.62        | (v2_struct_0 @ sk_A)
% 20.45/20.62        | (v2_struct_0 @ sk_A)
% 20.45/20.62        | (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.45/20.62        | (v2_struct_0 @ sk_B))),
% 20.45/20.62      inference('sup+', [status(thm)], ['440', '456'])).
% 20.45/20.62  thf('458', plain,
% 20.45/20.62      (((v2_struct_0 @ sk_B)
% 20.45/20.62        | (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.45/20.62        | (v2_struct_0 @ sk_A)
% 20.45/20.62        | (r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.45/20.62           (k10_yellow_6 @ sk_A @ sk_B)))),
% 20.45/20.62      inference('simplify', [status(thm)], ['457'])).
% 20.45/20.62  thf('459', plain,
% 20.45/20.62      ((~ (r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.45/20.62           (k10_yellow_6 @ sk_A @ sk_B)))
% 20.45/20.62         <= (~
% 20.45/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.45/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.45/20.62      inference('split', [status(esa)], ['323'])).
% 20.45/20.62  thf('460', plain,
% 20.45/20.62      ((((v2_struct_0 @ sk_A)
% 20.45/20.62         | (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.45/20.62         | (v2_struct_0 @ sk_B)))
% 20.45/20.62         <= (~
% 20.45/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.45/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.45/20.62      inference('sup-', [status(thm)], ['458', '459'])).
% 20.45/20.62  thf('461', plain, (~ (v2_struct_0 @ sk_B)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('462', plain,
% 20.45/20.62      ((((m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.45/20.62         | (v2_struct_0 @ sk_A)))
% 20.45/20.62         <= (~
% 20.45/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.45/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.45/20.62      inference('clc', [status(thm)], ['460', '461'])).
% 20.45/20.62  thf('463', plain,
% 20.45/20.62      ((((r3_waybel_9 @ sk_A @ sk_B @ (sk_D_1 @ sk_B @ sk_A))
% 20.45/20.62         | (v2_struct_0 @ sk_A)))
% 20.45/20.62         <= (~
% 20.45/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.45/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.45/20.62      inference('clc', [status(thm)], ['437', '438'])).
% 20.45/20.62  thf('464', plain,
% 20.45/20.62      ((((m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.45/20.62         | (v2_struct_0 @ sk_A)))
% 20.45/20.62         <= (~
% 20.45/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.45/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.45/20.62      inference('clc', [status(thm)], ['460', '461'])).
% 20.45/20.62  thf('465', plain,
% 20.45/20.62      (![X34 : $i, X35 : $i, X36 : $i]:
% 20.45/20.62         (~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X35))
% 20.45/20.62          | (m1_subset_1 @ (sk_D_2 @ X35) @ (u1_struct_0 @ X35))
% 20.45/20.62          | ~ (v11_waybel_0 @ X36 @ X35)
% 20.45/20.62          | ~ (r3_waybel_9 @ X35 @ X36 @ X34)
% 20.45/20.62          | ((X34) = (k1_waybel_9 @ X35 @ X36))
% 20.45/20.62          | ~ (l1_waybel_0 @ X36 @ X35)
% 20.45/20.62          | ~ (v7_waybel_0 @ X36)
% 20.45/20.62          | ~ (v4_orders_2 @ X36)
% 20.45/20.62          | (v2_struct_0 @ X36)
% 20.45/20.62          | ~ (l1_waybel_9 @ X35)
% 20.45/20.62          | ~ (v1_compts_1 @ X35)
% 20.45/20.62          | ~ (v2_lattice3 @ X35)
% 20.45/20.62          | ~ (v1_lattice3 @ X35)
% 20.45/20.62          | ~ (v5_orders_2 @ X35)
% 20.45/20.62          | ~ (v4_orders_2 @ X35)
% 20.45/20.62          | ~ (v3_orders_2 @ X35)
% 20.45/20.62          | ~ (v8_pre_topc @ X35)
% 20.45/20.62          | ~ (v2_pre_topc @ X35))),
% 20.45/20.62      inference('cnf', [status(esa)], [t36_waybel_9])).
% 20.45/20.62  thf('466', plain,
% 20.45/20.62      ((![X0 : $i]:
% 20.45/20.62          ((v2_struct_0 @ sk_A)
% 20.45/20.62           | ~ (v2_pre_topc @ sk_A)
% 20.45/20.62           | ~ (v8_pre_topc @ sk_A)
% 20.45/20.62           | ~ (v3_orders_2 @ sk_A)
% 20.45/20.62           | ~ (v4_orders_2 @ sk_A)
% 20.45/20.62           | ~ (v5_orders_2 @ sk_A)
% 20.45/20.62           | ~ (v1_lattice3 @ sk_A)
% 20.45/20.62           | ~ (v2_lattice3 @ sk_A)
% 20.45/20.62           | ~ (v1_compts_1 @ sk_A)
% 20.45/20.62           | ~ (l1_waybel_9 @ sk_A)
% 20.45/20.62           | (v2_struct_0 @ X0)
% 20.45/20.62           | ~ (v4_orders_2 @ X0)
% 20.45/20.62           | ~ (v7_waybel_0 @ X0)
% 20.45/20.62           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 20.45/20.62           | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ X0))
% 20.45/20.62           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_D_1 @ sk_B @ sk_A))
% 20.45/20.62           | ~ (v11_waybel_0 @ X0 @ sk_A)
% 20.45/20.62           | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 20.45/20.62         <= (~
% 20.45/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.45/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.45/20.62      inference('sup-', [status(thm)], ['464', '465'])).
% 20.45/20.62  thf('467', plain, ((v2_pre_topc @ sk_A)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('468', plain, ((v8_pre_topc @ sk_A)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('469', plain, ((v3_orders_2 @ sk_A)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('470', plain, ((v4_orders_2 @ sk_A)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('471', plain, ((v5_orders_2 @ sk_A)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('472', plain, ((v1_lattice3 @ sk_A)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('473', plain, ((v2_lattice3 @ sk_A)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('474', plain, ((v1_compts_1 @ sk_A)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('475', plain, ((l1_waybel_9 @ sk_A)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('476', plain,
% 20.45/20.62      ((![X0 : $i]:
% 20.45/20.62          ((v2_struct_0 @ sk_A)
% 20.45/20.62           | (v2_struct_0 @ X0)
% 20.45/20.62           | ~ (v4_orders_2 @ X0)
% 20.45/20.62           | ~ (v7_waybel_0 @ X0)
% 20.45/20.62           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 20.45/20.62           | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ X0))
% 20.45/20.62           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_D_1 @ sk_B @ sk_A))
% 20.45/20.62           | ~ (v11_waybel_0 @ X0 @ sk_A)
% 20.45/20.62           | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 20.45/20.62         <= (~
% 20.45/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.45/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.45/20.62      inference('demod', [status(thm)],
% 20.45/20.62                ['466', '467', '468', '469', '470', '471', '472', '473', 
% 20.45/20.62                 '474', '475'])).
% 20.45/20.62  thf('477', plain,
% 20.45/20.62      ((((v2_struct_0 @ sk_A)
% 20.45/20.62         | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.45/20.62         | ~ (v11_waybel_0 @ sk_B @ sk_A)
% 20.45/20.62         | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 20.45/20.62         | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 20.45/20.62         | ~ (v7_waybel_0 @ sk_B)
% 20.45/20.62         | ~ (v4_orders_2 @ sk_B)
% 20.45/20.62         | (v2_struct_0 @ sk_B)
% 20.45/20.62         | (v2_struct_0 @ sk_A)))
% 20.45/20.62         <= (~
% 20.45/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.45/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.45/20.62      inference('sup-', [status(thm)], ['463', '476'])).
% 20.45/20.62  thf('478', plain, ((v11_waybel_0 @ sk_B @ sk_A)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('479', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('480', plain, ((v7_waybel_0 @ sk_B)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('481', plain, ((v4_orders_2 @ sk_B)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('482', plain,
% 20.45/20.62      ((((v2_struct_0 @ sk_A)
% 20.45/20.62         | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.45/20.62         | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 20.45/20.62         | (v2_struct_0 @ sk_B)
% 20.45/20.62         | (v2_struct_0 @ sk_A)))
% 20.45/20.62         <= (~
% 20.45/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.45/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.45/20.62      inference('demod', [status(thm)], ['477', '478', '479', '480', '481'])).
% 20.45/20.62  thf('483', plain,
% 20.45/20.62      ((((v2_struct_0 @ sk_B)
% 20.45/20.62         | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 20.45/20.62         | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))
% 20.45/20.62         | (v2_struct_0 @ sk_A)))
% 20.45/20.62         <= (~
% 20.45/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.45/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.45/20.62      inference('simplify', [status(thm)], ['482'])).
% 20.45/20.62  thf('484', plain,
% 20.45/20.62      (![X37 : $i]:
% 20.45/20.62         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X37) @ sk_A @ sk_A)
% 20.45/20.62          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A)))),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('485', plain,
% 20.45/20.62      ((((v2_struct_0 @ sk_A)
% 20.45/20.62         | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 20.45/20.62         | (v2_struct_0 @ sk_B)
% 20.45/20.62         | (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_D_2 @ sk_A)) @ sk_A @ sk_A)))
% 20.45/20.62         <= (~
% 20.45/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.45/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.45/20.62      inference('sup-', [status(thm)], ['483', '484'])).
% 20.45/20.62  thf('486', plain,
% 20.45/20.62      (![X34 : $i, X35 : $i, X36 : $i]:
% 20.45/20.62         (~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X35))
% 20.45/20.62          | ~ (v5_pre_topc @ (k4_waybel_1 @ X35 @ (sk_D_2 @ X35)) @ X35 @ X35)
% 20.45/20.62          | ~ (v11_waybel_0 @ X36 @ X35)
% 20.45/20.62          | ~ (r3_waybel_9 @ X35 @ X36 @ X34)
% 20.45/20.62          | ((X34) = (k1_waybel_9 @ X35 @ X36))
% 20.45/20.62          | ~ (l1_waybel_0 @ X36 @ X35)
% 20.45/20.62          | ~ (v7_waybel_0 @ X36)
% 20.45/20.62          | ~ (v4_orders_2 @ X36)
% 20.45/20.62          | (v2_struct_0 @ X36)
% 20.45/20.62          | ~ (l1_waybel_9 @ X35)
% 20.45/20.62          | ~ (v1_compts_1 @ X35)
% 20.45/20.62          | ~ (v2_lattice3 @ X35)
% 20.45/20.62          | ~ (v1_lattice3 @ X35)
% 20.45/20.62          | ~ (v5_orders_2 @ X35)
% 20.45/20.62          | ~ (v4_orders_2 @ X35)
% 20.45/20.62          | ~ (v3_orders_2 @ X35)
% 20.45/20.62          | ~ (v8_pre_topc @ X35)
% 20.45/20.62          | ~ (v2_pre_topc @ X35))),
% 20.45/20.62      inference('cnf', [status(esa)], [t36_waybel_9])).
% 20.45/20.62  thf('487', plain,
% 20.45/20.62      ((![X0 : $i, X1 : $i]:
% 20.45/20.62          ((v2_struct_0 @ sk_B)
% 20.45/20.62           | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 20.45/20.62           | (v2_struct_0 @ sk_A)
% 20.45/20.62           | ~ (v2_pre_topc @ sk_A)
% 20.45/20.62           | ~ (v8_pre_topc @ sk_A)
% 20.45/20.62           | ~ (v3_orders_2 @ sk_A)
% 20.45/20.62           | ~ (v4_orders_2 @ sk_A)
% 20.45/20.62           | ~ (v5_orders_2 @ sk_A)
% 20.45/20.62           | ~ (v1_lattice3 @ sk_A)
% 20.45/20.62           | ~ (v2_lattice3 @ sk_A)
% 20.45/20.62           | ~ (v1_compts_1 @ sk_A)
% 20.45/20.62           | ~ (l1_waybel_9 @ sk_A)
% 20.45/20.62           | (v2_struct_0 @ X0)
% 20.45/20.62           | ~ (v4_orders_2 @ X0)
% 20.45/20.62           | ~ (v7_waybel_0 @ X0)
% 20.45/20.62           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 20.45/20.62           | ((X1) = (k1_waybel_9 @ sk_A @ X0))
% 20.45/20.62           | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 20.45/20.62           | ~ (v11_waybel_0 @ X0 @ sk_A)
% 20.45/20.62           | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))))
% 20.45/20.62         <= (~
% 20.45/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.45/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.45/20.62      inference('sup-', [status(thm)], ['485', '486'])).
% 20.45/20.62  thf('488', plain, ((v2_pre_topc @ sk_A)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('489', plain, ((v8_pre_topc @ sk_A)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('490', plain, ((v3_orders_2 @ sk_A)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('491', plain, ((v4_orders_2 @ sk_A)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('492', plain, ((v5_orders_2 @ sk_A)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('493', plain, ((v1_lattice3 @ sk_A)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('494', plain, ((v2_lattice3 @ sk_A)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('495', plain, ((v1_compts_1 @ sk_A)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('496', plain, ((l1_waybel_9 @ sk_A)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('497', plain,
% 20.45/20.62      ((![X0 : $i, X1 : $i]:
% 20.45/20.62          ((v2_struct_0 @ sk_B)
% 20.45/20.62           | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 20.45/20.62           | (v2_struct_0 @ sk_A)
% 20.45/20.62           | (v2_struct_0 @ X0)
% 20.45/20.62           | ~ (v4_orders_2 @ X0)
% 20.45/20.62           | ~ (v7_waybel_0 @ X0)
% 20.45/20.62           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 20.45/20.62           | ((X1) = (k1_waybel_9 @ sk_A @ X0))
% 20.45/20.62           | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 20.45/20.62           | ~ (v11_waybel_0 @ X0 @ sk_A)
% 20.45/20.62           | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))))
% 20.45/20.62         <= (~
% 20.45/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.45/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.45/20.62      inference('demod', [status(thm)],
% 20.45/20.62                ['487', '488', '489', '490', '491', '492', '493', '494', 
% 20.45/20.62                 '495', '496'])).
% 20.45/20.62  thf('498', plain,
% 20.45/20.62      ((![X0 : $i]:
% 20.45/20.62          ((v2_struct_0 @ sk_A)
% 20.45/20.62           | ~ (v11_waybel_0 @ X0 @ sk_A)
% 20.45/20.62           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_D_1 @ sk_B @ sk_A))
% 20.45/20.62           | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ X0))
% 20.45/20.62           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 20.45/20.62           | ~ (v7_waybel_0 @ X0)
% 20.45/20.62           | ~ (v4_orders_2 @ X0)
% 20.45/20.62           | (v2_struct_0 @ X0)
% 20.45/20.62           | (v2_struct_0 @ sk_A)
% 20.45/20.62           | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 20.45/20.62           | (v2_struct_0 @ sk_B)))
% 20.45/20.62         <= (~
% 20.45/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.45/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.45/20.62      inference('sup-', [status(thm)], ['462', '497'])).
% 20.45/20.62  thf('499', plain,
% 20.45/20.62      ((![X0 : $i]:
% 20.45/20.62          ((v2_struct_0 @ sk_B)
% 20.45/20.62           | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 20.45/20.62           | (v2_struct_0 @ X0)
% 20.45/20.62           | ~ (v4_orders_2 @ X0)
% 20.45/20.62           | ~ (v7_waybel_0 @ X0)
% 20.45/20.62           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 20.45/20.62           | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ X0))
% 20.45/20.62           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_D_1 @ sk_B @ sk_A))
% 20.45/20.62           | ~ (v11_waybel_0 @ X0 @ sk_A)
% 20.45/20.62           | (v2_struct_0 @ sk_A)))
% 20.45/20.62         <= (~
% 20.45/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.45/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.45/20.62      inference('simplify', [status(thm)], ['498'])).
% 20.45/20.62  thf('500', plain,
% 20.45/20.62      ((((v2_struct_0 @ sk_A)
% 20.45/20.62         | (v2_struct_0 @ sk_A)
% 20.45/20.62         | ~ (v11_waybel_0 @ sk_B @ sk_A)
% 20.45/20.62         | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 20.45/20.62         | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 20.45/20.62         | ~ (v7_waybel_0 @ sk_B)
% 20.45/20.62         | ~ (v4_orders_2 @ sk_B)
% 20.45/20.62         | (v2_struct_0 @ sk_B)
% 20.45/20.62         | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 20.45/20.62         | (v2_struct_0 @ sk_B)))
% 20.45/20.62         <= (~
% 20.45/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.45/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.45/20.62      inference('sup-', [status(thm)], ['439', '499'])).
% 20.45/20.62  thf('501', plain, ((v11_waybel_0 @ sk_B @ sk_A)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('502', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('503', plain, ((v7_waybel_0 @ sk_B)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('504', plain, ((v4_orders_2 @ sk_B)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('505', plain,
% 20.45/20.62      ((((v2_struct_0 @ sk_A)
% 20.45/20.62         | (v2_struct_0 @ sk_A)
% 20.45/20.62         | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 20.45/20.62         | (v2_struct_0 @ sk_B)
% 20.45/20.62         | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 20.45/20.62         | (v2_struct_0 @ sk_B)))
% 20.45/20.62         <= (~
% 20.45/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.45/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.45/20.62      inference('demod', [status(thm)], ['500', '501', '502', '503', '504'])).
% 20.45/20.62  thf('506', plain,
% 20.45/20.62      ((((v2_struct_0 @ sk_B)
% 20.45/20.62         | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 20.45/20.62         | (v2_struct_0 @ sk_A)))
% 20.45/20.62         <= (~
% 20.45/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.45/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.45/20.62      inference('simplify', [status(thm)], ['505'])).
% 20.45/20.62  thf('507', plain, (~ (v2_struct_0 @ sk_B)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('508', plain,
% 20.45/20.62      ((((v2_struct_0 @ sk_A)
% 20.45/20.62         | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))))
% 20.45/20.62         <= (~
% 20.45/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.45/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.45/20.62      inference('clc', [status(thm)], ['506', '507'])).
% 20.45/20.62  thf('509', plain,
% 20.45/20.62      (((v2_struct_0 @ sk_A)
% 20.45/20.62        | (r3_waybel_9 @ sk_A @ sk_B @ (k1_waybel_9 @ sk_A @ sk_B)))),
% 20.45/20.62      inference('simplify', [status(thm)], ['73'])).
% 20.45/20.62  thf('510', plain,
% 20.45/20.62      (((v2_struct_0 @ sk_A)
% 20.45/20.62        | (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 20.45/20.62      inference('simplify', [status(thm)], ['77'])).
% 20.45/20.62  thf('511', plain,
% 20.45/20.62      (![X31 : $i, X32 : $i, X33 : $i]:
% 20.45/20.62         ((v2_struct_0 @ X31)
% 20.45/20.62          | ~ (v4_orders_2 @ X31)
% 20.45/20.62          | ~ (v7_waybel_0 @ X31)
% 20.45/20.62          | ~ (l1_waybel_0 @ X31 @ X32)
% 20.45/20.62          | ~ (r3_waybel_9 @ X32 @ X31 @ X33)
% 20.45/20.62          | (r2_hidden @ X33 @ (k10_yellow_6 @ X32 @ X31))
% 20.45/20.62          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 20.45/20.62          | ((sk_C_1 @ X31 @ X32) != (sk_D_1 @ X31 @ X32))
% 20.45/20.62          | ~ (l1_pre_topc @ X32)
% 20.45/20.62          | ~ (v1_compts_1 @ X32)
% 20.45/20.62          | ~ (v8_pre_topc @ X32)
% 20.45/20.62          | ~ (v2_pre_topc @ X32)
% 20.45/20.62          | (v2_struct_0 @ X32))),
% 20.45/20.62      inference('cnf', [status(esa)], [t33_waybel_9])).
% 20.45/20.62  thf('512', plain,
% 20.45/20.62      (![X0 : $i]:
% 20.45/20.62         ((v2_struct_0 @ sk_A)
% 20.45/20.62          | (v2_struct_0 @ sk_A)
% 20.45/20.62          | ~ (v2_pre_topc @ sk_A)
% 20.45/20.62          | ~ (v8_pre_topc @ sk_A)
% 20.45/20.62          | ~ (v1_compts_1 @ sk_A)
% 20.45/20.62          | ~ (l1_pre_topc @ sk_A)
% 20.45/20.62          | ((sk_C_1 @ X0 @ sk_A) != (sk_D_1 @ X0 @ sk_A))
% 20.45/20.62          | (r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.45/20.62             (k10_yellow_6 @ sk_A @ X0))
% 20.45/20.62          | ~ (r3_waybel_9 @ sk_A @ X0 @ (k1_waybel_9 @ sk_A @ sk_B))
% 20.45/20.62          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 20.45/20.62          | ~ (v7_waybel_0 @ X0)
% 20.45/20.62          | ~ (v4_orders_2 @ X0)
% 20.45/20.62          | (v2_struct_0 @ X0))),
% 20.45/20.62      inference('sup-', [status(thm)], ['510', '511'])).
% 20.45/20.62  thf('513', plain, ((v2_pre_topc @ sk_A)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('514', plain, ((v8_pre_topc @ sk_A)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('515', plain, ((v1_compts_1 @ sk_A)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('516', plain, ((l1_pre_topc @ sk_A)),
% 20.45/20.62      inference('sup-', [status(thm)], ['6', '7'])).
% 20.45/20.62  thf('517', plain,
% 20.45/20.62      (![X0 : $i]:
% 20.45/20.62         ((v2_struct_0 @ sk_A)
% 20.45/20.62          | (v2_struct_0 @ sk_A)
% 20.45/20.62          | ((sk_C_1 @ X0 @ sk_A) != (sk_D_1 @ X0 @ sk_A))
% 20.45/20.62          | (r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.45/20.62             (k10_yellow_6 @ sk_A @ X0))
% 20.45/20.62          | ~ (r3_waybel_9 @ sk_A @ X0 @ (k1_waybel_9 @ sk_A @ sk_B))
% 20.45/20.62          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 20.45/20.62          | ~ (v7_waybel_0 @ X0)
% 20.45/20.62          | ~ (v4_orders_2 @ X0)
% 20.45/20.62          | (v2_struct_0 @ X0))),
% 20.45/20.62      inference('demod', [status(thm)], ['512', '513', '514', '515', '516'])).
% 20.45/20.62  thf('518', plain,
% 20.45/20.62      (![X0 : $i]:
% 20.45/20.62         ((v2_struct_0 @ X0)
% 20.45/20.62          | ~ (v4_orders_2 @ X0)
% 20.45/20.62          | ~ (v7_waybel_0 @ X0)
% 20.45/20.62          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 20.45/20.62          | ~ (r3_waybel_9 @ sk_A @ X0 @ (k1_waybel_9 @ sk_A @ sk_B))
% 20.45/20.62          | (r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.45/20.62             (k10_yellow_6 @ sk_A @ X0))
% 20.45/20.62          | ((sk_C_1 @ X0 @ sk_A) != (sk_D_1 @ X0 @ sk_A))
% 20.45/20.62          | (v2_struct_0 @ sk_A))),
% 20.45/20.62      inference('simplify', [status(thm)], ['517'])).
% 20.45/20.62  thf('519', plain,
% 20.45/20.62      (((v2_struct_0 @ sk_A)
% 20.45/20.62        | (v2_struct_0 @ sk_A)
% 20.45/20.62        | ((sk_C_1 @ sk_B @ sk_A) != (sk_D_1 @ sk_B @ sk_A))
% 20.45/20.62        | (r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.45/20.62           (k10_yellow_6 @ sk_A @ sk_B))
% 20.45/20.62        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 20.45/20.62        | ~ (v7_waybel_0 @ sk_B)
% 20.45/20.62        | ~ (v4_orders_2 @ sk_B)
% 20.45/20.62        | (v2_struct_0 @ sk_B))),
% 20.45/20.62      inference('sup-', [status(thm)], ['509', '518'])).
% 20.45/20.62  thf('520', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('521', plain, ((v7_waybel_0 @ sk_B)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('522', plain, ((v4_orders_2 @ sk_B)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('523', plain,
% 20.45/20.62      (((v2_struct_0 @ sk_A)
% 20.45/20.62        | (v2_struct_0 @ sk_A)
% 20.45/20.62        | ((sk_C_1 @ sk_B @ sk_A) != (sk_D_1 @ sk_B @ sk_A))
% 20.45/20.62        | (r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.45/20.62           (k10_yellow_6 @ sk_A @ sk_B))
% 20.45/20.62        | (v2_struct_0 @ sk_B))),
% 20.45/20.62      inference('demod', [status(thm)], ['519', '520', '521', '522'])).
% 20.45/20.62  thf('524', plain,
% 20.45/20.62      (((v2_struct_0 @ sk_B)
% 20.45/20.62        | (r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.45/20.62           (k10_yellow_6 @ sk_A @ sk_B))
% 20.45/20.62        | ((sk_C_1 @ sk_B @ sk_A) != (sk_D_1 @ sk_B @ sk_A))
% 20.45/20.62        | (v2_struct_0 @ sk_A))),
% 20.45/20.62      inference('simplify', [status(thm)], ['523'])).
% 20.45/20.62  thf('525', plain,
% 20.45/20.62      (((((sk_C_1 @ sk_B @ sk_A) != (k1_waybel_9 @ sk_A @ sk_B))
% 20.45/20.62         | (v2_struct_0 @ sk_A)
% 20.45/20.62         | (v2_struct_0 @ sk_A)
% 20.45/20.62         | (r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.45/20.62            (k10_yellow_6 @ sk_A @ sk_B))
% 20.45/20.62         | (v2_struct_0 @ sk_B)))
% 20.45/20.62         <= (~
% 20.45/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.45/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.45/20.62      inference('sup-', [status(thm)], ['508', '524'])).
% 20.45/20.62  thf('526', plain,
% 20.45/20.62      ((((v2_struct_0 @ sk_B)
% 20.45/20.62         | (r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.45/20.62            (k10_yellow_6 @ sk_A @ sk_B))
% 20.45/20.62         | (v2_struct_0 @ sk_A)
% 20.45/20.62         | ((sk_C_1 @ sk_B @ sk_A) != (k1_waybel_9 @ sk_A @ sk_B))))
% 20.45/20.62         <= (~
% 20.45/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.45/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.45/20.62      inference('simplify', [status(thm)], ['525'])).
% 20.45/20.62  thf('527', plain,
% 20.45/20.62      (((((k1_waybel_9 @ sk_A @ sk_B) != (k1_waybel_9 @ sk_A @ sk_B))
% 20.45/20.62         | (v2_struct_0 @ sk_A)
% 20.45/20.62         | (v2_struct_0 @ sk_A)
% 20.45/20.62         | (r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.45/20.62            (k10_yellow_6 @ sk_A @ sk_B))
% 20.45/20.62         | (v2_struct_0 @ sk_B)))
% 20.45/20.62         <= (~
% 20.45/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.45/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.45/20.62      inference('sup-', [status(thm)], ['416', '526'])).
% 20.45/20.62  thf('528', plain,
% 20.45/20.62      ((((v2_struct_0 @ sk_B)
% 20.45/20.62         | (r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.45/20.62            (k10_yellow_6 @ sk_A @ sk_B))
% 20.45/20.62         | (v2_struct_0 @ sk_A)))
% 20.45/20.62         <= (~
% 20.45/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.45/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.45/20.62      inference('simplify', [status(thm)], ['527'])).
% 20.45/20.62  thf('529', plain, (~ (v2_struct_0 @ sk_B)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('530', plain,
% 20.45/20.62      ((((v2_struct_0 @ sk_A)
% 20.45/20.62         | (r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.45/20.62            (k10_yellow_6 @ sk_A @ sk_B))))
% 20.45/20.62         <= (~
% 20.45/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.45/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.45/20.62      inference('clc', [status(thm)], ['528', '529'])).
% 20.45/20.62  thf('531', plain,
% 20.45/20.62      ((~ (r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.45/20.62           (k10_yellow_6 @ sk_A @ sk_B)))
% 20.45/20.62         <= (~
% 20.45/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.45/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.45/20.62      inference('split', [status(esa)], ['323'])).
% 20.45/20.62  thf('532', plain,
% 20.45/20.62      (((v2_struct_0 @ sk_A))
% 20.45/20.62         <= (~
% 20.45/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.45/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.45/20.62      inference('clc', [status(thm)], ['530', '531'])).
% 20.45/20.62  thf(cc1_lattice3, axiom,
% 20.45/20.62    (![A:$i]:
% 20.45/20.62     ( ( l1_orders_2 @ A ) =>
% 20.45/20.62       ( ( v1_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 20.45/20.62  thf('533', plain,
% 20.45/20.62      (![X0 : $i]:
% 20.45/20.62         (~ (v1_lattice3 @ X0) | ~ (v2_struct_0 @ X0) | ~ (l1_orders_2 @ X0))),
% 20.45/20.62      inference('cnf', [status(esa)], [cc1_lattice3])).
% 20.45/20.62  thf('534', plain,
% 20.45/20.62      (((~ (l1_orders_2 @ sk_A) | ~ (v1_lattice3 @ sk_A)))
% 20.45/20.62         <= (~
% 20.45/20.62             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 20.45/20.62               (k10_yellow_6 @ sk_A @ sk_B))))),
% 20.45/20.62      inference('sup-', [status(thm)], ['532', '533'])).
% 20.45/20.62  thf('535', plain, ((l1_orders_2 @ sk_A)),
% 20.45/20.62      inference('sup-', [status(thm)], ['140', '141'])).
% 20.45/20.62  thf('536', plain, ((v1_lattice3 @ sk_A)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('537', plain,
% 20.45/20.62      (((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ (k10_yellow_6 @ sk_A @ sk_B)))),
% 20.45/20.62      inference('demod', [status(thm)], ['534', '535', '536'])).
% 20.45/20.62  thf('538', plain,
% 20.45/20.62      (~ ((r2_waybel_9 @ sk_A @ sk_B)) | 
% 20.45/20.62       ~
% 20.45/20.62       ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ (k10_yellow_6 @ sk_A @ sk_B)))),
% 20.45/20.62      inference('split', [status(esa)], ['323'])).
% 20.45/20.62  thf('539', plain, (~ ((r2_waybel_9 @ sk_A @ sk_B))),
% 20.45/20.62      inference('sat_resolution*', [status(thm)], ['537', '538'])).
% 20.45/20.62  thf('540', plain, (~ (r2_waybel_9 @ sk_A @ sk_B)),
% 20.45/20.62      inference('simpl_trail', [status(thm)], ['324', '539'])).
% 20.45/20.62  thf('541', plain, ((v2_struct_0 @ sk_A)),
% 20.45/20.62      inference('clc', [status(thm)], ['322', '540'])).
% 20.45/20.62  thf('542', plain,
% 20.45/20.62      (![X0 : $i]:
% 20.45/20.62         (~ (v1_lattice3 @ X0) | ~ (v2_struct_0 @ X0) | ~ (l1_orders_2 @ X0))),
% 20.45/20.62      inference('cnf', [status(esa)], [cc1_lattice3])).
% 20.45/20.62  thf('543', plain, ((~ (l1_orders_2 @ sk_A) | ~ (v1_lattice3 @ sk_A))),
% 20.45/20.62      inference('sup-', [status(thm)], ['541', '542'])).
% 20.45/20.62  thf('544', plain, ((l1_orders_2 @ sk_A)),
% 20.45/20.62      inference('sup-', [status(thm)], ['140', '141'])).
% 20.45/20.62  thf('545', plain, ((v1_lattice3 @ sk_A)),
% 20.45/20.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.62  thf('546', plain, ($false),
% 20.45/20.62      inference('demod', [status(thm)], ['543', '544', '545'])).
% 20.45/20.62  
% 20.45/20.62  % SZS output end Refutation
% 20.45/20.62  
% 20.45/20.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
