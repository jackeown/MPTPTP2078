%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT2042+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BZUwEhPDrL

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:42 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 562 expanded)
%              Number of leaves         :   49 ( 205 expanded)
%              Depth                    :   17
%              Number of atoms          : 1160 (9310 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   20 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_waybel_9_type,type,(
    l1_waybel_9: $i > $o )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_waybel_2_type,type,(
    k1_waybel_2: $i > $i > $i )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(r1_waybel_9_type,type,(
    r1_waybel_9: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k4_waybel_1_type,type,(
    k4_waybel_1: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $o )).

thf(v2_waybel_2_type,type,(
    v2_waybel_2: $i > $o )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v10_waybel_0_type,type,(
    v10_waybel_0: $i > $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(t41_waybel_9,conjecture,(
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
       => ( v2_waybel_2 @ A ) ) ) )).

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
         => ( v2_waybel_2 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t41_waybel_9])).

thf('0',plain,(
    ~ ( v2_waybel_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t37_waybel_9,axiom,(
    ! [A: $i] :
      ( ( ( l1_waybel_9 @ A )
        & ( v2_lattice3 @ A )
        & ( v1_lattice3 @ A )
        & ( v5_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v3_orders_2 @ A )
        & ( v8_pre_topc @ A )
        & ( v2_pre_topc @ A ) )
     => ( ( ! [B: $i] :
              ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
             => ( v5_pre_topc @ ( k4_waybel_1 @ A @ B ) @ A @ A ) )
          & ! [B: $i] :
              ( ( ( l1_waybel_0 @ B @ A )
                & ( v7_waybel_0 @ B )
                & ( v4_orders_2 @ B )
                & ~ ( v2_struct_0 @ B ) )
             => ( ( v10_waybel_0 @ B @ A )
               => ( ( r2_hidden @ ( k1_waybel_2 @ A @ B ) @ ( k10_yellow_6 @ A @ B ) )
                  & ( r1_waybel_9 @ A @ B ) ) ) ) )
       => ( v2_waybel_2 @ A ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
       => ( v5_pre_topc @ ( k4_waybel_1 @ A @ B ) @ A @ A ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,(
    ! [X15: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X15 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ X0 @ sk_A )
      | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X0 ) @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X1 @ X0 ) @ X1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ sk_A ) ),
    inference(clc,[status(thm)],['3','4'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( v10_waybel_0 @ B @ A )
       => ( ( r1_waybel_9 @ A @ B )
          & ( r2_hidden @ ( k1_waybel_2 @ A @ B ) @ ( k10_yellow_6 @ A @ B ) ) ) )
     => ( zip_tseitin_2 @ B @ A ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ( zip_tseitin_2 @ X4 @ X5 )
      | ( v10_waybel_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(zf_stmt_3,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( zip_tseitin_1 @ B @ A )
       => ( zip_tseitin_2 @ B @ A ) )
     => ( zip_tseitin_3 @ B @ A ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( ( zip_tseitin_3 @ X6 @ X7 )
      | ~ ( zip_tseitin_2 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v10_waybel_0 @ X1 @ X0 )
      | ( zip_tseitin_3 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(zf_stmt_4,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zf_stmt_5,type,(
    zip_tseitin_2: $i > $i > $o )).

thf(zf_stmt_6,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_1 @ B @ A )
     => ( ~ ( v2_struct_0 @ B )
        & ( v4_orders_2 @ B )
        & ( v7_waybel_0 @ B )
        & ( l1_waybel_0 @ B @ A ) ) ) )).

thf(zf_stmt_8,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_9,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( v8_pre_topc @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_waybel_9 @ A ) )
     => ( ( ! [B: $i] :
              ( zip_tseitin_3 @ B @ A )
          & ! [B: $i] :
              ( zip_tseitin_0 @ B @ A ) )
       => ( v2_waybel_2 @ A ) ) ) )).

thf('9',plain,(
    ! [X8: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_B @ X8 ) @ X8 )
      | ~ ( zip_tseitin_0 @ ( sk_B_1 @ X8 ) @ X8 )
      | ( v2_waybel_2 @ X8 )
      | ~ ( l1_waybel_9 @ X8 )
      | ~ ( v2_lattice3 @ X8 )
      | ~ ( v1_lattice3 @ X8 )
      | ~ ( v5_orders_2 @ X8 )
      | ~ ( v4_orders_2 @ X8 )
      | ~ ( v3_orders_2 @ X8 )
      | ~ ( v8_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v10_waybel_0 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v8_pre_topc @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_lattice3 @ X0 )
      | ~ ( v2_lattice3 @ X0 )
      | ~ ( l1_waybel_9 @ X0 )
      | ( v2_waybel_2 @ X0 )
      | ~ ( zip_tseitin_0 @ ( sk_B_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( v2_waybel_2 @ sk_A )
    | ~ ( l1_waybel_9 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v10_waybel_0 @ ( sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v2_waybel_2 @ sk_A )
    | ( v10_waybel_0 @ ( sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['11','12','13','14','15','16','17','18','19'])).

thf('21',plain,(
    ~ ( v2_waybel_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v10_waybel_0 @ ( sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['20','21'])).

thf(t38_waybel_9,axiom,(
    ! [A: $i] :
      ( ( ( l1_waybel_9 @ A )
        & ( v1_compts_1 @ A )
        & ( v2_lattice3 @ A )
        & ( v1_lattice3 @ A )
        & ( v5_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v3_orders_2 @ A )
        & ( v8_pre_topc @ A )
        & ( v2_pre_topc @ A ) )
     => ( ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( v5_pre_topc @ ( k4_waybel_1 @ A @ B ) @ A @ A ) )
       => ! [B: $i] :
            ( ( ( l1_waybel_0 @ B @ A )
              & ( v7_waybel_0 @ B )
              & ( v4_orders_2 @ B )
              & ~ ( v2_struct_0 @ B ) )
           => ( ( v10_waybel_0 @ B @ A )
             => ( ( r2_hidden @ ( k1_waybel_2 @ A @ B ) @ ( k10_yellow_6 @ A @ B ) )
                & ( r1_waybel_9 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_10,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
       => ( v5_pre_topc @ ( k4_waybel_1 @ A @ B ) @ A @ A ) )
     => ( zip_tseitin_4 @ B @ A ) ) )).

thf('23',plain,(
    ! [X9: $i,X10: $i] :
      ( ( zip_tseitin_4 @ X9 @ X10 )
      | ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('24',plain,(
    ! [X15: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X15 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_4 @ X0 @ sk_A )
      | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X0 ) @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X9: $i,X10: $i] :
      ( ( zip_tseitin_4 @ X9 @ X10 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X10 @ X9 ) @ X10 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_4 @ X0 @ sk_A )
      | ( zip_tseitin_4 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( zip_tseitin_4 @ X0 @ sk_A ) ),
    inference(simplify,[status(thm)],['27'])).

thf(zf_stmt_11,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(zf_stmt_12,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_5 @ B @ A )
     => ( ( r1_waybel_9 @ A @ B )
        & ( r2_hidden @ ( k1_waybel_2 @ A @ B ) @ ( k10_yellow_6 @ A @ B ) ) ) ) )).

thf(zf_stmt_13,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(zf_stmt_14,axiom,(
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
            ( zip_tseitin_4 @ B @ A )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v4_orders_2 @ B )
              & ( v7_waybel_0 @ B )
              & ( l1_waybel_0 @ B @ A ) )
           => ( ( v10_waybel_0 @ B @ A )
             => ( zip_tseitin_5 @ B @ A ) ) ) ) ) )).

thf('29',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( zip_tseitin_4 @ ( sk_B_2 @ X13 ) @ X13 )
      | ( v2_struct_0 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v7_waybel_0 @ X14 )
      | ~ ( l1_waybel_0 @ X14 @ X13 )
      | ( zip_tseitin_5 @ X14 @ X13 )
      | ~ ( v10_waybel_0 @ X14 @ X13 )
      | ~ ( l1_waybel_9 @ X13 )
      | ~ ( v1_compts_1 @ X13 )
      | ~ ( v2_lattice3 @ X13 )
      | ~ ( v1_lattice3 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ~ ( v8_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_14])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( v8_pre_topc @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( v1_compts_1 @ sk_A )
      | ~ ( l1_waybel_9 @ sk_A )
      | ~ ( v10_waybel_0 @ X0 @ sk_A )
      | ( zip_tseitin_5 @ X0 @ sk_A )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v10_waybel_0 @ X0 @ sk_A )
      | ( zip_tseitin_5 @ X0 @ sk_A )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31','32','33','34','35','36','37','38','39'])).

thf('41',plain,
    ( ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
    | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
    | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
    | ( zip_tseitin_5 @ ( sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['22','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ sk_A ) ),
    inference(clc,[status(thm)],['3','4'])).

thf('43',plain,(
    ! [X6: $i,X7: $i] :
      ( ( zip_tseitin_3 @ X6 @ X7 )
      | ( zip_tseitin_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('44',plain,(
    ! [X2: $i,X3: $i] :
      ( ( v4_orders_2 @ X2 )
      | ~ ( zip_tseitin_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X1 @ X0 )
      | ( v4_orders_2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X8: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_B @ X8 ) @ X8 )
      | ~ ( zip_tseitin_0 @ ( sk_B_1 @ X8 ) @ X8 )
      | ( v2_waybel_2 @ X8 )
      | ~ ( l1_waybel_9 @ X8 )
      | ~ ( v2_lattice3 @ X8 )
      | ~ ( v1_lattice3 @ X8 )
      | ~ ( v5_orders_2 @ X8 )
      | ~ ( v4_orders_2 @ X8 )
      | ~ ( v3_orders_2 @ X8 )
      | ~ ( v8_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( sk_B @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v8_pre_topc @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_lattice3 @ X0 )
      | ~ ( v2_lattice3 @ X0 )
      | ~ ( l1_waybel_9 @ X0 )
      | ( v2_waybel_2 @ X0 )
      | ~ ( zip_tseitin_0 @ ( sk_B_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( v2_waybel_2 @ sk_A )
    | ~ ( l1_waybel_9 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v4_orders_2 @ ( sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v2_waybel_2 @ sk_A )
    | ( v4_orders_2 @ ( sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49','50','51','52','53','54','55','56'])).

thf('58',plain,(
    ~ ( v2_waybel_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v4_orders_2 @ ( sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ sk_A ) ),
    inference(clc,[status(thm)],['3','4'])).

thf('61',plain,(
    ! [X6: $i,X7: $i] :
      ( ( zip_tseitin_3 @ X6 @ X7 )
      | ( zip_tseitin_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('62',plain,(
    ! [X2: $i,X3: $i] :
      ( ( v7_waybel_0 @ X2 )
      | ~ ( zip_tseitin_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X1 @ X0 )
      | ( v7_waybel_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X8: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_B @ X8 ) @ X8 )
      | ~ ( zip_tseitin_0 @ ( sk_B_1 @ X8 ) @ X8 )
      | ( v2_waybel_2 @ X8 )
      | ~ ( l1_waybel_9 @ X8 )
      | ~ ( v2_lattice3 @ X8 )
      | ~ ( v1_lattice3 @ X8 )
      | ~ ( v5_orders_2 @ X8 )
      | ~ ( v4_orders_2 @ X8 )
      | ~ ( v3_orders_2 @ X8 )
      | ~ ( v8_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( sk_B @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v8_pre_topc @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_lattice3 @ X0 )
      | ~ ( v2_lattice3 @ X0 )
      | ~ ( l1_waybel_9 @ X0 )
      | ( v2_waybel_2 @ X0 )
      | ~ ( zip_tseitin_0 @ ( sk_B_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( v2_waybel_2 @ sk_A )
    | ~ ( l1_waybel_9 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v7_waybel_0 @ ( sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf('67',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v2_waybel_2 @ sk_A )
    | ( v7_waybel_0 @ ( sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','67','68','69','70','71','72','73','74'])).

thf('76',plain,(
    ~ ( v2_waybel_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v7_waybel_0 @ ( sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ sk_A ) ),
    inference(clc,[status(thm)],['3','4'])).

thf('79',plain,(
    ! [X6: $i,X7: $i] :
      ( ( zip_tseitin_3 @ X6 @ X7 )
      | ( zip_tseitin_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('80',plain,(
    ! [X2: $i,X3: $i] :
      ( ( l1_waybel_0 @ X2 @ X3 )
      | ~ ( zip_tseitin_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X1 @ X0 )
      | ( l1_waybel_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X8: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_B @ X8 ) @ X8 )
      | ~ ( zip_tseitin_0 @ ( sk_B_1 @ X8 ) @ X8 )
      | ( v2_waybel_2 @ X8 )
      | ~ ( l1_waybel_9 @ X8 )
      | ~ ( v2_lattice3 @ X8 )
      | ~ ( v1_lattice3 @ X8 )
      | ~ ( v5_orders_2 @ X8 )
      | ~ ( v4_orders_2 @ X8 )
      | ~ ( v3_orders_2 @ X8 )
      | ~ ( v8_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v8_pre_topc @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_lattice3 @ X0 )
      | ~ ( v2_lattice3 @ X0 )
      | ~ ( l1_waybel_9 @ X0 )
      | ( v2_waybel_2 @ X0 )
      | ~ ( zip_tseitin_0 @ ( sk_B_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( v2_waybel_2 @ sk_A )
    | ~ ( l1_waybel_9 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['78','83'])).

thf('85',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( v2_waybel_2 @ sk_A )
    | ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['84','85','86','87','88','89','90','91','92'])).

thf('94',plain,(
    ~ ( v2_waybel_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ( zip_tseitin_5 @ ( sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['41','59','77','95'])).

thf('97',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ ( k1_waybel_2 @ X11 @ X12 ) @ ( k10_yellow_6 @ X11 @ X12 ) )
      | ~ ( zip_tseitin_5 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('98',plain,
    ( ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ( r2_hidden @ ( k1_waybel_2 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k10_yellow_6 @ sk_A @ ( sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X4: $i,X5: $i] :
      ( ( zip_tseitin_2 @ X4 @ X5 )
      | ~ ( r1_waybel_9 @ X5 @ X4 )
      | ~ ( r2_hidden @ ( k1_waybel_2 @ X5 @ X4 ) @ ( k10_yellow_6 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('100',plain,
    ( ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ~ ( r1_waybel_9 @ sk_A @ ( sk_B @ sk_A ) )
    | ( zip_tseitin_2 @ ( sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ( zip_tseitin_5 @ ( sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['41','59','77','95'])).

thf('102',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_waybel_9 @ X11 @ X12 )
      | ~ ( zip_tseitin_5 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('103',plain,
    ( ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ( r1_waybel_9 @ sk_A @ ( sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( zip_tseitin_2 @ ( sk_B @ sk_A ) @ sk_A )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['100','103'])).

thf('105',plain,(
    ! [X6: $i,X7: $i] :
      ( ( zip_tseitin_3 @ X6 @ X7 )
      | ~ ( zip_tseitin_2 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('106',plain,
    ( ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ( zip_tseitin_3 @ ( sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X6: $i,X7: $i] :
      ( ( zip_tseitin_3 @ X6 @ X7 )
      | ( zip_tseitin_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('108',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v2_struct_0 @ X2 )
      | ~ ( zip_tseitin_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X1 @ X0 )
      | ~ ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    zip_tseitin_3 @ ( sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['106','109'])).

thf('111',plain,(
    ! [X8: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_B @ X8 ) @ X8 )
      | ~ ( zip_tseitin_0 @ ( sk_B_1 @ X8 ) @ X8 )
      | ( v2_waybel_2 @ X8 )
      | ~ ( l1_waybel_9 @ X8 )
      | ~ ( v2_lattice3 @ X8 )
      | ~ ( v1_lattice3 @ X8 )
      | ~ ( v5_orders_2 @ X8 )
      | ~ ( v4_orders_2 @ X8 )
      | ~ ( v3_orders_2 @ X8 )
      | ~ ( v8_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('112',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( l1_waybel_9 @ sk_A )
    | ( v2_waybel_2 @ sk_A )
    | ~ ( zip_tseitin_0 @ ( sk_B_1 @ sk_A ) @ sk_A ) ),
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
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ sk_A ) ),
    inference(clc,[status(thm)],['3','4'])).

thf('122',plain,(
    v2_waybel_2 @ sk_A ),
    inference(demod,[status(thm)],['112','113','114','115','116','117','118','119','120','121'])).

thf('123',plain,(
    $false ),
    inference(demod,[status(thm)],['0','122'])).


%------------------------------------------------------------------------------
