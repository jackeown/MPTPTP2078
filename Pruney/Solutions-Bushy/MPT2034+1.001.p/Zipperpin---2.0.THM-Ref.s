%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT2034+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uORXn4bubB

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:41 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  186 (1764 expanded)
%              Number of leaves         :   28 ( 514 expanded)
%              Depth                    :   46
%              Number of atoms          : 3167 (53454 expanded)
%              Number of equality atoms :    8 ( 782 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m2_yellow_6_type,type,(
    m2_yellow_6: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r3_waybel_9_type,type,(
    r3_waybel_9: $i > $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(t33_waybel_9,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
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
                   => ( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_waybel_9])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t46_yellow_6,axiom,(
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
             => ~ ( ~ ( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) )
                  & ! [D: $i] :
                      ( ( m2_yellow_6 @ D @ A @ B )
                     => ? [E: $i] :
                          ( ( r2_hidden @ C @ ( k10_yellow_6 @ A @ E ) )
                          & ( m2_yellow_6 @ E @ A @ D ) ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v7_waybel_0 @ X13 )
      | ~ ( l1_waybel_0 @ X13 @ X14 )
      | ( m2_yellow_6 @ ( sk_D_1 @ X16 @ X13 @ X14 ) @ X14 @ X13 )
      | ( r2_hidden @ X16 @ ( k10_yellow_6 @ X14 @ X13 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_6])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ( m2_yellow_6 @ ( sk_D_1 @ sk_C_1 @ X0 @ sk_A ) @ sk_A @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ( m2_yellow_6 @ ( sk_D_1 @ sk_C_1 @ X0 @ sk_A ) @ sk_A @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ~ ( v7_waybel_0 @ sk_B )
    | ( m2_yellow_6 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m2_yellow_6 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf(dt_m2_yellow_6,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ~ ( v2_struct_0 @ B )
        & ( v4_orders_2 @ B )
        & ( v7_waybel_0 @ B )
        & ( l1_waybel_0 @ B @ A ) )
     => ! [C: $i] :
          ( ( m2_yellow_6 @ C @ A @ B )
         => ( ~ ( v2_struct_0 @ C )
            & ( v4_orders_2 @ C )
            & ( v7_waybel_0 @ C )
            & ( l1_waybel_0 @ C @ A ) ) ) ) )).

thf('12',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X2 )
      | ~ ( v4_orders_2 @ X2 )
      | ~ ( v7_waybel_0 @ X2 )
      | ~ ( l1_waybel_0 @ X2 @ X1 )
      | ( v4_orders_2 @ X3 )
      | ~ ( m2_yellow_6 @ X3 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v4_orders_2 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('18',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('19',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v4_orders_2 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14','15','16','19'])).

thf('21',plain,
    ( ( v4_orders_2 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m2_yellow_6 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('23',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X2 )
      | ~ ( v4_orders_2 @ X2 )
      | ~ ( v7_waybel_0 @ X2 )
      | ~ ( l1_waybel_0 @ X2 @ X1 )
      | ( v7_waybel_0 @ X3 )
      | ~ ( m2_yellow_6 @ X3 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v7_waybel_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v7_waybel_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','26','27','28'])).

thf('30',plain,
    ( ( v7_waybel_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m2_yellow_6 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('32',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X2 )
      | ~ ( v4_orders_2 @ X2 )
      | ~ ( v7_waybel_0 @ X2 )
      | ~ ( l1_waybel_0 @ X2 @ X1 )
      | ( l1_waybel_0 @ X3 @ X1 )
      | ~ ( m2_yellow_6 @ X3 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( l1_waybel_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( l1_waybel_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','35','36','37'])).

thf('39',plain,
    ( ( l1_waybel_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m2_yellow_6 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('41',plain,
    ( ( v7_waybel_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['29'])).

thf('42',plain,
    ( ( v4_orders_2 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['20'])).

thf('43',plain,
    ( ( l1_waybel_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['38'])).

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

thf('44',plain,(
    ! [X4: $i,X5: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( v4_orders_2 @ X4 )
      | ~ ( v7_waybel_0 @ X4 )
      | ~ ( l1_waybel_0 @ X4 @ X5 )
      | ( r3_waybel_9 @ X5 @ X4 @ ( sk_C @ X4 @ X5 ) )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v1_compts_1 @ X5 )
      | ~ ( v8_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t30_waybel_9])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v1_compts_1 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r3_waybel_9 @ sk_A @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_C @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) )
    | ~ ( v7_waybel_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_C @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) )
    | ~ ( v7_waybel_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46','47','48','49'])).

thf('51',plain,
    ( ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( v7_waybel_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( r3_waybel_9 @ sk_A @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_C @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( r3_waybel_9 @ sk_A @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_C @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) )
    | ~ ( v7_waybel_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','51'])).

thf('53',plain,
    ( ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( v7_waybel_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( r3_waybel_9 @ sk_A @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_C @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( r3_waybel_9 @ sk_A @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_C @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) )
    | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','53'])).

thf('55',plain,
    ( ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( r3_waybel_9 @ sk_A @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_C @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( v7_waybel_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['29'])).

thf('57',plain,
    ( ( v4_orders_2 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['20'])).

thf('58',plain,
    ( ( l1_waybel_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['38'])).

thf('59',plain,(
    ! [X4: $i,X5: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( v4_orders_2 @ X4 )
      | ~ ( v7_waybel_0 @ X4 )
      | ~ ( l1_waybel_0 @ X4 @ X5 )
      | ( m1_subset_1 @ ( sk_C @ X4 @ X5 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v1_compts_1 @ X5 )
      | ~ ( v8_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t30_waybel_9])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v1_compts_1 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v7_waybel_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v7_waybel_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','61','62','63','64'])).

thf('66',plain,
    ( ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( v7_waybel_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_C @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v7_waybel_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','66'])).

thf('68',plain,
    ( ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( v7_waybel_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_C @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','68'])).

thf('70',plain,
    ( ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['69'])).

thf(t31_waybel_9,axiom,(
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
              ( ( m2_yellow_6 @ C @ A @ B )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( r3_waybel_9 @ A @ C @ D )
                   => ( r3_waybel_9 @ A @ B @ D ) ) ) ) ) ) )).

thf('71',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( v4_orders_2 @ X6 )
      | ~ ( v7_waybel_0 @ X6 )
      | ~ ( l1_waybel_0 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( r3_waybel_9 @ X7 @ X6 @ X8 )
      | ~ ( r3_waybel_9 @ X7 @ X9 @ X8 )
      | ~ ( m2_yellow_6 @ X9 @ X7 @ X6 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t31_waybel_9])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m2_yellow_6 @ X1 @ sk_A @ X0 )
      | ~ ( r3_waybel_9 @ sk_A @ X1 @ ( sk_C @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m2_yellow_6 @ X1 @ sk_A @ X0 )
      | ~ ( r3_waybel_9 @ sk_A @ X1 @ ( sk_C @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ X1 @ ( sk_C @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( m2_yellow_6 @ X1 @ sk_A @ X0 )
      | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
      | ~ ( m2_yellow_6 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A @ X0 )
      | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( m2_yellow_6 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A @ X0 )
      | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['40','78'])).

thf('80',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('84',plain,
    ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) )
    | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['69'])).

thf('86',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ sk_A ) )
      | ( X18 = X17 )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X17 )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ sk_C_1 )
      | ( X0 = sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    r3_waybel_9 @ sk_A @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ( X0 = sk_C_1 ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( ( sk_C @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A )
      = sk_C_1 )
    | ~ ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','90'])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( ( sk_C @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A )
      = sk_C_1 )
    | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['84','91'])).

thf('93',plain,
    ( ( ( sk_C @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A )
      = sk_C_1 )
    | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,
    ( ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( r3_waybel_9 @ sk_A @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_C @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['54'])).

thf('95',plain,
    ( ( r3_waybel_9 @ sk_A @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t32_waybel_9,axiom,(
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
             => ~ ( ( r3_waybel_9 @ A @ B @ C )
                  & ! [D: $i] :
                      ( ( m2_yellow_6 @ D @ A @ B )
                     => ~ ( r2_hidden @ C @ ( k10_yellow_6 @ A @ D ) ) ) ) ) ) ) )).

thf('98',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v4_orders_2 @ X10 )
      | ~ ( v7_waybel_0 @ X10 )
      | ~ ( l1_waybel_0 @ X10 @ X11 )
      | ( r2_hidden @ X12 @ ( k10_yellow_6 @ X11 @ ( sk_D @ X12 @ X10 @ X11 ) ) )
      | ~ ( r3_waybel_9 @ X11 @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t32_waybel_9])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ sk_C_1 )
      | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( sk_D @ sk_C_1 @ X0 @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ sk_C_1 )
      | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( sk_D @ sk_C_1 @ X0 @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( v7_waybel_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( l1_waybel_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( sk_D @ sk_C_1 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['96','102'])).

thf('104',plain,
    ( ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( sk_D @ sk_C_1 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) ) )
    | ~ ( l1_waybel_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A )
    | ~ ( v7_waybel_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( v7_waybel_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( sk_D @ sk_C_1 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','104'])).

thf('106',plain,
    ( ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( sk_D @ sk_C_1 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) ) )
    | ~ ( v7_waybel_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( sk_D @ sk_C_1 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','106'])).

thf('108',plain,
    ( ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( sk_D @ sk_C_1 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) ) )
    | ~ ( v4_orders_2 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( sk_D @ sk_C_1 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','108'])).

thf('110',plain,
    ( ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( sk_D @ sk_C_1 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) ) )
    | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,
    ( ( v4_orders_2 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['20'])).

thf('112',plain,
    ( ( v7_waybel_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['29'])).

thf('113',plain,
    ( ( l1_waybel_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['38'])).

thf('114',plain,
    ( ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['95'])).

thf('115',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v4_orders_2 @ X10 )
      | ~ ( v7_waybel_0 @ X10 )
      | ~ ( l1_waybel_0 @ X10 @ X11 )
      | ( m2_yellow_6 @ ( sk_D @ X12 @ X10 @ X11 ) @ X11 @ X10 )
      | ~ ( r3_waybel_9 @ X11 @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t32_waybel_9])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ sk_C_1 )
      | ( m2_yellow_6 @ ( sk_D @ sk_C_1 @ X0 @ sk_A ) @ sk_A @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ sk_C_1 )
      | ( m2_yellow_6 @ ( sk_D @ sk_C_1 @ X0 @ sk_A ) @ sk_A @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( v7_waybel_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( l1_waybel_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A )
    | ( m2_yellow_6 @ ( sk_D @ sk_C_1 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) @ sk_A @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['114','120'])).

thf('122',plain,
    ( ( m2_yellow_6 @ ( sk_D @ sk_C_1 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) @ sk_A @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( l1_waybel_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A )
    | ~ ( v7_waybel_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( v7_waybel_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( m2_yellow_6 @ ( sk_D @ sk_C_1 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) @ sk_A @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['113','122'])).

thf('124',plain,
    ( ( m2_yellow_6 @ ( sk_D @ sk_C_1 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) @ sk_A @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( v7_waybel_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( m2_yellow_6 @ ( sk_D @ sk_C_1 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) @ sk_A @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['112','124'])).

thf('126',plain,
    ( ( m2_yellow_6 @ ( sk_D @ sk_C_1 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) @ sk_A @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( m2_yellow_6 @ ( sk_D @ sk_C_1 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) @ sk_A @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['111','126'])).

thf('128',plain,
    ( ( m2_yellow_6 @ ( sk_D @ sk_C_1 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) @ sk_A @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v7_waybel_0 @ X13 )
      | ~ ( l1_waybel_0 @ X13 @ X14 )
      | ~ ( m2_yellow_6 @ X15 @ X14 @ ( sk_D_1 @ X16 @ X13 @ X14 ) )
      | ~ ( r2_hidden @ X16 @ ( k10_yellow_6 @ X14 @ X15 ) )
      | ( r2_hidden @ X16 @ ( k10_yellow_6 @ X14 @ X13 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t46_yellow_6])).

thf('130',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( sk_D @ sk_C_1 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( sk_D @ sk_C_1 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['130','131','132','133','134','135','136'])).

thf('138',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( sk_D @ sk_C_1 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) ) )
    | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['110','138'])).

thf('140',plain,
    ( ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m2_yellow_6 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('142',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X2 )
      | ~ ( v4_orders_2 @ X2 )
      | ~ ( v7_waybel_0 @ X2 )
      | ~ ( l1_waybel_0 @ X2 @ X1 )
      | ~ ( v2_struct_0 @ X3 )
      | ~ ( m2_yellow_6 @ X3 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('143',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('148',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['143','144','145','146','147'])).

thf('149',plain,
    ( ~ ( v2_struct_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['140','149'])).

thf('151',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['151','152'])).

thf('154',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['153','154'])).

thf('156',plain,(
    $false ),
    inference(demod,[status(thm)],['0','155'])).


%------------------------------------------------------------------------------
