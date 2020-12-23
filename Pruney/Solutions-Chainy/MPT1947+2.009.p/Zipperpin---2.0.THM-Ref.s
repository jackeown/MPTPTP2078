%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BSvZdrpADq

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 173 expanded)
%              Number of leaves         :   28 (  65 expanded)
%              Depth                    :   12
%              Number of atoms          :  736 (2639 expanded)
%              Number of equality atoms :   14 (  84 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_yellow_6_type,type,(
    v3_yellow_6: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_yellow_6_type,type,(
    k4_yellow_6: $i > $i > $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_yellow_6_type,type,(
    v1_yellow_6: $i > $i > $o )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(k11_yellow_6_type,type,(
    k11_yellow_6: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(t45_yellow_6,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v8_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( v1_yellow_6 @ B @ A )
            & ( l1_waybel_0 @ B @ A ) )
         => ( ( k11_yellow_6 @ A @ B )
            = ( k4_yellow_6 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v8_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v4_orders_2 @ B )
              & ( v7_waybel_0 @ B )
              & ( v1_yellow_6 @ B @ A )
              & ( l1_waybel_0 @ B @ A ) )
           => ( ( k11_yellow_6 @ A @ B )
              = ( k4_yellow_6 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t45_yellow_6])).

thf('0',plain,(
    v1_yellow_6 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t42_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( v1_yellow_6 @ B @ A )
            & ( l1_waybel_0 @ B @ A ) )
         => ( r2_hidden @ ( k4_yellow_6 @ A @ B ) @ ( k10_yellow_6 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v7_waybel_0 @ X13 )
      | ~ ( v1_yellow_6 @ X13 @ X14 )
      | ~ ( l1_waybel_0 @ X13 @ X14 )
      | ( r2_hidden @ ( k4_yellow_6 @ X14 @ X13 ) @ ( k10_yellow_6 @ X14 @ X13 ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_6])).

thf('2',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B_1 )
    | ~ ( v4_orders_2 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v7_waybel_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v4_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['2','3','4','5','6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['10','11'])).

thf(d20_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v8_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( v3_yellow_6 @ B @ A )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( C
                  = ( k11_yellow_6 @ A @ B ) )
              <=> ( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( v4_orders_2 @ X7 )
      | ~ ( v7_waybel_0 @ X7 )
      | ~ ( v3_yellow_6 @ X7 @ X8 )
      | ~ ( l1_waybel_0 @ X7 @ X8 )
      | ~ ( r2_hidden @ X9 @ ( k10_yellow_6 @ X8 @ X7 ) )
      | ( X9
        = ( k11_yellow_6 @ X8 @ X7 ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v8_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d20_yellow_6])).

thf('14',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_subset_1 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k4_yellow_6 @ sk_A @ sk_B_1 )
      = ( k11_yellow_6 @ sk_A @ sk_B_1 ) )
    | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
    | ~ ( v3_yellow_6 @ sk_B_1 @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B_1 )
    | ~ ( v4_orders_2 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ( ( ~ ( v2_struct_0 @ B )
              & ( v4_orders_2 @ B )
              & ( v7_waybel_0 @ B )
              & ( v1_yellow_6 @ B @ A ) )
           => ( ~ ( v2_struct_0 @ B )
              & ( v4_orders_2 @ B )
              & ( v7_waybel_0 @ B )
              & ( v3_yellow_6 @ B @ A ) ) ) ) ) )).

thf('20',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_waybel_0 @ X5 @ X6 )
      | ( v3_yellow_6 @ X5 @ X6 )
      | ~ ( v1_yellow_6 @ X5 @ X6 )
      | ~ ( v7_waybel_0 @ X5 )
      | ~ ( v4_orders_2 @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc4_yellow_6])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( v4_orders_2 @ sk_B_1 )
    | ~ ( v7_waybel_0 @ sk_B_1 )
    | ~ ( v1_yellow_6 @ sk_B_1 @ sk_A )
    | ( v3_yellow_6 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v4_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v7_waybel_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_yellow_6 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v3_yellow_6 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['21','22','23','24','25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v3_yellow_6 @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v3_yellow_6 @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    v7_waybel_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v4_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k4_yellow_6 @ sk_A @ sk_B_1 )
      = ( k11_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['14','15','16','17','18','31','32','33'])).

thf('35',plain,(
    ( k11_yellow_6 @ sk_A @ sk_B_1 )
 != ( k4_yellow_6 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ~ ( m1_subset_1 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ~ ( m1_subset_1 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('42',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(dt_k2_waybel_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ~ ( v2_struct_0 @ B )
        & ( l1_waybel_0 @ B @ A )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) )
     => ( m1_subset_1 @ ( k2_waybel_0 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ) )).

thf('43',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( l1_waybel_0 @ X2 @ X3 )
      | ( v2_struct_0 @ X2 )
      | ~ ( l1_struct_0 @ X3 )
      | ( v2_struct_0 @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X2 ) )
      | ( m1_subset_1 @ ( k2_waybel_0 @ X3 @ X2 @ X4 ) @ ( u1_struct_0 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_waybel_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k2_waybel_0 @ X1 @ X0 @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X1 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('47',plain,(
    ! [X1: $i] :
      ( ( l1_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('48',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( m1_subset_1 @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t25_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( v1_yellow_6 @ B @ A )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ( ( k2_waybel_0 @ A @ B @ C )
                = ( k4_yellow_6 @ A @ B ) ) ) ) ) )).

thf('56',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v4_orders_2 @ X10 )
      | ~ ( v7_waybel_0 @ X10 )
      | ~ ( v1_yellow_6 @ X10 @ X11 )
      | ~ ( l1_waybel_0 @ X10 @ X11 )
      | ( ( k2_waybel_0 @ X11 @ X10 @ X12 )
        = ( k4_yellow_6 @ X11 @ X10 ) )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t25_yellow_6])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( ( k2_waybel_0 @ X1 @ X0 @ ( sk_B @ ( u1_struct_0 @ X0 ) ) )
        = ( k4_yellow_6 @ X1 @ X0 ) )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ~ ( v1_yellow_6 @ X0 @ X1 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ~ ( v4_orders_2 @ sk_B_1 )
    | ~ ( v7_waybel_0 @ sk_B_1 )
    | ~ ( v1_yellow_6 @ sk_B_1 @ sk_A )
    | ( ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) )
      = ( k4_yellow_6 @ sk_A @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    v4_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v7_waybel_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_yellow_6 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['46','47'])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) )
      = ( k4_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['58','59','60','61','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) )
      = ( k4_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) )
    = ( k4_yellow_6 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','67'])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['40','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BSvZdrpADq
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:03:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 31 iterations in 0.022s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.48  thf(v3_yellow_6_type, type, v3_yellow_6: $i > $i > $o).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(k4_yellow_6_type, type, k4_yellow_6: $i > $i > $i).
% 0.21/0.48  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(v1_yellow_6_type, type, v1_yellow_6: $i > $i > $o).
% 0.21/0.48  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.21/0.48  thf(k11_yellow_6_type, type, k11_yellow_6: $i > $i > $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.48  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.21/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.48  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.48  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 0.21/0.48  thf(k10_yellow_6_type, type, k10_yellow_6: $i > $i > $i).
% 0.21/0.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.48  thf(t45_yellow_6, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.48         ( v8_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.48             ( v7_waybel_0 @ B ) & ( v1_yellow_6 @ B @ A ) & 
% 0.21/0.48             ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.48           ( ( k11_yellow_6 @ A @ B ) = ( k4_yellow_6 @ A @ B ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.48            ( v8_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.48          ( ![B:$i]:
% 0.21/0.48            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.48                ( v7_waybel_0 @ B ) & ( v1_yellow_6 @ B @ A ) & 
% 0.21/0.48                ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.48              ( ( k11_yellow_6 @ A @ B ) = ( k4_yellow_6 @ A @ B ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t45_yellow_6])).
% 0.21/0.48  thf('0', plain, ((v1_yellow_6 @ sk_B_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t42_yellow_6, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.48             ( v7_waybel_0 @ B ) & ( v1_yellow_6 @ B @ A ) & 
% 0.21/0.48             ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.48           ( r2_hidden @ ( k4_yellow_6 @ A @ B ) @ ( k10_yellow_6 @ A @ B ) ) ) ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X13 : $i, X14 : $i]:
% 0.21/0.48         ((v2_struct_0 @ X13)
% 0.21/0.48          | ~ (v4_orders_2 @ X13)
% 0.21/0.48          | ~ (v7_waybel_0 @ X13)
% 0.21/0.48          | ~ (v1_yellow_6 @ X13 @ X14)
% 0.21/0.48          | ~ (l1_waybel_0 @ X13 @ X14)
% 0.21/0.48          | (r2_hidden @ (k4_yellow_6 @ X14 @ X13) @ (k10_yellow_6 @ X14 @ X13))
% 0.21/0.48          | ~ (l1_pre_topc @ X14)
% 0.21/0.48          | ~ (v2_pre_topc @ X14)
% 0.21/0.48          | (v2_struct_0 @ X14))),
% 0.21/0.48      inference('cnf', [status(esa)], [t42_yellow_6])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_A)
% 0.21/0.48        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.48        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.21/0.48           (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.48        | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.21/0.48        | ~ (v7_waybel_0 @ sk_B_1)
% 0.21/0.48        | ~ (v4_orders_2 @ sk_B_1)
% 0.21/0.48        | (v2_struct_0 @ sk_B_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.48  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('5', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('6', plain, ((v7_waybel_0 @ sk_B_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('7', plain, ((v4_orders_2 @ sk_B_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_A)
% 0.21/0.48        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.21/0.48           (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.48        | (v2_struct_0 @ sk_B_1))),
% 0.21/0.48      inference('demod', [status(thm)], ['2', '3', '4', '5', '6', '7'])).
% 0.21/0.48  thf('9', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_B_1)
% 0.21/0.48        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.21/0.48           (k10_yellow_6 @ sk_A @ sk_B_1)))),
% 0.21/0.48      inference('clc', [status(thm)], ['8', '9'])).
% 0.21/0.48  thf('11', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      ((r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.21/0.48        (k10_yellow_6 @ sk_A @ sk_B_1))),
% 0.21/0.48      inference('clc', [status(thm)], ['10', '11'])).
% 0.21/0.48  thf(d20_yellow_6, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.48         ( v8_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.48             ( v7_waybel_0 @ B ) & ( v3_yellow_6 @ B @ A ) & 
% 0.21/0.48             ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.48           ( ![C:$i]:
% 0.21/0.48             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.48               ( ( ( C ) = ( k11_yellow_6 @ A @ B ) ) <=>
% 0.21/0.48                 ( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) ) ) ) ) ) ) ))).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.48         ((v2_struct_0 @ X7)
% 0.21/0.48          | ~ (v4_orders_2 @ X7)
% 0.21/0.48          | ~ (v7_waybel_0 @ X7)
% 0.21/0.48          | ~ (v3_yellow_6 @ X7 @ X8)
% 0.21/0.48          | ~ (l1_waybel_0 @ X7 @ X8)
% 0.21/0.48          | ~ (r2_hidden @ X9 @ (k10_yellow_6 @ X8 @ X7))
% 0.21/0.48          | ((X9) = (k11_yellow_6 @ X8 @ X7))
% 0.21/0.48          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.21/0.48          | ~ (l1_pre_topc @ X8)
% 0.21/0.48          | ~ (v8_pre_topc @ X8)
% 0.21/0.48          | ~ (v2_pre_topc @ X8)
% 0.21/0.48          | (v2_struct_0 @ X8))),
% 0.21/0.48      inference('cnf', [status(esa)], [d20_yellow_6])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_A)
% 0.21/0.48        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.48        | ~ (v8_pre_topc @ sk_A)
% 0.21/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.48        | ~ (m1_subset_1 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.21/0.48        | ((k4_yellow_6 @ sk_A @ sk_B_1) = (k11_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.48        | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.21/0.48        | ~ (v3_yellow_6 @ sk_B_1 @ sk_A)
% 0.21/0.48        | ~ (v7_waybel_0 @ sk_B_1)
% 0.21/0.48        | ~ (v4_orders_2 @ sk_B_1)
% 0.21/0.48        | (v2_struct_0 @ sk_B_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.48  thf('15', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('16', plain, ((v8_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('18', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('19', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(cc4_yellow_6, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( l1_waybel_0 @ B @ A ) =>
% 0.21/0.48           ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.48               ( v7_waybel_0 @ B ) & ( v1_yellow_6 @ B @ A ) ) =>
% 0.21/0.48             ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.48               ( v7_waybel_0 @ B ) & ( v3_yellow_6 @ B @ A ) ) ) ) ) ))).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (![X5 : $i, X6 : $i]:
% 0.21/0.48         (~ (l1_waybel_0 @ X5 @ X6)
% 0.21/0.48          | (v3_yellow_6 @ X5 @ X6)
% 0.21/0.48          | ~ (v1_yellow_6 @ X5 @ X6)
% 0.21/0.48          | ~ (v7_waybel_0 @ X5)
% 0.21/0.48          | ~ (v4_orders_2 @ X5)
% 0.21/0.48          | (v2_struct_0 @ X5)
% 0.21/0.48          | ~ (l1_pre_topc @ X6)
% 0.21/0.48          | ~ (v2_pre_topc @ X6)
% 0.21/0.48          | (v2_struct_0 @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [cc4_yellow_6])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_A)
% 0.21/0.48        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.48        | (v2_struct_0 @ sk_B_1)
% 0.21/0.48        | ~ (v4_orders_2 @ sk_B_1)
% 0.21/0.48        | ~ (v7_waybel_0 @ sk_B_1)
% 0.21/0.48        | ~ (v1_yellow_6 @ sk_B_1 @ sk_A)
% 0.21/0.48        | (v3_yellow_6 @ sk_B_1 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.48  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('24', plain, ((v4_orders_2 @ sk_B_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('25', plain, ((v7_waybel_0 @ sk_B_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('26', plain, ((v1_yellow_6 @ sk_B_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_A)
% 0.21/0.48        | (v2_struct_0 @ sk_B_1)
% 0.21/0.48        | (v3_yellow_6 @ sk_B_1 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['21', '22', '23', '24', '25', '26'])).
% 0.21/0.48  thf('28', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('29', plain, (((v3_yellow_6 @ sk_B_1 @ sk_A) | (v2_struct_0 @ sk_B_1))),
% 0.21/0.48      inference('clc', [status(thm)], ['27', '28'])).
% 0.21/0.48  thf('30', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('31', plain, ((v3_yellow_6 @ sk_B_1 @ sk_A)),
% 0.21/0.48      inference('clc', [status(thm)], ['29', '30'])).
% 0.21/0.48  thf('32', plain, ((v7_waybel_0 @ sk_B_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('33', plain, ((v4_orders_2 @ sk_B_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('34', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_A)
% 0.21/0.48        | ~ (m1_subset_1 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.21/0.48        | ((k4_yellow_6 @ sk_A @ sk_B_1) = (k11_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.48        | (v2_struct_0 @ sk_B_1))),
% 0.21/0.48      inference('demod', [status(thm)],
% 0.21/0.48                ['14', '15', '16', '17', '18', '31', '32', '33'])).
% 0.21/0.48  thf('35', plain,
% 0.21/0.48      (((k11_yellow_6 @ sk_A @ sk_B_1) != (k4_yellow_6 @ sk_A @ sk_B_1))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('36', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_A)
% 0.21/0.48        | ~ (m1_subset_1 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.21/0.48        | (v2_struct_0 @ sk_B_1))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['34', '35'])).
% 0.21/0.48  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('38', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_B_1)
% 0.21/0.48        | ~ (m1_subset_1 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('clc', [status(thm)], ['36', '37'])).
% 0.21/0.48  thf('39', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('40', plain,
% 0.21/0.48      (~ (m1_subset_1 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.21/0.48      inference('clc', [status(thm)], ['38', '39'])).
% 0.21/0.48  thf('41', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(existence_m1_subset_1, axiom,
% 0.21/0.48    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.21/0.48  thf('42', plain, (![X0 : $i]: (m1_subset_1 @ (sk_B @ X0) @ X0)),
% 0.21/0.48      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.21/0.48  thf(dt_k2_waybel_0, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.21/0.48         ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) & 
% 0.21/0.48         ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.48       ( m1_subset_1 @ ( k2_waybel_0 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ))).
% 0.21/0.48  thf('43', plain,
% 0.21/0.48      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.48         (~ (l1_waybel_0 @ X2 @ X3)
% 0.21/0.48          | (v2_struct_0 @ X2)
% 0.21/0.48          | ~ (l1_struct_0 @ X3)
% 0.21/0.48          | (v2_struct_0 @ X3)
% 0.21/0.48          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X2))
% 0.21/0.48          | (m1_subset_1 @ (k2_waybel_0 @ X3 @ X2 @ X4) @ (u1_struct_0 @ X3)))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k2_waybel_0])).
% 0.21/0.48  thf('44', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((m1_subset_1 @ 
% 0.21/0.48           (k2_waybel_0 @ X1 @ X0 @ (sk_B @ (u1_struct_0 @ X0))) @ 
% 0.21/0.48           (u1_struct_0 @ X1))
% 0.21/0.48          | (v2_struct_0 @ X1)
% 0.21/0.48          | ~ (l1_struct_0 @ X1)
% 0.21/0.48          | (v2_struct_0 @ X0)
% 0.21/0.48          | ~ (l1_waybel_0 @ X0 @ X1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.48  thf('45', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_B_1)
% 0.21/0.48        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.48        | (v2_struct_0 @ sk_A)
% 0.21/0.48        | (m1_subset_1 @ 
% 0.21/0.48           (k2_waybel_0 @ sk_A @ sk_B_1 @ (sk_B @ (u1_struct_0 @ sk_B_1))) @ 
% 0.21/0.48           (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['41', '44'])).
% 0.21/0.48  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(dt_l1_pre_topc, axiom,
% 0.21/0.48    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.48  thf('47', plain, (![X1 : $i]: ((l1_struct_0 @ X1) | ~ (l1_pre_topc @ X1))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.48  thf('48', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.48      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.48  thf('49', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_B_1)
% 0.21/0.48        | (v2_struct_0 @ sk_A)
% 0.21/0.48        | (m1_subset_1 @ 
% 0.21/0.48           (k2_waybel_0 @ sk_A @ sk_B_1 @ (sk_B @ (u1_struct_0 @ sk_B_1))) @ 
% 0.21/0.48           (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('demod', [status(thm)], ['45', '48'])).
% 0.21/0.48  thf('50', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('51', plain,
% 0.21/0.48      (((m1_subset_1 @ 
% 0.21/0.48         (k2_waybel_0 @ sk_A @ sk_B_1 @ (sk_B @ (u1_struct_0 @ sk_B_1))) @ 
% 0.21/0.48         (u1_struct_0 @ sk_A))
% 0.21/0.48        | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('clc', [status(thm)], ['49', '50'])).
% 0.21/0.48  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('53', plain,
% 0.21/0.48      ((m1_subset_1 @ 
% 0.21/0.48        (k2_waybel_0 @ sk_A @ sk_B_1 @ (sk_B @ (u1_struct_0 @ sk_B_1))) @ 
% 0.21/0.48        (u1_struct_0 @ sk_A))),
% 0.21/0.48      inference('clc', [status(thm)], ['51', '52'])).
% 0.21/0.48  thf('54', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('55', plain, (![X0 : $i]: (m1_subset_1 @ (sk_B @ X0) @ X0)),
% 0.21/0.48      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.21/0.48  thf(t25_yellow_6, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.48             ( v7_waybel_0 @ B ) & ( v1_yellow_6 @ B @ A ) & 
% 0.21/0.48             ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.48           ( ![C:$i]:
% 0.21/0.48             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.48               ( ( k2_waybel_0 @ A @ B @ C ) = ( k4_yellow_6 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.48  thf('56', plain,
% 0.21/0.48      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.48         ((v2_struct_0 @ X10)
% 0.21/0.48          | ~ (v4_orders_2 @ X10)
% 0.21/0.48          | ~ (v7_waybel_0 @ X10)
% 0.21/0.48          | ~ (v1_yellow_6 @ X10 @ X11)
% 0.21/0.48          | ~ (l1_waybel_0 @ X10 @ X11)
% 0.21/0.48          | ((k2_waybel_0 @ X11 @ X10 @ X12) = (k4_yellow_6 @ X11 @ X10))
% 0.21/0.48          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X10))
% 0.21/0.48          | ~ (l1_struct_0 @ X11)
% 0.21/0.48          | (v2_struct_0 @ X11))),
% 0.21/0.48      inference('cnf', [status(esa)], [t25_yellow_6])).
% 0.21/0.48  thf('57', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((v2_struct_0 @ X1)
% 0.21/0.48          | ~ (l1_struct_0 @ X1)
% 0.21/0.48          | ((k2_waybel_0 @ X1 @ X0 @ (sk_B @ (u1_struct_0 @ X0)))
% 0.21/0.48              = (k4_yellow_6 @ X1 @ X0))
% 0.21/0.48          | ~ (l1_waybel_0 @ X0 @ X1)
% 0.21/0.48          | ~ (v1_yellow_6 @ X0 @ X1)
% 0.21/0.48          | ~ (v7_waybel_0 @ X0)
% 0.21/0.48          | ~ (v4_orders_2 @ X0)
% 0.21/0.48          | (v2_struct_0 @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.48  thf('58', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_B_1)
% 0.21/0.48        | ~ (v4_orders_2 @ sk_B_1)
% 0.21/0.48        | ~ (v7_waybel_0 @ sk_B_1)
% 0.21/0.48        | ~ (v1_yellow_6 @ sk_B_1 @ sk_A)
% 0.21/0.48        | ((k2_waybel_0 @ sk_A @ sk_B_1 @ (sk_B @ (u1_struct_0 @ sk_B_1)))
% 0.21/0.48            = (k4_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.48        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.48        | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['54', '57'])).
% 0.21/0.48  thf('59', plain, ((v4_orders_2 @ sk_B_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('60', plain, ((v7_waybel_0 @ sk_B_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('61', plain, ((v1_yellow_6 @ sk_B_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('62', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.48      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.48  thf('63', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_B_1)
% 0.21/0.48        | ((k2_waybel_0 @ sk_A @ sk_B_1 @ (sk_B @ (u1_struct_0 @ sk_B_1)))
% 0.21/0.48            = (k4_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.48        | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['58', '59', '60', '61', '62'])).
% 0.21/0.48  thf('64', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('65', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_A)
% 0.21/0.48        | ((k2_waybel_0 @ sk_A @ sk_B_1 @ (sk_B @ (u1_struct_0 @ sk_B_1)))
% 0.21/0.48            = (k4_yellow_6 @ sk_A @ sk_B_1)))),
% 0.21/0.48      inference('clc', [status(thm)], ['63', '64'])).
% 0.21/0.48  thf('66', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('67', plain,
% 0.21/0.48      (((k2_waybel_0 @ sk_A @ sk_B_1 @ (sk_B @ (u1_struct_0 @ sk_B_1)))
% 0.21/0.48         = (k4_yellow_6 @ sk_A @ sk_B_1))),
% 0.21/0.48      inference('clc', [status(thm)], ['65', '66'])).
% 0.21/0.48  thf('68', plain,
% 0.21/0.48      ((m1_subset_1 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['53', '67'])).
% 0.21/0.48  thf('69', plain, ($false), inference('demod', [status(thm)], ['40', '68'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
