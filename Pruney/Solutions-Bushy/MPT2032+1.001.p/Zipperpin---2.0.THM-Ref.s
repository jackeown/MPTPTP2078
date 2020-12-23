%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT2032+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aVrvNnR04K

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:41 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 172 expanded)
%              Number of leaves         :   23 (  61 expanded)
%              Depth                    :   18
%              Number of atoms          :  833 (2967 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m2_yellow_6_type,type,(
    m2_yellow_6: $i > $i > $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r3_waybel_9_type,type,(
    r3_waybel_9: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r2_waybel_0_type,type,(
    r2_waybel_0: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(t31_waybel_9,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
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
                     => ( r3_waybel_9 @ A @ B @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_waybel_9])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r3_waybel_9 @ sk_A @ sk_C @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_waybel_9,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r3_waybel_9 @ A @ B @ C )
              <=> ! [D: $i] :
                    ( ( m1_connsp_2 @ D @ A @ C )
                   => ( r2_waybel_0 @ A @ B @ D ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( m1_connsp_2 @ ( sk_D @ X2 @ X0 @ X1 ) @ X1 @ X2 )
      | ( r3_waybel_9 @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d9_waybel_9])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r3_waybel_9 @ sk_A @ X0 @ sk_D_1 )
      | ( m1_connsp_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) @ sk_A @ sk_D_1 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r3_waybel_9 @ sk_A @ X0 @ sk_D_1 )
      | ( m1_connsp_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_A ) @ sk_A @ sk_D_1 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_connsp_2 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) @ sk_A @ sk_D_1 )
    | ( r3_waybel_9 @ sk_A @ sk_B @ sk_D_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ~ ( r3_waybel_9 @ X1 @ X0 @ X2 )
      | ( r2_waybel_0 @ X1 @ X0 @ X3 )
      | ~ ( m1_connsp_2 @ X3 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d9_waybel_9])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_D_1 )
      | ( r2_waybel_0 @ sk_A @ X1 @ X0 )
      | ~ ( r3_waybel_9 @ sk_A @ X1 @ sk_D_1 )
      | ~ ( l1_waybel_0 @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_D_1 )
      | ( r2_waybel_0 @ sk_A @ X1 @ X0 )
      | ~ ( r3_waybel_9 @ sk_A @ X1 @ sk_D_1 )
      | ~ ( l1_waybel_0 @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r3_waybel_9 @ sk_A @ sk_B @ sk_D_1 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ sk_D_1 )
      | ( r2_waybel_0 @ sk_A @ X0 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_waybel_0 @ sk_A @ X0 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ sk_D_1 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( r3_waybel_9 @ sk_A @ sk_B @ sk_D_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ sk_D_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_waybel_0 @ sk_C @ sk_A )
    | ( r2_waybel_0 @ sk_A @ sk_C @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','17'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('19',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('20',plain,(
    m2_yellow_6 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('21',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 )
      | ( v2_struct_0 @ X6 )
      | ~ ( v4_orders_2 @ X6 )
      | ~ ( v7_waybel_0 @ X6 )
      | ~ ( l1_waybel_0 @ X6 @ X5 )
      | ( l1_waybel_0 @ X7 @ X5 )
      | ~ ( m2_yellow_6 @ X7 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('22',plain,
    ( ( l1_waybel_0 @ sk_C @ sk_A )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( l1_waybel_0 @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23','24','25'])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( l1_waybel_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['19','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( l1_waybel_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( l1_waybel_0 @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ sk_D_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( r2_waybel_0 @ sk_A @ sk_C @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','33'])).

thf('35',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('36',plain,(
    m2_yellow_6 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t27_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m2_yellow_6 @ C @ A @ B )
             => ! [D: $i] :
                  ( ( r2_waybel_0 @ A @ C @ D )
                 => ( r2_waybel_0 @ A @ B @ D ) ) ) ) ) )).

thf('37',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v4_orders_2 @ X8 )
      | ~ ( v7_waybel_0 @ X8 )
      | ~ ( l1_waybel_0 @ X8 @ X9 )
      | ~ ( r2_waybel_0 @ X9 @ X10 @ X11 )
      | ( r2_waybel_0 @ X9 @ X8 @ X11 )
      | ~ ( m2_yellow_6 @ X10 @ X9 @ X8 )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t27_yellow_6])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_waybel_0 @ sk_A @ sk_C @ X0 )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_waybel_0 @ sk_A @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','39','40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( r2_waybel_0 @ sk_A @ sk_C @ X0 )
      | ( r2_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( r2_waybel_0 @ sk_A @ sk_C @ X0 )
      | ( r2_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( r3_waybel_9 @ sk_A @ sk_B @ sk_D_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r2_waybel_0 @ sk_A @ sk_B @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['34','45'])).

thf('47',plain,
    ( ( r2_waybel_0 @ sk_A @ sk_B @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ sk_D_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ~ ( r2_waybel_0 @ X1 @ X0 @ ( sk_D @ X2 @ X0 @ X1 ) )
      | ( r3_waybel_9 @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d9_waybel_9])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( r3_waybel_9 @ sk_A @ sk_B @ sk_D_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r3_waybel_9 @ sk_A @ sk_B @ sk_D_1 )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( r3_waybel_9 @ sk_A @ sk_B @ sk_D_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['49','50','51','52','53'])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ sk_D_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ~ ( r3_waybel_9 @ sk_A @ sk_B @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('59',plain,(
    m2_yellow_6 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 )
      | ( v2_struct_0 @ X6 )
      | ~ ( v4_orders_2 @ X6 )
      | ~ ( v7_waybel_0 @ X6 )
      | ~ ( l1_waybel_0 @ X6 @ X5 )
      | ~ ( v2_struct_0 @ X7 )
      | ~ ( m2_yellow_6 @ X7 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('61',plain,
    ( ~ ( v2_struct_0 @ sk_C )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ~ ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','63','64'])).

thf('66',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['58','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ~ ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['57','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v2_struct_0 @ sk_B ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,(
    $false ),
    inference(demod,[status(thm)],['0','75'])).


%------------------------------------------------------------------------------
