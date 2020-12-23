%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2k73rAznRy

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:56 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 274 expanded)
%              Number of leaves         :   24 (  89 expanded)
%              Depth                    :   20
%              Number of atoms          : 1160 (4129 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   22 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_waybel_0_type,type,(
    r2_waybel_0: $i > $i > $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t28_yellow_6,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( r1_waybel_0 @ A @ B @ C )
             => ( r2_waybel_0 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_struct_0 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v4_orders_2 @ B )
              & ( v7_waybel_0 @ B )
              & ( l1_waybel_0 @ B @ A ) )
           => ! [C: $i] :
                ( ( r1_waybel_0 @ A @ B @ C )
               => ( r2_waybel_0 @ A @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_yellow_6])).

thf('0',plain,(
    ~ ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d12_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( r2_waybel_0 @ A @ B @ C )
            <=> ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) )
                 => ? [E: $i] :
                      ( ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C )
                      & ( r1_orders_2 @ B @ D @ E )
                      & ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( l1_waybel_0 @ X6 @ X7 )
      | ( m1_subset_1 @ ( sk_D_1 @ X8 @ X6 @ X7 ) @ ( u1_struct_0 @ X6 ) )
      | ( r2_waybel_0 @ X7 @ X6 @ X8 )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d11_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( r1_waybel_0 @ A @ B @ C )
            <=> ? [D: $i] :
                  ( ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                     => ( ( r1_orders_2 @ B @ D @ E )
                       => ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) ) )
                  & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i,X4: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ~ ( r1_waybel_0 @ X1 @ X0 @ X4 )
      | ( m1_subset_1 @ ( sk_D @ X4 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d11_waybel_0])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['13','14'])).

thf(d5_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( v7_waybel_0 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ? [D: $i] :
                    ( ( r1_orders_2 @ A @ C @ D )
                    & ( r1_orders_2 @ A @ B @ D )
                    & ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ~ ( v7_waybel_0 @ X14 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X14 ) )
      | ( m1_subset_1 @ ( sk_D_2 @ X16 @ X17 @ X14 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_yellow_6])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_orders_2 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( m1_subset_1 @ ( sk_D_2 @ ( sk_D @ sk_C_1 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v7_waybel_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ( l1_orders_2 @ B ) ) ) )).

thf('19',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_waybel_0 @ X12 @ X13 )
      | ( l1_orders_2 @ X12 )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_0])).

thf('20',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( l1_orders_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    v7_waybel_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( m1_subset_1 @ ( sk_D_2 @ ( sk_D @ sk_C_1 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['17','22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D_2 @ ( sk_D @ sk_C_1 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_2 @ ( sk_D @ sk_C_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['5','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('29',plain,(
    m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('30',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ~ ( v7_waybel_0 @ X14 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X14 ) )
      | ( r1_orders_2 @ X14 @ X16 @ ( sk_D_2 @ X16 @ X17 @ X14 ) )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_yellow_6])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_orders_2 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_orders_2 @ sk_B_1 @ ( sk_D @ sk_C_1 @ sk_B_1 @ sk_A ) @ ( sk_D_2 @ ( sk_D @ sk_C_1 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 ) )
      | ~ ( v7_waybel_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('33',plain,(
    v7_waybel_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_orders_2 @ sk_B_1 @ ( sk_D @ sk_C_1 @ sk_B_1 @ sk_A ) @ ( sk_D_2 @ ( sk_D @ sk_C_1 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ sk_B_1 @ ( sk_D @ sk_C_1 @ sk_B_1 @ sk_A ) @ ( sk_D_2 @ ( sk_D @ sk_C_1 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_orders_2 @ sk_B_1 @ ( sk_D @ sk_C_1 @ sk_B_1 @ sk_A ) @ ( sk_D_2 @ ( sk_D @ sk_C_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['28','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X4: $i,X5: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ~ ( r1_waybel_0 @ X1 @ X0 @ X4 )
      | ~ ( r1_orders_2 @ X0 @ ( sk_D @ X4 @ X0 @ X1 ) @ X5 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ X0 @ X5 ) @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d11_waybel_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_D_2 @ ( sk_D @ sk_C_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_D_2 @ ( sk_D @ sk_C_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ sk_B_1 ) ) @ sk_C_1 )
      | ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C_1 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_D_2 @ ( sk_D @ sk_C_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_D_2 @ ( sk_D @ sk_C_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ sk_B_1 ) ) @ sk_C_1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_D_2 @ ( sk_D @ sk_C_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ sk_B_1 ) ) @ sk_C_1 )
      | ~ ( m1_subset_1 @ ( sk_D_2 @ ( sk_D @ sk_C_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_D_2 @ ( sk_D @ sk_C_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ sk_B_1 ) ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['27','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_D_2 @ ( sk_D @ sk_C_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ sk_B_1 ) ) @ sk_C_1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('48',plain,(
    m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('49',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ~ ( v7_waybel_0 @ X14 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X14 ) )
      | ( r1_orders_2 @ X14 @ X17 @ ( sk_D_2 @ X16 @ X17 @ X14 ) )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_yellow_6])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_orders_2 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_orders_2 @ sk_B_1 @ X0 @ ( sk_D_2 @ ( sk_D @ sk_C_1 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 ) )
      | ~ ( v7_waybel_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('52',plain,(
    v7_waybel_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_orders_2 @ sk_B_1 @ X0 @ ( sk_D_2 @ ( sk_D @ sk_C_1 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ sk_B_1 @ X0 @ ( sk_D_2 @ ( sk_D @ sk_C_1 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_orders_2 @ sk_B_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ ( sk_D_2 @ ( sk_D @ sk_C_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['47','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_2 @ ( sk_D @ sk_C_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['5','26'])).

thf('58',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( l1_waybel_0 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X6 ) )
      | ~ ( r1_orders_2 @ X6 @ ( sk_D_1 @ X8 @ X6 @ X7 ) @ X9 )
      | ~ ( r2_hidden @ ( k2_waybel_0 @ X7 @ X6 @ X9 ) @ X8 )
      | ( r2_waybel_0 @ X7 @ X6 @ X8 )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r2_waybel_0 @ X1 @ sk_B_1 @ X2 )
      | ~ ( r2_hidden @ ( k2_waybel_0 @ X1 @ sk_B_1 @ ( sk_D_2 @ ( sk_D @ sk_C_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ sk_B_1 ) ) @ X2 )
      | ~ ( r1_orders_2 @ sk_B_1 @ ( sk_D_1 @ X2 @ sk_B_1 @ X1 ) @ ( sk_D_2 @ ( sk_D @ sk_C_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ sk_B_1 ) )
      | ~ ( l1_waybel_0 @ sk_B_1 @ X1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_waybel_0 @ sk_B_1 @ X1 )
      | ~ ( r1_orders_2 @ sk_B_1 @ ( sk_D_1 @ X2 @ sk_B_1 @ X1 ) @ ( sk_D_2 @ ( sk_D @ sk_C_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ sk_B_1 ) )
      | ~ ( r2_hidden @ ( k2_waybel_0 @ X1 @ sk_B_1 @ ( sk_D_2 @ ( sk_D @ sk_C_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ sk_B_1 ) ) @ X2 )
      | ( r2_waybel_0 @ X1 @ sk_B_1 @ X2 )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ~ ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_D_2 @ ( sk_D @ sk_C_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ sk_B_1 ) ) @ X0 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','60'])).

thf('62',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ~ ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_D_2 @ ( sk_D @ sk_C_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ sk_B_1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_D_2 @ ( sk_D @ sk_C_1 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ sk_B_1 ) ) @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['46','65'])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C_1 ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    $false ),
    inference(demod,[status(thm)],['0','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2k73rAznRy
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:03:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.70  % Solved by: fo/fo7.sh
% 0.46/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.70  % done 133 iterations in 0.242s
% 0.46/0.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.70  % SZS output start Refutation
% 0.46/0.70  thf(r2_waybel_0_type, type, r2_waybel_0: $i > $i > $i > $o).
% 0.46/0.70  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.46/0.70  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.46/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.70  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.46/0.70  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.70  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 0.46/0.70  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.46/0.70  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.46/0.70  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.46/0.70  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.46/0.70  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 0.46/0.70  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.70  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.46/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.70  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.46/0.70  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.46/0.70  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.70  thf(t28_yellow_6, conjecture,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.46/0.70       ( ![B:$i]:
% 0.46/0.70         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.46/0.70             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.46/0.70           ( ![C:$i]:
% 0.46/0.70             ( ( r1_waybel_0 @ A @ B @ C ) => ( r2_waybel_0 @ A @ B @ C ) ) ) ) ) ))).
% 0.46/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.70    (~( ![A:$i]:
% 0.46/0.70        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.46/0.70          ( ![B:$i]:
% 0.46/0.70            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.46/0.70                ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.46/0.70              ( ![C:$i]:
% 0.46/0.70                ( ( r1_waybel_0 @ A @ B @ C ) => ( r2_waybel_0 @ A @ B @ C ) ) ) ) ) ) )),
% 0.46/0.70    inference('cnf.neg', [status(esa)], [t28_yellow_6])).
% 0.46/0.70  thf('0', plain, (~ (r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C_1)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('1', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(d12_waybel_0, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.46/0.70       ( ![B:$i]:
% 0.46/0.70         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.46/0.70           ( ![C:$i]:
% 0.46/0.70             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.46/0.70               ( ![D:$i]:
% 0.46/0.70                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.46/0.70                   ( ?[E:$i]:
% 0.46/0.70                     ( ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) & 
% 0.46/0.70                       ( r1_orders_2 @ B @ D @ E ) & 
% 0.46/0.70                       ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.70  thf('2', plain,
% 0.46/0.70      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.70         ((v2_struct_0 @ X6)
% 0.46/0.70          | ~ (l1_waybel_0 @ X6 @ X7)
% 0.46/0.70          | (m1_subset_1 @ (sk_D_1 @ X8 @ X6 @ X7) @ (u1_struct_0 @ X6))
% 0.46/0.70          | (r2_waybel_0 @ X7 @ X6 @ X8)
% 0.46/0.70          | ~ (l1_struct_0 @ X7)
% 0.46/0.70          | (v2_struct_0 @ X7))),
% 0.46/0.70      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.46/0.70  thf('3', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((v2_struct_0 @ sk_A)
% 0.46/0.70          | ~ (l1_struct_0 @ sk_A)
% 0.46/0.70          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.46/0.70          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ 
% 0.46/0.70             (u1_struct_0 @ sk_B_1))
% 0.46/0.70          | (v2_struct_0 @ sk_B_1))),
% 0.46/0.70      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.70  thf('4', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('5', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((v2_struct_0 @ sk_A)
% 0.46/0.70          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.46/0.70          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ 
% 0.46/0.70             (u1_struct_0 @ sk_B_1))
% 0.46/0.70          | (v2_struct_0 @ sk_B_1))),
% 0.46/0.70      inference('demod', [status(thm)], ['3', '4'])).
% 0.46/0.70  thf('6', plain, ((r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C_1)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(d11_waybel_0, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.46/0.70       ( ![B:$i]:
% 0.46/0.70         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.46/0.70           ( ![C:$i]:
% 0.46/0.70             ( ( r1_waybel_0 @ A @ B @ C ) <=>
% 0.46/0.70               ( ?[D:$i]:
% 0.46/0.70                 ( ( ![E:$i]:
% 0.46/0.70                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.46/0.70                       ( ( r1_orders_2 @ B @ D @ E ) =>
% 0.46/0.70                         ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) ) ) ) & 
% 0.46/0.70                   ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ))).
% 0.46/0.70  thf('7', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i, X4 : $i]:
% 0.46/0.70         ((v2_struct_0 @ X0)
% 0.46/0.70          | ~ (l1_waybel_0 @ X0 @ X1)
% 0.46/0.70          | ~ (r1_waybel_0 @ X1 @ X0 @ X4)
% 0.46/0.70          | (m1_subset_1 @ (sk_D @ X4 @ X0 @ X1) @ (u1_struct_0 @ X0))
% 0.46/0.70          | ~ (l1_struct_0 @ X1)
% 0.46/0.70          | (v2_struct_0 @ X1))),
% 0.46/0.70      inference('cnf', [status(esa)], [d11_waybel_0])).
% 0.46/0.70  thf('8', plain,
% 0.46/0.70      (((v2_struct_0 @ sk_A)
% 0.46/0.70        | ~ (l1_struct_0 @ sk_A)
% 0.46/0.70        | (m1_subset_1 @ (sk_D @ sk_C_1 @ sk_B_1 @ sk_A) @ 
% 0.46/0.70           (u1_struct_0 @ sk_B_1))
% 0.46/0.70        | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.46/0.70        | (v2_struct_0 @ sk_B_1))),
% 0.46/0.70      inference('sup-', [status(thm)], ['6', '7'])).
% 0.46/0.70  thf('9', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('10', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('11', plain,
% 0.46/0.70      (((v2_struct_0 @ sk_A)
% 0.46/0.70        | (m1_subset_1 @ (sk_D @ sk_C_1 @ sk_B_1 @ sk_A) @ 
% 0.46/0.70           (u1_struct_0 @ sk_B_1))
% 0.46/0.70        | (v2_struct_0 @ sk_B_1))),
% 0.46/0.70      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.46/0.70  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('13', plain,
% 0.46/0.70      (((v2_struct_0 @ sk_B_1)
% 0.46/0.70        | (m1_subset_1 @ (sk_D @ sk_C_1 @ sk_B_1 @ sk_A) @ 
% 0.46/0.70           (u1_struct_0 @ sk_B_1)))),
% 0.46/0.70      inference('clc', [status(thm)], ['11', '12'])).
% 0.46/0.70  thf('14', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('15', plain,
% 0.46/0.70      ((m1_subset_1 @ (sk_D @ sk_C_1 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.46/0.70      inference('clc', [status(thm)], ['13', '14'])).
% 0.46/0.70  thf(d5_yellow_6, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) ) =>
% 0.46/0.70       ( ( v7_waybel_0 @ A ) <=>
% 0.46/0.70         ( ![B:$i]:
% 0.46/0.70           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.70             ( ![C:$i]:
% 0.46/0.70               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.70                 ( ?[D:$i]:
% 0.46/0.70                   ( ( r1_orders_2 @ A @ C @ D ) & 
% 0.46/0.70                     ( r1_orders_2 @ A @ B @ D ) & 
% 0.46/0.70                     ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.70  thf('16', plain,
% 0.46/0.70      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.46/0.70         (~ (v7_waybel_0 @ X14)
% 0.46/0.70          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X14))
% 0.46/0.70          | (m1_subset_1 @ (sk_D_2 @ X16 @ X17 @ X14) @ (u1_struct_0 @ X14))
% 0.46/0.70          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X14))
% 0.46/0.70          | ~ (l1_orders_2 @ X14)
% 0.46/0.70          | (v2_struct_0 @ X14))),
% 0.46/0.70      inference('cnf', [status(esa)], [d5_yellow_6])).
% 0.46/0.70  thf('17', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((v2_struct_0 @ sk_B_1)
% 0.46/0.70          | ~ (l1_orders_2 @ sk_B_1)
% 0.46/0.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.46/0.70          | (m1_subset_1 @ 
% 0.46/0.70             (sk_D_2 @ (sk_D @ sk_C_1 @ sk_B_1 @ sk_A) @ X0 @ sk_B_1) @ 
% 0.46/0.70             (u1_struct_0 @ sk_B_1))
% 0.46/0.70          | ~ (v7_waybel_0 @ sk_B_1))),
% 0.46/0.70      inference('sup-', [status(thm)], ['15', '16'])).
% 0.46/0.70  thf('18', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(dt_l1_waybel_0, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( l1_struct_0 @ A ) =>
% 0.46/0.70       ( ![B:$i]: ( ( l1_waybel_0 @ B @ A ) => ( l1_orders_2 @ B ) ) ) ))).
% 0.46/0.70  thf('19', plain,
% 0.46/0.70      (![X12 : $i, X13 : $i]:
% 0.46/0.70         (~ (l1_waybel_0 @ X12 @ X13)
% 0.46/0.70          | (l1_orders_2 @ X12)
% 0.46/0.70          | ~ (l1_struct_0 @ X13))),
% 0.46/0.70      inference('cnf', [status(esa)], [dt_l1_waybel_0])).
% 0.46/0.70  thf('20', plain, ((~ (l1_struct_0 @ sk_A) | (l1_orders_2 @ sk_B_1))),
% 0.46/0.70      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.70  thf('21', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('22', plain, ((l1_orders_2 @ sk_B_1)),
% 0.46/0.70      inference('demod', [status(thm)], ['20', '21'])).
% 0.46/0.70  thf('23', plain, ((v7_waybel_0 @ sk_B_1)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('24', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((v2_struct_0 @ sk_B_1)
% 0.46/0.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.46/0.70          | (m1_subset_1 @ 
% 0.46/0.70             (sk_D_2 @ (sk_D @ sk_C_1 @ sk_B_1 @ sk_A) @ X0 @ sk_B_1) @ 
% 0.46/0.70             (u1_struct_0 @ sk_B_1)))),
% 0.46/0.70      inference('demod', [status(thm)], ['17', '22', '23'])).
% 0.46/0.70  thf('25', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('26', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((m1_subset_1 @ 
% 0.46/0.70           (sk_D_2 @ (sk_D @ sk_C_1 @ sk_B_1 @ sk_A) @ X0 @ sk_B_1) @ 
% 0.46/0.70           (u1_struct_0 @ sk_B_1))
% 0.46/0.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1)))),
% 0.46/0.70      inference('clc', [status(thm)], ['24', '25'])).
% 0.46/0.70  thf('27', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((v2_struct_0 @ sk_B_1)
% 0.46/0.70          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.46/0.70          | (v2_struct_0 @ sk_A)
% 0.46/0.70          | (m1_subset_1 @ 
% 0.46/0.70             (sk_D_2 @ (sk_D @ sk_C_1 @ sk_B_1 @ sk_A) @ 
% 0.46/0.70              (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ sk_B_1) @ 
% 0.46/0.70             (u1_struct_0 @ sk_B_1)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['5', '26'])).
% 0.46/0.70  thf('28', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((v2_struct_0 @ sk_A)
% 0.46/0.70          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.46/0.70          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ 
% 0.46/0.70             (u1_struct_0 @ sk_B_1))
% 0.46/0.70          | (v2_struct_0 @ sk_B_1))),
% 0.46/0.70      inference('demod', [status(thm)], ['3', '4'])).
% 0.46/0.70  thf('29', plain,
% 0.46/0.70      ((m1_subset_1 @ (sk_D @ sk_C_1 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.46/0.70      inference('clc', [status(thm)], ['13', '14'])).
% 0.46/0.70  thf('30', plain,
% 0.46/0.70      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.46/0.70         (~ (v7_waybel_0 @ X14)
% 0.46/0.70          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X14))
% 0.46/0.70          | (r1_orders_2 @ X14 @ X16 @ (sk_D_2 @ X16 @ X17 @ X14))
% 0.46/0.70          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X14))
% 0.46/0.70          | ~ (l1_orders_2 @ X14)
% 0.46/0.70          | (v2_struct_0 @ X14))),
% 0.46/0.70      inference('cnf', [status(esa)], [d5_yellow_6])).
% 0.46/0.70  thf('31', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((v2_struct_0 @ sk_B_1)
% 0.46/0.70          | ~ (l1_orders_2 @ sk_B_1)
% 0.46/0.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.46/0.70          | (r1_orders_2 @ sk_B_1 @ (sk_D @ sk_C_1 @ sk_B_1 @ sk_A) @ 
% 0.46/0.70             (sk_D_2 @ (sk_D @ sk_C_1 @ sk_B_1 @ sk_A) @ X0 @ sk_B_1))
% 0.46/0.70          | ~ (v7_waybel_0 @ sk_B_1))),
% 0.46/0.70      inference('sup-', [status(thm)], ['29', '30'])).
% 0.46/0.70  thf('32', plain, ((l1_orders_2 @ sk_B_1)),
% 0.46/0.70      inference('demod', [status(thm)], ['20', '21'])).
% 0.46/0.70  thf('33', plain, ((v7_waybel_0 @ sk_B_1)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('34', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((v2_struct_0 @ sk_B_1)
% 0.46/0.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.46/0.70          | (r1_orders_2 @ sk_B_1 @ (sk_D @ sk_C_1 @ sk_B_1 @ sk_A) @ 
% 0.46/0.70             (sk_D_2 @ (sk_D @ sk_C_1 @ sk_B_1 @ sk_A) @ X0 @ sk_B_1)))),
% 0.46/0.70      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.46/0.70  thf('35', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('36', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((r1_orders_2 @ sk_B_1 @ (sk_D @ sk_C_1 @ sk_B_1 @ sk_A) @ 
% 0.46/0.70           (sk_D_2 @ (sk_D @ sk_C_1 @ sk_B_1 @ sk_A) @ X0 @ sk_B_1))
% 0.46/0.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1)))),
% 0.46/0.70      inference('clc', [status(thm)], ['34', '35'])).
% 0.46/0.70  thf('37', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((v2_struct_0 @ sk_B_1)
% 0.46/0.70          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.46/0.70          | (v2_struct_0 @ sk_A)
% 0.46/0.70          | (r1_orders_2 @ sk_B_1 @ (sk_D @ sk_C_1 @ sk_B_1 @ sk_A) @ 
% 0.46/0.70             (sk_D_2 @ (sk_D @ sk_C_1 @ sk_B_1 @ sk_A) @ 
% 0.46/0.70              (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ sk_B_1)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['28', '36'])).
% 0.46/0.70  thf('38', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i, X4 : $i, X5 : $i]:
% 0.46/0.70         ((v2_struct_0 @ X0)
% 0.46/0.70          | ~ (l1_waybel_0 @ X0 @ X1)
% 0.46/0.70          | ~ (r1_waybel_0 @ X1 @ X0 @ X4)
% 0.46/0.70          | ~ (r1_orders_2 @ X0 @ (sk_D @ X4 @ X0 @ X1) @ X5)
% 0.46/0.70          | (r2_hidden @ (k2_waybel_0 @ X1 @ X0 @ X5) @ X4)
% 0.46/0.70          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X0))
% 0.46/0.70          | ~ (l1_struct_0 @ X1)
% 0.46/0.70          | (v2_struct_0 @ X1))),
% 0.46/0.70      inference('cnf', [status(esa)], [d11_waybel_0])).
% 0.46/0.70  thf('39', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((v2_struct_0 @ sk_A)
% 0.46/0.70          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.46/0.70          | (v2_struct_0 @ sk_B_1)
% 0.46/0.70          | (v2_struct_0 @ sk_A)
% 0.46/0.70          | ~ (l1_struct_0 @ sk_A)
% 0.46/0.70          | ~ (m1_subset_1 @ 
% 0.46/0.70               (sk_D_2 @ (sk_D @ sk_C_1 @ sk_B_1 @ sk_A) @ 
% 0.46/0.70                (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ sk_B_1) @ 
% 0.46/0.70               (u1_struct_0 @ sk_B_1))
% 0.46/0.70          | (r2_hidden @ 
% 0.46/0.70             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.46/0.70              (sk_D_2 @ (sk_D @ sk_C_1 @ sk_B_1 @ sk_A) @ 
% 0.46/0.70               (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ sk_B_1)) @ 
% 0.46/0.70             sk_C_1)
% 0.46/0.70          | ~ (r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C_1)
% 0.46/0.70          | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.46/0.70          | (v2_struct_0 @ sk_B_1))),
% 0.46/0.70      inference('sup-', [status(thm)], ['37', '38'])).
% 0.46/0.70  thf('40', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('41', plain, ((r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C_1)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('42', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('43', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((v2_struct_0 @ sk_A)
% 0.46/0.70          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.46/0.70          | (v2_struct_0 @ sk_B_1)
% 0.46/0.70          | (v2_struct_0 @ sk_A)
% 0.46/0.70          | ~ (m1_subset_1 @ 
% 0.46/0.70               (sk_D_2 @ (sk_D @ sk_C_1 @ sk_B_1 @ sk_A) @ 
% 0.46/0.70                (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ sk_B_1) @ 
% 0.46/0.70               (u1_struct_0 @ sk_B_1))
% 0.46/0.70          | (r2_hidden @ 
% 0.46/0.70             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.46/0.70              (sk_D_2 @ (sk_D @ sk_C_1 @ sk_B_1 @ sk_A) @ 
% 0.46/0.70               (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ sk_B_1)) @ 
% 0.46/0.70             sk_C_1)
% 0.46/0.70          | (v2_struct_0 @ sk_B_1))),
% 0.46/0.70      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 0.46/0.70  thf('44', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((r2_hidden @ 
% 0.46/0.70           (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.46/0.70            (sk_D_2 @ (sk_D @ sk_C_1 @ sk_B_1 @ sk_A) @ 
% 0.46/0.70             (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ sk_B_1)) @ 
% 0.46/0.70           sk_C_1)
% 0.46/0.70          | ~ (m1_subset_1 @ 
% 0.46/0.70               (sk_D_2 @ (sk_D @ sk_C_1 @ sk_B_1 @ sk_A) @ 
% 0.46/0.70                (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ sk_B_1) @ 
% 0.46/0.70               (u1_struct_0 @ sk_B_1))
% 0.46/0.70          | (v2_struct_0 @ sk_B_1)
% 0.46/0.70          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.46/0.70          | (v2_struct_0 @ sk_A))),
% 0.46/0.70      inference('simplify', [status(thm)], ['43'])).
% 0.46/0.70  thf('45', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((v2_struct_0 @ sk_A)
% 0.46/0.70          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.46/0.70          | (v2_struct_0 @ sk_B_1)
% 0.46/0.70          | (v2_struct_0 @ sk_A)
% 0.46/0.70          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.46/0.70          | (v2_struct_0 @ sk_B_1)
% 0.46/0.70          | (r2_hidden @ 
% 0.46/0.70             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.46/0.70              (sk_D_2 @ (sk_D @ sk_C_1 @ sk_B_1 @ sk_A) @ 
% 0.46/0.70               (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ sk_B_1)) @ 
% 0.46/0.70             sk_C_1))),
% 0.46/0.70      inference('sup-', [status(thm)], ['27', '44'])).
% 0.46/0.70  thf('46', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((r2_hidden @ 
% 0.46/0.70           (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.46/0.70            (sk_D_2 @ (sk_D @ sk_C_1 @ sk_B_1 @ sk_A) @ 
% 0.46/0.70             (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ sk_B_1)) @ 
% 0.46/0.70           sk_C_1)
% 0.46/0.70          | (v2_struct_0 @ sk_B_1)
% 0.46/0.70          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.46/0.70          | (v2_struct_0 @ sk_A))),
% 0.46/0.70      inference('simplify', [status(thm)], ['45'])).
% 0.46/0.70  thf('47', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((v2_struct_0 @ sk_A)
% 0.46/0.70          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.46/0.70          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ 
% 0.46/0.70             (u1_struct_0 @ sk_B_1))
% 0.46/0.70          | (v2_struct_0 @ sk_B_1))),
% 0.46/0.70      inference('demod', [status(thm)], ['3', '4'])).
% 0.46/0.70  thf('48', plain,
% 0.46/0.70      ((m1_subset_1 @ (sk_D @ sk_C_1 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.46/0.70      inference('clc', [status(thm)], ['13', '14'])).
% 0.46/0.70  thf('49', plain,
% 0.46/0.70      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.46/0.70         (~ (v7_waybel_0 @ X14)
% 0.46/0.70          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X14))
% 0.46/0.70          | (r1_orders_2 @ X14 @ X17 @ (sk_D_2 @ X16 @ X17 @ X14))
% 0.46/0.70          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X14))
% 0.46/0.70          | ~ (l1_orders_2 @ X14)
% 0.46/0.70          | (v2_struct_0 @ X14))),
% 0.46/0.70      inference('cnf', [status(esa)], [d5_yellow_6])).
% 0.46/0.70  thf('50', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((v2_struct_0 @ sk_B_1)
% 0.46/0.70          | ~ (l1_orders_2 @ sk_B_1)
% 0.46/0.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.46/0.70          | (r1_orders_2 @ sk_B_1 @ X0 @ 
% 0.46/0.70             (sk_D_2 @ (sk_D @ sk_C_1 @ sk_B_1 @ sk_A) @ X0 @ sk_B_1))
% 0.46/0.70          | ~ (v7_waybel_0 @ sk_B_1))),
% 0.46/0.70      inference('sup-', [status(thm)], ['48', '49'])).
% 0.46/0.70  thf('51', plain, ((l1_orders_2 @ sk_B_1)),
% 0.46/0.70      inference('demod', [status(thm)], ['20', '21'])).
% 0.46/0.70  thf('52', plain, ((v7_waybel_0 @ sk_B_1)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('53', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((v2_struct_0 @ sk_B_1)
% 0.46/0.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.46/0.70          | (r1_orders_2 @ sk_B_1 @ X0 @ 
% 0.46/0.70             (sk_D_2 @ (sk_D @ sk_C_1 @ sk_B_1 @ sk_A) @ X0 @ sk_B_1)))),
% 0.46/0.70      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.46/0.70  thf('54', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('55', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((r1_orders_2 @ sk_B_1 @ X0 @ 
% 0.46/0.70           (sk_D_2 @ (sk_D @ sk_C_1 @ sk_B_1 @ sk_A) @ X0 @ sk_B_1))
% 0.46/0.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1)))),
% 0.46/0.70      inference('clc', [status(thm)], ['53', '54'])).
% 0.46/0.70  thf('56', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((v2_struct_0 @ sk_B_1)
% 0.46/0.70          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.46/0.70          | (v2_struct_0 @ sk_A)
% 0.46/0.70          | (r1_orders_2 @ sk_B_1 @ (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ 
% 0.46/0.70             (sk_D_2 @ (sk_D @ sk_C_1 @ sk_B_1 @ sk_A) @ 
% 0.46/0.70              (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ sk_B_1)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['47', '55'])).
% 0.46/0.70  thf('57', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((v2_struct_0 @ sk_B_1)
% 0.46/0.70          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.46/0.70          | (v2_struct_0 @ sk_A)
% 0.46/0.70          | (m1_subset_1 @ 
% 0.46/0.70             (sk_D_2 @ (sk_D @ sk_C_1 @ sk_B_1 @ sk_A) @ 
% 0.46/0.70              (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ sk_B_1) @ 
% 0.46/0.70             (u1_struct_0 @ sk_B_1)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['5', '26'])).
% 0.46/0.70  thf('58', plain,
% 0.46/0.70      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.46/0.70         ((v2_struct_0 @ X6)
% 0.46/0.70          | ~ (l1_waybel_0 @ X6 @ X7)
% 0.46/0.70          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X6))
% 0.46/0.70          | ~ (r1_orders_2 @ X6 @ (sk_D_1 @ X8 @ X6 @ X7) @ X9)
% 0.46/0.70          | ~ (r2_hidden @ (k2_waybel_0 @ X7 @ X6 @ X9) @ X8)
% 0.46/0.70          | (r2_waybel_0 @ X7 @ X6 @ X8)
% 0.46/0.70          | ~ (l1_struct_0 @ X7)
% 0.46/0.70          | (v2_struct_0 @ X7))),
% 0.46/0.70      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.46/0.70  thf('59', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.70         ((v2_struct_0 @ sk_A)
% 0.46/0.70          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.46/0.70          | (v2_struct_0 @ sk_B_1)
% 0.46/0.70          | (v2_struct_0 @ X1)
% 0.46/0.70          | ~ (l1_struct_0 @ X1)
% 0.46/0.70          | (r2_waybel_0 @ X1 @ sk_B_1 @ X2)
% 0.46/0.70          | ~ (r2_hidden @ 
% 0.46/0.70               (k2_waybel_0 @ X1 @ sk_B_1 @ 
% 0.46/0.70                (sk_D_2 @ (sk_D @ sk_C_1 @ sk_B_1 @ sk_A) @ 
% 0.46/0.70                 (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ sk_B_1)) @ 
% 0.46/0.70               X2)
% 0.46/0.70          | ~ (r1_orders_2 @ sk_B_1 @ (sk_D_1 @ X2 @ sk_B_1 @ X1) @ 
% 0.46/0.70               (sk_D_2 @ (sk_D @ sk_C_1 @ sk_B_1 @ sk_A) @ 
% 0.46/0.70                (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ sk_B_1))
% 0.46/0.70          | ~ (l1_waybel_0 @ sk_B_1 @ X1)
% 0.46/0.70          | (v2_struct_0 @ sk_B_1))),
% 0.46/0.70      inference('sup-', [status(thm)], ['57', '58'])).
% 0.46/0.70  thf('60', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.70         (~ (l1_waybel_0 @ sk_B_1 @ X1)
% 0.46/0.70          | ~ (r1_orders_2 @ sk_B_1 @ (sk_D_1 @ X2 @ sk_B_1 @ X1) @ 
% 0.46/0.70               (sk_D_2 @ (sk_D @ sk_C_1 @ sk_B_1 @ sk_A) @ 
% 0.46/0.70                (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ sk_B_1))
% 0.46/0.70          | ~ (r2_hidden @ 
% 0.46/0.70               (k2_waybel_0 @ X1 @ sk_B_1 @ 
% 0.46/0.70                (sk_D_2 @ (sk_D @ sk_C_1 @ sk_B_1 @ sk_A) @ 
% 0.46/0.70                 (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ sk_B_1)) @ 
% 0.46/0.70               X2)
% 0.46/0.70          | (r2_waybel_0 @ X1 @ sk_B_1 @ X2)
% 0.46/0.70          | ~ (l1_struct_0 @ X1)
% 0.46/0.70          | (v2_struct_0 @ X1)
% 0.46/0.70          | (v2_struct_0 @ sk_B_1)
% 0.46/0.70          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.46/0.70          | (v2_struct_0 @ sk_A))),
% 0.46/0.70      inference('simplify', [status(thm)], ['59'])).
% 0.46/0.70  thf('61', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((v2_struct_0 @ sk_A)
% 0.46/0.70          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.46/0.70          | (v2_struct_0 @ sk_B_1)
% 0.46/0.70          | (v2_struct_0 @ sk_A)
% 0.46/0.70          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.46/0.70          | (v2_struct_0 @ sk_B_1)
% 0.46/0.70          | (v2_struct_0 @ sk_A)
% 0.46/0.70          | ~ (l1_struct_0 @ sk_A)
% 0.46/0.70          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.46/0.70          | ~ (r2_hidden @ 
% 0.46/0.70               (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.46/0.70                (sk_D_2 @ (sk_D @ sk_C_1 @ sk_B_1 @ sk_A) @ 
% 0.46/0.70                 (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ sk_B_1)) @ 
% 0.46/0.70               X0)
% 0.46/0.70          | ~ (l1_waybel_0 @ sk_B_1 @ sk_A))),
% 0.46/0.70      inference('sup-', [status(thm)], ['56', '60'])).
% 0.46/0.70  thf('62', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('63', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('64', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((v2_struct_0 @ sk_A)
% 0.46/0.70          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.46/0.70          | (v2_struct_0 @ sk_B_1)
% 0.46/0.70          | (v2_struct_0 @ sk_A)
% 0.46/0.70          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.46/0.70          | (v2_struct_0 @ sk_B_1)
% 0.46/0.70          | (v2_struct_0 @ sk_A)
% 0.46/0.70          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.46/0.70          | ~ (r2_hidden @ 
% 0.46/0.70               (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.46/0.70                (sk_D_2 @ (sk_D @ sk_C_1 @ sk_B_1 @ sk_A) @ 
% 0.46/0.70                 (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ sk_B_1)) @ 
% 0.46/0.70               X0))),
% 0.46/0.70      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.46/0.70  thf('65', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (r2_hidden @ 
% 0.46/0.70             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.46/0.70              (sk_D_2 @ (sk_D @ sk_C_1 @ sk_B_1 @ sk_A) @ 
% 0.46/0.70               (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ sk_B_1)) @ 
% 0.46/0.70             X0)
% 0.46/0.70          | (v2_struct_0 @ sk_B_1)
% 0.46/0.70          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.46/0.70          | (v2_struct_0 @ sk_A))),
% 0.46/0.70      inference('simplify', [status(thm)], ['64'])).
% 0.46/0.70  thf('66', plain,
% 0.46/0.70      (((v2_struct_0 @ sk_A)
% 0.46/0.70        | (r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C_1)
% 0.46/0.70        | (v2_struct_0 @ sk_B_1)
% 0.46/0.70        | (v2_struct_0 @ sk_A)
% 0.46/0.70        | (r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C_1)
% 0.46/0.70        | (v2_struct_0 @ sk_B_1))),
% 0.46/0.70      inference('sup-', [status(thm)], ['46', '65'])).
% 0.46/0.70  thf('67', plain,
% 0.46/0.70      (((v2_struct_0 @ sk_B_1)
% 0.46/0.70        | (r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C_1)
% 0.46/0.70        | (v2_struct_0 @ sk_A))),
% 0.46/0.70      inference('simplify', [status(thm)], ['66'])).
% 0.46/0.70  thf('68', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('69', plain,
% 0.46/0.70      (((v2_struct_0 @ sk_A) | (r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.46/0.70      inference('clc', [status(thm)], ['67', '68'])).
% 0.46/0.70  thf('70', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('71', plain, ((r2_waybel_0 @ sk_A @ sk_B_1 @ sk_C_1)),
% 0.46/0.70      inference('clc', [status(thm)], ['69', '70'])).
% 0.46/0.70  thf('72', plain, ($false), inference('demod', [status(thm)], ['0', '71'])).
% 0.46/0.70  
% 0.46/0.70  % SZS output end Refutation
% 0.46/0.70  
% 0.46/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
