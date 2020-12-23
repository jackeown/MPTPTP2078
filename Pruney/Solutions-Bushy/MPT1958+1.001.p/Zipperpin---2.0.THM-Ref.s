%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1958+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KQi63AwXLI

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 247 expanded)
%              Number of leaves         :   25 (  80 expanded)
%              Depth                    :   17
%              Number of atoms          : 1235 (2612 expanded)
%              Number of equality atoms :   71 ( 156 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_yellow_0_type,type,(
    v2_yellow_0: $i > $o )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_yellow_0_type,type,(
    v3_yellow_0: $i > $o )).

thf(k4_yellow_0_type,type,(
    k4_yellow_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(t5_waybel_7,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v3_yellow_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( v7_struct_0 @ A )
      <=> ( ( k4_yellow_0 @ A )
          = ( k3_yellow_0 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v5_orders_2 @ A )
          & ( v3_yellow_0 @ A )
          & ( l1_orders_2 @ A ) )
       => ( ( v7_struct_0 @ A )
        <=> ( ( k4_yellow_0 @ A )
            = ( k3_yellow_0 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t5_waybel_7])).

thf('0',plain,
    ( ( ( k4_yellow_0 @ sk_A )
     != ( k3_yellow_0 @ sk_A ) )
    | ~ ( v7_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k4_yellow_0 @ sk_A )
     != ( k3_yellow_0 @ sk_A ) )
    | ~ ( v7_struct_0 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k4_yellow_0 @ sk_A )
      = ( k3_yellow_0 @ sk_A ) )
    | ( v7_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v7_struct_0 @ sk_A )
   <= ( v7_struct_0 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k4_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('5',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( k4_yellow_0 @ X5 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_yellow_0])).

thf(dt_k3_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('6',plain,(
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X4 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_0])).

thf(d10_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( v7_struct_0 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( B = C ) ) ) ) ) )).

thf('7',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v7_struct_0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( X3 = X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d10_struct_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( X1
        = ( k3_yellow_0 @ X0 ) )
      | ~ ( v7_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ( ( k4_yellow_0 @ X0 )
        = ( k3_yellow_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k4_yellow_0 @ X0 )
        = ( k3_yellow_0 @ X0 ) )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ~ ( v7_struct_0 @ sk_A )
    | ( ( k4_yellow_0 @ sk_A )
      = ( k3_yellow_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf('12',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('13',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('14',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( v7_struct_0 @ sk_A )
    | ( ( k4_yellow_0 @ sk_A )
      = ( k3_yellow_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('16',plain,
    ( ( ( k4_yellow_0 @ sk_A )
      = ( k3_yellow_0 @ sk_A ) )
   <= ( v7_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','15'])).

thf('17',plain,
    ( ( ( k4_yellow_0 @ sk_A )
     != ( k3_yellow_0 @ sk_A ) )
   <= ( ( k4_yellow_0 @ sk_A )
     != ( k3_yellow_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,
    ( ( ( k3_yellow_0 @ sk_A )
     != ( k3_yellow_0 @ sk_A ) )
   <= ( ( ( k4_yellow_0 @ sk_A )
       != ( k3_yellow_0 @ sk_A ) )
      & ( v7_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k4_yellow_0 @ sk_A )
      = ( k3_yellow_0 @ sk_A ) )
    | ~ ( v7_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( ( k4_yellow_0 @ sk_A )
      = ( k3_yellow_0 @ sk_A ) )
    | ( v7_struct_0 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('21',plain,
    ( ( ( k4_yellow_0 @ sk_A )
      = ( k3_yellow_0 @ sk_A ) )
   <= ( ( k4_yellow_0 @ sk_A )
      = ( k3_yellow_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('22',plain,(
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ( v7_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d10_struct_0])).

thf(t45_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v2_yellow_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r1_orders_2 @ A @ B @ ( k4_yellow_0 @ A ) ) ) ) )).

thf('23',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ( r1_orders_2 @ X13 @ X12 @ ( k4_yellow_0 @ X13 ) )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( v2_yellow_0 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t45_yellow_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v7_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v2_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( sk_C @ X0 ) @ ( k4_yellow_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( r1_orders_2 @ sk_A @ ( sk_C @ sk_A ) @ ( k3_yellow_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v2_yellow_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v7_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k4_yellow_0 @ sk_A )
      = ( k3_yellow_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('26',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v3_yellow_0 @ A )
       => ( ( v1_yellow_0 @ A )
          & ( v2_yellow_0 @ A ) ) ) ) )).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v3_yellow_0 @ X0 )
      | ( v2_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc4_yellow_0])).

thf('29',plain,
    ( ( v2_yellow_0 @ sk_A )
    | ~ ( v3_yellow_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v3_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v2_yellow_0 @ sk_A ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf('34',plain,
    ( ( ( r1_orders_2 @ sk_A @ ( sk_C @ sk_A ) @ ( k3_yellow_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v7_struct_0 @ sk_A ) )
   <= ( ( k4_yellow_0 @ sk_A )
      = ( k3_yellow_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26','31','32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( v7_struct_0 @ sk_A )
      | ( r1_orders_2 @ sk_A @ ( sk_C @ sk_A ) @ ( k3_yellow_0 @ sk_A ) ) )
   <= ( ( k4_yellow_0 @ sk_A )
      = ( k3_yellow_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ( v7_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d10_struct_0])).

thf(t44_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r1_orders_2 @ A @ ( k3_yellow_0 @ A ) @ B ) ) ) )).

thf('38',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ( r1_orders_2 @ X11 @ ( k3_yellow_0 @ X11 ) @ X10 )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v1_yellow_0 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t44_yellow_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v7_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X4 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_0])).

thf('41',plain,(
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ( v7_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d10_struct_0])).

thf(t25_orders_2,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( r1_orders_2 @ A @ B @ C )
                  & ( r1_orders_2 @ A @ C @ B ) )
               => ( B = C ) ) ) ) ) )).

thf('42',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r1_orders_2 @ X8 @ X7 @ X9 )
      | ~ ( r1_orders_2 @ X8 @ X9 @ X7 )
      | ( X7 = X9 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v5_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t25_orders_2])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v7_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( sk_C @ X0 )
        = X1 )
      | ~ ( r1_orders_2 @ X0 @ X1 @ ( sk_C @ X0 ) )
      | ~ ( r1_orders_2 @ X0 @ ( sk_C @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_orders_2 @ X0 @ ( sk_C @ X0 ) @ ( k3_yellow_0 @ X0 ) )
      | ~ ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( sk_C @ X0 ) )
      | ( ( sk_C @ X0 )
        = ( k3_yellow_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v7_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( ( sk_C @ X0 )
        = ( k3_yellow_0 @ X0 ) )
      | ~ ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( sk_C @ X0 ) )
      | ~ ( r1_orders_2 @ X0 @ ( sk_C @ X0 ) @ ( k3_yellow_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_orders_2 @ X0 @ ( sk_C @ X0 ) @ ( k3_yellow_0 @ X0 ) )
      | ( ( sk_C @ X0 )
        = ( k3_yellow_0 @ X0 ) )
      | ~ ( v5_orders_2 @ X0 )
      | ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 )
        = ( k3_yellow_0 @ X0 ) )
      | ~ ( r1_orders_2 @ X0 @ ( sk_C @ X0 ) @ ( k3_yellow_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v7_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( ( v7_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v1_yellow_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v7_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( ( sk_C @ sk_A )
        = ( k3_yellow_0 @ sk_A ) ) )
   <= ( ( k4_yellow_0 @ sk_A )
      = ( k3_yellow_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','47'])).

thf('49',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v3_yellow_0 @ X0 )
      | ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc4_yellow_0])).

thf('52',plain,
    ( ( v1_yellow_0 @ sk_A )
    | ~ ( v3_yellow_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v3_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_yellow_0 @ sk_A ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf('57',plain,
    ( ( ( v7_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v7_struct_0 @ sk_A )
      | ( ( sk_C @ sk_A )
        = ( k3_yellow_0 @ sk_A ) ) )
   <= ( ( k4_yellow_0 @ sk_A )
      = ( k3_yellow_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49','54','55','56'])).

thf('58',plain,
    ( ( ( ( sk_C @ sk_A )
        = ( k3_yellow_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v7_struct_0 @ sk_A ) )
   <= ( ( k4_yellow_0 @ sk_A )
      = ( k3_yellow_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( v7_struct_0 @ sk_A )
      | ( ( sk_C @ sk_A )
        = ( k3_yellow_0 @ sk_A ) ) )
   <= ( ( k4_yellow_0 @ sk_A )
      = ( k3_yellow_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( v7_struct_0 @ sk_A )
   <= ~ ( v7_struct_0 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('62',plain,
    ( ( ( sk_C @ sk_A )
      = ( k3_yellow_0 @ sk_A ) )
   <= ( ~ ( v7_struct_0 @ sk_A )
      & ( ( k4_yellow_0 @ sk_A )
        = ( k3_yellow_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( k4_yellow_0 @ sk_A )
      = ( k3_yellow_0 @ sk_A ) )
   <= ( ( k4_yellow_0 @ sk_A )
      = ( k3_yellow_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('64',plain,(
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ( v7_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d10_struct_0])).

thf('65',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ( r1_orders_2 @ X13 @ X12 @ ( k4_yellow_0 @ X13 ) )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( v2_yellow_0 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t45_yellow_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v7_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v2_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( sk_B @ X0 ) @ ( k4_yellow_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( r1_orders_2 @ sk_A @ ( sk_B @ sk_A ) @ ( k3_yellow_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v2_yellow_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v7_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k4_yellow_0 @ sk_A )
      = ( k3_yellow_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['63','66'])).

thf('68',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_yellow_0 @ sk_A ),
    inference(demod,[status(thm)],['29','30'])).

thf('70',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf('72',plain,
    ( ( ( r1_orders_2 @ sk_A @ ( sk_B @ sk_A ) @ ( k3_yellow_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v7_struct_0 @ sk_A ) )
   <= ( ( k4_yellow_0 @ sk_A )
      = ( k3_yellow_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68','69','70','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ( v7_struct_0 @ sk_A )
      | ( r1_orders_2 @ sk_A @ ( sk_B @ sk_A ) @ ( k3_yellow_0 @ sk_A ) ) )
   <= ( ( k4_yellow_0 @ sk_A )
      = ( k3_yellow_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ( v7_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d10_struct_0])).

thf('76',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ( r1_orders_2 @ X11 @ ( k3_yellow_0 @ X11 ) @ X10 )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v1_yellow_0 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t44_yellow_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v7_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X4 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_0])).

thf('79',plain,(
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ( v7_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d10_struct_0])).

thf('80',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r1_orders_2 @ X8 @ X7 @ X9 )
      | ~ ( r1_orders_2 @ X8 @ X9 @ X7 )
      | ( X7 = X9 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v5_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t25_orders_2])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v7_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( sk_B @ X0 )
        = X1 )
      | ~ ( r1_orders_2 @ X0 @ X1 @ ( sk_B @ X0 ) )
      | ~ ( r1_orders_2 @ X0 @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_orders_2 @ X0 @ ( sk_B @ X0 ) @ ( k3_yellow_0 @ X0 ) )
      | ~ ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( sk_B @ X0 ) )
      | ( ( sk_B @ X0 )
        = ( k3_yellow_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v7_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( ( sk_B @ X0 )
        = ( k3_yellow_0 @ X0 ) )
      | ~ ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( sk_B @ X0 ) )
      | ~ ( r1_orders_2 @ X0 @ ( sk_B @ X0 ) @ ( k3_yellow_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_orders_2 @ X0 @ ( sk_B @ X0 ) @ ( k3_yellow_0 @ X0 ) )
      | ( ( sk_B @ X0 )
        = ( k3_yellow_0 @ X0 ) )
      | ~ ( v5_orders_2 @ X0 )
      | ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
        = ( k3_yellow_0 @ X0 ) )
      | ~ ( r1_orders_2 @ X0 @ ( sk_B @ X0 ) @ ( k3_yellow_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v7_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,
    ( ( ( v7_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v1_yellow_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v7_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( ( sk_B @ sk_A )
        = ( k3_yellow_0 @ sk_A ) ) )
   <= ( ( k4_yellow_0 @ sk_A )
      = ( k3_yellow_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','85'])).

thf('87',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_yellow_0 @ sk_A ),
    inference(demod,[status(thm)],['52','53'])).

thf('89',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf('91',plain,
    ( ( ( v7_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v7_struct_0 @ sk_A )
      | ( ( sk_B @ sk_A )
        = ( k3_yellow_0 @ sk_A ) ) )
   <= ( ( k4_yellow_0 @ sk_A )
      = ( k3_yellow_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['86','87','88','89','90'])).

thf('92',plain,
    ( ( ( ( sk_B @ sk_A )
        = ( k3_yellow_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v7_struct_0 @ sk_A ) )
   <= ( ( k4_yellow_0 @ sk_A )
      = ( k3_yellow_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( ( v7_struct_0 @ sk_A )
      | ( ( sk_B @ sk_A )
        = ( k3_yellow_0 @ sk_A ) ) )
   <= ( ( k4_yellow_0 @ sk_A )
      = ( k3_yellow_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,
    ( ~ ( v7_struct_0 @ sk_A )
   <= ~ ( v7_struct_0 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('96',plain,
    ( ( ( sk_B @ sk_A )
      = ( k3_yellow_0 @ sk_A ) )
   <= ( ~ ( v7_struct_0 @ sk_A )
      & ( ( k4_yellow_0 @ sk_A )
        = ( k3_yellow_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ( sk_B @ sk_A )
      = ( sk_C @ sk_A ) )
   <= ( ~ ( v7_struct_0 @ sk_A )
      & ( ( k4_yellow_0 @ sk_A )
        = ( k3_yellow_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['62','96'])).

thf('98',plain,(
    ! [X1: $i] :
      ( ( ( sk_B @ X1 )
       != ( sk_C @ X1 ) )
      | ( v7_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d10_struct_0])).

thf('99',plain,
    ( ( ( ( sk_B @ sk_A )
       != ( sk_B @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v7_struct_0 @ sk_A ) )
   <= ( ~ ( v7_struct_0 @ sk_A )
      & ( ( k4_yellow_0 @ sk_A )
        = ( k3_yellow_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf('101',plain,
    ( ( ( ( sk_B @ sk_A )
       != ( sk_B @ sk_A ) )
      | ( v7_struct_0 @ sk_A ) )
   <= ( ~ ( v7_struct_0 @ sk_A )
      & ( ( k4_yellow_0 @ sk_A )
        = ( k3_yellow_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( v7_struct_0 @ sk_A )
   <= ( ~ ( v7_struct_0 @ sk_A )
      & ( ( k4_yellow_0 @ sk_A )
        = ( k3_yellow_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,
    ( ~ ( v7_struct_0 @ sk_A )
   <= ~ ( v7_struct_0 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('104',plain,
    ( ( ( k4_yellow_0 @ sk_A )
     != ( k3_yellow_0 @ sk_A ) )
    | ( v7_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','19','20','104'])).


%------------------------------------------------------------------------------
