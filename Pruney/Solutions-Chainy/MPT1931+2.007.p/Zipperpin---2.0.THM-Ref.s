%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oUO7vtZ9Nt

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 122 expanded)
%              Number of leaves         :   27 (  46 expanded)
%              Depth                    :   28
%              Number of atoms          :  781 (1393 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k4_yellow_6_type,type,(
    k4_yellow_6: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t29_yellow_6,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_struct_0 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v4_orders_2 @ B )
              & ( v7_waybel_0 @ B )
              & ( l1_waybel_0 @ B @ A ) )
           => ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_yellow_6])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('1',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf(existence_l1_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ? [B: $i] :
          ( l1_waybel_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X15: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X15 ) @ X15 )
      | ~ ( l1_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[existence_l1_waybel_0])).

thf(dt_k4_yellow_6,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ( l1_waybel_0 @ B @ A ) )
     => ( m1_subset_1 @ ( k4_yellow_6 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_waybel_0 @ X17 @ X16 )
      | ( m1_subset_1 @ ( k4_yellow_6 @ X16 @ X17 ) @ ( u1_struct_0 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_yellow_6])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k4_yellow_6 @ X0 @ ( sk_B @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k4_yellow_6 @ X0 @ ( sk_B @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('8',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k4_yellow_6 @ X0 @ ( sk_B @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

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

thf('10',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( l1_waybel_0 @ X4 @ X5 )
      | ( m1_subset_1 @ ( sk_E @ X6 @ X7 @ X4 @ X5 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X4 ) )
      | ( r1_waybel_0 @ X5 @ X4 @ X7 )
      | ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d11_waybel_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r1_waybel_0 @ X1 @ X0 @ X2 )
      | ( m1_subset_1 @ ( sk_E @ ( k4_yellow_6 @ X0 @ ( sk_B @ X0 ) ) @ X2 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( m1_subset_1 @ ( sk_E @ ( k4_yellow_6 @ X0 @ ( sk_B @ X0 ) ) @ X2 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ( r1_waybel_0 @ X1 @ X0 @ X2 )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( m1_subset_1 @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf('14',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( m1_subset_1 @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','15'])).

thf('17',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ( l1_orders_2 @ B ) ) ) )).

thf('18',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_waybel_0 @ X13 @ X14 )
      | ( l1_orders_2 @ X13 )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_0])).

thf('19',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( l1_orders_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['16','21'])).

thf(dt_k2_waybel_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ~ ( v2_struct_0 @ B )
        & ( l1_waybel_0 @ B @ A )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) )
     => ( m1_subset_1 @ ( k2_waybel_0 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ) )).

thf('23',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( l1_waybel_0 @ X10 @ X11 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_struct_0 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X10 ) )
      | ( m1_subset_1 @ ( k2_waybel_0 @ X11 @ X10 @ X12 ) @ ( u1_struct_0 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_waybel_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( m1_subset_1 @ ( k2_waybel_0 @ X1 @ sk_B_1 @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) @ ( u1_struct_0 @ X1 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_waybel_0 @ sk_B_1 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( m1_subset_1 @ ( k2_waybel_0 @ X1 @ sk_B_1 @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) @ ( u1_struct_0 @ X1 ) )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( m1_subset_1 @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','25'])).

thf('27',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( m1_subset_1 @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( l1_waybel_0 @ X4 @ X5 )
      | ~ ( r2_hidden @ ( k2_waybel_0 @ X5 @ X4 @ ( sk_E @ X6 @ X7 @ X4 @ X5 ) ) @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X4 ) )
      | ( r1_waybel_0 @ X5 @ X4 @ X7 )
      | ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d11_waybel_0])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ~ ( m1_subset_1 @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ~ ( l1_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['5','37'])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ~ ( l1_orders_2 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','39'])).

thf('41',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['19','20'])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['46','47'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('49',plain,(
    ! [X2: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['0','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oUO7vtZ9Nt
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:25:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 63 iterations in 0.055s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.48  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.48  thf(k4_yellow_6_type, type, k4_yellow_6: $i > $i > $i).
% 0.21/0.48  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 0.21/0.48  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.21/0.48  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.21/0.48  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.21/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.48  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.48  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(t29_yellow_6, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.48             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.48           ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.48          ( ![B:$i]:
% 0.21/0.48            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.48                ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.48              ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t29_yellow_6])).
% 0.21/0.48  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(dt_l1_orders_2, axiom,
% 0.21/0.48    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.48  thf('1', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_orders_2 @ X3))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.21/0.48  thf(existence_l1_waybel_0, axiom,
% 0.21/0.48    (![A:$i]: ( ( l1_struct_0 @ A ) => ( ?[B:$i]: ( l1_waybel_0 @ B @ A ) ) ))).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X15 : $i]:
% 0.21/0.48         ((l1_waybel_0 @ (sk_B @ X15) @ X15) | ~ (l1_struct_0 @ X15))),
% 0.21/0.48      inference('cnf', [status(esa)], [existence_l1_waybel_0])).
% 0.21/0.48  thf(dt_k4_yellow_6, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.21/0.48         ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.48       ( m1_subset_1 @ ( k4_yellow_6 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X16 : $i, X17 : $i]:
% 0.21/0.48         (~ (l1_struct_0 @ X16)
% 0.21/0.48          | (v2_struct_0 @ X16)
% 0.21/0.48          | ~ (l1_waybel_0 @ X17 @ X16)
% 0.21/0.48          | (m1_subset_1 @ (k4_yellow_6 @ X16 @ X17) @ (u1_struct_0 @ X16)))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k4_yellow_6])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (l1_struct_0 @ X0)
% 0.21/0.48          | (m1_subset_1 @ (k4_yellow_6 @ X0 @ (sk_B @ X0)) @ 
% 0.21/0.48             (u1_struct_0 @ X0))
% 0.21/0.48          | (v2_struct_0 @ X0)
% 0.21/0.48          | ~ (l1_struct_0 @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((v2_struct_0 @ X0)
% 0.21/0.48          | (m1_subset_1 @ (k4_yellow_6 @ X0 @ (sk_B @ X0)) @ 
% 0.21/0.48             (u1_struct_0 @ X0))
% 0.21/0.48          | ~ (l1_struct_0 @ X0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.48  thf('6', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('7', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_orders_2 @ X3))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.21/0.48  thf('8', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((v2_struct_0 @ X0)
% 0.21/0.48          | (m1_subset_1 @ (k4_yellow_6 @ X0 @ (sk_B @ X0)) @ 
% 0.21/0.48             (u1_struct_0 @ X0))
% 0.21/0.48          | ~ (l1_struct_0 @ X0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.48  thf(d11_waybel_0, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.48           ( ![C:$i]:
% 0.21/0.48             ( ( r1_waybel_0 @ A @ B @ C ) <=>
% 0.21/0.48               ( ?[D:$i]:
% 0.21/0.48                 ( ( ![E:$i]:
% 0.21/0.48                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.48                       ( ( r1_orders_2 @ B @ D @ E ) =>
% 0.21/0.48                         ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) ) ) ) & 
% 0.21/0.48                   ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ))).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.48         ((v2_struct_0 @ X4)
% 0.21/0.48          | ~ (l1_waybel_0 @ X4 @ X5)
% 0.21/0.48          | (m1_subset_1 @ (sk_E @ X6 @ X7 @ X4 @ X5) @ (u1_struct_0 @ X4))
% 0.21/0.48          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X4))
% 0.21/0.48          | (r1_waybel_0 @ X5 @ X4 @ X7)
% 0.21/0.48          | ~ (l1_struct_0 @ X5)
% 0.21/0.48          | (v2_struct_0 @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [d11_waybel_0])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (l1_struct_0 @ X0)
% 0.21/0.48          | (v2_struct_0 @ X0)
% 0.21/0.48          | (v2_struct_0 @ X1)
% 0.21/0.48          | ~ (l1_struct_0 @ X1)
% 0.21/0.48          | (r1_waybel_0 @ X1 @ X0 @ X2)
% 0.21/0.48          | (m1_subset_1 @ 
% 0.21/0.48             (sk_E @ (k4_yellow_6 @ X0 @ (sk_B @ X0)) @ X2 @ X0 @ X1) @ 
% 0.21/0.48             (u1_struct_0 @ X0))
% 0.21/0.48          | ~ (l1_waybel_0 @ X0 @ X1)
% 0.21/0.48          | (v2_struct_0 @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (l1_waybel_0 @ X0 @ X1)
% 0.21/0.48          | (m1_subset_1 @ 
% 0.21/0.48             (sk_E @ (k4_yellow_6 @ X0 @ (sk_B @ X0)) @ X2 @ X0 @ X1) @ 
% 0.21/0.48             (u1_struct_0 @ X0))
% 0.21/0.48          | (r1_waybel_0 @ X1 @ X0 @ X2)
% 0.21/0.48          | ~ (l1_struct_0 @ X1)
% 0.21/0.48          | (v2_struct_0 @ X1)
% 0.21/0.48          | (v2_struct_0 @ X0)
% 0.21/0.48          | ~ (l1_struct_0 @ X0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (l1_struct_0 @ sk_B_1)
% 0.21/0.48          | (v2_struct_0 @ sk_B_1)
% 0.21/0.48          | (v2_struct_0 @ sk_A)
% 0.21/0.48          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.48          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.48          | (m1_subset_1 @ 
% 0.21/0.48             (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0 @ sk_B_1 @ 
% 0.21/0.48              sk_A) @ 
% 0.21/0.48             (u1_struct_0 @ sk_B_1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['8', '12'])).
% 0.21/0.48  thf('14', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (l1_struct_0 @ sk_B_1)
% 0.21/0.48          | (v2_struct_0 @ sk_B_1)
% 0.21/0.48          | (v2_struct_0 @ sk_A)
% 0.21/0.48          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.48          | (m1_subset_1 @ 
% 0.21/0.48             (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0 @ sk_B_1 @ 
% 0.21/0.48              sk_A) @ 
% 0.21/0.48             (u1_struct_0 @ sk_B_1)))),
% 0.21/0.48      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (l1_orders_2 @ sk_B_1)
% 0.21/0.48          | (m1_subset_1 @ 
% 0.21/0.48             (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0 @ sk_B_1 @ 
% 0.21/0.48              sk_A) @ 
% 0.21/0.48             (u1_struct_0 @ sk_B_1))
% 0.21/0.48          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.48          | (v2_struct_0 @ sk_A)
% 0.21/0.48          | (v2_struct_0 @ sk_B_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['7', '15'])).
% 0.21/0.48  thf('17', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(dt_l1_waybel_0, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_struct_0 @ A ) =>
% 0.21/0.48       ( ![B:$i]: ( ( l1_waybel_0 @ B @ A ) => ( l1_orders_2 @ B ) ) ) ))).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (![X13 : $i, X14 : $i]:
% 0.21/0.48         (~ (l1_waybel_0 @ X13 @ X14)
% 0.21/0.48          | (l1_orders_2 @ X13)
% 0.21/0.48          | ~ (l1_struct_0 @ X14))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_l1_waybel_0])).
% 0.21/0.48  thf('19', plain, ((~ (l1_struct_0 @ sk_A) | (l1_orders_2 @ sk_B_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf('20', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('21', plain, ((l1_orders_2 @ sk_B_1)),
% 0.21/0.48      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((m1_subset_1 @ 
% 0.21/0.48           (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0 @ sk_B_1 @ 
% 0.21/0.48            sk_A) @ 
% 0.21/0.48           (u1_struct_0 @ sk_B_1))
% 0.21/0.48          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.48          | (v2_struct_0 @ sk_A)
% 0.21/0.48          | (v2_struct_0 @ sk_B_1))),
% 0.21/0.48      inference('demod', [status(thm)], ['16', '21'])).
% 0.21/0.48  thf(dt_k2_waybel_0, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.21/0.48         ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) & 
% 0.21/0.48         ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.48       ( m1_subset_1 @ ( k2_waybel_0 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ))).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.48         (~ (l1_waybel_0 @ X10 @ X11)
% 0.21/0.48          | (v2_struct_0 @ X10)
% 0.21/0.48          | ~ (l1_struct_0 @ X11)
% 0.21/0.48          | (v2_struct_0 @ X11)
% 0.21/0.48          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X10))
% 0.21/0.48          | (m1_subset_1 @ (k2_waybel_0 @ X11 @ X10 @ X12) @ 
% 0.21/0.48             (u1_struct_0 @ X11)))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k2_waybel_0])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((v2_struct_0 @ sk_B_1)
% 0.21/0.48          | (v2_struct_0 @ sk_A)
% 0.21/0.48          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.48          | (m1_subset_1 @ 
% 0.21/0.48             (k2_waybel_0 @ X1 @ sk_B_1 @ 
% 0.21/0.48              (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0 @ sk_B_1 @ 
% 0.21/0.48               sk_A)) @ 
% 0.21/0.48             (u1_struct_0 @ X1))
% 0.21/0.48          | (v2_struct_0 @ X1)
% 0.21/0.48          | ~ (l1_struct_0 @ X1)
% 0.21/0.48          | (v2_struct_0 @ sk_B_1)
% 0.21/0.48          | ~ (l1_waybel_0 @ sk_B_1 @ X1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (l1_waybel_0 @ sk_B_1 @ X1)
% 0.21/0.48          | ~ (l1_struct_0 @ X1)
% 0.21/0.48          | (v2_struct_0 @ X1)
% 0.21/0.48          | (m1_subset_1 @ 
% 0.21/0.48             (k2_waybel_0 @ X1 @ sk_B_1 @ 
% 0.21/0.48              (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0 @ sk_B_1 @ 
% 0.21/0.48               sk_A)) @ 
% 0.21/0.48             (u1_struct_0 @ X1))
% 0.21/0.48          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.48          | (v2_struct_0 @ sk_A)
% 0.21/0.48          | (v2_struct_0 @ sk_B_1))),
% 0.21/0.48      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((v2_struct_0 @ sk_B_1)
% 0.21/0.48          | (v2_struct_0 @ sk_A)
% 0.21/0.48          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.48          | (m1_subset_1 @ 
% 0.21/0.48             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.21/0.48              (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0 @ sk_B_1 @ 
% 0.21/0.48               sk_A)) @ 
% 0.21/0.48             (u1_struct_0 @ sk_A))
% 0.21/0.48          | (v2_struct_0 @ sk_A)
% 0.21/0.48          | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['6', '25'])).
% 0.21/0.48  thf('27', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((v2_struct_0 @ sk_B_1)
% 0.21/0.48          | (v2_struct_0 @ sk_A)
% 0.21/0.48          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.48          | (m1_subset_1 @ 
% 0.21/0.48             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.21/0.48              (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0 @ sk_B_1 @ 
% 0.21/0.48               sk_A)) @ 
% 0.21/0.48             (u1_struct_0 @ sk_A))
% 0.21/0.48          | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((m1_subset_1 @ 
% 0.21/0.48           (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.21/0.48            (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0 @ sk_B_1 @ 
% 0.21/0.48             sk_A)) @ 
% 0.21/0.48           (u1_struct_0 @ sk_A))
% 0.21/0.49          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.49          | (v2_struct_0 @ sk_A)
% 0.21/0.49          | (v2_struct_0 @ sk_B_1))),
% 0.21/0.49      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.49  thf(t2_subset, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.49       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((r2_hidden @ X0 @ X1)
% 0.21/0.49          | (v1_xboole_0 @ X1)
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_struct_0 @ sk_B_1)
% 0.21/0.49          | (v2_struct_0 @ sk_A)
% 0.21/0.49          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.49          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49          | (r2_hidden @ 
% 0.21/0.49             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.21/0.49              (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0 @ sk_B_1 @ 
% 0.21/0.49               sk_A)) @ 
% 0.21/0.49             (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.49         ((v2_struct_0 @ X4)
% 0.21/0.49          | ~ (l1_waybel_0 @ X4 @ X5)
% 0.21/0.49          | ~ (r2_hidden @ 
% 0.21/0.49               (k2_waybel_0 @ X5 @ X4 @ (sk_E @ X6 @ X7 @ X4 @ X5)) @ X7)
% 0.21/0.49          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X4))
% 0.21/0.49          | (r1_waybel_0 @ X5 @ X4 @ X7)
% 0.21/0.49          | ~ (l1_struct_0 @ X5)
% 0.21/0.49          | (v2_struct_0 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [d11_waybel_0])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | (v2_struct_0 @ sk_A)
% 0.21/0.49        | (v2_struct_0 @ sk_B_1)
% 0.21/0.49        | (v2_struct_0 @ sk_A)
% 0.21/0.49        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.49        | (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | ~ (m1_subset_1 @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ 
% 0.21/0.49             (u1_struct_0 @ sk_B_1))
% 0.21/0.49        | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.21/0.49        | (v2_struct_0 @ sk_B_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.49  thf('34', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('35', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | (v2_struct_0 @ sk_A)
% 0.21/0.49        | (v2_struct_0 @ sk_B_1)
% 0.21/0.49        | (v2_struct_0 @ sk_A)
% 0.21/0.49        | (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | ~ (m1_subset_1 @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ 
% 0.21/0.49             (u1_struct_0 @ sk_B_1))
% 0.21/0.49        | (v2_struct_0 @ sk_B_1))),
% 0.21/0.49      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      ((~ (m1_subset_1 @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ 
% 0.21/0.49           (u1_struct_0 @ sk_B_1))
% 0.21/0.49        | (v2_struct_0 @ sk_B_1)
% 0.21/0.49        | (v2_struct_0 @ sk_A)
% 0.21/0.49        | (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['36'])).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      ((~ (l1_struct_0 @ sk_B_1)
% 0.21/0.49        | (v2_struct_0 @ sk_B_1)
% 0.21/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | (v2_struct_0 @ sk_A)
% 0.21/0.49        | (v2_struct_0 @ sk_B_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['5', '37'])).
% 0.21/0.49  thf('39', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A)
% 0.21/0.49        | (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | (v2_struct_0 @ sk_B_1)
% 0.21/0.49        | ~ (l1_struct_0 @ sk_B_1))),
% 0.21/0.49      inference('simplify', [status(thm)], ['38'])).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      ((~ (l1_orders_2 @ sk_B_1)
% 0.21/0.49        | (v2_struct_0 @ sk_B_1)
% 0.21/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '39'])).
% 0.21/0.49  thf('41', plain, ((l1_orders_2 @ sk_B_1)),
% 0.21/0.49      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.49  thf('42', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_B_1)
% 0.21/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.49  thf('43', plain, (~ (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('44', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A)
% 0.21/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | (v2_struct_0 @ sk_B_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.49  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('46', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_B_1) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('clc', [status(thm)], ['44', '45'])).
% 0.21/0.49  thf('47', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('48', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('clc', [status(thm)], ['46', '47'])).
% 0.21/0.49  thf(fc2_struct_0, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.49       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.49  thf('49', plain,
% 0.21/0.49      (![X2 : $i]:
% 0.21/0.49         (~ (v1_xboole_0 @ (u1_struct_0 @ X2))
% 0.21/0.49          | ~ (l1_struct_0 @ X2)
% 0.21/0.49          | (v2_struct_0 @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.49  thf('50', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.49  thf('51', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('52', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['50', '51'])).
% 0.21/0.49  thf('53', plain, ($false), inference('demod', [status(thm)], ['0', '52'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
