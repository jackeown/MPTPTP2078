%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LtDVy22cfn

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 108 expanded)
%              Number of leaves         :   26 (  42 expanded)
%              Depth                    :   26
%              Number of atoms          :  711 (1204 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

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

thf('8',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( l1_waybel_0 @ X9 @ X10 )
      | ( m1_subset_1 @ ( sk_E @ X11 @ X12 @ X9 @ X10 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X9 ) )
      | ( r1_waybel_0 @ X10 @ X9 @ X12 )
      | ~ ( l1_struct_0 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d11_waybel_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r1_waybel_0 @ X1 @ X0 @ X2 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X2 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(dt_k2_waybel_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ~ ( v2_struct_0 @ B )
        & ( l1_waybel_0 @ B @ A )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) )
     => ( m1_subset_1 @ ( k2_waybel_0 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( l1_waybel_0 @ X15 @ X16 )
      | ( v2_struct_0 @ X15 )
      | ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X15 ) )
      | ( m1_subset_1 @ ( k2_waybel_0 @ X16 @ X15 @ X17 ) @ ( u1_struct_0 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_waybel_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( k2_waybel_0 @ X1 @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) @ ( u1_struct_0 @ X1 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_waybel_0 @ sk_B_1 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( m1_subset_1 @ ( k2_waybel_0 @ X1 @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) @ ( u1_struct_0 @ X1 ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','15'])).

thf('17',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( l1_waybel_0 @ X9 @ X10 )
      | ~ ( r2_hidden @ ( k2_waybel_0 @ X10 @ X9 @ ( sk_E @ X11 @ X12 @ X9 @ X10 ) ) @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X9 ) )
      | ( r1_waybel_0 @ X10 @ X9 @ X12 )
      | ~ ( l1_struct_0 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d11_waybel_0])).

thf('23',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ~ ( m1_subset_1 @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['4','27'])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('32',plain,(
    ! [X7: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( l1_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ~ ( l1_orders_2 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','34'])).

thf('36',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ( l1_orders_2 @ B ) ) ) )).

thf('37',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_waybel_0 @ X18 @ X19 )
      | ( l1_orders_2 @ X18 )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_0])).

thf('38',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( l1_orders_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X7: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['0','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LtDVy22cfn
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:38:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 43 iterations in 0.031s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.49  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.49  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.21/0.49  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.21/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.49  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 0.21/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.49  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.49  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.21/0.49  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.49  thf(t29_yellow_6, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.49             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.49           ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.49                ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.49              ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t29_yellow_6])).
% 0.21/0.49  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(dt_l1_orders_2, axiom,
% 0.21/0.49    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.49  thf('1', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_orders_2 @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.21/0.49  thf(d1_xboole_0, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.49  thf(t1_subset, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i]: ((m1_subset_1 @ X3 @ X4) | ~ (r2_hidden @ X3 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [t1_subset])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.49  thf('5', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('6', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.49  thf(d11_waybel_0, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( r1_waybel_0 @ A @ B @ C ) <=>
% 0.21/0.49               ( ?[D:$i]:
% 0.21/0.49                 ( ( ![E:$i]:
% 0.21/0.49                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.49                       ( ( r1_orders_2 @ B @ D @ E ) =>
% 0.21/0.49                         ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) ) ) ) & 
% 0.21/0.49                   ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.49         ((v2_struct_0 @ X9)
% 0.21/0.49          | ~ (l1_waybel_0 @ X9 @ X10)
% 0.21/0.49          | (m1_subset_1 @ (sk_E @ X11 @ X12 @ X9 @ X10) @ (u1_struct_0 @ X9))
% 0.21/0.49          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X9))
% 0.21/0.49          | (r1_waybel_0 @ X10 @ X9 @ X12)
% 0.21/0.49          | ~ (l1_struct_0 @ X10)
% 0.21/0.49          | (v2_struct_0 @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [d11_waybel_0])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.21/0.49          | (v2_struct_0 @ X1)
% 0.21/0.49          | ~ (l1_struct_0 @ X1)
% 0.21/0.49          | (r1_waybel_0 @ X1 @ X0 @ X2)
% 0.21/0.49          | (m1_subset_1 @ 
% 0.21/0.49             (sk_E @ (sk_B @ (u1_struct_0 @ X0)) @ X2 @ X0 @ X1) @ 
% 0.21/0.49             (u1_struct_0 @ X0))
% 0.21/0.49          | ~ (l1_waybel_0 @ X0 @ X1)
% 0.21/0.49          | (v2_struct_0 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_struct_0 @ sk_B_1)
% 0.21/0.49          | (m1_subset_1 @ 
% 0.21/0.49             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.21/0.49             (u1_struct_0 @ sk_B_1))
% 0.21/0.49          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.49          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.49          | (v2_struct_0 @ sk_A)
% 0.21/0.49          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['6', '9'])).
% 0.21/0.49  thf('11', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_struct_0 @ sk_B_1)
% 0.21/0.49          | (m1_subset_1 @ 
% 0.21/0.49             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.21/0.49             (u1_struct_0 @ sk_B_1))
% 0.21/0.49          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.49          | (v2_struct_0 @ sk_A)
% 0.21/0.49          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.49  thf(dt_k2_waybel_0, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.21/0.49         ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) & 
% 0.21/0.49         ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.49       ( m1_subset_1 @ ( k2_waybel_0 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ))).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.49         (~ (l1_waybel_0 @ X15 @ X16)
% 0.21/0.49          | (v2_struct_0 @ X15)
% 0.21/0.49          | ~ (l1_struct_0 @ X16)
% 0.21/0.49          | (v2_struct_0 @ X16)
% 0.21/0.49          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X15))
% 0.21/0.49          | (m1_subset_1 @ (k2_waybel_0 @ X16 @ X15 @ X17) @ 
% 0.21/0.49             (u1_struct_0 @ X16)))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k2_waybel_0])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.49          | (v2_struct_0 @ sk_A)
% 0.21/0.49          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.49          | (v2_struct_0 @ sk_B_1)
% 0.21/0.49          | (m1_subset_1 @ 
% 0.21/0.49             (k2_waybel_0 @ X1 @ sk_B_1 @ 
% 0.21/0.49              (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A)) @ 
% 0.21/0.49             (u1_struct_0 @ X1))
% 0.21/0.49          | (v2_struct_0 @ X1)
% 0.21/0.49          | ~ (l1_struct_0 @ X1)
% 0.21/0.49          | (v2_struct_0 @ sk_B_1)
% 0.21/0.49          | ~ (l1_waybel_0 @ sk_B_1 @ X1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (l1_waybel_0 @ sk_B_1 @ X1)
% 0.21/0.49          | ~ (l1_struct_0 @ X1)
% 0.21/0.49          | (v2_struct_0 @ X1)
% 0.21/0.49          | (m1_subset_1 @ 
% 0.21/0.49             (k2_waybel_0 @ X1 @ sk_B_1 @ 
% 0.21/0.49              (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A)) @ 
% 0.21/0.49             (u1_struct_0 @ X1))
% 0.21/0.49          | (v2_struct_0 @ sk_B_1)
% 0.21/0.49          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.49          | (v2_struct_0 @ sk_A)
% 0.21/0.49          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.49          | (v2_struct_0 @ sk_A)
% 0.21/0.49          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.49          | (v2_struct_0 @ sk_B_1)
% 0.21/0.49          | (m1_subset_1 @ 
% 0.21/0.49             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.21/0.49              (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A)) @ 
% 0.21/0.49             (u1_struct_0 @ sk_A))
% 0.21/0.49          | (v2_struct_0 @ sk_A)
% 0.21/0.49          | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['5', '15'])).
% 0.21/0.49  thf('17', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.49          | (v2_struct_0 @ sk_A)
% 0.21/0.49          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.49          | (v2_struct_0 @ sk_B_1)
% 0.21/0.49          | (m1_subset_1 @ 
% 0.21/0.49             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.21/0.49              (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A)) @ 
% 0.21/0.49             (u1_struct_0 @ sk_A))
% 0.21/0.49          | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((m1_subset_1 @ 
% 0.21/0.49           (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.21/0.49            (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A)) @ 
% 0.21/0.49           (u1_struct_0 @ sk_A))
% 0.21/0.49          | (v2_struct_0 @ sk_B_1)
% 0.21/0.49          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.49          | (v2_struct_0 @ sk_A)
% 0.21/0.49          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.49  thf(t2_subset, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.49       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (![X5 : $i, X6 : $i]:
% 0.21/0.49         ((r2_hidden @ X5 @ X6)
% 0.21/0.49          | (v1_xboole_0 @ X6)
% 0.21/0.49          | ~ (m1_subset_1 @ X5 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.49          | (v2_struct_0 @ sk_A)
% 0.21/0.49          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.49          | (v2_struct_0 @ sk_B_1)
% 0.21/0.49          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49          | (r2_hidden @ 
% 0.21/0.49             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.21/0.49              (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A)) @ 
% 0.21/0.49             (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.49         ((v2_struct_0 @ X9)
% 0.21/0.49          | ~ (l1_waybel_0 @ X9 @ X10)
% 0.21/0.49          | ~ (r2_hidden @ 
% 0.21/0.49               (k2_waybel_0 @ X10 @ X9 @ (sk_E @ X11 @ X12 @ X9 @ X10)) @ X12)
% 0.21/0.49          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X9))
% 0.21/0.49          | (r1_waybel_0 @ X10 @ X9 @ X12)
% 0.21/0.49          | ~ (l1_struct_0 @ X10)
% 0.21/0.49          | (v2_struct_0 @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [d11_waybel_0])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | (v2_struct_0 @ sk_B_1)
% 0.21/0.49        | (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | (v2_struct_0 @ sk_A)
% 0.21/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.49        | (v2_struct_0 @ sk_A)
% 0.21/0.49        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.49        | (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | ~ (m1_subset_1 @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ 
% 0.21/0.49             (u1_struct_0 @ sk_B_1))
% 0.21/0.49        | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.21/0.49        | (v2_struct_0 @ sk_B_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.49  thf('24', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('25', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | (v2_struct_0 @ sk_B_1)
% 0.21/0.49        | (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | (v2_struct_0 @ sk_A)
% 0.21/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.49        | (v2_struct_0 @ sk_A)
% 0.21/0.49        | (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | ~ (m1_subset_1 @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ 
% 0.21/0.49             (u1_struct_0 @ sk_B_1))
% 0.21/0.49        | (v2_struct_0 @ sk_B_1))),
% 0.21/0.49      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      ((~ (m1_subset_1 @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ 
% 0.21/0.49           (u1_struct_0 @ sk_B_1))
% 0.21/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.49        | (v2_struct_0 @ sk_A)
% 0.21/0.49        | (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | (v2_struct_0 @ sk_B_1)
% 0.21/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | (v2_struct_0 @ sk_B_1)
% 0.21/0.49        | (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | (v2_struct_0 @ sk_A)
% 0.21/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['4', '27'])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A)
% 0.21/0.49        | (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | (v2_struct_0 @ sk_B_1)
% 0.21/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.49  thf('30', plain, (~ (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | (v2_struct_0 @ sk_B_1)
% 0.21/0.49        | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.49  thf(fc2_struct_0, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.49       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      (![X7 : $i]:
% 0.21/0.49         (~ (v1_xboole_0 @ (u1_struct_0 @ X7))
% 0.21/0.49          | ~ (l1_struct_0 @ X7)
% 0.21/0.49          | (v2_struct_0 @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A)
% 0.21/0.49        | (v2_struct_0 @ sk_B_1)
% 0.21/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | (v2_struct_0 @ sk_B_1)
% 0.21/0.49        | ~ (l1_struct_0 @ sk_B_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      ((~ (l1_struct_0 @ sk_B_1)
% 0.21/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | (v2_struct_0 @ sk_B_1)
% 0.21/0.49        | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('simplify', [status(thm)], ['33'])).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      ((~ (l1_orders_2 @ sk_B_1)
% 0.21/0.49        | (v2_struct_0 @ sk_A)
% 0.21/0.49        | (v2_struct_0 @ sk_B_1)
% 0.21/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '34'])).
% 0.21/0.49  thf('36', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(dt_l1_waybel_0, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_struct_0 @ A ) =>
% 0.21/0.49       ( ![B:$i]: ( ( l1_waybel_0 @ B @ A ) => ( l1_orders_2 @ B ) ) ) ))).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      (![X18 : $i, X19 : $i]:
% 0.21/0.49         (~ (l1_waybel_0 @ X18 @ X19)
% 0.21/0.49          | (l1_orders_2 @ X18)
% 0.21/0.49          | ~ (l1_struct_0 @ X19))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_l1_waybel_0])).
% 0.21/0.49  thf('38', plain, ((~ (l1_struct_0 @ sk_A) | (l1_orders_2 @ sk_B_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.49  thf('39', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('40', plain, ((l1_orders_2 @ sk_B_1)),
% 0.21/0.49      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.49  thf('41', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A)
% 0.21/0.49        | (v2_struct_0 @ sk_B_1)
% 0.21/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['35', '40'])).
% 0.21/0.49  thf('42', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('43', plain,
% 0.21/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B_1))),
% 0.21/0.49      inference('clc', [status(thm)], ['41', '42'])).
% 0.21/0.49  thf('44', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('45', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('clc', [status(thm)], ['43', '44'])).
% 0.21/0.49  thf('46', plain,
% 0.21/0.49      (![X7 : $i]:
% 0.21/0.49         (~ (v1_xboole_0 @ (u1_struct_0 @ X7))
% 0.21/0.49          | ~ (l1_struct_0 @ X7)
% 0.21/0.49          | (v2_struct_0 @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.49  thf('47', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.49  thf('48', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('49', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['47', '48'])).
% 0.21/0.49  thf('50', plain, ($false), inference('demod', [status(thm)], ['0', '49'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
