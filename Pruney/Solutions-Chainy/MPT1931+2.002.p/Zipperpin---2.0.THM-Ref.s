%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VjXRG300ea

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:57 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 675 expanded)
%              Number of leaves         :   22 ( 187 expanded)
%              Depth                    :   43
%              Number of atoms          : 1456 (10729 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

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
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( m1_subset_1 @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

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
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( l1_waybel_0 @ X7 @ X8 )
      | ( m1_subset_1 @ ( sk_E @ X9 @ X10 @ X7 @ X8 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X7 ) )
      | ( r1_waybel_0 @ X8 @ X7 @ X10 )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_waybel_0 @ X13 @ X14 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ( m1_subset_1 @ ( k2_waybel_0 @ X14 @ X13 @ X15 ) @ ( u1_struct_0 @ X14 ) ) ) ),
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

thf('20',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

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
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( l1_waybel_0 @ X7 @ X8 )
      | ~ ( r2_hidden @ ( k2_waybel_0 @ X8 @ X7 @ ( sk_E @ X9 @ X10 @ X7 @ X8 ) ) @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X7 ) )
      | ( r1_waybel_0 @ X8 @ X7 @ X10 )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
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

thf('32',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('33',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_xboole_0 @ X5 )
      | ( m1_subset_1 @ X5 @ X4 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('35',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('37',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_xboole_0 @ X5 )
      | ( m1_subset_1 @ X5 @ X4 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('38',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( l1_waybel_0 @ X7 @ X8 )
      | ( m1_subset_1 @ ( sk_E @ X9 @ X10 @ X7 @ X8 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X7 ) )
      | ( r1_waybel_0 @ X8 @ X7 @ X10 )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d11_waybel_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v2_struct_0 @ X2 )
      | ~ ( l1_struct_0 @ X2 )
      | ( r1_waybel_0 @ X2 @ X0 @ X3 )
      | ( m1_subset_1 @ ( sk_E @ X1 @ X3 @ X0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_waybel_0 @ X0 @ X2 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ X0 )
      | ( m1_subset_1 @ ( sk_E @ X2 @ X1 @ sk_B_1 @ X0 ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_waybel_0 @ X0 @ sk_B_1 @ X1 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( r1_waybel_0 @ X0 @ sk_B_1 @ X1 )
      | ( m1_subset_1 @ ( sk_E @ X2 @ X1 @ sk_B_1 @ X0 ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( l1_waybel_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_E @ X1 @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','41'])).

thf('43',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_E @ X1 @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( m1_subset_1 @ ( sk_E @ X1 @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X5 @ X4 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( sk_E @ X1 @ X0 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_E @ X1 @ X0 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ ( sk_E @ X1 @ X0 @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('52',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_xboole_0 @ X5 )
      | ( m1_subset_1 @ X5 @ X4 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('53',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_waybel_0 @ X13 @ X14 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ( m1_subset_1 @ ( k2_waybel_0 @ X14 @ X13 @ X15 ) @ ( u1_struct_0 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_waybel_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ ( k2_waybel_0 @ X2 @ X0 @ X1 ) @ ( u1_struct_0 @ X2 ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( l1_struct_0 @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_waybel_0 @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_waybel_0 @ X0 @ sk_B_1 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ ( k2_waybel_0 @ X0 @ sk_B_1 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','56'])).

thf('58',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( l1_waybel_0 @ X7 @ X8 )
      | ~ ( r2_hidden @ ( k2_waybel_0 @ X8 @ X7 @ ( sk_E @ X9 @ X10 @ X7 @ X8 ) ) @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X7 ) )
      | ( r1_waybel_0 @ X8 @ X7 @ X10 )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d11_waybel_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ ( sk_E @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ ( sk_E @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ ( sk_E @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['49','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['32','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','77'])).

thf('79',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('81',plain,(
    ! [X6: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ X0 ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['79','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v2_struct_0 @ sk_B_1 ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    $false ),
    inference(demod,[status(thm)],['0','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VjXRG300ea
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:55:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 64 iterations in 0.057s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.52  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 0.20/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.52  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.20/0.52  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.20/0.52  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.52  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.52  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.20/0.52  thf(t29_yellow_6, conjecture,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.20/0.52             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.52           ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i]:
% 0.20/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.52          ( ![B:$i]:
% 0.20/0.52            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.20/0.52                ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.52              ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t29_yellow_6])).
% 0.20/0.52  thf('0', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(d1_xboole_0, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.52  thf(d2_subset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( v1_xboole_0 @ A ) =>
% 0.20/0.52         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.20/0.52       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.52         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X3 : $i, X4 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X3 @ X4)
% 0.20/0.52          | (m1_subset_1 @ X3 @ X4)
% 0.20/0.52          | (v1_xboole_0 @ X4))),
% 0.20/0.52      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ X0)
% 0.20/0.52          | (v1_xboole_0 @ X0)
% 0.20/0.52          | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (![X0 : $i]: ((m1_subset_1 @ (sk_B @ X0) @ X0) | (v1_xboole_0 @ X0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.52  thf('5', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('6', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X0 : $i]: ((m1_subset_1 @ (sk_B @ X0) @ X0) | (v1_xboole_0 @ X0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.52  thf(d11_waybel_0, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( r1_waybel_0 @ A @ B @ C ) <=>
% 0.20/0.52               ( ?[D:$i]:
% 0.20/0.52                 ( ( ![E:$i]:
% 0.20/0.52                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.52                       ( ( r1_orders_2 @ B @ D @ E ) =>
% 0.20/0.52                         ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) ) ) ) & 
% 0.20/0.52                   ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X7)
% 0.20/0.52          | ~ (l1_waybel_0 @ X7 @ X8)
% 0.20/0.52          | (m1_subset_1 @ (sk_E @ X9 @ X10 @ X7 @ X8) @ (u1_struct_0 @ X7))
% 0.20/0.52          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X7))
% 0.20/0.52          | (r1_waybel_0 @ X8 @ X7 @ X10)
% 0.20/0.52          | ~ (l1_struct_0 @ X8)
% 0.20/0.52          | (v2_struct_0 @ X8))),
% 0.20/0.52      inference('cnf', [status(esa)], [d11_waybel_0])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.20/0.52          | (v2_struct_0 @ X1)
% 0.20/0.52          | ~ (l1_struct_0 @ X1)
% 0.20/0.52          | (r1_waybel_0 @ X1 @ X0 @ X2)
% 0.20/0.52          | (m1_subset_1 @ 
% 0.20/0.52             (sk_E @ (sk_B @ (u1_struct_0 @ X0)) @ X2 @ X0 @ X1) @ 
% 0.20/0.52             (u1_struct_0 @ X0))
% 0.20/0.52          | ~ (l1_waybel_0 @ X0 @ X1)
% 0.20/0.52          | (v2_struct_0 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_B_1)
% 0.20/0.52          | (m1_subset_1 @ 
% 0.20/0.52             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.20/0.52             (u1_struct_0 @ sk_B_1))
% 0.20/0.52          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.20/0.52          | ~ (l1_struct_0 @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ sk_A)
% 0.20/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['6', '9'])).
% 0.20/0.52  thf('11', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_B_1)
% 0.20/0.52          | (m1_subset_1 @ 
% 0.20/0.52             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.20/0.52             (u1_struct_0 @ sk_B_1))
% 0.20/0.52          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.20/0.52          | (v2_struct_0 @ sk_A)
% 0.20/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.20/0.52      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.52  thf(dt_k2_waybel_0, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.20/0.52         ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) & 
% 0.20/0.52         ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.52       ( m1_subset_1 @ ( k2_waybel_0 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ))).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.52         (~ (l1_waybel_0 @ X13 @ X14)
% 0.20/0.52          | (v2_struct_0 @ X13)
% 0.20/0.52          | ~ (l1_struct_0 @ X14)
% 0.20/0.52          | (v2_struct_0 @ X14)
% 0.20/0.52          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 0.20/0.52          | (m1_subset_1 @ (k2_waybel_0 @ X14 @ X13 @ X15) @ 
% 0.20/0.52             (u1_struct_0 @ X14)))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k2_waybel_0])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.20/0.52          | (v2_struct_0 @ sk_A)
% 0.20/0.52          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.20/0.52          | (v2_struct_0 @ sk_B_1)
% 0.20/0.52          | (m1_subset_1 @ 
% 0.20/0.52             (k2_waybel_0 @ X1 @ sk_B_1 @ 
% 0.20/0.52              (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A)) @ 
% 0.20/0.52             (u1_struct_0 @ X1))
% 0.20/0.52          | (v2_struct_0 @ X1)
% 0.20/0.52          | ~ (l1_struct_0 @ X1)
% 0.20/0.52          | (v2_struct_0 @ sk_B_1)
% 0.20/0.52          | ~ (l1_waybel_0 @ sk_B_1 @ X1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (l1_waybel_0 @ sk_B_1 @ X1)
% 0.20/0.52          | ~ (l1_struct_0 @ X1)
% 0.20/0.52          | (v2_struct_0 @ X1)
% 0.20/0.52          | (m1_subset_1 @ 
% 0.20/0.52             (k2_waybel_0 @ X1 @ sk_B_1 @ 
% 0.20/0.52              (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A)) @ 
% 0.20/0.52             (u1_struct_0 @ X1))
% 0.20/0.52          | (v2_struct_0 @ sk_B_1)
% 0.20/0.52          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.20/0.52          | (v2_struct_0 @ sk_A)
% 0.20/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.20/0.52          | (v2_struct_0 @ sk_A)
% 0.20/0.52          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.20/0.52          | (v2_struct_0 @ sk_B_1)
% 0.20/0.52          | (m1_subset_1 @ 
% 0.20/0.52             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.20/0.52              (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A)) @ 
% 0.20/0.52             (u1_struct_0 @ sk_A))
% 0.20/0.52          | (v2_struct_0 @ sk_A)
% 0.20/0.52          | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['5', '15'])).
% 0.20/0.52  thf('17', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.20/0.52          | (v2_struct_0 @ sk_A)
% 0.20/0.52          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.20/0.52          | (v2_struct_0 @ sk_B_1)
% 0.20/0.52          | (m1_subset_1 @ 
% 0.20/0.52             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.20/0.52              (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A)) @ 
% 0.20/0.52             (u1_struct_0 @ sk_A))
% 0.20/0.52          | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((m1_subset_1 @ 
% 0.20/0.52           (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.20/0.52            (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A)) @ 
% 0.20/0.52           (u1_struct_0 @ sk_A))
% 0.20/0.52          | (v2_struct_0 @ sk_B_1)
% 0.20/0.52          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.20/0.52          | (v2_struct_0 @ sk_A)
% 0.20/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (![X3 : $i, X4 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X3 @ X4)
% 0.20/0.52          | (r2_hidden @ X3 @ X4)
% 0.20/0.52          | (v1_xboole_0 @ X4))),
% 0.20/0.52      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.20/0.52          | (v2_struct_0 @ sk_A)
% 0.20/0.52          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.20/0.52          | (v2_struct_0 @ sk_B_1)
% 0.20/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | (r2_hidden @ 
% 0.20/0.52             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.20/0.52              (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A)) @ 
% 0.20/0.52             (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X7)
% 0.20/0.52          | ~ (l1_waybel_0 @ X7 @ X8)
% 0.20/0.52          | ~ (r2_hidden @ 
% 0.20/0.52               (k2_waybel_0 @ X8 @ X7 @ (sk_E @ X9 @ X10 @ X7 @ X8)) @ X10)
% 0.20/0.52          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X7))
% 0.20/0.52          | (r1_waybel_0 @ X8 @ X7 @ X10)
% 0.20/0.52          | ~ (l1_struct_0 @ X8)
% 0.20/0.52          | (v2_struct_0 @ X8))),
% 0.20/0.52      inference('cnf', [status(esa)], [d11_waybel_0])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | (v2_struct_0 @ sk_B_1)
% 0.20/0.52        | (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | (v2_struct_0 @ sk_A)
% 0.20/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.20/0.52        | (v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (l1_struct_0 @ sk_A)
% 0.20/0.52        | (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | ~ (m1_subset_1 @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ 
% 0.20/0.52             (u1_struct_0 @ sk_B_1))
% 0.20/0.52        | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.20/0.52        | (v2_struct_0 @ sk_B_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.52  thf('24', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('25', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | (v2_struct_0 @ sk_B_1)
% 0.20/0.52        | (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | (v2_struct_0 @ sk_A)
% 0.20/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.20/0.52        | (v2_struct_0 @ sk_A)
% 0.20/0.52        | (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | ~ (m1_subset_1 @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ 
% 0.20/0.52             (u1_struct_0 @ sk_B_1))
% 0.20/0.52        | (v2_struct_0 @ sk_B_1))),
% 0.20/0.52      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      ((~ (m1_subset_1 @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ 
% 0.20/0.52           (u1_struct_0 @ sk_B_1))
% 0.20/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.20/0.52        | (v2_struct_0 @ sk_A)
% 0.20/0.52        | (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | (v2_struct_0 @ sk_B_1)
% 0.20/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.20/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | (v2_struct_0 @ sk_B_1)
% 0.20/0.52        | (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | (v2_struct_0 @ sk_A)
% 0.20/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['4', '27'])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | (v2_struct_0 @ sk_B_1)
% 0.20/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.52  thf('30', plain, (~ (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.20/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | (v2_struct_0 @ sk_B_1)
% 0.20/0.52        | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.20/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | (v2_struct_0 @ sk_B_1)
% 0.20/0.52        | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      (![X4 : $i, X5 : $i]:
% 0.20/0.52         (~ (v1_xboole_0 @ X5) | (m1_subset_1 @ X5 @ X4) | ~ (v1_xboole_0 @ X4))),
% 0.20/0.52      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.20/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | (v2_struct_0 @ sk_B_1)
% 0.20/0.52        | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.52  thf('35', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.20/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | (v2_struct_0 @ sk_B_1)
% 0.20/0.52        | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      (![X4 : $i, X5 : $i]:
% 0.20/0.52         (~ (v1_xboole_0 @ X5) | (m1_subset_1 @ X5 @ X4) | ~ (v1_xboole_0 @ X4))),
% 0.20/0.52      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X7)
% 0.20/0.52          | ~ (l1_waybel_0 @ X7 @ X8)
% 0.20/0.52          | (m1_subset_1 @ (sk_E @ X9 @ X10 @ X7 @ X8) @ (u1_struct_0 @ X7))
% 0.20/0.52          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X7))
% 0.20/0.52          | (r1_waybel_0 @ X8 @ X7 @ X10)
% 0.20/0.52          | ~ (l1_struct_0 @ X8)
% 0.20/0.52          | (v2_struct_0 @ X8))),
% 0.20/0.52      inference('cnf', [status(esa)], [d11_waybel_0])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.52         (~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.20/0.52          | ~ (v1_xboole_0 @ X1)
% 0.20/0.52          | (v2_struct_0 @ X2)
% 0.20/0.52          | ~ (l1_struct_0 @ X2)
% 0.20/0.52          | (r1_waybel_0 @ X2 @ X0 @ X3)
% 0.20/0.52          | (m1_subset_1 @ (sk_E @ X1 @ X3 @ X0 @ X2) @ (u1_struct_0 @ X0))
% 0.20/0.52          | ~ (l1_waybel_0 @ X0 @ X2)
% 0.20/0.52          | (v2_struct_0 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ sk_B_1)
% 0.20/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | (v2_struct_0 @ sk_B_1)
% 0.20/0.52          | ~ (l1_waybel_0 @ sk_B_1 @ X0)
% 0.20/0.52          | (m1_subset_1 @ (sk_E @ X2 @ X1 @ sk_B_1 @ X0) @ 
% 0.20/0.52             (u1_struct_0 @ sk_B_1))
% 0.20/0.52          | (r1_waybel_0 @ X0 @ sk_B_1 @ X1)
% 0.20/0.52          | ~ (l1_struct_0 @ X0)
% 0.20/0.52          | (v2_struct_0 @ X0)
% 0.20/0.52          | ~ (v1_xboole_0 @ X2))),
% 0.20/0.52      inference('sup-', [status(thm)], ['36', '39'])).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (v1_xboole_0 @ X2)
% 0.20/0.52          | (v2_struct_0 @ X0)
% 0.20/0.52          | ~ (l1_struct_0 @ X0)
% 0.20/0.52          | (r1_waybel_0 @ X0 @ sk_B_1 @ X1)
% 0.20/0.52          | (m1_subset_1 @ (sk_E @ X2 @ X1 @ sk_B_1 @ X0) @ 
% 0.20/0.52             (u1_struct_0 @ sk_B_1))
% 0.20/0.52          | ~ (l1_waybel_0 @ sk_B_1 @ X0)
% 0.20/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | (v2_struct_0 @ sk_B_1)
% 0.20/0.52          | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('simplify', [status(thm)], ['40'])).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ sk_B_1)
% 0.20/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | (m1_subset_1 @ (sk_E @ X1 @ X0 @ sk_B_1 @ sk_A) @ 
% 0.20/0.52             (u1_struct_0 @ sk_B_1))
% 0.20/0.52          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.20/0.52          | ~ (l1_struct_0 @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ sk_A)
% 0.20/0.52          | ~ (v1_xboole_0 @ X1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['35', '41'])).
% 0.20/0.52  thf('43', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('44', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ sk_B_1)
% 0.20/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | (m1_subset_1 @ (sk_E @ X1 @ X0 @ sk_B_1 @ sk_A) @ 
% 0.20/0.52             (u1_struct_0 @ sk_B_1))
% 0.20/0.52          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.20/0.52          | (v2_struct_0 @ sk_A)
% 0.20/0.52          | ~ (v1_xboole_0 @ X1))),
% 0.20/0.52      inference('demod', [status(thm)], ['42', '43'])).
% 0.20/0.52  thf('45', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (v1_xboole_0 @ X1)
% 0.20/0.52          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.20/0.52          | (m1_subset_1 @ (sk_E @ X1 @ X0 @ sk_B_1 @ sk_A) @ 
% 0.20/0.52             (u1_struct_0 @ sk_B_1))
% 0.20/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | (v2_struct_0 @ sk_B_1)
% 0.20/0.52          | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('simplify', [status(thm)], ['44'])).
% 0.20/0.52  thf('46', plain,
% 0.20/0.52      (![X4 : $i, X5 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X5 @ X4) | (v1_xboole_0 @ X5) | ~ (v1_xboole_0 @ X4))),
% 0.20/0.52      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.52  thf('47', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ sk_B_1)
% 0.20/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.20/0.52          | ~ (v1_xboole_0 @ X1)
% 0.20/0.52          | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.20/0.52          | (v1_xboole_0 @ (sk_E @ X1 @ X0 @ sk_B_1 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ sk_B_1)
% 0.20/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | (v1_xboole_0 @ (sk_E @ X1 @ X0 @ sk_B_1 @ sk_A))
% 0.20/0.52          | ~ (v1_xboole_0 @ X1)
% 0.20/0.52          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.20/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | (v2_struct_0 @ sk_B_1)
% 0.20/0.52          | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['34', '47'])).
% 0.20/0.52  thf('49', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.20/0.52          | ~ (v1_xboole_0 @ X1)
% 0.20/0.52          | (v1_xboole_0 @ (sk_E @ X1 @ X0 @ sk_B_1 @ sk_A))
% 0.20/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | (v2_struct_0 @ sk_B_1)
% 0.20/0.52          | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('simplify', [status(thm)], ['48'])).
% 0.20/0.52  thf('50', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('51', plain,
% 0.20/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.20/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | (v2_struct_0 @ sk_B_1)
% 0.20/0.52        | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.52  thf('52', plain,
% 0.20/0.52      (![X4 : $i, X5 : $i]:
% 0.20/0.52         (~ (v1_xboole_0 @ X5) | (m1_subset_1 @ X5 @ X4) | ~ (v1_xboole_0 @ X4))),
% 0.20/0.52      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.52  thf('53', plain,
% 0.20/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.52         (~ (l1_waybel_0 @ X13 @ X14)
% 0.20/0.52          | (v2_struct_0 @ X13)
% 0.20/0.52          | ~ (l1_struct_0 @ X14)
% 0.20/0.52          | (v2_struct_0 @ X14)
% 0.20/0.52          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 0.20/0.52          | (m1_subset_1 @ (k2_waybel_0 @ X14 @ X13 @ X15) @ 
% 0.20/0.52             (u1_struct_0 @ X14)))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k2_waybel_0])).
% 0.20/0.52  thf('54', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.20/0.52          | ~ (v1_xboole_0 @ X1)
% 0.20/0.52          | (m1_subset_1 @ (k2_waybel_0 @ X2 @ X0 @ X1) @ (u1_struct_0 @ X2))
% 0.20/0.52          | (v2_struct_0 @ X2)
% 0.20/0.52          | ~ (l1_struct_0 @ X2)
% 0.20/0.52          | (v2_struct_0 @ X0)
% 0.20/0.52          | ~ (l1_waybel_0 @ X0 @ X2))),
% 0.20/0.52      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.52  thf('55', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ sk_B_1)
% 0.20/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | ~ (l1_waybel_0 @ sk_B_1 @ X0)
% 0.20/0.52          | (v2_struct_0 @ sk_B_1)
% 0.20/0.52          | ~ (l1_struct_0 @ X0)
% 0.20/0.52          | (v2_struct_0 @ X0)
% 0.20/0.52          | (m1_subset_1 @ (k2_waybel_0 @ X0 @ sk_B_1 @ X1) @ 
% 0.20/0.52             (u1_struct_0 @ X0))
% 0.20/0.52          | ~ (v1_xboole_0 @ X1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['51', '54'])).
% 0.20/0.52  thf('56', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (v1_xboole_0 @ X1)
% 0.20/0.52          | (m1_subset_1 @ (k2_waybel_0 @ X0 @ sk_B_1 @ X1) @ 
% 0.20/0.52             (u1_struct_0 @ X0))
% 0.20/0.52          | (v2_struct_0 @ X0)
% 0.20/0.52          | ~ (l1_struct_0 @ X0)
% 0.20/0.52          | ~ (l1_waybel_0 @ sk_B_1 @ X0)
% 0.20/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | (v2_struct_0 @ sk_B_1)
% 0.20/0.52          | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('simplify', [status(thm)], ['55'])).
% 0.20/0.52  thf('57', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ sk_B_1)
% 0.20/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | ~ (l1_struct_0 @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ sk_A)
% 0.20/0.52          | (m1_subset_1 @ (k2_waybel_0 @ sk_A @ sk_B_1 @ X0) @ 
% 0.20/0.52             (u1_struct_0 @ sk_A))
% 0.20/0.52          | ~ (v1_xboole_0 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['50', '56'])).
% 0.20/0.52  thf('58', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('59', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ sk_B_1)
% 0.20/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | (v2_struct_0 @ sk_A)
% 0.20/0.52          | (m1_subset_1 @ (k2_waybel_0 @ sk_A @ sk_B_1 @ X0) @ 
% 0.20/0.52             (u1_struct_0 @ sk_A))
% 0.20/0.52          | ~ (v1_xboole_0 @ X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['57', '58'])).
% 0.20/0.52  thf('60', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v1_xboole_0 @ X0)
% 0.20/0.52          | (m1_subset_1 @ (k2_waybel_0 @ sk_A @ sk_B_1 @ X0) @ 
% 0.20/0.52             (u1_struct_0 @ sk_A))
% 0.20/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | (v2_struct_0 @ sk_B_1)
% 0.20/0.52          | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('simplify', [status(thm)], ['59'])).
% 0.20/0.52  thf('61', plain,
% 0.20/0.52      (![X3 : $i, X4 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X3 @ X4)
% 0.20/0.52          | (r2_hidden @ X3 @ X4)
% 0.20/0.52          | (v1_xboole_0 @ X4))),
% 0.20/0.52      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.52  thf('62', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ sk_B_1)
% 0.20/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | ~ (v1_xboole_0 @ X0)
% 0.20/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | (r2_hidden @ (k2_waybel_0 @ sk_A @ sk_B_1 @ X0) @ 
% 0.20/0.52             (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.52  thf('63', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r2_hidden @ (k2_waybel_0 @ sk_A @ sk_B_1 @ X0) @ 
% 0.20/0.52           (u1_struct_0 @ sk_A))
% 0.20/0.52          | ~ (v1_xboole_0 @ X0)
% 0.20/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | (v2_struct_0 @ sk_B_1)
% 0.20/0.52          | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('simplify', [status(thm)], ['62'])).
% 0.20/0.52  thf('64', plain,
% 0.20/0.52      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X7)
% 0.20/0.52          | ~ (l1_waybel_0 @ X7 @ X8)
% 0.20/0.52          | ~ (r2_hidden @ 
% 0.20/0.52               (k2_waybel_0 @ X8 @ X7 @ (sk_E @ X9 @ X10 @ X7 @ X8)) @ X10)
% 0.20/0.52          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X7))
% 0.20/0.52          | (r1_waybel_0 @ X8 @ X7 @ X10)
% 0.20/0.52          | ~ (l1_struct_0 @ X8)
% 0.20/0.52          | (v2_struct_0 @ X8))),
% 0.20/0.52      inference('cnf', [status(esa)], [d11_waybel_0])).
% 0.20/0.52  thf('65', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ sk_B_1)
% 0.20/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | ~ (v1_xboole_0 @ (sk_E @ X0 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ sk_A))
% 0.20/0.52          | (v2_struct_0 @ sk_A)
% 0.20/0.52          | ~ (l1_struct_0 @ sk_A)
% 0.20/0.52          | (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.20/0.52          | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ sk_B_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.52  thf('66', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('67', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('68', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ sk_B_1)
% 0.20/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | ~ (v1_xboole_0 @ (sk_E @ X0 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ sk_A))
% 0.20/0.52          | (v2_struct_0 @ sk_A)
% 0.20/0.52          | (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.20/0.52          | (v2_struct_0 @ sk_B_1))),
% 0.20/0.52      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.20/0.52  thf('69', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.20/0.52          | (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | ~ (v1_xboole_0 @ (sk_E @ X0 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ sk_A))
% 0.20/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | (v2_struct_0 @ sk_B_1)
% 0.20/0.52          | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('simplify', [status(thm)], ['68'])).
% 0.20/0.52  thf('70', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ sk_B_1)
% 0.20/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | ~ (v1_xboole_0 @ X0)
% 0.20/0.52          | (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | (v2_struct_0 @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ sk_B_1)
% 0.20/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['49', '69'])).
% 0.20/0.52  thf('71', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.20/0.52          | (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | ~ (v1_xboole_0 @ X0)
% 0.20/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | (v2_struct_0 @ sk_B_1)
% 0.20/0.52          | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('simplify', [status(thm)], ['70'])).
% 0.20/0.52  thf('72', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.20/0.52          | ~ (v1_xboole_0 @ X0)
% 0.20/0.52          | (v2_struct_0 @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ sk_B_1)
% 0.20/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | ~ (v1_xboole_0 @ X0)
% 0.20/0.52          | (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['33', '71'])).
% 0.20/0.52  thf('73', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | (v2_struct_0 @ sk_B_1)
% 0.20/0.52          | (v2_struct_0 @ sk_A)
% 0.20/0.52          | ~ (v1_xboole_0 @ X0)
% 0.20/0.52          | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['72'])).
% 0.20/0.52  thf('74', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ sk_B_1)
% 0.20/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | ~ (v1_xboole_0 @ X0)
% 0.20/0.52          | (v2_struct_0 @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ sk_B_1)
% 0.20/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['32', '73'])).
% 0.20/0.52  thf('75', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | ~ (v1_xboole_0 @ X0)
% 0.20/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | (v2_struct_0 @ sk_B_1)
% 0.20/0.52          | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('simplify', [status(thm)], ['74'])).
% 0.20/0.52  thf('76', plain, (~ (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('77', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ sk_B_1)
% 0.20/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | ~ (v1_xboole_0 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['75', '76'])).
% 0.20/0.52  thf('78', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | (v2_struct_0 @ sk_B_1)
% 0.20/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | (v2_struct_0 @ sk_B_1)
% 0.20/0.52        | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['31', '77'])).
% 0.20/0.52  thf('79', plain,
% 0.20/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | (v2_struct_0 @ sk_B_1)
% 0.20/0.52        | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('simplify', [status(thm)], ['78'])).
% 0.20/0.52  thf('80', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ sk_B_1)
% 0.20/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | ~ (v1_xboole_0 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['75', '76'])).
% 0.20/0.52  thf(fc2_struct_0, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.52       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.52  thf('81', plain,
% 0.20/0.52      (![X6 : $i]:
% 0.20/0.52         (~ (v1_xboole_0 @ (u1_struct_0 @ X6))
% 0.20/0.52          | ~ (l1_struct_0 @ X6)
% 0.20/0.52          | (v2_struct_0 @ X6))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.52  thf('82', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v1_xboole_0 @ X0)
% 0.20/0.52          | (v2_struct_0 @ sk_B_1)
% 0.20/0.52          | (v2_struct_0 @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ sk_A)
% 0.20/0.52          | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['80', '81'])).
% 0.20/0.52  thf('83', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('84', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v1_xboole_0 @ X0)
% 0.20/0.52          | (v2_struct_0 @ sk_B_1)
% 0.20/0.52          | (v2_struct_0 @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['82', '83'])).
% 0.20/0.52  thf('85', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B_1) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['84'])).
% 0.20/0.52  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('87', plain,
% 0.20/0.52      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v2_struct_0 @ sk_B_1))),
% 0.20/0.52      inference('clc', [status(thm)], ['85', '86'])).
% 0.20/0.52  thf('88', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('89', plain, (![X0 : $i]: ~ (v1_xboole_0 @ X0)),
% 0.20/0.52      inference('clc', [status(thm)], ['87', '88'])).
% 0.20/0.52  thf('90', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B_1))),
% 0.20/0.52      inference('clc', [status(thm)], ['79', '89'])).
% 0.20/0.52  thf('91', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('92', plain, ((v2_struct_0 @ sk_B_1)),
% 0.20/0.52      inference('clc', [status(thm)], ['90', '91'])).
% 0.20/0.52  thf('93', plain, ($false), inference('demod', [status(thm)], ['0', '92'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
