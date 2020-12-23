%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pBQgF5gYvb

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:59 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 215 expanded)
%              Number of leaves         :   35 (  76 expanded)
%              Depth                    :   23
%              Number of atoms          : 1028 (2415 expanded)
%              Number of equality atoms :   12 (  28 expanded)
%              Maximal formula depth    :   20 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_waybel_0_type,type,(
    r2_waybel_0: $i > $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_yellow_6_type,type,(
    k4_yellow_6: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('2',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k6_subset_1 @ X10 @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k6_subset_1 @ X5 @ X6 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k6_subset_1 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['7'])).

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

thf('9',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( r2_waybel_0 @ A @ B @ C )
            <=> ~ ( r1_waybel_0 @ A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) )).

thf('10',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( l1_waybel_0 @ X24 @ X25 )
      | ( r1_waybel_0 @ X25 @ X24 @ ( k6_subset_1 @ ( u1_struct_0 @ X25 ) @ X26 ) )
      | ( r2_waybel_0 @ X25 @ X24 @ X26 )
      | ~ ( l1_struct_0 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t10_waybel_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t8_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i,D: $i] :
              ( ( r1_tarski @ C @ D )
             => ( ( ( r1_waybel_0 @ A @ B @ C )
                 => ( r1_waybel_0 @ A @ B @ D ) )
                & ( ( r2_waybel_0 @ A @ B @ C )
                 => ( r2_waybel_0 @ A @ B @ D ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( l1_waybel_0 @ X28 @ X29 )
      | ~ ( r1_waybel_0 @ X29 @ X28 @ X30 )
      | ( r1_waybel_0 @ X29 @ X28 @ X31 )
      | ~ ( r1_tarski @ X30 @ X31 )
      | ~ ( l1_struct_0 @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t8_waybel_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( r1_tarski @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ X1 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X1 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r1_tarski @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ X1 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_waybel_0 @ sk_A @ sk_B_1 @ X1 )
      | ~ ( r1_tarski @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','19'])).

thf('21',plain,(
    ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['24','25'])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('27',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('28',plain,(
    ! [X0: $i] :
      ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['24','25'])).

thf(existence_l1_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ? [B: $i] :
          ( l1_waybel_0 @ B @ A ) ) )).

thf('29',plain,(
    ! [X23: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X23 ) @ X23 )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[existence_l1_waybel_0])).

thf(dt_k4_yellow_6,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ( l1_waybel_0 @ B @ A ) )
     => ( m1_subset_1 @ ( k4_yellow_6 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('30',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_struct_0 @ X32 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_waybel_0 @ X33 @ X32 )
      | ( m1_subset_1 @ ( k4_yellow_6 @ X32 @ X33 ) @ ( u1_struct_0 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_yellow_6])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k4_yellow_6 @ X0 @ ( sk_B @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k4_yellow_6 @ X0 @ ( sk_B @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

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

thf('33',plain,(
    ! [X15: $i,X16: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( l1_waybel_0 @ X15 @ X16 )
      | ~ ( r2_waybel_0 @ X16 @ X15 @ X19 )
      | ( m1_subset_1 @ ( sk_E @ X20 @ X19 @ X15 @ X16 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( m1_subset_1 @ ( sk_E @ ( k4_yellow_6 @ X0 @ ( sk_B @ X0 ) ) @ X2 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_waybel_0 @ X1 @ X0 @ X2 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_waybel_0 @ X0 @ X1 )
      | ~ ( r2_waybel_0 @ X1 @ X0 @ X2 )
      | ( m1_subset_1 @ ( sk_E @ ( k4_yellow_6 @ X0 @ ( sk_B @ X0 ) ) @ X2 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','35'])).

thf('37',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['27','39'])).

thf('41',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ( l1_orders_2 @ B ) ) ) )).

thf('42',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_waybel_0 @ X21 @ X22 )
      | ( l1_orders_2 @ X21 )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_0])).

thf('43',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( l1_orders_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['40','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X15: $i,X16: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( l1_waybel_0 @ X15 @ X16 )
      | ~ ( r2_waybel_0 @ X16 @ X15 @ X19 )
      | ( r2_hidden @ ( k2_waybel_0 @ X16 @ X15 @ ( sk_E @ X20 @ X19 @ X15 @ X16 ) ) @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ sk_B_1 @ ( sk_E @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ X2 @ sk_B_1 @ X1 ) ) @ X2 )
      | ~ ( r2_waybel_0 @ X1 @ sk_B_1 @ X2 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ X1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X1 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','52'])).

thf('54',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X1 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X1 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X1 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k6_subset_1 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('62',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('63',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('64',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k6_subset_1 @ X10 @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('66',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k6_subset_1 @ X5 @ X6 ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k6_subset_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X0 @ X0 ) @ X1 )
      | ( r1_tarski @ ( k6_subset_1 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['61','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X0 @ X0 ) @ X1 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('71',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k6_subset_1 @ X10 @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('72',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k6_subset_1 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['72'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('74',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k6_subset_1 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X0 @ ( sk_D @ X0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k6_subset_1 @ ( k6_subset_1 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['69','75'])).

thf('77',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k6_subset_1 @ X5 @ X6 ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k6_subset_1 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k6_subset_1 @ X0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['78'])).

thf('80',plain,(
    $false ),
    inference('sup-',[status(thm)],['60','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pBQgF5gYvb
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:40:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.70/0.89  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.70/0.89  % Solved by: fo/fo7.sh
% 0.70/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.89  % done 690 iterations in 0.427s
% 0.70/0.89  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.70/0.89  % SZS output start Refutation
% 0.70/0.89  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.70/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.89  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.70/0.89  thf(sk_B_type, type, sk_B: $i > $i).
% 0.70/0.89  thf(r2_waybel_0_type, type, r2_waybel_0: $i > $i > $i > $o).
% 0.70/0.89  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.70/0.89  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.70/0.89  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.70/0.89  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.70/0.89  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.70/0.89  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.70/0.89  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.70/0.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.70/0.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.70/0.89  thf(k4_yellow_6_type, type, k4_yellow_6: $i > $i > $i).
% 0.70/0.89  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.70/0.89  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.70/0.89  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.70/0.89  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.70/0.89  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 0.70/0.89  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.70/0.89  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.70/0.89  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.70/0.89  thf(d3_tarski, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( r1_tarski @ A @ B ) <=>
% 0.70/0.89       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.70/0.89  thf('0', plain,
% 0.70/0.89      (![X1 : $i, X3 : $i]:
% 0.70/0.89         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.70/0.89      inference('cnf', [status(esa)], [d3_tarski])).
% 0.70/0.89  thf(d5_xboole_0, axiom,
% 0.70/0.89    (![A:$i,B:$i,C:$i]:
% 0.70/0.89     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.70/0.89       ( ![D:$i]:
% 0.70/0.89         ( ( r2_hidden @ D @ C ) <=>
% 0.70/0.89           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.70/0.89  thf('1', plain,
% 0.70/0.89      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.70/0.89         (~ (r2_hidden @ X8 @ X7)
% 0.70/0.89          | (r2_hidden @ X8 @ X5)
% 0.70/0.89          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.70/0.89      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.70/0.89  thf('2', plain,
% 0.70/0.89      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.70/0.89         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.70/0.89      inference('simplify', [status(thm)], ['1'])).
% 0.70/0.89  thf(redefinition_k6_subset_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.70/0.89  thf('3', plain,
% 0.70/0.89      (![X10 : $i, X11 : $i]:
% 0.70/0.89         ((k6_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))),
% 0.70/0.89      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.70/0.89  thf('4', plain,
% 0.70/0.89      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.70/0.89         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k6_subset_1 @ X5 @ X6)))),
% 0.70/0.89      inference('demod', [status(thm)], ['2', '3'])).
% 0.70/0.89  thf('5', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.89         ((r1_tarski @ (k6_subset_1 @ X1 @ X0) @ X2)
% 0.70/0.89          | (r2_hidden @ (sk_C @ X2 @ (k6_subset_1 @ X1 @ X0)) @ X1))),
% 0.70/0.89      inference('sup-', [status(thm)], ['0', '4'])).
% 0.70/0.89  thf('6', plain,
% 0.70/0.89      (![X1 : $i, X3 : $i]:
% 0.70/0.89         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.70/0.89      inference('cnf', [status(esa)], [d3_tarski])).
% 0.70/0.89  thf('7', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         ((r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)
% 0.70/0.89          | (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['5', '6'])).
% 0.70/0.89  thf('8', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)),
% 0.70/0.89      inference('simplify', [status(thm)], ['7'])).
% 0.70/0.89  thf(t29_yellow_6, conjecture,
% 0.70/0.89    (![A:$i]:
% 0.70/0.89     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.70/0.89       ( ![B:$i]:
% 0.70/0.89         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.70/0.89             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.70/0.89           ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.70/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.89    (~( ![A:$i]:
% 0.70/0.89        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.70/0.89          ( ![B:$i]:
% 0.70/0.89            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.70/0.89                ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.70/0.89              ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ) )),
% 0.70/0.89    inference('cnf.neg', [status(esa)], [t29_yellow_6])).
% 0.70/0.89  thf('9', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf(t10_waybel_0, axiom,
% 0.70/0.89    (![A:$i]:
% 0.70/0.89     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.70/0.89       ( ![B:$i]:
% 0.70/0.89         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.70/0.89           ( ![C:$i]:
% 0.70/0.89             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.70/0.89               ( ~( r1_waybel_0 @
% 0.70/0.89                    A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ))).
% 0.70/0.89  thf('10', plain,
% 0.70/0.89      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.70/0.89         ((v2_struct_0 @ X24)
% 0.70/0.89          | ~ (l1_waybel_0 @ X24 @ X25)
% 0.70/0.89          | (r1_waybel_0 @ X25 @ X24 @ 
% 0.70/0.89             (k6_subset_1 @ (u1_struct_0 @ X25) @ X26))
% 0.70/0.89          | (r2_waybel_0 @ X25 @ X24 @ X26)
% 0.70/0.89          | ~ (l1_struct_0 @ X25)
% 0.70/0.89          | (v2_struct_0 @ X25))),
% 0.70/0.89      inference('cnf', [status(esa)], [t10_waybel_0])).
% 0.70/0.89  thf('11', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         ((v2_struct_0 @ sk_A)
% 0.70/0.89          | ~ (l1_struct_0 @ sk_A)
% 0.70/0.89          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.70/0.89          | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.70/0.89             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.70/0.89          | (v2_struct_0 @ sk_B_1))),
% 0.70/0.89      inference('sup-', [status(thm)], ['9', '10'])).
% 0.70/0.89  thf('12', plain, ((l1_struct_0 @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('13', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         ((v2_struct_0 @ sk_A)
% 0.70/0.89          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.70/0.89          | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.70/0.89             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.70/0.89          | (v2_struct_0 @ sk_B_1))),
% 0.70/0.89      inference('demod', [status(thm)], ['11', '12'])).
% 0.70/0.89  thf(t8_waybel_0, axiom,
% 0.70/0.89    (![A:$i]:
% 0.70/0.89     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.70/0.89       ( ![B:$i]:
% 0.70/0.89         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.70/0.89           ( ![C:$i,D:$i]:
% 0.70/0.89             ( ( r1_tarski @ C @ D ) =>
% 0.70/0.89               ( ( ( r1_waybel_0 @ A @ B @ C ) => ( r1_waybel_0 @ A @ B @ D ) ) & 
% 0.70/0.89                 ( ( r2_waybel_0 @ A @ B @ C ) => ( r2_waybel_0 @ A @ B @ D ) ) ) ) ) ) ) ))).
% 0.70/0.89  thf('14', plain,
% 0.70/0.89      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.70/0.89         ((v2_struct_0 @ X28)
% 0.70/0.89          | ~ (l1_waybel_0 @ X28 @ X29)
% 0.70/0.89          | ~ (r1_waybel_0 @ X29 @ X28 @ X30)
% 0.70/0.89          | (r1_waybel_0 @ X29 @ X28 @ X31)
% 0.70/0.89          | ~ (r1_tarski @ X30 @ X31)
% 0.70/0.89          | ~ (l1_struct_0 @ X29)
% 0.70/0.89          | (v2_struct_0 @ X29))),
% 0.70/0.89      inference('cnf', [status(esa)], [t8_waybel_0])).
% 0.70/0.89  thf('15', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         ((v2_struct_0 @ sk_B_1)
% 0.70/0.89          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.70/0.89          | (v2_struct_0 @ sk_A)
% 0.70/0.89          | (v2_struct_0 @ sk_A)
% 0.70/0.89          | ~ (l1_struct_0 @ sk_A)
% 0.70/0.89          | ~ (r1_tarski @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ X1)
% 0.70/0.89          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X1)
% 0.70/0.89          | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.70/0.89          | (v2_struct_0 @ sk_B_1))),
% 0.70/0.89      inference('sup-', [status(thm)], ['13', '14'])).
% 0.70/0.89  thf('16', plain, ((l1_struct_0 @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('17', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('18', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         ((v2_struct_0 @ sk_B_1)
% 0.70/0.89          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.70/0.89          | (v2_struct_0 @ sk_A)
% 0.70/0.89          | (v2_struct_0 @ sk_A)
% 0.70/0.89          | ~ (r1_tarski @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ X1)
% 0.70/0.89          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X1)
% 0.70/0.89          | (v2_struct_0 @ sk_B_1))),
% 0.70/0.89      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.70/0.89  thf('19', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         ((r1_waybel_0 @ sk_A @ sk_B_1 @ X1)
% 0.70/0.89          | ~ (r1_tarski @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ X1)
% 0.70/0.89          | (v2_struct_0 @ sk_A)
% 0.70/0.89          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.70/0.89          | (v2_struct_0 @ sk_B_1))),
% 0.70/0.89      inference('simplify', [status(thm)], ['18'])).
% 0.70/0.89  thf('20', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         ((v2_struct_0 @ sk_B_1)
% 0.70/0.89          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.70/0.89          | (v2_struct_0 @ sk_A)
% 0.70/0.89          | (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['8', '19'])).
% 0.70/0.89  thf('21', plain, (~ (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('22', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         ((v2_struct_0 @ sk_A)
% 0.70/0.89          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.70/0.89          | (v2_struct_0 @ sk_B_1))),
% 0.70/0.89      inference('sup-', [status(thm)], ['20', '21'])).
% 0.70/0.89  thf('23', plain, (~ (v2_struct_0 @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('24', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         ((v2_struct_0 @ sk_B_1) | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0))),
% 0.70/0.89      inference('clc', [status(thm)], ['22', '23'])).
% 0.70/0.89  thf('25', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('26', plain, (![X0 : $i]: (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)),
% 0.70/0.89      inference('clc', [status(thm)], ['24', '25'])).
% 0.70/0.89  thf(dt_l1_orders_2, axiom,
% 0.70/0.89    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.70/0.89  thf('27', plain,
% 0.70/0.89      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_orders_2 @ X14))),
% 0.70/0.89      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.70/0.89  thf('28', plain, (![X0 : $i]: (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)),
% 0.70/0.89      inference('clc', [status(thm)], ['24', '25'])).
% 0.70/0.89  thf(existence_l1_waybel_0, axiom,
% 0.70/0.89    (![A:$i]: ( ( l1_struct_0 @ A ) => ( ?[B:$i]: ( l1_waybel_0 @ B @ A ) ) ))).
% 0.70/0.89  thf('29', plain,
% 0.70/0.89      (![X23 : $i]:
% 0.70/0.89         ((l1_waybel_0 @ (sk_B @ X23) @ X23) | ~ (l1_struct_0 @ X23))),
% 0.70/0.89      inference('cnf', [status(esa)], [existence_l1_waybel_0])).
% 0.70/0.89  thf(dt_k4_yellow_6, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.70/0.89         ( l1_waybel_0 @ B @ A ) ) =>
% 0.70/0.89       ( m1_subset_1 @ ( k4_yellow_6 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.70/0.89  thf('30', plain,
% 0.70/0.89      (![X32 : $i, X33 : $i]:
% 0.70/0.89         (~ (l1_struct_0 @ X32)
% 0.70/0.89          | (v2_struct_0 @ X32)
% 0.70/0.89          | ~ (l1_waybel_0 @ X33 @ X32)
% 0.70/0.89          | (m1_subset_1 @ (k4_yellow_6 @ X32 @ X33) @ (u1_struct_0 @ X32)))),
% 0.70/0.89      inference('cnf', [status(esa)], [dt_k4_yellow_6])).
% 0.70/0.89  thf('31', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         (~ (l1_struct_0 @ X0)
% 0.70/0.89          | (m1_subset_1 @ (k4_yellow_6 @ X0 @ (sk_B @ X0)) @ 
% 0.70/0.89             (u1_struct_0 @ X0))
% 0.70/0.89          | (v2_struct_0 @ X0)
% 0.70/0.89          | ~ (l1_struct_0 @ X0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['29', '30'])).
% 0.70/0.89  thf('32', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         ((v2_struct_0 @ X0)
% 0.70/0.89          | (m1_subset_1 @ (k4_yellow_6 @ X0 @ (sk_B @ X0)) @ 
% 0.70/0.89             (u1_struct_0 @ X0))
% 0.70/0.89          | ~ (l1_struct_0 @ X0))),
% 0.70/0.89      inference('simplify', [status(thm)], ['31'])).
% 0.70/0.89  thf(d12_waybel_0, axiom,
% 0.70/0.89    (![A:$i]:
% 0.70/0.89     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.70/0.89       ( ![B:$i]:
% 0.70/0.89         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.70/0.89           ( ![C:$i]:
% 0.70/0.89             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.70/0.89               ( ![D:$i]:
% 0.70/0.89                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.70/0.89                   ( ?[E:$i]:
% 0.70/0.89                     ( ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) & 
% 0.70/0.89                       ( r1_orders_2 @ B @ D @ E ) & 
% 0.70/0.89                       ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.70/0.89  thf('33', plain,
% 0.70/0.89      (![X15 : $i, X16 : $i, X19 : $i, X20 : $i]:
% 0.70/0.89         ((v2_struct_0 @ X15)
% 0.70/0.89          | ~ (l1_waybel_0 @ X15 @ X16)
% 0.70/0.89          | ~ (r2_waybel_0 @ X16 @ X15 @ X19)
% 0.70/0.89          | (m1_subset_1 @ (sk_E @ X20 @ X19 @ X15 @ X16) @ (u1_struct_0 @ X15))
% 0.70/0.89          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X15))
% 0.70/0.89          | ~ (l1_struct_0 @ X16)
% 0.70/0.89          | (v2_struct_0 @ X16))),
% 0.70/0.89      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.70/0.89  thf('34', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.89         (~ (l1_struct_0 @ X0)
% 0.70/0.89          | (v2_struct_0 @ X0)
% 0.70/0.89          | (v2_struct_0 @ X1)
% 0.70/0.89          | ~ (l1_struct_0 @ X1)
% 0.70/0.89          | (m1_subset_1 @ 
% 0.70/0.89             (sk_E @ (k4_yellow_6 @ X0 @ (sk_B @ X0)) @ X2 @ X0 @ X1) @ 
% 0.70/0.89             (u1_struct_0 @ X0))
% 0.70/0.89          | ~ (r2_waybel_0 @ X1 @ X0 @ X2)
% 0.70/0.89          | ~ (l1_waybel_0 @ X0 @ X1)
% 0.70/0.89          | (v2_struct_0 @ X0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['32', '33'])).
% 0.70/0.89  thf('35', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.89         (~ (l1_waybel_0 @ X0 @ X1)
% 0.70/0.89          | ~ (r2_waybel_0 @ X1 @ X0 @ X2)
% 0.70/0.89          | (m1_subset_1 @ 
% 0.70/0.89             (sk_E @ (k4_yellow_6 @ X0 @ (sk_B @ X0)) @ X2 @ X0 @ X1) @ 
% 0.70/0.89             (u1_struct_0 @ X0))
% 0.70/0.89          | ~ (l1_struct_0 @ X1)
% 0.70/0.89          | (v2_struct_0 @ X1)
% 0.70/0.89          | (v2_struct_0 @ X0)
% 0.70/0.89          | ~ (l1_struct_0 @ X0))),
% 0.70/0.89      inference('simplify', [status(thm)], ['34'])).
% 0.70/0.89  thf('36', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         (~ (l1_struct_0 @ sk_B_1)
% 0.70/0.89          | (v2_struct_0 @ sk_B_1)
% 0.70/0.89          | (v2_struct_0 @ sk_A)
% 0.70/0.89          | ~ (l1_struct_0 @ sk_A)
% 0.70/0.89          | (m1_subset_1 @ 
% 0.70/0.89             (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0 @ sk_B_1 @ 
% 0.70/0.89              sk_A) @ 
% 0.70/0.89             (u1_struct_0 @ sk_B_1))
% 0.70/0.89          | ~ (l1_waybel_0 @ sk_B_1 @ sk_A))),
% 0.70/0.89      inference('sup-', [status(thm)], ['28', '35'])).
% 0.70/0.89  thf('37', plain, ((l1_struct_0 @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('38', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('39', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         (~ (l1_struct_0 @ sk_B_1)
% 0.70/0.89          | (v2_struct_0 @ sk_B_1)
% 0.70/0.89          | (v2_struct_0 @ sk_A)
% 0.70/0.89          | (m1_subset_1 @ 
% 0.70/0.89             (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0 @ sk_B_1 @ 
% 0.70/0.89              sk_A) @ 
% 0.70/0.89             (u1_struct_0 @ sk_B_1)))),
% 0.70/0.89      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.70/0.89  thf('40', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         (~ (l1_orders_2 @ sk_B_1)
% 0.70/0.89          | (m1_subset_1 @ 
% 0.70/0.89             (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0 @ sk_B_1 @ 
% 0.70/0.89              sk_A) @ 
% 0.70/0.89             (u1_struct_0 @ sk_B_1))
% 0.70/0.89          | (v2_struct_0 @ sk_A)
% 0.70/0.89          | (v2_struct_0 @ sk_B_1))),
% 0.70/0.89      inference('sup-', [status(thm)], ['27', '39'])).
% 0.70/0.89  thf('41', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf(dt_l1_waybel_0, axiom,
% 0.70/0.89    (![A:$i]:
% 0.70/0.89     ( ( l1_struct_0 @ A ) =>
% 0.70/0.89       ( ![B:$i]: ( ( l1_waybel_0 @ B @ A ) => ( l1_orders_2 @ B ) ) ) ))).
% 0.70/0.89  thf('42', plain,
% 0.70/0.89      (![X21 : $i, X22 : $i]:
% 0.70/0.89         (~ (l1_waybel_0 @ X21 @ X22)
% 0.70/0.89          | (l1_orders_2 @ X21)
% 0.70/0.89          | ~ (l1_struct_0 @ X22))),
% 0.70/0.89      inference('cnf', [status(esa)], [dt_l1_waybel_0])).
% 0.70/0.89  thf('43', plain, ((~ (l1_struct_0 @ sk_A) | (l1_orders_2 @ sk_B_1))),
% 0.70/0.89      inference('sup-', [status(thm)], ['41', '42'])).
% 0.70/0.89  thf('44', plain, ((l1_struct_0 @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('45', plain, ((l1_orders_2 @ sk_B_1)),
% 0.70/0.89      inference('demod', [status(thm)], ['43', '44'])).
% 0.70/0.89  thf('46', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         ((m1_subset_1 @ 
% 0.70/0.89           (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0 @ sk_B_1 @ 
% 0.70/0.89            sk_A) @ 
% 0.70/0.89           (u1_struct_0 @ sk_B_1))
% 0.70/0.89          | (v2_struct_0 @ sk_A)
% 0.70/0.89          | (v2_struct_0 @ sk_B_1))),
% 0.70/0.89      inference('demod', [status(thm)], ['40', '45'])).
% 0.70/0.89  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('48', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         ((v2_struct_0 @ sk_B_1)
% 0.70/0.89          | (m1_subset_1 @ 
% 0.70/0.89             (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0 @ sk_B_1 @ 
% 0.70/0.89              sk_A) @ 
% 0.70/0.89             (u1_struct_0 @ sk_B_1)))),
% 0.70/0.89      inference('clc', [status(thm)], ['46', '47'])).
% 0.70/0.89  thf('49', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('50', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         (m1_subset_1 @ 
% 0.70/0.89          (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.70/0.89          (u1_struct_0 @ sk_B_1))),
% 0.70/0.89      inference('clc', [status(thm)], ['48', '49'])).
% 0.70/0.89  thf('51', plain,
% 0.70/0.89      (![X15 : $i, X16 : $i, X19 : $i, X20 : $i]:
% 0.70/0.89         ((v2_struct_0 @ X15)
% 0.70/0.89          | ~ (l1_waybel_0 @ X15 @ X16)
% 0.70/0.89          | ~ (r2_waybel_0 @ X16 @ X15 @ X19)
% 0.70/0.89          | (r2_hidden @ 
% 0.70/0.89             (k2_waybel_0 @ X16 @ X15 @ (sk_E @ X20 @ X19 @ X15 @ X16)) @ X19)
% 0.70/0.89          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X15))
% 0.70/0.89          | ~ (l1_struct_0 @ X16)
% 0.70/0.89          | (v2_struct_0 @ X16))),
% 0.70/0.89      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.70/0.89  thf('52', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.89         ((v2_struct_0 @ X1)
% 0.70/0.89          | ~ (l1_struct_0 @ X1)
% 0.70/0.89          | (r2_hidden @ 
% 0.70/0.89             (k2_waybel_0 @ X1 @ sk_B_1 @ 
% 0.70/0.89              (sk_E @ 
% 0.70/0.89               (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0 @ 
% 0.70/0.89                sk_B_1 @ sk_A) @ 
% 0.70/0.89               X2 @ sk_B_1 @ X1)) @ 
% 0.70/0.89             X2)
% 0.70/0.89          | ~ (r2_waybel_0 @ X1 @ sk_B_1 @ X2)
% 0.70/0.89          | ~ (l1_waybel_0 @ sk_B_1 @ X1)
% 0.70/0.89          | (v2_struct_0 @ sk_B_1))),
% 0.70/0.89      inference('sup-', [status(thm)], ['50', '51'])).
% 0.70/0.89  thf('53', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         ((v2_struct_0 @ sk_B_1)
% 0.70/0.89          | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.70/0.89          | (r2_hidden @ 
% 0.70/0.89             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.70/0.89              (sk_E @ 
% 0.70/0.89               (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X1 @ 
% 0.70/0.89                sk_B_1 @ sk_A) @ 
% 0.70/0.89               X0 @ sk_B_1 @ sk_A)) @ 
% 0.70/0.89             X0)
% 0.70/0.89          | ~ (l1_struct_0 @ sk_A)
% 0.70/0.89          | (v2_struct_0 @ sk_A))),
% 0.70/0.89      inference('sup-', [status(thm)], ['26', '52'])).
% 0.70/0.89  thf('54', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('55', plain, ((l1_struct_0 @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('56', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         ((v2_struct_0 @ sk_B_1)
% 0.70/0.89          | (r2_hidden @ 
% 0.70/0.89             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.70/0.89              (sk_E @ 
% 0.70/0.89               (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X1 @ 
% 0.70/0.89                sk_B_1 @ sk_A) @ 
% 0.70/0.89               X0 @ sk_B_1 @ sk_A)) @ 
% 0.70/0.89             X0)
% 0.70/0.89          | (v2_struct_0 @ sk_A))),
% 0.70/0.89      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.70/0.89  thf('57', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('58', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         ((v2_struct_0 @ sk_A)
% 0.70/0.89          | (r2_hidden @ 
% 0.70/0.89             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.70/0.89              (sk_E @ 
% 0.70/0.89               (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X1 @ 
% 0.70/0.89                sk_B_1 @ sk_A) @ 
% 0.70/0.89               X0 @ sk_B_1 @ sk_A)) @ 
% 0.70/0.89             X0))),
% 0.70/0.89      inference('clc', [status(thm)], ['56', '57'])).
% 0.70/0.89  thf('59', plain, (~ (v2_struct_0 @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('60', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         (r2_hidden @ 
% 0.70/0.89          (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.70/0.89           (sk_E @ 
% 0.70/0.89            (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X1 @ sk_B_1 @ 
% 0.70/0.89             sk_A) @ 
% 0.70/0.89            X0 @ sk_B_1 @ sk_A)) @ 
% 0.70/0.89          X0)),
% 0.70/0.89      inference('clc', [status(thm)], ['58', '59'])).
% 0.70/0.89  thf('61', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.89         ((r1_tarski @ (k6_subset_1 @ X1 @ X0) @ X2)
% 0.70/0.89          | (r2_hidden @ (sk_C @ X2 @ (k6_subset_1 @ X1 @ X0)) @ X1))),
% 0.70/0.89      inference('sup-', [status(thm)], ['0', '4'])).
% 0.70/0.89  thf('62', plain,
% 0.70/0.89      (![X1 : $i, X3 : $i]:
% 0.70/0.89         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.70/0.89      inference('cnf', [status(esa)], [d3_tarski])).
% 0.70/0.89  thf('63', plain,
% 0.70/0.89      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.70/0.89         (~ (r2_hidden @ X8 @ X7)
% 0.70/0.89          | ~ (r2_hidden @ X8 @ X6)
% 0.70/0.89          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.70/0.89      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.70/0.89  thf('64', plain,
% 0.70/0.89      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.70/0.89         (~ (r2_hidden @ X8 @ X6)
% 0.70/0.89          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.70/0.89      inference('simplify', [status(thm)], ['63'])).
% 0.70/0.89  thf('65', plain,
% 0.70/0.89      (![X10 : $i, X11 : $i]:
% 0.70/0.89         ((k6_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))),
% 0.70/0.89      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.70/0.89  thf('66', plain,
% 0.70/0.89      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.70/0.89         (~ (r2_hidden @ X8 @ X6)
% 0.70/0.89          | ~ (r2_hidden @ X8 @ (k6_subset_1 @ X5 @ X6)))),
% 0.70/0.89      inference('demod', [status(thm)], ['64', '65'])).
% 0.70/0.89  thf('67', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.89         ((r1_tarski @ (k6_subset_1 @ X1 @ X0) @ X2)
% 0.70/0.89          | ~ (r2_hidden @ (sk_C @ X2 @ (k6_subset_1 @ X1 @ X0)) @ X0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['62', '66'])).
% 0.70/0.89  thf('68', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         ((r1_tarski @ (k6_subset_1 @ X0 @ X0) @ X1)
% 0.70/0.89          | (r1_tarski @ (k6_subset_1 @ X0 @ X0) @ X1))),
% 0.70/0.89      inference('sup-', [status(thm)], ['61', '67'])).
% 0.70/0.89  thf('69', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X0 @ X0) @ X1)),
% 0.70/0.89      inference('simplify', [status(thm)], ['68'])).
% 0.70/0.89  thf('70', plain,
% 0.70/0.89      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.70/0.89         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 0.70/0.89          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 0.70/0.89          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.70/0.89      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.70/0.89  thf('71', plain,
% 0.70/0.89      (![X10 : $i, X11 : $i]:
% 0.70/0.89         ((k6_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))),
% 0.70/0.89      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.70/0.89  thf('72', plain,
% 0.70/0.89      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.70/0.89         (((X9) = (k6_subset_1 @ X5 @ X6))
% 0.70/0.89          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 0.70/0.89          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.70/0.89      inference('demod', [status(thm)], ['70', '71'])).
% 0.70/0.89  thf('73', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.70/0.89          | ((X0) = (k6_subset_1 @ X0 @ X1)))),
% 0.70/0.89      inference('eq_fact', [status(thm)], ['72'])).
% 0.70/0.89  thf(t7_ordinal1, axiom,
% 0.70/0.89    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.70/0.89  thf('74', plain,
% 0.70/0.89      (![X12 : $i, X13 : $i]:
% 0.70/0.89         (~ (r2_hidden @ X12 @ X13) | ~ (r1_tarski @ X13 @ X12))),
% 0.70/0.89      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.70/0.89  thf('75', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         (((X0) = (k6_subset_1 @ X0 @ X1))
% 0.70/0.89          | ~ (r1_tarski @ X0 @ (sk_D @ X0 @ X1 @ X0)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['73', '74'])).
% 0.70/0.89  thf('76', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         ((k6_subset_1 @ X0 @ X0)
% 0.70/0.89           = (k6_subset_1 @ (k6_subset_1 @ X0 @ X0) @ X1))),
% 0.70/0.89      inference('sup-', [status(thm)], ['69', '75'])).
% 0.70/0.89  thf('77', plain,
% 0.70/0.89      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.70/0.89         (~ (r2_hidden @ X8 @ X6)
% 0.70/0.89          | ~ (r2_hidden @ X8 @ (k6_subset_1 @ X5 @ X6)))),
% 0.70/0.89      inference('demod', [status(thm)], ['64', '65'])).
% 0.70/0.89  thf('78', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.89         (~ (r2_hidden @ X2 @ (k6_subset_1 @ X0 @ X0))
% 0.70/0.89          | ~ (r2_hidden @ X2 @ X1))),
% 0.70/0.89      inference('sup-', [status(thm)], ['76', '77'])).
% 0.70/0.89  thf('79', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k6_subset_1 @ X0 @ X0))),
% 0.70/0.89      inference('condensation', [status(thm)], ['78'])).
% 0.70/0.89  thf('80', plain, ($false), inference('sup-', [status(thm)], ['60', '79'])).
% 0.70/0.89  
% 0.70/0.89  % SZS output end Refutation
% 0.70/0.89  
% 0.70/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
