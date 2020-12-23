%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0bbFSKK5TG

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:01 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 301 expanded)
%              Number of leaves         :   30 (  99 expanded)
%              Depth                    :   26
%              Number of atoms          :  983 (3501 expanded)
%              Number of equality atoms :   18 (  88 expanded)
%              Maximal formula depth    :   20 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_waybel_0_type,type,(
    r2_waybel_0: $i > $i > $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k6_subset_1 @ X8 @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('2',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k6_subset_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k6_subset_1 @ X8 @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('5',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k6_subset_1 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k6_subset_1 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k6_subset_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k6_subset_1 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('8',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('9',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k6_subset_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['9'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k6_subset_1 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X0 @ ( sk_D @ X0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k6_subset_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf('14',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('15',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k6_subset_1 @ X8 @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('17',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k6_subset_1 @ X1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k6_subset_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','19'])).

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

thf('21',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t9_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( r1_waybel_0 @ A @ B @ C )
            <=> ~ ( r2_waybel_0 @ A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) )).

thf('22',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( l1_waybel_0 @ X18 @ X19 )
      | ( r2_waybel_0 @ X19 @ X18 @ ( k6_subset_1 @ ( u1_struct_0 @ X19 ) @ X20 ) )
      | ( r1_waybel_0 @ X19 @ X18 @ X20 )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t9_waybel_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['20','25'])).

thf('27',plain,(
    ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
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

thf('35',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( l1_waybel_0 @ X12 @ X13 )
      | ( m1_subset_1 @ ( sk_D_1 @ X14 @ X12 @ X13 ) @ ( u1_struct_0 @ X12 ) )
      | ( r2_waybel_0 @ X13 @ X12 @ X14 )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X12: $i,X13: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( l1_waybel_0 @ X12 @ X13 )
      | ~ ( r2_waybel_0 @ X13 @ X12 @ X16 )
      | ( r2_hidden @ ( k2_waybel_0 @ X13 @ X12 @ ( sk_E @ X17 @ X16 @ X12 @ X13 ) ) @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ sk_B_1 @ ( sk_E @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ X2 @ sk_B_1 @ X1 ) ) @ X2 )
      | ~ ( r2_waybel_0 @ X1 @ sk_B_1 @ X2 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ X1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_waybel_0 @ sk_B_1 @ X1 )
      | ~ ( r2_waybel_0 @ X1 @ sk_B_1 @ X2 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ sk_B_1 @ ( sk_E @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ X2 @ sk_B_1 @ X1 ) ) @ X2 )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ X1 @ sk_B_1 @ sk_A ) ) @ X1 )
      | ~ ( r2_waybel_0 @ sk_A @ sk_B_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','41'])).

thf('43',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ X1 @ sk_B_1 @ sk_A ) ) @ X1 )
      | ~ ( r2_waybel_0 @ sk_A @ sk_B_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_waybel_0 @ sk_A @ sk_B_1 @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ X1 @ sk_B_1 @ sk_A ) ) @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ k1_xboole_0 @ sk_B_1 @ sk_A ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['18'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['50','51'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('54',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( sk_B @ X7 ) @ X7 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf('55',plain,(
    ! [X12: $i,X13: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( l1_waybel_0 @ X12 @ X13 )
      | ~ ( r2_waybel_0 @ X13 @ X12 @ X16 )
      | ( m1_subset_1 @ ( sk_E @ X17 @ X16 @ X12 @ X13 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X2 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_waybel_0 @ X1 @ X0 @ X2 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X12: $i,X13: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( l1_waybel_0 @ X12 @ X13 )
      | ~ ( r2_waybel_0 @ X13 @ X12 @ X16 )
      | ( r2_hidden @ ( k2_waybel_0 @ X13 @ X12 @ ( sk_E @ X17 @ X16 @ X12 @ X13 ) ) @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ X2 @ sk_B_1 @ X1 ) ) @ X2 )
      | ~ ( r2_waybel_0 @ X1 @ sk_B_1 @ X2 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ X1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X1 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','66'])).

thf('68',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X1 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X1 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X1 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['18'])).

thf('76',plain,(
    $false ),
    inference('sup-',[status(thm)],['74','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0bbFSKK5TG
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:59:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.53/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.53/0.72  % Solved by: fo/fo7.sh
% 0.53/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.72  % done 461 iterations in 0.266s
% 0.53/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.53/0.72  % SZS output start Refutation
% 0.53/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.53/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.53/0.72  thf(r2_waybel_0_type, type, r2_waybel_0: $i > $i > $i > $o).
% 0.53/0.72  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.53/0.72  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.53/0.72  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 0.53/0.72  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.53/0.72  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.53/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.72  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.53/0.72  thf(sk_B_type, type, sk_B: $i > $i).
% 0.53/0.72  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.53/0.72  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.53/0.72  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.53/0.72  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.53/0.72  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.53/0.72  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.53/0.72  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.53/0.72  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.53/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.72  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.53/0.72  thf(d5_xboole_0, axiom,
% 0.53/0.72    (![A:$i,B:$i,C:$i]:
% 0.53/0.72     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.53/0.72       ( ![D:$i]:
% 0.53/0.72         ( ( r2_hidden @ D @ C ) <=>
% 0.53/0.72           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.53/0.72  thf('0', plain,
% 0.53/0.72      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.53/0.72         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.53/0.72          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.53/0.72          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.53/0.72      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.53/0.72  thf(redefinition_k6_subset_1, axiom,
% 0.53/0.72    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.53/0.72  thf('1', plain,
% 0.53/0.72      (![X8 : $i, X9 : $i]: ((k6_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))),
% 0.53/0.72      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.53/0.72  thf('2', plain,
% 0.53/0.72      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.53/0.72         (((X5) = (k6_subset_1 @ X1 @ X2))
% 0.53/0.72          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.53/0.72          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.53/0.72      inference('demod', [status(thm)], ['0', '1'])).
% 0.53/0.72  thf('3', plain,
% 0.53/0.72      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.53/0.72         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.53/0.72          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.53/0.72          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.53/0.72      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.53/0.72  thf('4', plain,
% 0.53/0.72      (![X8 : $i, X9 : $i]: ((k6_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))),
% 0.53/0.72      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.53/0.72  thf('5', plain,
% 0.53/0.72      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.53/0.72         (((X5) = (k6_subset_1 @ X1 @ X2))
% 0.53/0.72          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.53/0.72          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.53/0.72      inference('demod', [status(thm)], ['3', '4'])).
% 0.53/0.72  thf('6', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.53/0.72          | ((X1) = (k6_subset_1 @ X0 @ X0))
% 0.53/0.72          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.53/0.72          | ((X1) = (k6_subset_1 @ X0 @ X0)))),
% 0.53/0.72      inference('sup-', [status(thm)], ['2', '5'])).
% 0.53/0.72  thf('7', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         (((X1) = (k6_subset_1 @ X0 @ X0))
% 0.53/0.72          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 0.53/0.72      inference('simplify', [status(thm)], ['6'])).
% 0.53/0.72  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.53/0.72  thf('8', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.53/0.72      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.53/0.72  thf('9', plain,
% 0.53/0.72      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.53/0.72         (((X5) = (k6_subset_1 @ X1 @ X2))
% 0.53/0.72          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.53/0.72          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.53/0.72      inference('demod', [status(thm)], ['0', '1'])).
% 0.53/0.72  thf('10', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.53/0.72          | ((X0) = (k6_subset_1 @ X0 @ X1)))),
% 0.53/0.72      inference('eq_fact', [status(thm)], ['9'])).
% 0.53/0.72  thf(t7_ordinal1, axiom,
% 0.53/0.72    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.53/0.72  thf('11', plain,
% 0.53/0.72      (![X10 : $i, X11 : $i]:
% 0.53/0.72         (~ (r2_hidden @ X10 @ X11) | ~ (r1_tarski @ X11 @ X10))),
% 0.53/0.72      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.53/0.72  thf('12', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         (((X0) = (k6_subset_1 @ X0 @ X1))
% 0.53/0.72          | ~ (r1_tarski @ X0 @ (sk_D @ X0 @ X1 @ X0)))),
% 0.53/0.72      inference('sup-', [status(thm)], ['10', '11'])).
% 0.53/0.72  thf('13', plain,
% 0.53/0.72      (![X0 : $i]: ((k1_xboole_0) = (k6_subset_1 @ k1_xboole_0 @ X0))),
% 0.53/0.72      inference('sup-', [status(thm)], ['8', '12'])).
% 0.53/0.72  thf('14', plain,
% 0.53/0.72      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.53/0.72         (~ (r2_hidden @ X4 @ X3)
% 0.53/0.72          | ~ (r2_hidden @ X4 @ X2)
% 0.53/0.72          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.53/0.72      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.53/0.72  thf('15', plain,
% 0.53/0.72      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.53/0.72         (~ (r2_hidden @ X4 @ X2)
% 0.53/0.72          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.53/0.72      inference('simplify', [status(thm)], ['14'])).
% 0.53/0.72  thf('16', plain,
% 0.53/0.72      (![X8 : $i, X9 : $i]: ((k6_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))),
% 0.53/0.72      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.53/0.72  thf('17', plain,
% 0.53/0.72      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.53/0.72         (~ (r2_hidden @ X4 @ X2)
% 0.53/0.72          | ~ (r2_hidden @ X4 @ (k6_subset_1 @ X1 @ X2)))),
% 0.53/0.72      inference('demod', [status(thm)], ['15', '16'])).
% 0.53/0.72  thf('18', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.53/0.72      inference('sup-', [status(thm)], ['13', '17'])).
% 0.53/0.72  thf('19', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.53/0.72      inference('condensation', [status(thm)], ['18'])).
% 0.53/0.72  thf('20', plain, (![X0 : $i]: ((k1_xboole_0) = (k6_subset_1 @ X0 @ X0))),
% 0.53/0.72      inference('sup-', [status(thm)], ['7', '19'])).
% 0.53/0.72  thf(t29_yellow_6, conjecture,
% 0.53/0.72    (![A:$i]:
% 0.53/0.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.53/0.72       ( ![B:$i]:
% 0.53/0.72         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.53/0.72             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.53/0.72           ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.53/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.72    (~( ![A:$i]:
% 0.53/0.72        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.53/0.72          ( ![B:$i]:
% 0.53/0.72            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.53/0.72                ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.53/0.72              ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ) )),
% 0.53/0.72    inference('cnf.neg', [status(esa)], [t29_yellow_6])).
% 0.53/0.72  thf('21', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf(t9_waybel_0, axiom,
% 0.53/0.72    (![A:$i]:
% 0.53/0.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.53/0.72       ( ![B:$i]:
% 0.53/0.72         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.53/0.72           ( ![C:$i]:
% 0.53/0.72             ( ( r1_waybel_0 @ A @ B @ C ) <=>
% 0.53/0.72               ( ~( r2_waybel_0 @
% 0.53/0.72                    A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ))).
% 0.53/0.72  thf('22', plain,
% 0.53/0.72      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.53/0.72         ((v2_struct_0 @ X18)
% 0.53/0.72          | ~ (l1_waybel_0 @ X18 @ X19)
% 0.53/0.72          | (r2_waybel_0 @ X19 @ X18 @ 
% 0.53/0.72             (k6_subset_1 @ (u1_struct_0 @ X19) @ X20))
% 0.53/0.72          | (r1_waybel_0 @ X19 @ X18 @ X20)
% 0.53/0.72          | ~ (l1_struct_0 @ X19)
% 0.53/0.72          | (v2_struct_0 @ X19))),
% 0.53/0.72      inference('cnf', [status(esa)], [t9_waybel_0])).
% 0.53/0.72  thf('23', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((v2_struct_0 @ sk_A)
% 0.53/0.72          | ~ (l1_struct_0 @ sk_A)
% 0.53/0.72          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.53/0.72          | (r2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.53/0.72             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.53/0.72          | (v2_struct_0 @ sk_B_1))),
% 0.53/0.72      inference('sup-', [status(thm)], ['21', '22'])).
% 0.53/0.72  thf('24', plain, ((l1_struct_0 @ sk_A)),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('25', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((v2_struct_0 @ sk_A)
% 0.53/0.72          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.53/0.72          | (r2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.53/0.72             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.53/0.72          | (v2_struct_0 @ sk_B_1))),
% 0.53/0.72      inference('demod', [status(thm)], ['23', '24'])).
% 0.53/0.72  thf('26', plain,
% 0.53/0.72      (((r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0)
% 0.53/0.72        | (v2_struct_0 @ sk_B_1)
% 0.53/0.72        | (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.53/0.72        | (v2_struct_0 @ sk_A))),
% 0.53/0.72      inference('sup+', [status(thm)], ['20', '25'])).
% 0.53/0.72  thf('27', plain, (~ (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('28', plain,
% 0.53/0.72      (((v2_struct_0 @ sk_A)
% 0.53/0.72        | (v2_struct_0 @ sk_B_1)
% 0.53/0.72        | (r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0))),
% 0.53/0.72      inference('sup-', [status(thm)], ['26', '27'])).
% 0.53/0.72  thf('29', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('30', plain,
% 0.53/0.72      (((r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0) | (v2_struct_0 @ sk_B_1))),
% 0.53/0.72      inference('clc', [status(thm)], ['28', '29'])).
% 0.53/0.72  thf('31', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('32', plain, ((r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0)),
% 0.53/0.72      inference('clc', [status(thm)], ['30', '31'])).
% 0.53/0.72  thf('33', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('34', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf(d12_waybel_0, axiom,
% 0.53/0.72    (![A:$i]:
% 0.53/0.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.53/0.72       ( ![B:$i]:
% 0.53/0.72         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.53/0.72           ( ![C:$i]:
% 0.53/0.72             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.53/0.72               ( ![D:$i]:
% 0.53/0.72                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.53/0.72                   ( ?[E:$i]:
% 0.53/0.72                     ( ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) & 
% 0.53/0.72                       ( r1_orders_2 @ B @ D @ E ) & 
% 0.53/0.72                       ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.53/0.72  thf('35', plain,
% 0.53/0.72      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.53/0.72         ((v2_struct_0 @ X12)
% 0.53/0.72          | ~ (l1_waybel_0 @ X12 @ X13)
% 0.53/0.72          | (m1_subset_1 @ (sk_D_1 @ X14 @ X12 @ X13) @ (u1_struct_0 @ X12))
% 0.53/0.72          | (r2_waybel_0 @ X13 @ X12 @ X14)
% 0.53/0.72          | ~ (l1_struct_0 @ X13)
% 0.53/0.72          | (v2_struct_0 @ X13))),
% 0.53/0.72      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.53/0.72  thf('36', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((v2_struct_0 @ sk_A)
% 0.53/0.72          | ~ (l1_struct_0 @ sk_A)
% 0.53/0.72          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.53/0.72          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ 
% 0.53/0.72             (u1_struct_0 @ sk_B_1))
% 0.53/0.72          | (v2_struct_0 @ sk_B_1))),
% 0.53/0.72      inference('sup-', [status(thm)], ['34', '35'])).
% 0.53/0.72  thf('37', plain, ((l1_struct_0 @ sk_A)),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('38', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((v2_struct_0 @ sk_A)
% 0.53/0.72          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.53/0.72          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ 
% 0.53/0.72             (u1_struct_0 @ sk_B_1))
% 0.53/0.72          | (v2_struct_0 @ sk_B_1))),
% 0.53/0.72      inference('demod', [status(thm)], ['36', '37'])).
% 0.53/0.72  thf('39', plain,
% 0.53/0.72      (![X12 : $i, X13 : $i, X16 : $i, X17 : $i]:
% 0.53/0.72         ((v2_struct_0 @ X12)
% 0.53/0.72          | ~ (l1_waybel_0 @ X12 @ X13)
% 0.53/0.72          | ~ (r2_waybel_0 @ X13 @ X12 @ X16)
% 0.53/0.72          | (r2_hidden @ 
% 0.53/0.72             (k2_waybel_0 @ X13 @ X12 @ (sk_E @ X17 @ X16 @ X12 @ X13)) @ X16)
% 0.53/0.72          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X12))
% 0.53/0.72          | ~ (l1_struct_0 @ X13)
% 0.53/0.72          | (v2_struct_0 @ X13))),
% 0.53/0.72      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.53/0.72  thf('40', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.72         ((v2_struct_0 @ sk_B_1)
% 0.53/0.72          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.53/0.72          | (v2_struct_0 @ sk_A)
% 0.53/0.72          | (v2_struct_0 @ X1)
% 0.53/0.72          | ~ (l1_struct_0 @ X1)
% 0.53/0.72          | (r2_hidden @ 
% 0.53/0.72             (k2_waybel_0 @ X1 @ sk_B_1 @ 
% 0.53/0.72              (sk_E @ (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ X2 @ sk_B_1 @ X1)) @ 
% 0.53/0.72             X2)
% 0.53/0.72          | ~ (r2_waybel_0 @ X1 @ sk_B_1 @ X2)
% 0.53/0.72          | ~ (l1_waybel_0 @ sk_B_1 @ X1)
% 0.53/0.72          | (v2_struct_0 @ sk_B_1))),
% 0.53/0.72      inference('sup-', [status(thm)], ['38', '39'])).
% 0.53/0.72  thf('41', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.72         (~ (l1_waybel_0 @ sk_B_1 @ X1)
% 0.53/0.72          | ~ (r2_waybel_0 @ X1 @ sk_B_1 @ X2)
% 0.53/0.72          | (r2_hidden @ 
% 0.53/0.72             (k2_waybel_0 @ X1 @ sk_B_1 @ 
% 0.53/0.72              (sk_E @ (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ X2 @ sk_B_1 @ X1)) @ 
% 0.53/0.72             X2)
% 0.53/0.72          | ~ (l1_struct_0 @ X1)
% 0.53/0.72          | (v2_struct_0 @ X1)
% 0.53/0.72          | (v2_struct_0 @ sk_A)
% 0.53/0.72          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.53/0.72          | (v2_struct_0 @ sk_B_1))),
% 0.53/0.72      inference('simplify', [status(thm)], ['40'])).
% 0.53/0.72  thf('42', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         ((v2_struct_0 @ sk_B_1)
% 0.53/0.72          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.53/0.72          | (v2_struct_0 @ sk_A)
% 0.53/0.72          | (v2_struct_0 @ sk_A)
% 0.53/0.72          | ~ (l1_struct_0 @ sk_A)
% 0.53/0.72          | (r2_hidden @ 
% 0.53/0.72             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.53/0.72              (sk_E @ (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ X1 @ sk_B_1 @ sk_A)) @ 
% 0.53/0.72             X1)
% 0.53/0.72          | ~ (r2_waybel_0 @ sk_A @ sk_B_1 @ X1))),
% 0.53/0.72      inference('sup-', [status(thm)], ['33', '41'])).
% 0.53/0.72  thf('43', plain, ((l1_struct_0 @ sk_A)),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('44', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         ((v2_struct_0 @ sk_B_1)
% 0.53/0.72          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.53/0.72          | (v2_struct_0 @ sk_A)
% 0.53/0.72          | (v2_struct_0 @ sk_A)
% 0.53/0.72          | (r2_hidden @ 
% 0.53/0.72             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.53/0.72              (sk_E @ (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ X1 @ sk_B_1 @ sk_A)) @ 
% 0.53/0.72             X1)
% 0.53/0.72          | ~ (r2_waybel_0 @ sk_A @ sk_B_1 @ X1))),
% 0.53/0.72      inference('demod', [status(thm)], ['42', '43'])).
% 0.53/0.72  thf('45', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         (~ (r2_waybel_0 @ sk_A @ sk_B_1 @ X1)
% 0.53/0.72          | (r2_hidden @ 
% 0.53/0.72             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.53/0.72              (sk_E @ (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ X1 @ sk_B_1 @ sk_A)) @ 
% 0.53/0.72             X1)
% 0.53/0.72          | (v2_struct_0 @ sk_A)
% 0.53/0.72          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.53/0.72          | (v2_struct_0 @ sk_B_1))),
% 0.53/0.72      inference('simplify', [status(thm)], ['44'])).
% 0.53/0.72  thf('46', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((v2_struct_0 @ sk_B_1)
% 0.53/0.72          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.53/0.72          | (v2_struct_0 @ sk_A)
% 0.53/0.72          | (r2_hidden @ 
% 0.53/0.72             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.53/0.72              (sk_E @ (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ k1_xboole_0 @ sk_B_1 @ 
% 0.53/0.72               sk_A)) @ 
% 0.53/0.72             k1_xboole_0))),
% 0.53/0.72      inference('sup-', [status(thm)], ['32', '45'])).
% 0.53/0.72  thf('47', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.53/0.72      inference('condensation', [status(thm)], ['18'])).
% 0.53/0.72  thf('48', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((v2_struct_0 @ sk_A)
% 0.53/0.72          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.53/0.72          | (v2_struct_0 @ sk_B_1))),
% 0.53/0.72      inference('sup-', [status(thm)], ['46', '47'])).
% 0.53/0.72  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('50', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((v2_struct_0 @ sk_B_1) | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0))),
% 0.53/0.72      inference('clc', [status(thm)], ['48', '49'])).
% 0.53/0.72  thf('51', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('52', plain, (![X0 : $i]: (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)),
% 0.53/0.72      inference('clc', [status(thm)], ['50', '51'])).
% 0.53/0.72  thf('53', plain, (![X0 : $i]: (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)),
% 0.53/0.72      inference('clc', [status(thm)], ['50', '51'])).
% 0.53/0.72  thf(existence_m1_subset_1, axiom,
% 0.53/0.72    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.53/0.72  thf('54', plain, (![X7 : $i]: (m1_subset_1 @ (sk_B @ X7) @ X7)),
% 0.53/0.72      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.53/0.72  thf('55', plain,
% 0.53/0.72      (![X12 : $i, X13 : $i, X16 : $i, X17 : $i]:
% 0.53/0.72         ((v2_struct_0 @ X12)
% 0.53/0.72          | ~ (l1_waybel_0 @ X12 @ X13)
% 0.53/0.72          | ~ (r2_waybel_0 @ X13 @ X12 @ X16)
% 0.53/0.72          | (m1_subset_1 @ (sk_E @ X17 @ X16 @ X12 @ X13) @ (u1_struct_0 @ X12))
% 0.53/0.72          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X12))
% 0.53/0.72          | ~ (l1_struct_0 @ X13)
% 0.53/0.72          | (v2_struct_0 @ X13))),
% 0.53/0.72      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.53/0.72  thf('56', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.72         ((v2_struct_0 @ X1)
% 0.53/0.72          | ~ (l1_struct_0 @ X1)
% 0.53/0.72          | (m1_subset_1 @ 
% 0.53/0.72             (sk_E @ (sk_B @ (u1_struct_0 @ X0)) @ X2 @ X0 @ X1) @ 
% 0.53/0.72             (u1_struct_0 @ X0))
% 0.53/0.72          | ~ (r2_waybel_0 @ X1 @ X0 @ X2)
% 0.53/0.72          | ~ (l1_waybel_0 @ X0 @ X1)
% 0.53/0.72          | (v2_struct_0 @ X0))),
% 0.53/0.72      inference('sup-', [status(thm)], ['54', '55'])).
% 0.53/0.72  thf('57', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((v2_struct_0 @ sk_B_1)
% 0.53/0.72          | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.53/0.72          | (m1_subset_1 @ 
% 0.53/0.72             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.53/0.72             (u1_struct_0 @ sk_B_1))
% 0.53/0.72          | ~ (l1_struct_0 @ sk_A)
% 0.53/0.72          | (v2_struct_0 @ sk_A))),
% 0.53/0.72      inference('sup-', [status(thm)], ['53', '56'])).
% 0.53/0.72  thf('58', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('59', plain, ((l1_struct_0 @ sk_A)),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('60', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((v2_struct_0 @ sk_B_1)
% 0.53/0.72          | (m1_subset_1 @ 
% 0.53/0.72             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.53/0.72             (u1_struct_0 @ sk_B_1))
% 0.53/0.72          | (v2_struct_0 @ sk_A))),
% 0.53/0.72      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.53/0.72  thf('61', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('62', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((v2_struct_0 @ sk_A)
% 0.53/0.72          | (m1_subset_1 @ 
% 0.53/0.72             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.53/0.72             (u1_struct_0 @ sk_B_1)))),
% 0.53/0.72      inference('clc', [status(thm)], ['60', '61'])).
% 0.53/0.72  thf('63', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('64', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (m1_subset_1 @ 
% 0.53/0.72          (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.53/0.72          (u1_struct_0 @ sk_B_1))),
% 0.53/0.72      inference('clc', [status(thm)], ['62', '63'])).
% 0.53/0.72  thf('65', plain,
% 0.53/0.72      (![X12 : $i, X13 : $i, X16 : $i, X17 : $i]:
% 0.53/0.72         ((v2_struct_0 @ X12)
% 0.53/0.72          | ~ (l1_waybel_0 @ X12 @ X13)
% 0.53/0.72          | ~ (r2_waybel_0 @ X13 @ X12 @ X16)
% 0.53/0.72          | (r2_hidden @ 
% 0.53/0.72             (k2_waybel_0 @ X13 @ X12 @ (sk_E @ X17 @ X16 @ X12 @ X13)) @ X16)
% 0.53/0.72          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X12))
% 0.53/0.72          | ~ (l1_struct_0 @ X13)
% 0.53/0.72          | (v2_struct_0 @ X13))),
% 0.53/0.72      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.53/0.72  thf('66', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.72         ((v2_struct_0 @ X1)
% 0.53/0.72          | ~ (l1_struct_0 @ X1)
% 0.53/0.72          | (r2_hidden @ 
% 0.53/0.72             (k2_waybel_0 @ X1 @ sk_B_1 @ 
% 0.53/0.72              (sk_E @ 
% 0.53/0.72               (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.53/0.72               X2 @ sk_B_1 @ X1)) @ 
% 0.53/0.72             X2)
% 0.53/0.72          | ~ (r2_waybel_0 @ X1 @ sk_B_1 @ X2)
% 0.53/0.72          | ~ (l1_waybel_0 @ sk_B_1 @ X1)
% 0.53/0.72          | (v2_struct_0 @ sk_B_1))),
% 0.53/0.72      inference('sup-', [status(thm)], ['64', '65'])).
% 0.53/0.72  thf('67', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         ((v2_struct_0 @ sk_B_1)
% 0.53/0.72          | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.53/0.72          | (r2_hidden @ 
% 0.53/0.72             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.53/0.72              (sk_E @ 
% 0.53/0.72               (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X1 @ sk_B_1 @ sk_A) @ 
% 0.53/0.72               X0 @ sk_B_1 @ sk_A)) @ 
% 0.53/0.72             X0)
% 0.53/0.72          | ~ (l1_struct_0 @ sk_A)
% 0.53/0.72          | (v2_struct_0 @ sk_A))),
% 0.53/0.72      inference('sup-', [status(thm)], ['52', '66'])).
% 0.53/0.72  thf('68', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('69', plain, ((l1_struct_0 @ sk_A)),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('70', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         ((v2_struct_0 @ sk_B_1)
% 0.53/0.72          | (r2_hidden @ 
% 0.53/0.72             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.53/0.72              (sk_E @ 
% 0.53/0.72               (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X1 @ sk_B_1 @ sk_A) @ 
% 0.53/0.72               X0 @ sk_B_1 @ sk_A)) @ 
% 0.53/0.72             X0)
% 0.53/0.72          | (v2_struct_0 @ sk_A))),
% 0.53/0.72      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.53/0.72  thf('71', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('72', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         ((v2_struct_0 @ sk_A)
% 0.53/0.72          | (r2_hidden @ 
% 0.53/0.72             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.53/0.72              (sk_E @ 
% 0.53/0.72               (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X1 @ sk_B_1 @ sk_A) @ 
% 0.53/0.72               X0 @ sk_B_1 @ sk_A)) @ 
% 0.53/0.72             X0))),
% 0.53/0.72      inference('clc', [status(thm)], ['70', '71'])).
% 0.53/0.72  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('74', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         (r2_hidden @ 
% 0.53/0.72          (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.53/0.72           (sk_E @ 
% 0.53/0.72            (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X1 @ sk_B_1 @ sk_A) @ 
% 0.53/0.72            X0 @ sk_B_1 @ sk_A)) @ 
% 0.53/0.72          X0)),
% 0.53/0.72      inference('clc', [status(thm)], ['72', '73'])).
% 0.53/0.72  thf('75', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.53/0.72      inference('condensation', [status(thm)], ['18'])).
% 0.53/0.72  thf('76', plain, ($false), inference('sup-', [status(thm)], ['74', '75'])).
% 0.53/0.72  
% 0.53/0.72  % SZS output end Refutation
% 0.53/0.72  
% 0.53/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
