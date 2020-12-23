%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JkLTBovUMp

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:59 EST 2020

% Result     : Theorem 1.89s
% Output     : Refutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 204 expanded)
%              Number of leaves         :   29 (  72 expanded)
%              Depth                    :   21
%              Number of atoms          :  919 (2367 expanded)
%              Number of equality atoms :   21 (  51 expanded)
%              Maximal formula depth    :   20 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_waybel_0_type,type,(
    r2_waybel_0: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X14: $i,X15: $i] :
      ( ( k6_subset_1 @ X14 @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( l1_waybel_0 @ X22 @ X23 )
      | ( r1_waybel_0 @ X23 @ X22 @ ( k6_subset_1 @ ( u1_struct_0 @ X23 ) @ X24 ) )
      | ( r2_waybel_0 @ X23 @ X22 @ X24 )
      | ~ ( l1_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( l1_waybel_0 @ X26 @ X27 )
      | ~ ( r1_waybel_0 @ X27 @ X26 @ X28 )
      | ( r1_waybel_0 @ X27 @ X26 @ X29 )
      | ~ ( r1_tarski @ X28 @ X29 )
      | ~ ( l1_struct_0 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
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

thf('27',plain,(
    ! [X0: $i] :
      ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['24','25'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('28',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ ( sk_B @ X13 ) @ X13 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

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

thf('29',plain,(
    ! [X16: $i,X17: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( l1_waybel_0 @ X16 @ X17 )
      | ~ ( r2_waybel_0 @ X17 @ X16 @ X20 )
      | ( m1_subset_1 @ ( sk_E @ X21 @ X20 @ X16 @ X17 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X2 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_waybel_0 @ X1 @ X0 @ X2 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X16: $i,X17: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( l1_waybel_0 @ X16 @ X17 )
      | ~ ( r2_waybel_0 @ X17 @ X16 @ X20 )
      | ( r2_hidden @ ( k2_waybel_0 @ X17 @ X16 @ ( sk_E @ X21 @ X20 @ X16 @ X17 ) ) @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ X2 @ sk_B_1 @ X1 ) ) @ X2 )
      | ~ ( r2_waybel_0 @ X1 @ sk_B_1 @ X2 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ X1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X1 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','40'])).

thf('42',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X1 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X1 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X1 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('50',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k6_subset_1 @ X14 @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('51',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k6_subset_1 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('53',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k6_subset_1 @ X14 @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('54',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k6_subset_1 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k6_subset_1 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k6_subset_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k6_subset_1 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k6_subset_1 @ X5 @ X6 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k6_subset_1 @ X1 @ X0 )
        = ( k6_subset_1 @ X2 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ ( k6_subset_1 @ X1 @ X0 ) @ X2 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k6_subset_1 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('60',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('61',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k6_subset_1 @ X14 @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('63',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k6_subset_1 @ X5 @ X6 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k6_subset_1 @ X1 @ X0 )
        = ( k6_subset_1 @ X2 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k6_subset_1 @ X1 @ X0 ) @ X2 @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_subset_1 @ X0 @ X0 )
        = ( k6_subset_1 @ X1 @ X1 ) )
      | ( ( k6_subset_1 @ X0 @ X0 )
        = ( k6_subset_1 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['58','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k6_subset_1 @ X1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k6_subset_1 @ X5 @ X6 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k6_subset_1 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k6_subset_1 @ X0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['68'])).

thf('70',plain,(
    $false ),
    inference('sup-',[status(thm)],['48','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JkLTBovUMp
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:46:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.89/2.09  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.89/2.09  % Solved by: fo/fo7.sh
% 1.89/2.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.89/2.09  % done 1886 iterations in 1.639s
% 1.89/2.09  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.89/2.09  % SZS output start Refutation
% 1.89/2.09  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.89/2.09  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 1.89/2.09  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.89/2.09  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 1.89/2.09  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 1.89/2.09  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 1.89/2.09  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.89/2.09  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.89/2.09  thf(r2_waybel_0_type, type, r2_waybel_0: $i > $i > $i > $o).
% 1.89/2.09  thf(sk_B_type, type, sk_B: $i > $i).
% 1.89/2.09  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 1.89/2.09  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 1.89/2.09  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.89/2.09  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.89/2.09  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 1.89/2.09  thf(sk_A_type, type, sk_A: $i).
% 1.89/2.09  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.89/2.09  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 1.89/2.09  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.89/2.09  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.89/2.09  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.89/2.09  thf(d3_tarski, axiom,
% 1.89/2.09    (![A:$i,B:$i]:
% 1.89/2.09     ( ( r1_tarski @ A @ B ) <=>
% 1.89/2.09       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.89/2.09  thf('0', plain,
% 1.89/2.09      (![X1 : $i, X3 : $i]:
% 1.89/2.09         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.89/2.09      inference('cnf', [status(esa)], [d3_tarski])).
% 1.89/2.09  thf(d5_xboole_0, axiom,
% 1.89/2.09    (![A:$i,B:$i,C:$i]:
% 1.89/2.09     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.89/2.09       ( ![D:$i]:
% 1.89/2.09         ( ( r2_hidden @ D @ C ) <=>
% 1.89/2.09           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.89/2.09  thf('1', plain,
% 1.89/2.09      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.89/2.09         (~ (r2_hidden @ X8 @ X7)
% 1.89/2.09          | (r2_hidden @ X8 @ X5)
% 1.89/2.09          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 1.89/2.09      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.89/2.09  thf('2', plain,
% 1.89/2.09      (![X5 : $i, X6 : $i, X8 : $i]:
% 1.89/2.09         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 1.89/2.09      inference('simplify', [status(thm)], ['1'])).
% 1.89/2.09  thf(redefinition_k6_subset_1, axiom,
% 1.89/2.09    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.89/2.09  thf('3', plain,
% 1.89/2.09      (![X14 : $i, X15 : $i]:
% 1.89/2.09         ((k6_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))),
% 1.89/2.09      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.89/2.09  thf('4', plain,
% 1.89/2.09      (![X5 : $i, X6 : $i, X8 : $i]:
% 1.89/2.09         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k6_subset_1 @ X5 @ X6)))),
% 1.89/2.09      inference('demod', [status(thm)], ['2', '3'])).
% 1.89/2.09  thf('5', plain,
% 1.89/2.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.89/2.09         ((r1_tarski @ (k6_subset_1 @ X1 @ X0) @ X2)
% 1.89/2.09          | (r2_hidden @ (sk_C @ X2 @ (k6_subset_1 @ X1 @ X0)) @ X1))),
% 1.89/2.09      inference('sup-', [status(thm)], ['0', '4'])).
% 1.89/2.09  thf('6', plain,
% 1.89/2.09      (![X1 : $i, X3 : $i]:
% 1.89/2.09         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.89/2.09      inference('cnf', [status(esa)], [d3_tarski])).
% 1.89/2.09  thf('7', plain,
% 1.89/2.09      (![X0 : $i, X1 : $i]:
% 1.89/2.09         ((r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)
% 1.89/2.09          | (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0))),
% 1.89/2.09      inference('sup-', [status(thm)], ['5', '6'])).
% 1.89/2.09  thf('8', plain,
% 1.89/2.09      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)),
% 1.89/2.09      inference('simplify', [status(thm)], ['7'])).
% 1.89/2.09  thf(t29_yellow_6, conjecture,
% 1.89/2.09    (![A:$i]:
% 1.89/2.09     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.89/2.09       ( ![B:$i]:
% 1.89/2.09         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 1.89/2.09             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 1.89/2.09           ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ))).
% 1.89/2.09  thf(zf_stmt_0, negated_conjecture,
% 1.89/2.09    (~( ![A:$i]:
% 1.89/2.09        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.89/2.09          ( ![B:$i]:
% 1.89/2.09            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 1.89/2.09                ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 1.89/2.09              ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ) )),
% 1.89/2.09    inference('cnf.neg', [status(esa)], [t29_yellow_6])).
% 1.89/2.09  thf('9', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 1.89/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.09  thf(t10_waybel_0, axiom,
% 1.89/2.09    (![A:$i]:
% 1.89/2.09     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.89/2.09       ( ![B:$i]:
% 1.89/2.09         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 1.89/2.09           ( ![C:$i]:
% 1.89/2.09             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 1.89/2.09               ( ~( r1_waybel_0 @
% 1.89/2.09                    A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ))).
% 1.89/2.09  thf('10', plain,
% 1.89/2.09      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.89/2.09         ((v2_struct_0 @ X22)
% 1.89/2.09          | ~ (l1_waybel_0 @ X22 @ X23)
% 1.89/2.09          | (r1_waybel_0 @ X23 @ X22 @ 
% 1.89/2.09             (k6_subset_1 @ (u1_struct_0 @ X23) @ X24))
% 1.89/2.09          | (r2_waybel_0 @ X23 @ X22 @ X24)
% 1.89/2.09          | ~ (l1_struct_0 @ X23)
% 1.89/2.09          | (v2_struct_0 @ X23))),
% 1.89/2.09      inference('cnf', [status(esa)], [t10_waybel_0])).
% 1.89/2.09  thf('11', plain,
% 1.89/2.09      (![X0 : $i]:
% 1.89/2.09         ((v2_struct_0 @ sk_A)
% 1.89/2.09          | ~ (l1_struct_0 @ sk_A)
% 1.89/2.09          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 1.89/2.09          | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 1.89/2.09             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 1.89/2.09          | (v2_struct_0 @ sk_B_1))),
% 1.89/2.09      inference('sup-', [status(thm)], ['9', '10'])).
% 1.89/2.09  thf('12', plain, ((l1_struct_0 @ sk_A)),
% 1.89/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.09  thf('13', plain,
% 1.89/2.09      (![X0 : $i]:
% 1.89/2.09         ((v2_struct_0 @ sk_A)
% 1.89/2.09          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 1.89/2.09          | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 1.89/2.09             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 1.89/2.09          | (v2_struct_0 @ sk_B_1))),
% 1.89/2.09      inference('demod', [status(thm)], ['11', '12'])).
% 1.89/2.09  thf(t8_waybel_0, axiom,
% 1.89/2.09    (![A:$i]:
% 1.89/2.09     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.89/2.09       ( ![B:$i]:
% 1.89/2.09         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 1.89/2.09           ( ![C:$i,D:$i]:
% 1.89/2.09             ( ( r1_tarski @ C @ D ) =>
% 1.89/2.09               ( ( ( r1_waybel_0 @ A @ B @ C ) => ( r1_waybel_0 @ A @ B @ D ) ) & 
% 1.89/2.09                 ( ( r2_waybel_0 @ A @ B @ C ) => ( r2_waybel_0 @ A @ B @ D ) ) ) ) ) ) ) ))).
% 1.89/2.09  thf('14', plain,
% 1.89/2.09      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.89/2.09         ((v2_struct_0 @ X26)
% 1.89/2.09          | ~ (l1_waybel_0 @ X26 @ X27)
% 1.89/2.09          | ~ (r1_waybel_0 @ X27 @ X26 @ X28)
% 1.89/2.09          | (r1_waybel_0 @ X27 @ X26 @ X29)
% 1.89/2.09          | ~ (r1_tarski @ X28 @ X29)
% 1.89/2.09          | ~ (l1_struct_0 @ X27)
% 1.89/2.09          | (v2_struct_0 @ X27))),
% 1.89/2.09      inference('cnf', [status(esa)], [t8_waybel_0])).
% 1.89/2.09  thf('15', plain,
% 1.89/2.09      (![X0 : $i, X1 : $i]:
% 1.89/2.09         ((v2_struct_0 @ sk_B_1)
% 1.89/2.09          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 1.89/2.09          | (v2_struct_0 @ sk_A)
% 1.89/2.09          | (v2_struct_0 @ sk_A)
% 1.89/2.09          | ~ (l1_struct_0 @ sk_A)
% 1.89/2.09          | ~ (r1_tarski @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ X1)
% 1.89/2.09          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X1)
% 1.89/2.09          | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 1.89/2.09          | (v2_struct_0 @ sk_B_1))),
% 1.89/2.09      inference('sup-', [status(thm)], ['13', '14'])).
% 1.89/2.09  thf('16', plain, ((l1_struct_0 @ sk_A)),
% 1.89/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.09  thf('17', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 1.89/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.09  thf('18', plain,
% 1.89/2.09      (![X0 : $i, X1 : $i]:
% 1.89/2.09         ((v2_struct_0 @ sk_B_1)
% 1.89/2.09          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 1.89/2.09          | (v2_struct_0 @ sk_A)
% 1.89/2.09          | (v2_struct_0 @ sk_A)
% 1.89/2.09          | ~ (r1_tarski @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ X1)
% 1.89/2.09          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X1)
% 1.89/2.09          | (v2_struct_0 @ sk_B_1))),
% 1.89/2.09      inference('demod', [status(thm)], ['15', '16', '17'])).
% 1.89/2.09  thf('19', plain,
% 1.89/2.09      (![X0 : $i, X1 : $i]:
% 1.89/2.09         ((r1_waybel_0 @ sk_A @ sk_B_1 @ X1)
% 1.89/2.09          | ~ (r1_tarski @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ X1)
% 1.89/2.09          | (v2_struct_0 @ sk_A)
% 1.89/2.09          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 1.89/2.09          | (v2_struct_0 @ sk_B_1))),
% 1.89/2.09      inference('simplify', [status(thm)], ['18'])).
% 1.89/2.09  thf('20', plain,
% 1.89/2.09      (![X0 : $i]:
% 1.89/2.09         ((v2_struct_0 @ sk_B_1)
% 1.89/2.09          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 1.89/2.09          | (v2_struct_0 @ sk_A)
% 1.89/2.09          | (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 1.89/2.09      inference('sup-', [status(thm)], ['8', '19'])).
% 1.89/2.09  thf('21', plain, (~ (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 1.89/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.09  thf('22', plain,
% 1.89/2.09      (![X0 : $i]:
% 1.89/2.09         ((v2_struct_0 @ sk_A)
% 1.89/2.09          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 1.89/2.09          | (v2_struct_0 @ sk_B_1))),
% 1.89/2.09      inference('sup-', [status(thm)], ['20', '21'])).
% 1.89/2.09  thf('23', plain, (~ (v2_struct_0 @ sk_A)),
% 1.89/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.09  thf('24', plain,
% 1.89/2.09      (![X0 : $i]:
% 1.89/2.09         ((v2_struct_0 @ sk_B_1) | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0))),
% 1.89/2.09      inference('clc', [status(thm)], ['22', '23'])).
% 1.89/2.09  thf('25', plain, (~ (v2_struct_0 @ sk_B_1)),
% 1.89/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.09  thf('26', plain, (![X0 : $i]: (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)),
% 1.89/2.09      inference('clc', [status(thm)], ['24', '25'])).
% 1.89/2.09  thf('27', plain, (![X0 : $i]: (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)),
% 1.89/2.09      inference('clc', [status(thm)], ['24', '25'])).
% 1.89/2.09  thf(existence_m1_subset_1, axiom,
% 1.89/2.09    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 1.89/2.09  thf('28', plain, (![X13 : $i]: (m1_subset_1 @ (sk_B @ X13) @ X13)),
% 1.89/2.09      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 1.89/2.09  thf(d12_waybel_0, axiom,
% 1.89/2.09    (![A:$i]:
% 1.89/2.09     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.89/2.09       ( ![B:$i]:
% 1.89/2.09         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 1.89/2.09           ( ![C:$i]:
% 1.89/2.09             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 1.89/2.09               ( ![D:$i]:
% 1.89/2.09                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 1.89/2.09                   ( ?[E:$i]:
% 1.89/2.09                     ( ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) & 
% 1.89/2.09                       ( r1_orders_2 @ B @ D @ E ) & 
% 1.89/2.09                       ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ))).
% 1.89/2.09  thf('29', plain,
% 1.89/2.09      (![X16 : $i, X17 : $i, X20 : $i, X21 : $i]:
% 1.89/2.09         ((v2_struct_0 @ X16)
% 1.89/2.09          | ~ (l1_waybel_0 @ X16 @ X17)
% 1.89/2.09          | ~ (r2_waybel_0 @ X17 @ X16 @ X20)
% 1.89/2.09          | (m1_subset_1 @ (sk_E @ X21 @ X20 @ X16 @ X17) @ (u1_struct_0 @ X16))
% 1.89/2.09          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X16))
% 1.89/2.09          | ~ (l1_struct_0 @ X17)
% 1.89/2.09          | (v2_struct_0 @ X17))),
% 1.89/2.09      inference('cnf', [status(esa)], [d12_waybel_0])).
% 1.89/2.09  thf('30', plain,
% 1.89/2.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.89/2.09         ((v2_struct_0 @ X1)
% 1.89/2.09          | ~ (l1_struct_0 @ X1)
% 1.89/2.09          | (m1_subset_1 @ 
% 1.89/2.09             (sk_E @ (sk_B @ (u1_struct_0 @ X0)) @ X2 @ X0 @ X1) @ 
% 1.89/2.09             (u1_struct_0 @ X0))
% 1.89/2.09          | ~ (r2_waybel_0 @ X1 @ X0 @ X2)
% 1.89/2.09          | ~ (l1_waybel_0 @ X0 @ X1)
% 1.89/2.09          | (v2_struct_0 @ X0))),
% 1.89/2.09      inference('sup-', [status(thm)], ['28', '29'])).
% 1.89/2.09  thf('31', plain,
% 1.89/2.09      (![X0 : $i]:
% 1.89/2.09         ((v2_struct_0 @ sk_B_1)
% 1.89/2.09          | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 1.89/2.09          | (m1_subset_1 @ 
% 1.89/2.09             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 1.89/2.09             (u1_struct_0 @ sk_B_1))
% 1.89/2.09          | ~ (l1_struct_0 @ sk_A)
% 1.89/2.09          | (v2_struct_0 @ sk_A))),
% 1.89/2.09      inference('sup-', [status(thm)], ['27', '30'])).
% 1.89/2.09  thf('32', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 1.89/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.09  thf('33', plain, ((l1_struct_0 @ sk_A)),
% 1.89/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.09  thf('34', plain,
% 1.89/2.09      (![X0 : $i]:
% 1.89/2.09         ((v2_struct_0 @ sk_B_1)
% 1.89/2.09          | (m1_subset_1 @ 
% 1.89/2.09             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 1.89/2.09             (u1_struct_0 @ sk_B_1))
% 1.89/2.09          | (v2_struct_0 @ sk_A))),
% 1.89/2.09      inference('demod', [status(thm)], ['31', '32', '33'])).
% 1.89/2.09  thf('35', plain, (~ (v2_struct_0 @ sk_B_1)),
% 1.89/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.09  thf('36', plain,
% 1.89/2.09      (![X0 : $i]:
% 1.89/2.09         ((v2_struct_0 @ sk_A)
% 1.89/2.09          | (m1_subset_1 @ 
% 1.89/2.09             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 1.89/2.09             (u1_struct_0 @ sk_B_1)))),
% 1.89/2.09      inference('clc', [status(thm)], ['34', '35'])).
% 1.89/2.09  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 1.89/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.09  thf('38', plain,
% 1.89/2.09      (![X0 : $i]:
% 1.89/2.09         (m1_subset_1 @ 
% 1.89/2.09          (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 1.89/2.09          (u1_struct_0 @ sk_B_1))),
% 1.89/2.09      inference('clc', [status(thm)], ['36', '37'])).
% 1.89/2.09  thf('39', plain,
% 1.89/2.09      (![X16 : $i, X17 : $i, X20 : $i, X21 : $i]:
% 1.89/2.09         ((v2_struct_0 @ X16)
% 1.89/2.09          | ~ (l1_waybel_0 @ X16 @ X17)
% 1.89/2.09          | ~ (r2_waybel_0 @ X17 @ X16 @ X20)
% 1.89/2.09          | (r2_hidden @ 
% 1.89/2.09             (k2_waybel_0 @ X17 @ X16 @ (sk_E @ X21 @ X20 @ X16 @ X17)) @ X20)
% 1.89/2.09          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X16))
% 1.89/2.09          | ~ (l1_struct_0 @ X17)
% 1.89/2.09          | (v2_struct_0 @ X17))),
% 1.89/2.09      inference('cnf', [status(esa)], [d12_waybel_0])).
% 1.89/2.09  thf('40', plain,
% 1.89/2.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.89/2.09         ((v2_struct_0 @ X1)
% 1.89/2.09          | ~ (l1_struct_0 @ X1)
% 1.89/2.09          | (r2_hidden @ 
% 1.89/2.09             (k2_waybel_0 @ X1 @ sk_B_1 @ 
% 1.89/2.09              (sk_E @ 
% 1.89/2.09               (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 1.89/2.09               X2 @ sk_B_1 @ X1)) @ 
% 1.89/2.09             X2)
% 1.89/2.09          | ~ (r2_waybel_0 @ X1 @ sk_B_1 @ X2)
% 1.89/2.09          | ~ (l1_waybel_0 @ sk_B_1 @ X1)
% 1.89/2.09          | (v2_struct_0 @ sk_B_1))),
% 1.89/2.09      inference('sup-', [status(thm)], ['38', '39'])).
% 1.89/2.09  thf('41', plain,
% 1.89/2.09      (![X0 : $i, X1 : $i]:
% 1.89/2.09         ((v2_struct_0 @ sk_B_1)
% 1.89/2.09          | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 1.89/2.09          | (r2_hidden @ 
% 1.89/2.09             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 1.89/2.09              (sk_E @ 
% 1.89/2.09               (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X1 @ sk_B_1 @ sk_A) @ 
% 1.89/2.09               X0 @ sk_B_1 @ sk_A)) @ 
% 1.89/2.09             X0)
% 1.89/2.09          | ~ (l1_struct_0 @ sk_A)
% 1.89/2.09          | (v2_struct_0 @ sk_A))),
% 1.89/2.09      inference('sup-', [status(thm)], ['26', '40'])).
% 1.89/2.09  thf('42', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 1.89/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.09  thf('43', plain, ((l1_struct_0 @ sk_A)),
% 1.89/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.09  thf('44', plain,
% 1.89/2.09      (![X0 : $i, X1 : $i]:
% 1.89/2.09         ((v2_struct_0 @ sk_B_1)
% 1.89/2.09          | (r2_hidden @ 
% 1.89/2.09             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 1.89/2.09              (sk_E @ 
% 1.89/2.09               (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X1 @ sk_B_1 @ sk_A) @ 
% 1.89/2.09               X0 @ sk_B_1 @ sk_A)) @ 
% 1.89/2.09             X0)
% 1.89/2.09          | (v2_struct_0 @ sk_A))),
% 1.89/2.09      inference('demod', [status(thm)], ['41', '42', '43'])).
% 1.89/2.09  thf('45', plain, (~ (v2_struct_0 @ sk_B_1)),
% 1.89/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.09  thf('46', plain,
% 1.89/2.09      (![X0 : $i, X1 : $i]:
% 1.89/2.09         ((v2_struct_0 @ sk_A)
% 1.89/2.09          | (r2_hidden @ 
% 1.89/2.09             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 1.89/2.09              (sk_E @ 
% 1.89/2.09               (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X1 @ sk_B_1 @ sk_A) @ 
% 1.89/2.09               X0 @ sk_B_1 @ sk_A)) @ 
% 1.89/2.09             X0))),
% 1.89/2.09      inference('clc', [status(thm)], ['44', '45'])).
% 1.89/2.09  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 1.89/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.09  thf('48', plain,
% 1.89/2.09      (![X0 : $i, X1 : $i]:
% 1.89/2.09         (r2_hidden @ 
% 1.89/2.09          (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 1.89/2.09           (sk_E @ 
% 1.89/2.09            (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X1 @ sk_B_1 @ sk_A) @ 
% 1.89/2.09            X0 @ sk_B_1 @ sk_A)) @ 
% 1.89/2.09          X0)),
% 1.89/2.09      inference('clc', [status(thm)], ['46', '47'])).
% 1.89/2.09  thf('49', plain,
% 1.89/2.09      (![X5 : $i, X6 : $i, X9 : $i]:
% 1.89/2.09         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 1.89/2.09          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 1.89/2.09          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 1.89/2.09      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.89/2.09  thf('50', plain,
% 1.89/2.09      (![X14 : $i, X15 : $i]:
% 1.89/2.09         ((k6_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))),
% 1.89/2.09      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.89/2.09  thf('51', plain,
% 1.89/2.09      (![X5 : $i, X6 : $i, X9 : $i]:
% 1.89/2.09         (((X9) = (k6_subset_1 @ X5 @ X6))
% 1.89/2.09          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 1.89/2.09          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 1.89/2.09      inference('demod', [status(thm)], ['49', '50'])).
% 1.89/2.09  thf('52', plain,
% 1.89/2.09      (![X5 : $i, X6 : $i, X9 : $i]:
% 1.89/2.09         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 1.89/2.09          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 1.89/2.09          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 1.89/2.09      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.89/2.09  thf('53', plain,
% 1.89/2.09      (![X14 : $i, X15 : $i]:
% 1.89/2.09         ((k6_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))),
% 1.89/2.09      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.89/2.09  thf('54', plain,
% 1.89/2.09      (![X5 : $i, X6 : $i, X9 : $i]:
% 1.89/2.09         (((X9) = (k6_subset_1 @ X5 @ X6))
% 1.89/2.09          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 1.89/2.09          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 1.89/2.09      inference('demod', [status(thm)], ['52', '53'])).
% 1.89/2.09  thf('55', plain,
% 1.89/2.09      (![X0 : $i, X1 : $i]:
% 1.89/2.09         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 1.89/2.09          | ((X1) = (k6_subset_1 @ X0 @ X0))
% 1.89/2.09          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 1.89/2.09          | ((X1) = (k6_subset_1 @ X0 @ X0)))),
% 1.89/2.09      inference('sup-', [status(thm)], ['51', '54'])).
% 1.89/2.09  thf('56', plain,
% 1.89/2.09      (![X0 : $i, X1 : $i]:
% 1.89/2.09         (((X1) = (k6_subset_1 @ X0 @ X0))
% 1.89/2.09          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 1.89/2.09      inference('simplify', [status(thm)], ['55'])).
% 1.89/2.09  thf('57', plain,
% 1.89/2.09      (![X5 : $i, X6 : $i, X8 : $i]:
% 1.89/2.09         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k6_subset_1 @ X5 @ X6)))),
% 1.89/2.09      inference('demod', [status(thm)], ['2', '3'])).
% 1.89/2.09  thf('58', plain,
% 1.89/2.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.89/2.09         (((k6_subset_1 @ X1 @ X0) = (k6_subset_1 @ X2 @ X2))
% 1.89/2.09          | (r2_hidden @ (sk_D @ (k6_subset_1 @ X1 @ X0) @ X2 @ X2) @ X1))),
% 1.89/2.09      inference('sup-', [status(thm)], ['56', '57'])).
% 1.89/2.09  thf('59', plain,
% 1.89/2.09      (![X0 : $i, X1 : $i]:
% 1.89/2.09         (((X1) = (k6_subset_1 @ X0 @ X0))
% 1.89/2.09          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 1.89/2.09      inference('simplify', [status(thm)], ['55'])).
% 1.89/2.09  thf('60', plain,
% 1.89/2.09      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.89/2.09         (~ (r2_hidden @ X8 @ X7)
% 1.89/2.09          | ~ (r2_hidden @ X8 @ X6)
% 1.89/2.09          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 1.89/2.09      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.89/2.09  thf('61', plain,
% 1.89/2.09      (![X5 : $i, X6 : $i, X8 : $i]:
% 1.89/2.09         (~ (r2_hidden @ X8 @ X6)
% 1.89/2.09          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 1.89/2.09      inference('simplify', [status(thm)], ['60'])).
% 1.89/2.09  thf('62', plain,
% 1.89/2.09      (![X14 : $i, X15 : $i]:
% 1.89/2.09         ((k6_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))),
% 1.89/2.09      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.89/2.09  thf('63', plain,
% 1.89/2.09      (![X5 : $i, X6 : $i, X8 : $i]:
% 1.89/2.09         (~ (r2_hidden @ X8 @ X6)
% 1.89/2.09          | ~ (r2_hidden @ X8 @ (k6_subset_1 @ X5 @ X6)))),
% 1.89/2.09      inference('demod', [status(thm)], ['61', '62'])).
% 1.89/2.09  thf('64', plain,
% 1.89/2.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.89/2.09         (((k6_subset_1 @ X1 @ X0) = (k6_subset_1 @ X2 @ X2))
% 1.89/2.09          | ~ (r2_hidden @ (sk_D @ (k6_subset_1 @ X1 @ X0) @ X2 @ X2) @ X0))),
% 1.89/2.09      inference('sup-', [status(thm)], ['59', '63'])).
% 1.89/2.09  thf('65', plain,
% 1.89/2.09      (![X0 : $i, X1 : $i]:
% 1.89/2.09         (((k6_subset_1 @ X0 @ X0) = (k6_subset_1 @ X1 @ X1))
% 1.89/2.09          | ((k6_subset_1 @ X0 @ X0) = (k6_subset_1 @ X1 @ X1)))),
% 1.89/2.09      inference('sup-', [status(thm)], ['58', '64'])).
% 1.89/2.09  thf('66', plain,
% 1.89/2.09      (![X0 : $i, X1 : $i]: ((k6_subset_1 @ X0 @ X0) = (k6_subset_1 @ X1 @ X1))),
% 1.89/2.09      inference('simplify', [status(thm)], ['65'])).
% 1.89/2.09  thf('67', plain,
% 1.89/2.09      (![X5 : $i, X6 : $i, X8 : $i]:
% 1.89/2.09         (~ (r2_hidden @ X8 @ X6)
% 1.89/2.09          | ~ (r2_hidden @ X8 @ (k6_subset_1 @ X5 @ X6)))),
% 1.89/2.09      inference('demod', [status(thm)], ['61', '62'])).
% 1.89/2.09  thf('68', plain,
% 1.89/2.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.89/2.09         (~ (r2_hidden @ X2 @ (k6_subset_1 @ X0 @ X0))
% 1.89/2.09          | ~ (r2_hidden @ X2 @ X1))),
% 1.89/2.09      inference('sup-', [status(thm)], ['66', '67'])).
% 1.89/2.09  thf('69', plain,
% 1.89/2.09      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k6_subset_1 @ X0 @ X0))),
% 1.89/2.09      inference('condensation', [status(thm)], ['68'])).
% 1.89/2.09  thf('70', plain, ($false), inference('sup-', [status(thm)], ['48', '69'])).
% 1.89/2.09  
% 1.89/2.09  % SZS output end Refutation
% 1.89/2.09  
% 1.89/2.10  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
