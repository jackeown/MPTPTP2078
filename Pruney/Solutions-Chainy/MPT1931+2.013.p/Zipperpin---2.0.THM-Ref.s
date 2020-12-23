%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tjH1VIKoBN

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:58 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 118 expanded)
%              Number of leaves         :   33 (  50 expanded)
%              Depth                    :   16
%              Number of atoms          :  727 (1159 expanded)
%              Number of equality atoms :   17 (  23 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_waybel_0_type,type,(
    r2_waybel_0: $i > $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( r2_hidden @ X11 @ X8 )
      | ( X10
       != ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('2',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ( r2_hidden @ X11 @ X8 )
      | ~ ( r2_hidden @ X11 @ ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
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
    ! [X8: $i,X9: $i,X11: $i] :
      ( ( r2_hidden @ X11 @ X8 )
      | ~ ( r2_hidden @ X11 @ ( k6_subset_1 @ X8 @ X9 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k6_subset_1 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
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
    l1_waybel_0 @ sk_B_2 @ sk_A ),
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
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B_2 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B_2 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
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
      ( ( v2_struct_0 @ sk_B_2 )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( r1_tarski @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ X1 )
      | ( r1_waybel_0 @ sk_A @ sk_B_2 @ X1 )
      | ~ ( l1_waybel_0 @ sk_B_2 @ sk_A )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_waybel_0 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r1_tarski @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ X1 )
      | ( r1_waybel_0 @ sk_A @ sk_B_2 @ X1 )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_waybel_0 @ sk_A @ sk_B_2 @ X1 )
      | ~ ( r1_tarski @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','19'])).

thf('21',plain,(
    ~ ( r1_waybel_0 @ sk_A @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 ) ),
    inference(clc,[status(thm)],['24','25'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('27',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X13 ) @ X13 ) ),
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

thf('28',plain,(
    ! [X16: $i,X17: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( l1_waybel_0 @ X16 @ X17 )
      | ~ ( r2_waybel_0 @ X17 @ X16 @ X20 )
      | ( r2_hidden @ ( k2_waybel_0 @ X17 @ X16 @ ( sk_E @ X21 @ X20 @ X16 @ X17 ) ) @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ X0 @ ( sk_E @ ( sk_B_1 @ ( u1_struct_0 @ X0 ) ) @ X2 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r2_waybel_0 @ X1 @ X0 @ X2 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ~ ( l1_waybel_0 @ sk_B_2 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_2 @ ( sk_E @ ( sk_B_1 @ ( u1_struct_0 @ sk_B_2 ) ) @ X0 @ sk_B_2 @ sk_A ) ) @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    l1_waybel_0 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_2 @ ( sk_E @ ( sk_B_1 @ ( u1_struct_0 @ sk_B_2 ) ) @ X0 @ sk_B_2 @ sk_A ) ) @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_2 @ ( sk_E @ ( sk_B_1 @ ( u1_struct_0 @ sk_B_2 ) ) @ X0 @ sk_B_2 @ sk_A ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_2 @ ( sk_E @ ( sk_B_1 @ ( u1_struct_0 @ sk_B_2 ) ) @ X0 @ sk_B_2 @ sk_A ) ) @ X0 ) ),
    inference(clc,[status(thm)],['35','36'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('38',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('39',plain,(
    ! [X8: $i,X9: $i,X12: $i] :
      ( ( X12
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ( r2_hidden @ ( sk_D @ X12 @ X9 @ X8 ) @ X8 )
      | ( r2_hidden @ ( sk_D @ X12 @ X9 @ X8 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('40',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k6_subset_1 @ X14 @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('41',plain,(
    ! [X8: $i,X9: $i,X12: $i] :
      ( ( X12
        = ( k6_subset_1 @ X8 @ X9 ) )
      | ( r2_hidden @ ( sk_D @ X12 @ X9 @ X8 ) @ X8 )
      | ( r2_hidden @ ( sk_D @ X12 @ X9 @ X8 ) @ X12 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X8: $i,X9: $i,X12: $i] :
      ( ( X12
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( r2_hidden @ ( sk_D @ X12 @ X9 @ X8 ) @ X9 )
      | ( r2_hidden @ ( sk_D @ X12 @ X9 @ X8 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('43',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k6_subset_1 @ X14 @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('44',plain,(
    ! [X8: $i,X9: $i,X12: $i] :
      ( ( X12
        = ( k6_subset_1 @ X8 @ X9 ) )
      | ~ ( r2_hidden @ ( sk_D @ X12 @ X9 @ X8 ) @ X9 )
      | ( r2_hidden @ ( sk_D @ X12 @ X9 @ X8 ) @ X12 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k6_subset_1 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k6_subset_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k6_subset_1 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k6_subset_1 @ X1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k6_subset_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','48'])).

thf('50',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ~ ( r2_hidden @ X11 @ X9 )
      | ( X10
       != ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('51',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k6_subset_1 @ X14 @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('53',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k6_subset_1 @ X8 @ X9 ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['54'])).

thf('56',plain,(
    $false ),
    inference('sup-',[status(thm)],['37','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tjH1VIKoBN
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:57:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.53/0.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.53/0.77  % Solved by: fo/fo7.sh
% 0.53/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.77  % done 608 iterations in 0.348s
% 0.53/0.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.53/0.77  % SZS output start Refutation
% 0.53/0.77  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.53/0.77  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.53/0.77  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.53/0.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.77  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.53/0.77  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.53/0.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.53/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.77  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 0.53/0.77  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.53/0.77  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.53/0.77  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.53/0.77  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.53/0.77  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.53/0.77  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.53/0.77  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.53/0.77  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.53/0.77  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.53/0.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.53/0.77  thf(r2_waybel_0_type, type, r2_waybel_0: $i > $i > $i > $o).
% 0.53/0.77  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.53/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.77  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.53/0.77  thf(d3_tarski, axiom,
% 0.53/0.77    (![A:$i,B:$i]:
% 0.53/0.77     ( ( r1_tarski @ A @ B ) <=>
% 0.53/0.77       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.53/0.77  thf('0', plain,
% 0.53/0.77      (![X4 : $i, X6 : $i]:
% 0.53/0.77         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.53/0.77      inference('cnf', [status(esa)], [d3_tarski])).
% 0.53/0.77  thf(d5_xboole_0, axiom,
% 0.53/0.77    (![A:$i,B:$i,C:$i]:
% 0.53/0.77     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.53/0.77       ( ![D:$i]:
% 0.53/0.77         ( ( r2_hidden @ D @ C ) <=>
% 0.53/0.77           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.53/0.77  thf('1', plain,
% 0.53/0.77      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.53/0.77         (~ (r2_hidden @ X11 @ X10)
% 0.53/0.77          | (r2_hidden @ X11 @ X8)
% 0.53/0.77          | ((X10) != (k4_xboole_0 @ X8 @ X9)))),
% 0.53/0.77      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.53/0.77  thf('2', plain,
% 0.53/0.77      (![X8 : $i, X9 : $i, X11 : $i]:
% 0.53/0.77         ((r2_hidden @ X11 @ X8)
% 0.53/0.77          | ~ (r2_hidden @ X11 @ (k4_xboole_0 @ X8 @ X9)))),
% 0.53/0.77      inference('simplify', [status(thm)], ['1'])).
% 0.53/0.77  thf(redefinition_k6_subset_1, axiom,
% 0.53/0.77    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.53/0.77  thf('3', plain,
% 0.53/0.77      (![X14 : $i, X15 : $i]:
% 0.53/0.77         ((k6_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))),
% 0.53/0.77      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.53/0.77  thf('4', plain,
% 0.53/0.77      (![X8 : $i, X9 : $i, X11 : $i]:
% 0.53/0.77         ((r2_hidden @ X11 @ X8)
% 0.53/0.77          | ~ (r2_hidden @ X11 @ (k6_subset_1 @ X8 @ X9)))),
% 0.53/0.77      inference('demod', [status(thm)], ['2', '3'])).
% 0.53/0.77  thf('5', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.77         ((r1_tarski @ (k6_subset_1 @ X1 @ X0) @ X2)
% 0.53/0.77          | (r2_hidden @ (sk_C @ X2 @ (k6_subset_1 @ X1 @ X0)) @ X1))),
% 0.53/0.77      inference('sup-', [status(thm)], ['0', '4'])).
% 0.53/0.77  thf('6', plain,
% 0.53/0.77      (![X4 : $i, X6 : $i]:
% 0.53/0.77         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.53/0.77      inference('cnf', [status(esa)], [d3_tarski])).
% 0.53/0.77  thf('7', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         ((r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)
% 0.53/0.77          | (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0))),
% 0.53/0.77      inference('sup-', [status(thm)], ['5', '6'])).
% 0.53/0.77  thf('8', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)),
% 0.53/0.77      inference('simplify', [status(thm)], ['7'])).
% 0.53/0.77  thf(t29_yellow_6, conjecture,
% 0.53/0.77    (![A:$i]:
% 0.53/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.53/0.77       ( ![B:$i]:
% 0.53/0.77         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.53/0.77             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.53/0.77           ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.53/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.77    (~( ![A:$i]:
% 0.53/0.77        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.53/0.77          ( ![B:$i]:
% 0.53/0.77            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.53/0.77                ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.53/0.77              ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ) )),
% 0.53/0.77    inference('cnf.neg', [status(esa)], [t29_yellow_6])).
% 0.53/0.77  thf('9', plain, ((l1_waybel_0 @ sk_B_2 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf(t10_waybel_0, axiom,
% 0.53/0.77    (![A:$i]:
% 0.53/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.53/0.77       ( ![B:$i]:
% 0.53/0.77         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.53/0.77           ( ![C:$i]:
% 0.53/0.77             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.53/0.77               ( ~( r1_waybel_0 @
% 0.53/0.77                    A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ))).
% 0.53/0.77  thf('10', plain,
% 0.53/0.77      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.53/0.77         ((v2_struct_0 @ X22)
% 0.53/0.77          | ~ (l1_waybel_0 @ X22 @ X23)
% 0.53/0.77          | (r1_waybel_0 @ X23 @ X22 @ 
% 0.53/0.77             (k6_subset_1 @ (u1_struct_0 @ X23) @ X24))
% 0.53/0.77          | (r2_waybel_0 @ X23 @ X22 @ X24)
% 0.53/0.77          | ~ (l1_struct_0 @ X23)
% 0.53/0.77          | (v2_struct_0 @ X23))),
% 0.53/0.77      inference('cnf', [status(esa)], [t10_waybel_0])).
% 0.53/0.77  thf('11', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         ((v2_struct_0 @ sk_A)
% 0.53/0.77          | ~ (l1_struct_0 @ sk_A)
% 0.53/0.77          | (r2_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.53/0.77          | (r1_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.53/0.77             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.53/0.77          | (v2_struct_0 @ sk_B_2))),
% 0.53/0.77      inference('sup-', [status(thm)], ['9', '10'])).
% 0.53/0.77  thf('12', plain, ((l1_struct_0 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('13', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         ((v2_struct_0 @ sk_A)
% 0.53/0.77          | (r2_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.53/0.77          | (r1_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.53/0.77             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.53/0.77          | (v2_struct_0 @ sk_B_2))),
% 0.53/0.77      inference('demod', [status(thm)], ['11', '12'])).
% 0.53/0.77  thf(t8_waybel_0, axiom,
% 0.53/0.77    (![A:$i]:
% 0.53/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.53/0.77       ( ![B:$i]:
% 0.53/0.77         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.53/0.77           ( ![C:$i,D:$i]:
% 0.53/0.77             ( ( r1_tarski @ C @ D ) =>
% 0.53/0.77               ( ( ( r1_waybel_0 @ A @ B @ C ) => ( r1_waybel_0 @ A @ B @ D ) ) & 
% 0.53/0.77                 ( ( r2_waybel_0 @ A @ B @ C ) => ( r2_waybel_0 @ A @ B @ D ) ) ) ) ) ) ) ))).
% 0.53/0.77  thf('14', plain,
% 0.53/0.77      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.53/0.77         ((v2_struct_0 @ X26)
% 0.53/0.77          | ~ (l1_waybel_0 @ X26 @ X27)
% 0.53/0.77          | ~ (r1_waybel_0 @ X27 @ X26 @ X28)
% 0.53/0.77          | (r1_waybel_0 @ X27 @ X26 @ X29)
% 0.53/0.77          | ~ (r1_tarski @ X28 @ X29)
% 0.53/0.77          | ~ (l1_struct_0 @ X27)
% 0.53/0.77          | (v2_struct_0 @ X27))),
% 0.53/0.77      inference('cnf', [status(esa)], [t8_waybel_0])).
% 0.53/0.77  thf('15', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         ((v2_struct_0 @ sk_B_2)
% 0.53/0.77          | (r2_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.53/0.77          | (v2_struct_0 @ sk_A)
% 0.53/0.77          | (v2_struct_0 @ sk_A)
% 0.53/0.77          | ~ (l1_struct_0 @ sk_A)
% 0.53/0.77          | ~ (r1_tarski @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ X1)
% 0.53/0.77          | (r1_waybel_0 @ sk_A @ sk_B_2 @ X1)
% 0.53/0.77          | ~ (l1_waybel_0 @ sk_B_2 @ sk_A)
% 0.53/0.77          | (v2_struct_0 @ sk_B_2))),
% 0.53/0.77      inference('sup-', [status(thm)], ['13', '14'])).
% 0.53/0.77  thf('16', plain, ((l1_struct_0 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('17', plain, ((l1_waybel_0 @ sk_B_2 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('18', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         ((v2_struct_0 @ sk_B_2)
% 0.53/0.77          | (r2_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.53/0.77          | (v2_struct_0 @ sk_A)
% 0.53/0.77          | (v2_struct_0 @ sk_A)
% 0.53/0.77          | ~ (r1_tarski @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ X1)
% 0.53/0.77          | (r1_waybel_0 @ sk_A @ sk_B_2 @ X1)
% 0.53/0.77          | (v2_struct_0 @ sk_B_2))),
% 0.53/0.77      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.53/0.77  thf('19', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         ((r1_waybel_0 @ sk_A @ sk_B_2 @ X1)
% 0.53/0.77          | ~ (r1_tarski @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ X1)
% 0.53/0.77          | (v2_struct_0 @ sk_A)
% 0.53/0.77          | (r2_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.53/0.77          | (v2_struct_0 @ sk_B_2))),
% 0.53/0.77      inference('simplify', [status(thm)], ['18'])).
% 0.53/0.77  thf('20', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         ((v2_struct_0 @ sk_B_2)
% 0.53/0.77          | (r2_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.53/0.77          | (v2_struct_0 @ sk_A)
% 0.53/0.77          | (r1_waybel_0 @ sk_A @ sk_B_2 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.77      inference('sup-', [status(thm)], ['8', '19'])).
% 0.53/0.77  thf('21', plain, (~ (r1_waybel_0 @ sk_A @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('22', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         ((v2_struct_0 @ sk_A)
% 0.53/0.77          | (r2_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.53/0.77          | (v2_struct_0 @ sk_B_2))),
% 0.53/0.77      inference('sup-', [status(thm)], ['20', '21'])).
% 0.53/0.77  thf('23', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('24', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         ((v2_struct_0 @ sk_B_2) | (r2_waybel_0 @ sk_A @ sk_B_2 @ X0))),
% 0.53/0.77      inference('clc', [status(thm)], ['22', '23'])).
% 0.53/0.77  thf('25', plain, (~ (v2_struct_0 @ sk_B_2)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('26', plain, (![X0 : $i]: (r2_waybel_0 @ sk_A @ sk_B_2 @ X0)),
% 0.53/0.77      inference('clc', [status(thm)], ['24', '25'])).
% 0.53/0.77  thf(existence_m1_subset_1, axiom,
% 0.53/0.77    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.53/0.77  thf('27', plain, (![X13 : $i]: (m1_subset_1 @ (sk_B_1 @ X13) @ X13)),
% 0.53/0.77      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.53/0.77  thf(d12_waybel_0, axiom,
% 0.53/0.77    (![A:$i]:
% 0.53/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.53/0.77       ( ![B:$i]:
% 0.53/0.77         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.53/0.77           ( ![C:$i]:
% 0.53/0.77             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.53/0.77               ( ![D:$i]:
% 0.53/0.77                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.53/0.77                   ( ?[E:$i]:
% 0.53/0.77                     ( ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) & 
% 0.53/0.77                       ( r1_orders_2 @ B @ D @ E ) & 
% 0.53/0.77                       ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.53/0.77  thf('28', plain,
% 0.53/0.77      (![X16 : $i, X17 : $i, X20 : $i, X21 : $i]:
% 0.53/0.77         ((v2_struct_0 @ X16)
% 0.53/0.77          | ~ (l1_waybel_0 @ X16 @ X17)
% 0.53/0.77          | ~ (r2_waybel_0 @ X17 @ X16 @ X20)
% 0.53/0.77          | (r2_hidden @ 
% 0.53/0.77             (k2_waybel_0 @ X17 @ X16 @ (sk_E @ X21 @ X20 @ X16 @ X17)) @ X20)
% 0.53/0.77          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X16))
% 0.53/0.77          | ~ (l1_struct_0 @ X17)
% 0.53/0.77          | (v2_struct_0 @ X17))),
% 0.53/0.77      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.53/0.77  thf('29', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.77         ((v2_struct_0 @ X1)
% 0.53/0.77          | ~ (l1_struct_0 @ X1)
% 0.53/0.77          | (r2_hidden @ 
% 0.53/0.77             (k2_waybel_0 @ X1 @ X0 @ 
% 0.53/0.77              (sk_E @ (sk_B_1 @ (u1_struct_0 @ X0)) @ X2 @ X0 @ X1)) @ 
% 0.53/0.77             X2)
% 0.53/0.77          | ~ (r2_waybel_0 @ X1 @ X0 @ X2)
% 0.53/0.77          | ~ (l1_waybel_0 @ X0 @ X1)
% 0.53/0.77          | (v2_struct_0 @ X0))),
% 0.53/0.77      inference('sup-', [status(thm)], ['27', '28'])).
% 0.53/0.77  thf('30', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         ((v2_struct_0 @ sk_B_2)
% 0.53/0.77          | ~ (l1_waybel_0 @ sk_B_2 @ sk_A)
% 0.53/0.77          | (r2_hidden @ 
% 0.53/0.77             (k2_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.53/0.77              (sk_E @ (sk_B_1 @ (u1_struct_0 @ sk_B_2)) @ X0 @ sk_B_2 @ sk_A)) @ 
% 0.53/0.77             X0)
% 0.53/0.77          | ~ (l1_struct_0 @ sk_A)
% 0.53/0.77          | (v2_struct_0 @ sk_A))),
% 0.53/0.77      inference('sup-', [status(thm)], ['26', '29'])).
% 0.53/0.77  thf('31', plain, ((l1_waybel_0 @ sk_B_2 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('32', plain, ((l1_struct_0 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('33', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         ((v2_struct_0 @ sk_B_2)
% 0.53/0.77          | (r2_hidden @ 
% 0.53/0.77             (k2_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.53/0.77              (sk_E @ (sk_B_1 @ (u1_struct_0 @ sk_B_2)) @ X0 @ sk_B_2 @ sk_A)) @ 
% 0.53/0.77             X0)
% 0.53/0.77          | (v2_struct_0 @ sk_A))),
% 0.53/0.77      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.53/0.77  thf('34', plain, (~ (v2_struct_0 @ sk_B_2)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('35', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         ((v2_struct_0 @ sk_A)
% 0.53/0.77          | (r2_hidden @ 
% 0.53/0.77             (k2_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.53/0.77              (sk_E @ (sk_B_1 @ (u1_struct_0 @ sk_B_2)) @ X0 @ sk_B_2 @ sk_A)) @ 
% 0.53/0.77             X0))),
% 0.53/0.77      inference('clc', [status(thm)], ['33', '34'])).
% 0.53/0.77  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('37', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         (r2_hidden @ 
% 0.53/0.77          (k2_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.53/0.77           (sk_E @ (sk_B_1 @ (u1_struct_0 @ sk_B_2)) @ X0 @ sk_B_2 @ sk_A)) @ 
% 0.53/0.77          X0)),
% 0.53/0.77      inference('clc', [status(thm)], ['35', '36'])).
% 0.53/0.77  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.53/0.77  thf('38', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.53/0.77      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.53/0.77  thf('39', plain,
% 0.53/0.77      (![X8 : $i, X9 : $i, X12 : $i]:
% 0.53/0.77         (((X12) = (k4_xboole_0 @ X8 @ X9))
% 0.53/0.77          | (r2_hidden @ (sk_D @ X12 @ X9 @ X8) @ X8)
% 0.53/0.77          | (r2_hidden @ (sk_D @ X12 @ X9 @ X8) @ X12))),
% 0.53/0.77      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.53/0.77  thf('40', plain,
% 0.53/0.77      (![X14 : $i, X15 : $i]:
% 0.53/0.77         ((k6_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))),
% 0.53/0.77      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.53/0.77  thf('41', plain,
% 0.53/0.77      (![X8 : $i, X9 : $i, X12 : $i]:
% 0.53/0.77         (((X12) = (k6_subset_1 @ X8 @ X9))
% 0.53/0.77          | (r2_hidden @ (sk_D @ X12 @ X9 @ X8) @ X8)
% 0.53/0.77          | (r2_hidden @ (sk_D @ X12 @ X9 @ X8) @ X12))),
% 0.53/0.77      inference('demod', [status(thm)], ['39', '40'])).
% 0.53/0.77  thf('42', plain,
% 0.53/0.77      (![X8 : $i, X9 : $i, X12 : $i]:
% 0.53/0.77         (((X12) = (k4_xboole_0 @ X8 @ X9))
% 0.53/0.77          | ~ (r2_hidden @ (sk_D @ X12 @ X9 @ X8) @ X9)
% 0.53/0.77          | (r2_hidden @ (sk_D @ X12 @ X9 @ X8) @ X12))),
% 0.53/0.77      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.53/0.77  thf('43', plain,
% 0.53/0.77      (![X14 : $i, X15 : $i]:
% 0.53/0.77         ((k6_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))),
% 0.53/0.77      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.53/0.77  thf('44', plain,
% 0.53/0.77      (![X8 : $i, X9 : $i, X12 : $i]:
% 0.53/0.77         (((X12) = (k6_subset_1 @ X8 @ X9))
% 0.53/0.77          | ~ (r2_hidden @ (sk_D @ X12 @ X9 @ X8) @ X9)
% 0.53/0.77          | (r2_hidden @ (sk_D @ X12 @ X9 @ X8) @ X12))),
% 0.53/0.77      inference('demod', [status(thm)], ['42', '43'])).
% 0.53/0.77  thf('45', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.53/0.77          | ((X1) = (k6_subset_1 @ X0 @ X0))
% 0.53/0.77          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.53/0.77          | ((X1) = (k6_subset_1 @ X0 @ X0)))),
% 0.53/0.77      inference('sup-', [status(thm)], ['41', '44'])).
% 0.53/0.77  thf('46', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         (((X1) = (k6_subset_1 @ X0 @ X0))
% 0.53/0.77          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 0.53/0.77      inference('simplify', [status(thm)], ['45'])).
% 0.53/0.77  thf(d1_xboole_0, axiom,
% 0.53/0.77    (![A:$i]:
% 0.53/0.77     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.53/0.77  thf('47', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.53/0.77      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.53/0.77  thf('48', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         (((X0) = (k6_subset_1 @ X1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.53/0.77      inference('sup-', [status(thm)], ['46', '47'])).
% 0.53/0.77  thf('49', plain, (![X0 : $i]: ((k1_xboole_0) = (k6_subset_1 @ X0 @ X0))),
% 0.53/0.77      inference('sup-', [status(thm)], ['38', '48'])).
% 0.53/0.77  thf('50', plain,
% 0.53/0.77      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.53/0.77         (~ (r2_hidden @ X11 @ X10)
% 0.53/0.77          | ~ (r2_hidden @ X11 @ X9)
% 0.53/0.77          | ((X10) != (k4_xboole_0 @ X8 @ X9)))),
% 0.53/0.77      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.53/0.77  thf('51', plain,
% 0.53/0.77      (![X8 : $i, X9 : $i, X11 : $i]:
% 0.53/0.77         (~ (r2_hidden @ X11 @ X9)
% 0.53/0.77          | ~ (r2_hidden @ X11 @ (k4_xboole_0 @ X8 @ X9)))),
% 0.53/0.77      inference('simplify', [status(thm)], ['50'])).
% 0.53/0.77  thf('52', plain,
% 0.53/0.77      (![X14 : $i, X15 : $i]:
% 0.53/0.77         ((k6_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))),
% 0.53/0.77      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.53/0.77  thf('53', plain,
% 0.53/0.77      (![X8 : $i, X9 : $i, X11 : $i]:
% 0.53/0.77         (~ (r2_hidden @ X11 @ X9)
% 0.53/0.77          | ~ (r2_hidden @ X11 @ (k6_subset_1 @ X8 @ X9)))),
% 0.53/0.77      inference('demod', [status(thm)], ['51', '52'])).
% 0.53/0.77  thf('54', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.53/0.77      inference('sup-', [status(thm)], ['49', '53'])).
% 0.53/0.77  thf('55', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.53/0.77      inference('condensation', [status(thm)], ['54'])).
% 0.53/0.77  thf('56', plain, ($false), inference('sup-', [status(thm)], ['37', '55'])).
% 0.53/0.77  
% 0.53/0.77  % SZS output end Refutation
% 0.53/0.77  
% 0.61/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
