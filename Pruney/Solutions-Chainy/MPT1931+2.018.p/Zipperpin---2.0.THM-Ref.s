%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.u3hrec35Zv

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:59 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 177 expanded)
%              Number of leaves         :   28 (  66 expanded)
%              Depth                    :   18
%              Number of atoms          :  666 (1622 expanded)
%              Number of equality atoms :   21 (  65 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(r2_waybel_0_type,type,(
    r2_waybel_0: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

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
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ( X8
        = ( k4_xboole_0 @ X4 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k6_subset_1 @ X10 @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('3',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ( X8
        = ( k6_subset_1 @ X4 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X8 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['3'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k6_subset_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('8',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r2_hidden @ X7 @ X4 )
      | ( X6
       != ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('9',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ X4 )
      | ~ ( r2_hidden @ X7 @ ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k6_subset_1 @ X10 @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('11',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ X4 )
      | ~ ( r2_hidden @ X7 @ ( k6_subset_1 @ X4 @ X5 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k6_subset_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_B @ ( k6_subset_1 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('14',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ~ ( r2_hidden @ X7 @ X5 )
      | ( X6
       != ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('15',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k6_subset_1 @ X10 @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('17',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k6_subset_1 @ X4 @ X5 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k6_subset_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_B @ ( k6_subset_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k6_subset_1 @ X0 @ X0 ) )
      | ( v1_xboole_0 @ ( k6_subset_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k6_subset_1 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ( X8
        = ( k6_subset_1 @ X4 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X8 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('22',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ( X8
        = ( k4_xboole_0 @ X4 @ X5 ) )
      | ~ ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('23',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k6_subset_1 @ X10 @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('24',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ( X8
        = ( k6_subset_1 @ X4 @ X5 ) )
      | ~ ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X8 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k6_subset_1 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k6_subset_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k6_subset_1 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k6_subset_1 @ X1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k6_subset_1 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','28'])).

thf('30',plain,(
    l1_waybel_0 @ sk_B_2 @ sk_A ),
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

thf('31',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( l1_waybel_0 @ X18 @ X19 )
      | ( r2_waybel_0 @ X19 @ X18 @ ( k6_subset_1 @ ( u1_struct_0 @ X19 ) @ X20 ) )
      | ( r1_waybel_0 @ X19 @ X18 @ X20 )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t9_waybel_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r2_waybel_0 @ sk_A @ sk_B_2 @ ( k6_subset_1 @ X0 @ X0 ) )
      | ( v2_struct_0 @ sk_B_2 )
      | ( r1_waybel_0 @ sk_A @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['29','34'])).

thf('36',plain,(
    ~ ( r1_waybel_0 @ sk_A @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_2 )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ ( k6_subset_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_waybel_0 @ sk_A @ sk_B_2 @ ( k6_subset_1 @ X0 @ X0 ) )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( r2_waybel_0 @ sk_A @ sk_B_2 @ ( k6_subset_1 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','41'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('43',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X9 ) @ X9 ) ),
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

thf('44',plain,(
    ! [X12: $i,X13: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( l1_waybel_0 @ X12 @ X13 )
      | ~ ( r2_waybel_0 @ X13 @ X12 @ X16 )
      | ( r2_hidden @ ( k2_waybel_0 @ X13 @ X12 @ ( sk_E @ X17 @ X16 @ X12 @ X13 ) ) @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ X0 @ ( sk_E @ ( sk_B_1 @ ( u1_struct_0 @ X0 ) ) @ X2 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r2_waybel_0 @ X1 @ X0 @ X2 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_B_2 )
      | ~ ( l1_waybel_0 @ sk_B_2 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_2 @ ( sk_E @ ( sk_B_1 @ ( u1_struct_0 @ sk_B_2 ) ) @ X0 @ sk_B_2 @ sk_A ) ) @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    l1_waybel_0 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_B_2 )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_2 @ ( sk_E @ ( sk_B_1 @ ( u1_struct_0 @ sk_B_2 ) ) @ X0 @ sk_B_2 @ sk_A ) ) @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k6_subset_1 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','28'])).

thf('51',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k6_subset_1 @ X4 @ X5 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k6_subset_1 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k6_subset_1 @ X0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_2 )
      | ~ ( v1_xboole_0 @ ( k6_subset_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k6_subset_1 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v2_struct_0 @ sk_B_2 ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['0','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.u3hrec35Zv
% 0.12/0.31  % Computer   : n002.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % DateTime   : Tue Dec  1 14:25:22 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running portfolio for 600 s
% 0.12/0.32  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.32  % Number of cores: 8
% 0.12/0.32  % Python version: Python 3.6.8
% 0.12/0.32  % Running in FO mode
% 0.76/0.97  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.76/0.97  % Solved by: fo/fo7.sh
% 0.76/0.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.97  % done 840 iterations in 0.547s
% 0.76/0.97  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.76/0.97  % SZS output start Refutation
% 0.76/0.97  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.76/0.97  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.76/0.97  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.76/0.97  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.76/0.97  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.76/0.97  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.76/0.97  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.76/0.97  thf(r2_waybel_0_type, type, r2_waybel_0: $i > $i > $i > $o).
% 0.76/0.97  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.76/0.97  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.76/0.97  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.97  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.76/0.97  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.97  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.76/0.97  thf(sk_B_type, type, sk_B: $i > $i).
% 0.76/0.97  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.76/0.97  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.76/0.97  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.76/0.97  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.76/0.97  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.76/0.97  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 0.76/0.97  thf(t29_yellow_6, conjecture,
% 0.76/0.97    (![A:$i]:
% 0.76/0.97     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.76/0.97       ( ![B:$i]:
% 0.76/0.97         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.76/0.97             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.76/0.97           ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.76/0.97  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.97    (~( ![A:$i]:
% 0.76/0.97        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.76/0.97          ( ![B:$i]:
% 0.76/0.97            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.76/0.97                ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.76/0.97              ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ) )),
% 0.76/0.97    inference('cnf.neg', [status(esa)], [t29_yellow_6])).
% 0.76/0.97  thf('0', plain, (~ (v2_struct_0 @ sk_B_2)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(d5_xboole_0, axiom,
% 0.76/0.97    (![A:$i,B:$i,C:$i]:
% 0.76/0.97     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.76/0.97       ( ![D:$i]:
% 0.76/0.97         ( ( r2_hidden @ D @ C ) <=>
% 0.76/0.97           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.76/0.97  thf('1', plain,
% 0.76/0.97      (![X4 : $i, X5 : $i, X8 : $i]:
% 0.76/0.97         (((X8) = (k4_xboole_0 @ X4 @ X5))
% 0.76/0.97          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X4)
% 0.76/0.97          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X8))),
% 0.76/0.97      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.76/0.97  thf(redefinition_k6_subset_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.76/0.97  thf('2', plain,
% 0.76/0.97      (![X10 : $i, X11 : $i]:
% 0.76/0.97         ((k6_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))),
% 0.76/0.97      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.76/0.97  thf('3', plain,
% 0.76/0.97      (![X4 : $i, X5 : $i, X8 : $i]:
% 0.76/0.97         (((X8) = (k6_subset_1 @ X4 @ X5))
% 0.76/0.97          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X4)
% 0.76/0.97          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X8))),
% 0.76/0.97      inference('demod', [status(thm)], ['1', '2'])).
% 0.76/0.97  thf('4', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.76/0.97          | ((X0) = (k6_subset_1 @ X0 @ X1)))),
% 0.76/0.97      inference('eq_fact', [status(thm)], ['3'])).
% 0.76/0.97  thf(d1_xboole_0, axiom,
% 0.76/0.97    (![A:$i]:
% 0.76/0.97     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.76/0.97  thf('5', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.76/0.97      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.76/0.97  thf('6', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (((X0) = (k6_subset_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['4', '5'])).
% 0.76/0.97  thf('7', plain,
% 0.76/0.97      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.76/0.97      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.76/0.97  thf('8', plain,
% 0.76/0.97      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.76/0.97         (~ (r2_hidden @ X7 @ X6)
% 0.76/0.97          | (r2_hidden @ X7 @ X4)
% 0.76/0.97          | ((X6) != (k4_xboole_0 @ X4 @ X5)))),
% 0.76/0.97      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.76/0.97  thf('9', plain,
% 0.76/0.97      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.76/0.97         ((r2_hidden @ X7 @ X4) | ~ (r2_hidden @ X7 @ (k4_xboole_0 @ X4 @ X5)))),
% 0.76/0.97      inference('simplify', [status(thm)], ['8'])).
% 0.76/0.97  thf('10', plain,
% 0.76/0.97      (![X10 : $i, X11 : $i]:
% 0.76/0.97         ((k6_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))),
% 0.76/0.97      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.76/0.97  thf('11', plain,
% 0.76/0.97      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.76/0.97         ((r2_hidden @ X7 @ X4) | ~ (r2_hidden @ X7 @ (k6_subset_1 @ X4 @ X5)))),
% 0.76/0.97      inference('demod', [status(thm)], ['9', '10'])).
% 0.76/0.97  thf('12', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         ((v1_xboole_0 @ (k6_subset_1 @ X1 @ X0))
% 0.76/0.97          | (r2_hidden @ (sk_B @ (k6_subset_1 @ X1 @ X0)) @ X1))),
% 0.76/0.97      inference('sup-', [status(thm)], ['7', '11'])).
% 0.76/0.97  thf('13', plain,
% 0.76/0.97      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.76/0.97      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.76/0.97  thf('14', plain,
% 0.76/0.97      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.76/0.97         (~ (r2_hidden @ X7 @ X6)
% 0.76/0.97          | ~ (r2_hidden @ X7 @ X5)
% 0.76/0.97          | ((X6) != (k4_xboole_0 @ X4 @ X5)))),
% 0.76/0.97      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.76/0.97  thf('15', plain,
% 0.76/0.97      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.76/0.97         (~ (r2_hidden @ X7 @ X5)
% 0.76/0.97          | ~ (r2_hidden @ X7 @ (k4_xboole_0 @ X4 @ X5)))),
% 0.76/0.97      inference('simplify', [status(thm)], ['14'])).
% 0.76/0.97  thf('16', plain,
% 0.76/0.97      (![X10 : $i, X11 : $i]:
% 0.76/0.97         ((k6_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))),
% 0.76/0.97      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.76/0.97  thf('17', plain,
% 0.76/0.97      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.76/0.97         (~ (r2_hidden @ X7 @ X5)
% 0.76/0.97          | ~ (r2_hidden @ X7 @ (k6_subset_1 @ X4 @ X5)))),
% 0.76/0.97      inference('demod', [status(thm)], ['15', '16'])).
% 0.76/0.97  thf('18', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         ((v1_xboole_0 @ (k6_subset_1 @ X1 @ X0))
% 0.76/0.97          | ~ (r2_hidden @ (sk_B @ (k6_subset_1 @ X1 @ X0)) @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['13', '17'])).
% 0.76/0.97  thf('19', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v1_xboole_0 @ (k6_subset_1 @ X0 @ X0))
% 0.76/0.97          | (v1_xboole_0 @ (k6_subset_1 @ X0 @ X0)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['12', '18'])).
% 0.76/0.97  thf('20', plain, (![X0 : $i]: (v1_xboole_0 @ (k6_subset_1 @ X0 @ X0))),
% 0.76/0.97      inference('simplify', [status(thm)], ['19'])).
% 0.76/0.97  thf('21', plain,
% 0.76/0.97      (![X4 : $i, X5 : $i, X8 : $i]:
% 0.76/0.97         (((X8) = (k6_subset_1 @ X4 @ X5))
% 0.76/0.97          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X4)
% 0.76/0.97          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X8))),
% 0.76/0.97      inference('demod', [status(thm)], ['1', '2'])).
% 0.76/0.97  thf('22', plain,
% 0.76/0.97      (![X4 : $i, X5 : $i, X8 : $i]:
% 0.76/0.97         (((X8) = (k4_xboole_0 @ X4 @ X5))
% 0.76/0.97          | ~ (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X5)
% 0.76/0.97          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X8))),
% 0.76/0.97      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.76/0.97  thf('23', plain,
% 0.76/0.97      (![X10 : $i, X11 : $i]:
% 0.76/0.97         ((k6_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))),
% 0.76/0.97      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.76/0.97  thf('24', plain,
% 0.76/0.97      (![X4 : $i, X5 : $i, X8 : $i]:
% 0.76/0.97         (((X8) = (k6_subset_1 @ X4 @ X5))
% 0.76/0.97          | ~ (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X5)
% 0.76/0.97          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X8))),
% 0.76/0.97      inference('demod', [status(thm)], ['22', '23'])).
% 0.76/0.97  thf('25', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.76/0.97          | ((X1) = (k6_subset_1 @ X0 @ X0))
% 0.76/0.97          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.76/0.97          | ((X1) = (k6_subset_1 @ X0 @ X0)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['21', '24'])).
% 0.76/0.97  thf('26', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (((X1) = (k6_subset_1 @ X0 @ X0))
% 0.76/0.97          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 0.76/0.97      inference('simplify', [status(thm)], ['25'])).
% 0.76/0.97  thf('27', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.76/0.97      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.76/0.97  thf('28', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (((X0) = (k6_subset_1 @ X1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['26', '27'])).
% 0.76/0.97  thf('29', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]: ((k6_subset_1 @ X0 @ X0) = (k6_subset_1 @ X1 @ X1))),
% 0.76/0.97      inference('sup-', [status(thm)], ['20', '28'])).
% 0.76/0.97  thf('30', plain, ((l1_waybel_0 @ sk_B_2 @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(t9_waybel_0, axiom,
% 0.76/0.97    (![A:$i]:
% 0.76/0.97     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.76/0.97       ( ![B:$i]:
% 0.76/0.97         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.76/0.97           ( ![C:$i]:
% 0.76/0.97             ( ( r1_waybel_0 @ A @ B @ C ) <=>
% 0.76/0.97               ( ~( r2_waybel_0 @
% 0.76/0.97                    A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ))).
% 0.76/0.97  thf('31', plain,
% 0.76/0.97      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.76/0.97         ((v2_struct_0 @ X18)
% 0.76/0.97          | ~ (l1_waybel_0 @ X18 @ X19)
% 0.76/0.97          | (r2_waybel_0 @ X19 @ X18 @ 
% 0.76/0.97             (k6_subset_1 @ (u1_struct_0 @ X19) @ X20))
% 0.76/0.97          | (r1_waybel_0 @ X19 @ X18 @ X20)
% 0.76/0.97          | ~ (l1_struct_0 @ X19)
% 0.76/0.97          | (v2_struct_0 @ X19))),
% 0.76/0.97      inference('cnf', [status(esa)], [t9_waybel_0])).
% 0.76/0.97  thf('32', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_A)
% 0.76/0.97          | ~ (l1_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.76/0.97          | (r2_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.76/0.97             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.76/0.97          | (v2_struct_0 @ sk_B_2))),
% 0.76/0.97      inference('sup-', [status(thm)], ['30', '31'])).
% 0.76/0.97  thf('33', plain, ((l1_struct_0 @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('34', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.76/0.97          | (r2_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.76/0.97             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.76/0.97          | (v2_struct_0 @ sk_B_2))),
% 0.76/0.97      inference('demod', [status(thm)], ['32', '33'])).
% 0.76/0.97  thf('35', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((r2_waybel_0 @ sk_A @ sk_B_2 @ (k6_subset_1 @ X0 @ X0))
% 0.76/0.97          | (v2_struct_0 @ sk_B_2)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.76/0.97          | (v2_struct_0 @ sk_A))),
% 0.76/0.97      inference('sup+', [status(thm)], ['29', '34'])).
% 0.76/0.97  thf('36', plain, (~ (r1_waybel_0 @ sk_A @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('37', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_A)
% 0.76/0.97          | (v2_struct_0 @ sk_B_2)
% 0.76/0.97          | (r2_waybel_0 @ sk_A @ sk_B_2 @ (k6_subset_1 @ X0 @ X0)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['35', '36'])).
% 0.76/0.97  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('39', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((r2_waybel_0 @ sk_A @ sk_B_2 @ (k6_subset_1 @ X0 @ X0))
% 0.76/0.97          | (v2_struct_0 @ sk_B_2))),
% 0.76/0.97      inference('clc', [status(thm)], ['37', '38'])).
% 0.76/0.97  thf('40', plain, (~ (v2_struct_0 @ sk_B_2)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('41', plain,
% 0.76/0.97      (![X0 : $i]: (r2_waybel_0 @ sk_A @ sk_B_2 @ (k6_subset_1 @ X0 @ X0))),
% 0.76/0.97      inference('clc', [status(thm)], ['39', '40'])).
% 0.76/0.97  thf('42', plain,
% 0.76/0.97      (![X0 : $i]: ((r2_waybel_0 @ sk_A @ sk_B_2 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.76/0.97      inference('sup+', [status(thm)], ['6', '41'])).
% 0.76/0.97  thf(existence_m1_subset_1, axiom,
% 0.76/0.97    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.76/0.97  thf('43', plain, (![X9 : $i]: (m1_subset_1 @ (sk_B_1 @ X9) @ X9)),
% 0.76/0.97      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.76/0.97  thf(d12_waybel_0, axiom,
% 0.76/0.97    (![A:$i]:
% 0.76/0.97     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.76/0.97       ( ![B:$i]:
% 0.76/0.97         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.76/0.97           ( ![C:$i]:
% 0.76/0.97             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.76/0.97               ( ![D:$i]:
% 0.76/0.97                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.76/0.97                   ( ?[E:$i]:
% 0.76/0.97                     ( ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) & 
% 0.76/0.97                       ( r1_orders_2 @ B @ D @ E ) & 
% 0.76/0.97                       ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.76/0.97  thf('44', plain,
% 0.76/0.97      (![X12 : $i, X13 : $i, X16 : $i, X17 : $i]:
% 0.76/0.97         ((v2_struct_0 @ X12)
% 0.76/0.97          | ~ (l1_waybel_0 @ X12 @ X13)
% 0.76/0.97          | ~ (r2_waybel_0 @ X13 @ X12 @ X16)
% 0.76/0.97          | (r2_hidden @ 
% 0.76/0.97             (k2_waybel_0 @ X13 @ X12 @ (sk_E @ X17 @ X16 @ X12 @ X13)) @ X16)
% 0.76/0.97          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X12))
% 0.76/0.97          | ~ (l1_struct_0 @ X13)
% 0.76/0.97          | (v2_struct_0 @ X13))),
% 0.76/0.97      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.76/0.97  thf('45', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         ((v2_struct_0 @ X1)
% 0.76/0.97          | ~ (l1_struct_0 @ X1)
% 0.76/0.97          | (r2_hidden @ 
% 0.76/0.97             (k2_waybel_0 @ X1 @ X0 @ 
% 0.76/0.97              (sk_E @ (sk_B_1 @ (u1_struct_0 @ X0)) @ X2 @ X0 @ X1)) @ 
% 0.76/0.97             X2)
% 0.76/0.97          | ~ (r2_waybel_0 @ X1 @ X0 @ X2)
% 0.76/0.97          | ~ (l1_waybel_0 @ X0 @ X1)
% 0.76/0.97          | (v2_struct_0 @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['43', '44'])).
% 0.76/0.97  thf('46', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (v1_xboole_0 @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B_2)
% 0.76/0.97          | ~ (l1_waybel_0 @ sk_B_2 @ sk_A)
% 0.76/0.97          | (r2_hidden @ 
% 0.76/0.97             (k2_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.76/0.97              (sk_E @ (sk_B_1 @ (u1_struct_0 @ sk_B_2)) @ X0 @ sk_B_2 @ sk_A)) @ 
% 0.76/0.97             X0)
% 0.76/0.97          | ~ (l1_struct_0 @ sk_A)
% 0.76/0.97          | (v2_struct_0 @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['42', '45'])).
% 0.76/0.97  thf('47', plain, ((l1_waybel_0 @ sk_B_2 @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('48', plain, ((l1_struct_0 @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('49', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (v1_xboole_0 @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B_2)
% 0.76/0.97          | (r2_hidden @ 
% 0.76/0.97             (k2_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.76/0.97              (sk_E @ (sk_B_1 @ (u1_struct_0 @ sk_B_2)) @ X0 @ sk_B_2 @ sk_A)) @ 
% 0.76/0.97             X0)
% 0.76/0.97          | (v2_struct_0 @ sk_A))),
% 0.76/0.97      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.76/0.97  thf('50', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]: ((k6_subset_1 @ X0 @ X0) = (k6_subset_1 @ X1 @ X1))),
% 0.76/0.97      inference('sup-', [status(thm)], ['20', '28'])).
% 0.76/0.97  thf('51', plain,
% 0.76/0.97      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.76/0.97         (~ (r2_hidden @ X7 @ X5)
% 0.76/0.97          | ~ (r2_hidden @ X7 @ (k6_subset_1 @ X4 @ X5)))),
% 0.76/0.97      inference('demod', [status(thm)], ['15', '16'])).
% 0.76/0.97  thf('52', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         (~ (r2_hidden @ X2 @ (k6_subset_1 @ X0 @ X0))
% 0.76/0.97          | ~ (r2_hidden @ X2 @ X1))),
% 0.76/0.97      inference('sup-', [status(thm)], ['50', '51'])).
% 0.76/0.97  thf('53', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k6_subset_1 @ X0 @ X0))),
% 0.76/0.97      inference('condensation', [status(thm)], ['52'])).
% 0.76/0.97  thf('54', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_A)
% 0.76/0.97          | (v2_struct_0 @ sk_B_2)
% 0.76/0.97          | ~ (v1_xboole_0 @ (k6_subset_1 @ X0 @ X0)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['49', '53'])).
% 0.76/0.97  thf('55', plain, (![X0 : $i]: (v1_xboole_0 @ (k6_subset_1 @ X0 @ X0))),
% 0.76/0.97      inference('simplify', [status(thm)], ['19'])).
% 0.76/0.97  thf('56', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B_2))),
% 0.76/0.97      inference('demod', [status(thm)], ['54', '55'])).
% 0.76/0.97  thf('57', plain, (~ (v2_struct_0 @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('58', plain, ((v2_struct_0 @ sk_B_2)),
% 0.76/0.97      inference('clc', [status(thm)], ['56', '57'])).
% 0.76/0.97  thf('59', plain, ($false), inference('demod', [status(thm)], ['0', '58'])).
% 0.76/0.97  
% 0.76/0.97  % SZS output end Refutation
% 0.76/0.97  
% 0.76/0.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
