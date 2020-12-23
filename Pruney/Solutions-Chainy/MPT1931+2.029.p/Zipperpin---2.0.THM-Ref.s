%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W0Lxnw4Ku7

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:00 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 400 expanded)
%              Number of leaves         :   31 ( 124 expanded)
%              Depth                    :   29
%              Number of atoms          : 1252 (4854 expanded)
%              Number of equality atoms :   24 ( 173 expanded)
%              Maximal formula depth    :   20 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_waybel_0_type,type,(
    r2_waybel_0: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k4_yellow_6_type,type,(
    k4_yellow_6: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

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
    ! [X6: $i,X7: $i] :
      ( ( k6_subset_1 @ X6 @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ( k6_subset_1 @ X6 @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
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

thf('8',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k6_subset_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['8'])).

thf('10',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('11',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k6_subset_1 @ X6 @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('13',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k6_subset_1 @ X1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k6_subset_1 @ X1 @ X0 )
        = ( k6_subset_1 @ ( k6_subset_1 @ X1 @ X0 ) @ X2 ) )
      | ( r2_hidden @ ( sk_D @ ( k6_subset_1 @ X1 @ X0 ) @ X2 @ ( k6_subset_1 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['8'])).

thf('16',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('17',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k6_subset_1 @ X6 @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('19',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k6_subset_1 @ X1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k6_subset_1 @ X1 @ X0 )
        = ( k6_subset_1 @ ( k6_subset_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k6_subset_1 @ X1 @ X0 ) @ X2 @ ( k6_subset_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_subset_1 @ X0 @ X0 )
        = ( k6_subset_1 @ ( k6_subset_1 @ X0 @ X0 ) @ X1 ) )
      | ( ( k6_subset_1 @ X0 @ X0 )
        = ( k6_subset_1 @ ( k6_subset_1 @ X0 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k6_subset_1 @ ( k6_subset_1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k6_subset_1 @ X1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k6_subset_1 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k6_subset_1 @ X0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k6_subset_1 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','25'])).

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

thf('27',plain,(
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

thf('28',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( l1_waybel_0 @ X18 @ X19 )
      | ( r2_waybel_0 @ X19 @ X18 @ ( k6_subset_1 @ ( u1_struct_0 @ X19 ) @ X20 ) )
      | ( r1_waybel_0 @ X19 @ X18 @ X20 )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t9_waybel_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_waybel_0 @ sk_A @ sk_B_1 @ ( k6_subset_1 @ X0 @ X0 ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['26','31'])).

thf('33',plain,(
    ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ ( k6_subset_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_waybel_0 @ sk_A @ sk_B_1 @ ( k6_subset_1 @ X0 @ X0 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( r2_waybel_0 @ sk_A @ sk_B_1 @ ( k6_subset_1 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
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

thf('41',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( l1_waybel_0 @ X9 @ X10 )
      | ( m1_subset_1 @ ( sk_D_1 @ X11 @ X9 @ X10 ) @ ( u1_struct_0 @ X9 ) )
      | ( r2_waybel_0 @ X10 @ X9 @ X11 )
      | ~ ( l1_struct_0 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X9: $i,X10: $i,X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( l1_waybel_0 @ X9 @ X10 )
      | ~ ( r2_waybel_0 @ X10 @ X9 @ X13 )
      | ( r2_hidden @ ( k2_waybel_0 @ X10 @ X9 @ ( sk_E @ X14 @ X13 @ X9 @ X10 ) ) @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('46',plain,(
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
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_waybel_0 @ sk_B_1 @ X1 )
      | ~ ( r2_waybel_0 @ X1 @ sk_B_1 @ X2 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ sk_B_1 @ ( sk_E @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ X2 @ sk_B_1 @ X1 ) ) @ X2 )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ X1 @ sk_B_1 @ sk_A ) ) @ X1 )
      | ~ ( r2_waybel_0 @ sk_A @ sk_B_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','47'])).

thf('49',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ X1 @ sk_B_1 @ sk_A ) ) @ X1 )
      | ~ ( r2_waybel_0 @ sk_A @ sk_B_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_waybel_0 @ sk_A @ sk_B_1 @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ X1 @ sk_B_1 @ sk_A ) ) @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_D_1 @ X1 @ sk_B_1 @ sk_A ) @ ( k6_subset_1 @ X0 @ X0 ) @ sk_B_1 @ sk_A ) ) @ ( k6_subset_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k6_subset_1 @ X0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['24'])).

thf('54',plain,(
    ! [X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X1 ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X1: $i] :
      ( r2_waybel_0 @ sk_A @ sk_B_1 @ X1 ) ),
    inference(clc,[status(thm)],['56','57'])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('59',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('60',plain,(
    ! [X1: $i] :
      ( r2_waybel_0 @ sk_A @ sk_B_1 @ X1 ) ),
    inference(clc,[status(thm)],['56','57'])).

thf(existence_l1_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ? [B: $i] :
          ( l1_waybel_0 @ B @ A ) ) )).

thf('61',plain,(
    ! [X17: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X17 ) @ X17 )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[existence_l1_waybel_0])).

thf(dt_k4_yellow_6,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ( l1_waybel_0 @ B @ A ) )
     => ( m1_subset_1 @ ( k4_yellow_6 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('62',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_struct_0 @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( l1_waybel_0 @ X23 @ X22 )
      | ( m1_subset_1 @ ( k4_yellow_6 @ X22 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_yellow_6])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k4_yellow_6 @ X0 @ ( sk_B @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k4_yellow_6 @ X0 @ ( sk_B @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X9: $i,X10: $i,X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( l1_waybel_0 @ X9 @ X10 )
      | ~ ( r2_waybel_0 @ X10 @ X9 @ X13 )
      | ( m1_subset_1 @ ( sk_E @ X14 @ X13 @ X9 @ X10 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( m1_subset_1 @ ( sk_E @ ( k4_yellow_6 @ X0 @ ( sk_B @ X0 ) ) @ X2 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_waybel_0 @ X1 @ X0 @ X2 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_waybel_0 @ X0 @ X1 )
      | ~ ( r2_waybel_0 @ X1 @ X0 @ X2 )
      | ( m1_subset_1 @ ( sk_E @ ( k4_yellow_6 @ X0 @ ( sk_B @ X0 ) ) @ X2 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','67'])).

thf('69',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['59','71'])).

thf('73',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ( l1_orders_2 @ B ) ) ) )).

thf('74',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_waybel_0 @ X15 @ X16 )
      | ( l1_orders_2 @ X15 )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_0])).

thf('75',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( l1_orders_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['72','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X9: $i,X10: $i,X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( l1_waybel_0 @ X9 @ X10 )
      | ~ ( r2_waybel_0 @ X10 @ X9 @ X13 )
      | ( r2_hidden @ ( k2_waybel_0 @ X10 @ X9 @ ( sk_E @ X14 @ X13 @ X9 @ X10 ) ) @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ sk_B_1 @ ( sk_E @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ X2 @ sk_B_1 @ X1 ) ) @ X2 )
      | ~ ( r2_waybel_0 @ X1 @ sk_B_1 @ X2 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ X1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X1 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','84'])).

thf('86',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X1 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X1 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_E @ ( k4_yellow_6 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X1 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k6_subset_1 @ X0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['24'])).

thf('94',plain,(
    $false ),
    inference('sup-',[status(thm)],['92','93'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W0Lxnw4Ku7
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:29:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.90/1.08  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.90/1.08  % Solved by: fo/fo7.sh
% 0.90/1.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.08  % done 652 iterations in 0.625s
% 0.90/1.08  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.90/1.08  % SZS output start Refutation
% 0.90/1.08  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.08  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.90/1.08  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.90/1.08  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.90/1.08  thf(r2_waybel_0_type, type, r2_waybel_0: $i > $i > $i > $o).
% 0.90/1.08  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.90/1.08  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.90/1.08  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.90/1.08  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.90/1.08  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.90/1.08  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.90/1.08  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 0.90/1.08  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.90/1.08  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.90/1.08  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.08  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.90/1.08  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.90/1.08  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.90/1.08  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.90/1.08  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.90/1.08  thf(k4_yellow_6_type, type, k4_yellow_6: $i > $i > $i).
% 0.90/1.08  thf(sk_B_type, type, sk_B: $i > $i).
% 0.90/1.08  thf(d5_xboole_0, axiom,
% 0.90/1.08    (![A:$i,B:$i,C:$i]:
% 0.90/1.08     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.90/1.08       ( ![D:$i]:
% 0.90/1.08         ( ( r2_hidden @ D @ C ) <=>
% 0.90/1.08           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.90/1.08  thf('0', plain,
% 0.90/1.08      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.90/1.08         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.90/1.08          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.90/1.08          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.90/1.08      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.90/1.08  thf(redefinition_k6_subset_1, axiom,
% 0.90/1.08    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.90/1.08  thf('1', plain,
% 0.90/1.08      (![X6 : $i, X7 : $i]: ((k6_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))),
% 0.90/1.08      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.90/1.08  thf('2', plain,
% 0.90/1.08      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.90/1.08         (((X5) = (k6_subset_1 @ X1 @ X2))
% 0.90/1.08          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.90/1.08          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.90/1.08      inference('demod', [status(thm)], ['0', '1'])).
% 0.90/1.08  thf('3', plain,
% 0.90/1.08      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.90/1.08         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.90/1.08          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.90/1.08          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.90/1.08      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.90/1.08  thf('4', plain,
% 0.90/1.08      (![X6 : $i, X7 : $i]: ((k6_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))),
% 0.90/1.08      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.90/1.08  thf('5', plain,
% 0.90/1.08      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.90/1.08         (((X5) = (k6_subset_1 @ X1 @ X2))
% 0.90/1.08          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.90/1.08          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.90/1.08      inference('demod', [status(thm)], ['3', '4'])).
% 0.90/1.08  thf('6', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.90/1.08          | ((X1) = (k6_subset_1 @ X0 @ X0))
% 0.90/1.08          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.90/1.08          | ((X1) = (k6_subset_1 @ X0 @ X0)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['2', '5'])).
% 0.90/1.08  thf('7', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         (((X1) = (k6_subset_1 @ X0 @ X0))
% 0.90/1.08          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 0.90/1.08      inference('simplify', [status(thm)], ['6'])).
% 0.90/1.08  thf('8', plain,
% 0.90/1.08      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.90/1.08         (((X5) = (k6_subset_1 @ X1 @ X2))
% 0.90/1.08          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.90/1.08          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.90/1.08      inference('demod', [status(thm)], ['0', '1'])).
% 0.90/1.08  thf('9', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.90/1.08          | ((X0) = (k6_subset_1 @ X0 @ X1)))),
% 0.90/1.08      inference('eq_fact', [status(thm)], ['8'])).
% 0.90/1.08  thf('10', plain,
% 0.90/1.08      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X4 @ X3)
% 0.90/1.08          | (r2_hidden @ X4 @ X1)
% 0.90/1.08          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.90/1.08      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.90/1.08  thf('11', plain,
% 0.90/1.08      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.90/1.08         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.90/1.08      inference('simplify', [status(thm)], ['10'])).
% 0.90/1.08  thf('12', plain,
% 0.90/1.08      (![X6 : $i, X7 : $i]: ((k6_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))),
% 0.90/1.08      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.90/1.08  thf('13', plain,
% 0.90/1.08      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.90/1.08         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k6_subset_1 @ X1 @ X2)))),
% 0.90/1.08      inference('demod', [status(thm)], ['11', '12'])).
% 0.90/1.08  thf('14', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.08         (((k6_subset_1 @ X1 @ X0)
% 0.90/1.08            = (k6_subset_1 @ (k6_subset_1 @ X1 @ X0) @ X2))
% 0.90/1.08          | (r2_hidden @ 
% 0.90/1.08             (sk_D @ (k6_subset_1 @ X1 @ X0) @ X2 @ (k6_subset_1 @ X1 @ X0)) @ 
% 0.90/1.08             X1))),
% 0.90/1.08      inference('sup-', [status(thm)], ['9', '13'])).
% 0.90/1.08  thf('15', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.90/1.08          | ((X0) = (k6_subset_1 @ X0 @ X1)))),
% 0.90/1.08      inference('eq_fact', [status(thm)], ['8'])).
% 0.90/1.08  thf('16', plain,
% 0.90/1.08      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X4 @ X3)
% 0.90/1.08          | ~ (r2_hidden @ X4 @ X2)
% 0.90/1.08          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.90/1.08      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.90/1.08  thf('17', plain,
% 0.90/1.08      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X4 @ X2)
% 0.90/1.08          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.90/1.08      inference('simplify', [status(thm)], ['16'])).
% 0.90/1.08  thf('18', plain,
% 0.90/1.08      (![X6 : $i, X7 : $i]: ((k6_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))),
% 0.90/1.08      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.90/1.08  thf('19', plain,
% 0.90/1.08      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X4 @ X2)
% 0.90/1.08          | ~ (r2_hidden @ X4 @ (k6_subset_1 @ X1 @ X2)))),
% 0.90/1.08      inference('demod', [status(thm)], ['17', '18'])).
% 0.90/1.08  thf('20', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.08         (((k6_subset_1 @ X1 @ X0)
% 0.90/1.08            = (k6_subset_1 @ (k6_subset_1 @ X1 @ X0) @ X2))
% 0.90/1.08          | ~ (r2_hidden @ 
% 0.90/1.08               (sk_D @ (k6_subset_1 @ X1 @ X0) @ X2 @ (k6_subset_1 @ X1 @ X0)) @ 
% 0.90/1.08               X0))),
% 0.90/1.08      inference('sup-', [status(thm)], ['15', '19'])).
% 0.90/1.08  thf('21', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         (((k6_subset_1 @ X0 @ X0)
% 0.90/1.08            = (k6_subset_1 @ (k6_subset_1 @ X0 @ X0) @ X1))
% 0.90/1.08          | ((k6_subset_1 @ X0 @ X0)
% 0.90/1.08              = (k6_subset_1 @ (k6_subset_1 @ X0 @ X0) @ X1)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['14', '20'])).
% 0.90/1.08  thf('22', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         ((k6_subset_1 @ X0 @ X0)
% 0.90/1.08           = (k6_subset_1 @ (k6_subset_1 @ X0 @ X0) @ X1))),
% 0.90/1.08      inference('simplify', [status(thm)], ['21'])).
% 0.90/1.08  thf('23', plain,
% 0.90/1.08      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X4 @ X2)
% 0.90/1.08          | ~ (r2_hidden @ X4 @ (k6_subset_1 @ X1 @ X2)))),
% 0.90/1.08      inference('demod', [status(thm)], ['17', '18'])).
% 0.90/1.08  thf('24', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X2 @ (k6_subset_1 @ X0 @ X0))
% 0.90/1.08          | ~ (r2_hidden @ X2 @ X1))),
% 0.90/1.08      inference('sup-', [status(thm)], ['22', '23'])).
% 0.90/1.08  thf('25', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k6_subset_1 @ X0 @ X0))),
% 0.90/1.08      inference('condensation', [status(thm)], ['24'])).
% 0.90/1.08  thf('26', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]: ((k6_subset_1 @ X0 @ X0) = (k6_subset_1 @ X1 @ X1))),
% 0.90/1.08      inference('sup-', [status(thm)], ['7', '25'])).
% 0.90/1.08  thf(t29_yellow_6, conjecture,
% 0.90/1.08    (![A:$i]:
% 0.90/1.08     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.90/1.08       ( ![B:$i]:
% 0.90/1.08         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.90/1.08             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.90/1.08           ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.90/1.08  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.08    (~( ![A:$i]:
% 0.90/1.08        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.90/1.08          ( ![B:$i]:
% 0.90/1.08            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.90/1.08                ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.90/1.08              ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ) )),
% 0.90/1.08    inference('cnf.neg', [status(esa)], [t29_yellow_6])).
% 0.90/1.08  thf('27', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf(t9_waybel_0, axiom,
% 0.90/1.08    (![A:$i]:
% 0.90/1.08     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.90/1.08       ( ![B:$i]:
% 0.90/1.08         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.90/1.08           ( ![C:$i]:
% 0.90/1.08             ( ( r1_waybel_0 @ A @ B @ C ) <=>
% 0.90/1.08               ( ~( r2_waybel_0 @
% 0.90/1.08                    A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ))).
% 0.90/1.08  thf('28', plain,
% 0.90/1.08      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.90/1.08         ((v2_struct_0 @ X18)
% 0.90/1.08          | ~ (l1_waybel_0 @ X18 @ X19)
% 0.90/1.08          | (r2_waybel_0 @ X19 @ X18 @ 
% 0.90/1.08             (k6_subset_1 @ (u1_struct_0 @ X19) @ X20))
% 0.90/1.08          | (r1_waybel_0 @ X19 @ X18 @ X20)
% 0.90/1.08          | ~ (l1_struct_0 @ X19)
% 0.90/1.08          | (v2_struct_0 @ X19))),
% 0.90/1.08      inference('cnf', [status(esa)], [t9_waybel_0])).
% 0.90/1.08  thf('29', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         ((v2_struct_0 @ sk_A)
% 0.90/1.08          | ~ (l1_struct_0 @ sk_A)
% 0.90/1.08          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.90/1.08          | (r2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.90/1.08             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.90/1.08          | (v2_struct_0 @ sk_B_1))),
% 0.90/1.08      inference('sup-', [status(thm)], ['27', '28'])).
% 0.90/1.08  thf('30', plain, ((l1_struct_0 @ sk_A)),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('31', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         ((v2_struct_0 @ sk_A)
% 0.90/1.08          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.90/1.08          | (r2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.90/1.08             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.90/1.08          | (v2_struct_0 @ sk_B_1))),
% 0.90/1.08      inference('demod', [status(thm)], ['29', '30'])).
% 0.90/1.08  thf('32', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         ((r2_waybel_0 @ sk_A @ sk_B_1 @ (k6_subset_1 @ X0 @ X0))
% 0.90/1.08          | (v2_struct_0 @ sk_B_1)
% 0.90/1.08          | (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.90/1.08          | (v2_struct_0 @ sk_A))),
% 0.90/1.08      inference('sup+', [status(thm)], ['26', '31'])).
% 0.90/1.08  thf('33', plain, (~ (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('34', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         ((v2_struct_0 @ sk_A)
% 0.90/1.08          | (v2_struct_0 @ sk_B_1)
% 0.90/1.08          | (r2_waybel_0 @ sk_A @ sk_B_1 @ (k6_subset_1 @ X0 @ X0)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['32', '33'])).
% 0.90/1.08  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('36', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         ((r2_waybel_0 @ sk_A @ sk_B_1 @ (k6_subset_1 @ X0 @ X0))
% 0.90/1.08          | (v2_struct_0 @ sk_B_1))),
% 0.90/1.08      inference('clc', [status(thm)], ['34', '35'])).
% 0.90/1.08  thf('37', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('38', plain,
% 0.90/1.08      (![X0 : $i]: (r2_waybel_0 @ sk_A @ sk_B_1 @ (k6_subset_1 @ X0 @ X0))),
% 0.90/1.08      inference('clc', [status(thm)], ['36', '37'])).
% 0.90/1.08  thf('39', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('40', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf(d12_waybel_0, axiom,
% 0.90/1.08    (![A:$i]:
% 0.90/1.08     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.90/1.08       ( ![B:$i]:
% 0.90/1.08         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.90/1.09           ( ![C:$i]:
% 0.90/1.09             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.90/1.09               ( ![D:$i]:
% 0.90/1.09                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.90/1.09                   ( ?[E:$i]:
% 0.90/1.09                     ( ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) & 
% 0.90/1.09                       ( r1_orders_2 @ B @ D @ E ) & 
% 0.90/1.09                       ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.90/1.09  thf('41', plain,
% 0.90/1.09      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.90/1.09         ((v2_struct_0 @ X9)
% 0.90/1.09          | ~ (l1_waybel_0 @ X9 @ X10)
% 0.90/1.09          | (m1_subset_1 @ (sk_D_1 @ X11 @ X9 @ X10) @ (u1_struct_0 @ X9))
% 0.90/1.09          | (r2_waybel_0 @ X10 @ X9 @ X11)
% 0.90/1.09          | ~ (l1_struct_0 @ X10)
% 0.90/1.09          | (v2_struct_0 @ X10))),
% 0.90/1.09      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.90/1.09  thf('42', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         ((v2_struct_0 @ sk_A)
% 0.90/1.09          | ~ (l1_struct_0 @ sk_A)
% 0.90/1.09          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.90/1.09          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ 
% 0.90/1.09             (u1_struct_0 @ sk_B_1))
% 0.90/1.09          | (v2_struct_0 @ sk_B_1))),
% 0.90/1.09      inference('sup-', [status(thm)], ['40', '41'])).
% 0.90/1.09  thf('43', plain, ((l1_struct_0 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('44', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         ((v2_struct_0 @ sk_A)
% 0.90/1.09          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.90/1.09          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ 
% 0.90/1.09             (u1_struct_0 @ sk_B_1))
% 0.90/1.09          | (v2_struct_0 @ sk_B_1))),
% 0.90/1.09      inference('demod', [status(thm)], ['42', '43'])).
% 0.90/1.09  thf('45', plain,
% 0.90/1.09      (![X9 : $i, X10 : $i, X13 : $i, X14 : $i]:
% 0.90/1.09         ((v2_struct_0 @ X9)
% 0.90/1.09          | ~ (l1_waybel_0 @ X9 @ X10)
% 0.90/1.09          | ~ (r2_waybel_0 @ X10 @ X9 @ X13)
% 0.90/1.09          | (r2_hidden @ 
% 0.90/1.09             (k2_waybel_0 @ X10 @ X9 @ (sk_E @ X14 @ X13 @ X9 @ X10)) @ X13)
% 0.90/1.09          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X9))
% 0.90/1.09          | ~ (l1_struct_0 @ X10)
% 0.90/1.09          | (v2_struct_0 @ X10))),
% 0.90/1.09      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.90/1.09  thf('46', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.09         ((v2_struct_0 @ sk_B_1)
% 0.90/1.09          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.90/1.09          | (v2_struct_0 @ sk_A)
% 0.90/1.09          | (v2_struct_0 @ X1)
% 0.90/1.09          | ~ (l1_struct_0 @ X1)
% 0.90/1.09          | (r2_hidden @ 
% 0.90/1.09             (k2_waybel_0 @ X1 @ sk_B_1 @ 
% 0.90/1.09              (sk_E @ (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ X2 @ sk_B_1 @ X1)) @ 
% 0.90/1.09             X2)
% 0.90/1.09          | ~ (r2_waybel_0 @ X1 @ sk_B_1 @ X2)
% 0.90/1.09          | ~ (l1_waybel_0 @ sk_B_1 @ X1)
% 0.90/1.09          | (v2_struct_0 @ sk_B_1))),
% 0.90/1.09      inference('sup-', [status(thm)], ['44', '45'])).
% 0.90/1.09  thf('47', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.09         (~ (l1_waybel_0 @ sk_B_1 @ X1)
% 0.90/1.09          | ~ (r2_waybel_0 @ X1 @ sk_B_1 @ X2)
% 0.90/1.09          | (r2_hidden @ 
% 0.90/1.09             (k2_waybel_0 @ X1 @ sk_B_1 @ 
% 0.90/1.09              (sk_E @ (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ X2 @ sk_B_1 @ X1)) @ 
% 0.90/1.09             X2)
% 0.90/1.09          | ~ (l1_struct_0 @ X1)
% 0.90/1.09          | (v2_struct_0 @ X1)
% 0.90/1.09          | (v2_struct_0 @ sk_A)
% 0.90/1.09          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.90/1.09          | (v2_struct_0 @ sk_B_1))),
% 0.90/1.09      inference('simplify', [status(thm)], ['46'])).
% 0.90/1.09  thf('48', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]:
% 0.90/1.09         ((v2_struct_0 @ sk_B_1)
% 0.90/1.09          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.90/1.09          | (v2_struct_0 @ sk_A)
% 0.90/1.09          | (v2_struct_0 @ sk_A)
% 0.90/1.09          | ~ (l1_struct_0 @ sk_A)
% 0.90/1.09          | (r2_hidden @ 
% 0.90/1.09             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.90/1.09              (sk_E @ (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ X1 @ sk_B_1 @ sk_A)) @ 
% 0.90/1.09             X1)
% 0.90/1.09          | ~ (r2_waybel_0 @ sk_A @ sk_B_1 @ X1))),
% 0.90/1.09      inference('sup-', [status(thm)], ['39', '47'])).
% 0.90/1.09  thf('49', plain, ((l1_struct_0 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('50', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]:
% 0.90/1.09         ((v2_struct_0 @ sk_B_1)
% 0.90/1.09          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.90/1.09          | (v2_struct_0 @ sk_A)
% 0.90/1.09          | (v2_struct_0 @ sk_A)
% 0.90/1.09          | (r2_hidden @ 
% 0.90/1.09             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.90/1.09              (sk_E @ (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ X1 @ sk_B_1 @ sk_A)) @ 
% 0.90/1.09             X1)
% 0.90/1.09          | ~ (r2_waybel_0 @ sk_A @ sk_B_1 @ X1))),
% 0.90/1.09      inference('demod', [status(thm)], ['48', '49'])).
% 0.90/1.09  thf('51', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]:
% 0.90/1.09         (~ (r2_waybel_0 @ sk_A @ sk_B_1 @ X1)
% 0.90/1.09          | (r2_hidden @ 
% 0.90/1.09             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.90/1.09              (sk_E @ (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ X1 @ sk_B_1 @ sk_A)) @ 
% 0.90/1.09             X1)
% 0.90/1.09          | (v2_struct_0 @ sk_A)
% 0.90/1.09          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.90/1.09          | (v2_struct_0 @ sk_B_1))),
% 0.90/1.09      inference('simplify', [status(thm)], ['50'])).
% 0.90/1.09  thf('52', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]:
% 0.90/1.09         ((v2_struct_0 @ sk_B_1)
% 0.90/1.09          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X1)
% 0.90/1.09          | (v2_struct_0 @ sk_A)
% 0.90/1.09          | (r2_hidden @ 
% 0.90/1.09             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.90/1.09              (sk_E @ (sk_D_1 @ X1 @ sk_B_1 @ sk_A) @ 
% 0.90/1.09               (k6_subset_1 @ X0 @ X0) @ sk_B_1 @ sk_A)) @ 
% 0.90/1.09             (k6_subset_1 @ X0 @ X0)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['38', '51'])).
% 0.90/1.09  thf('53', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k6_subset_1 @ X0 @ X0))),
% 0.90/1.09      inference('condensation', [status(thm)], ['24'])).
% 0.90/1.09  thf('54', plain,
% 0.90/1.09      (![X1 : $i]:
% 0.90/1.09         ((v2_struct_0 @ sk_A)
% 0.90/1.09          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X1)
% 0.90/1.09          | (v2_struct_0 @ sk_B_1))),
% 0.90/1.09      inference('sup-', [status(thm)], ['52', '53'])).
% 0.90/1.09  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('56', plain,
% 0.90/1.09      (![X1 : $i]:
% 0.90/1.09         ((v2_struct_0 @ sk_B_1) | (r2_waybel_0 @ sk_A @ sk_B_1 @ X1))),
% 0.90/1.09      inference('clc', [status(thm)], ['54', '55'])).
% 0.90/1.09  thf('57', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('58', plain, (![X1 : $i]: (r2_waybel_0 @ sk_A @ sk_B_1 @ X1)),
% 0.90/1.09      inference('clc', [status(thm)], ['56', '57'])).
% 0.90/1.09  thf(dt_l1_orders_2, axiom,
% 0.90/1.09    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.90/1.09  thf('59', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_orders_2 @ X8))),
% 0.90/1.09      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.90/1.09  thf('60', plain, (![X1 : $i]: (r2_waybel_0 @ sk_A @ sk_B_1 @ X1)),
% 0.90/1.09      inference('clc', [status(thm)], ['56', '57'])).
% 0.90/1.09  thf(existence_l1_waybel_0, axiom,
% 0.90/1.09    (![A:$i]: ( ( l1_struct_0 @ A ) => ( ?[B:$i]: ( l1_waybel_0 @ B @ A ) ) ))).
% 0.90/1.09  thf('61', plain,
% 0.90/1.09      (![X17 : $i]:
% 0.90/1.09         ((l1_waybel_0 @ (sk_B @ X17) @ X17) | ~ (l1_struct_0 @ X17))),
% 0.90/1.09      inference('cnf', [status(esa)], [existence_l1_waybel_0])).
% 0.90/1.09  thf(dt_k4_yellow_6, axiom,
% 0.90/1.09    (![A:$i,B:$i]:
% 0.90/1.09     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.90/1.09         ( l1_waybel_0 @ B @ A ) ) =>
% 0.90/1.09       ( m1_subset_1 @ ( k4_yellow_6 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.90/1.09  thf('62', plain,
% 0.90/1.09      (![X22 : $i, X23 : $i]:
% 0.90/1.09         (~ (l1_struct_0 @ X22)
% 0.90/1.09          | (v2_struct_0 @ X22)
% 0.90/1.09          | ~ (l1_waybel_0 @ X23 @ X22)
% 0.90/1.09          | (m1_subset_1 @ (k4_yellow_6 @ X22 @ X23) @ (u1_struct_0 @ X22)))),
% 0.90/1.09      inference('cnf', [status(esa)], [dt_k4_yellow_6])).
% 0.90/1.09  thf('63', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (~ (l1_struct_0 @ X0)
% 0.90/1.09          | (m1_subset_1 @ (k4_yellow_6 @ X0 @ (sk_B @ X0)) @ 
% 0.90/1.09             (u1_struct_0 @ X0))
% 0.90/1.09          | (v2_struct_0 @ X0)
% 0.90/1.09          | ~ (l1_struct_0 @ X0))),
% 0.90/1.09      inference('sup-', [status(thm)], ['61', '62'])).
% 0.90/1.09  thf('64', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         ((v2_struct_0 @ X0)
% 0.90/1.09          | (m1_subset_1 @ (k4_yellow_6 @ X0 @ (sk_B @ X0)) @ 
% 0.90/1.09             (u1_struct_0 @ X0))
% 0.90/1.09          | ~ (l1_struct_0 @ X0))),
% 0.90/1.09      inference('simplify', [status(thm)], ['63'])).
% 0.90/1.09  thf('65', plain,
% 0.90/1.09      (![X9 : $i, X10 : $i, X13 : $i, X14 : $i]:
% 0.90/1.09         ((v2_struct_0 @ X9)
% 0.90/1.09          | ~ (l1_waybel_0 @ X9 @ X10)
% 0.90/1.09          | ~ (r2_waybel_0 @ X10 @ X9 @ X13)
% 0.90/1.09          | (m1_subset_1 @ (sk_E @ X14 @ X13 @ X9 @ X10) @ (u1_struct_0 @ X9))
% 0.90/1.09          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X9))
% 0.90/1.09          | ~ (l1_struct_0 @ X10)
% 0.90/1.09          | (v2_struct_0 @ X10))),
% 0.90/1.09      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.90/1.09  thf('66', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.09         (~ (l1_struct_0 @ X0)
% 0.90/1.09          | (v2_struct_0 @ X0)
% 0.90/1.09          | (v2_struct_0 @ X1)
% 0.90/1.09          | ~ (l1_struct_0 @ X1)
% 0.90/1.09          | (m1_subset_1 @ 
% 0.90/1.09             (sk_E @ (k4_yellow_6 @ X0 @ (sk_B @ X0)) @ X2 @ X0 @ X1) @ 
% 0.90/1.09             (u1_struct_0 @ X0))
% 0.90/1.09          | ~ (r2_waybel_0 @ X1 @ X0 @ X2)
% 0.90/1.09          | ~ (l1_waybel_0 @ X0 @ X1)
% 0.90/1.09          | (v2_struct_0 @ X0))),
% 0.90/1.09      inference('sup-', [status(thm)], ['64', '65'])).
% 0.90/1.09  thf('67', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.09         (~ (l1_waybel_0 @ X0 @ X1)
% 0.90/1.09          | ~ (r2_waybel_0 @ X1 @ X0 @ X2)
% 0.90/1.09          | (m1_subset_1 @ 
% 0.90/1.09             (sk_E @ (k4_yellow_6 @ X0 @ (sk_B @ X0)) @ X2 @ X0 @ X1) @ 
% 0.90/1.09             (u1_struct_0 @ X0))
% 0.90/1.09          | ~ (l1_struct_0 @ X1)
% 0.90/1.09          | (v2_struct_0 @ X1)
% 0.90/1.09          | (v2_struct_0 @ X0)
% 0.90/1.09          | ~ (l1_struct_0 @ X0))),
% 0.90/1.09      inference('simplify', [status(thm)], ['66'])).
% 0.90/1.09  thf('68', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (~ (l1_struct_0 @ sk_B_1)
% 0.90/1.09          | (v2_struct_0 @ sk_B_1)
% 0.90/1.09          | (v2_struct_0 @ sk_A)
% 0.90/1.09          | ~ (l1_struct_0 @ sk_A)
% 0.90/1.09          | (m1_subset_1 @ 
% 0.90/1.09             (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0 @ sk_B_1 @ 
% 0.90/1.09              sk_A) @ 
% 0.90/1.09             (u1_struct_0 @ sk_B_1))
% 0.90/1.09          | ~ (l1_waybel_0 @ sk_B_1 @ sk_A))),
% 0.90/1.09      inference('sup-', [status(thm)], ['60', '67'])).
% 0.90/1.09  thf('69', plain, ((l1_struct_0 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('70', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('71', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (~ (l1_struct_0 @ sk_B_1)
% 0.90/1.09          | (v2_struct_0 @ sk_B_1)
% 0.90/1.09          | (v2_struct_0 @ sk_A)
% 0.90/1.09          | (m1_subset_1 @ 
% 0.90/1.09             (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0 @ sk_B_1 @ 
% 0.90/1.09              sk_A) @ 
% 0.90/1.09             (u1_struct_0 @ sk_B_1)))),
% 0.90/1.09      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.90/1.09  thf('72', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (~ (l1_orders_2 @ sk_B_1)
% 0.90/1.09          | (m1_subset_1 @ 
% 0.90/1.09             (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0 @ sk_B_1 @ 
% 0.90/1.09              sk_A) @ 
% 0.90/1.09             (u1_struct_0 @ sk_B_1))
% 0.90/1.09          | (v2_struct_0 @ sk_A)
% 0.90/1.09          | (v2_struct_0 @ sk_B_1))),
% 0.90/1.09      inference('sup-', [status(thm)], ['59', '71'])).
% 0.90/1.09  thf('73', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf(dt_l1_waybel_0, axiom,
% 0.90/1.09    (![A:$i]:
% 0.90/1.09     ( ( l1_struct_0 @ A ) =>
% 0.90/1.09       ( ![B:$i]: ( ( l1_waybel_0 @ B @ A ) => ( l1_orders_2 @ B ) ) ) ))).
% 0.90/1.09  thf('74', plain,
% 0.90/1.09      (![X15 : $i, X16 : $i]:
% 0.90/1.09         (~ (l1_waybel_0 @ X15 @ X16)
% 0.90/1.09          | (l1_orders_2 @ X15)
% 0.90/1.09          | ~ (l1_struct_0 @ X16))),
% 0.90/1.09      inference('cnf', [status(esa)], [dt_l1_waybel_0])).
% 0.90/1.09  thf('75', plain, ((~ (l1_struct_0 @ sk_A) | (l1_orders_2 @ sk_B_1))),
% 0.90/1.09      inference('sup-', [status(thm)], ['73', '74'])).
% 0.90/1.09  thf('76', plain, ((l1_struct_0 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('77', plain, ((l1_orders_2 @ sk_B_1)),
% 0.90/1.09      inference('demod', [status(thm)], ['75', '76'])).
% 0.90/1.09  thf('78', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         ((m1_subset_1 @ 
% 0.90/1.09           (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0 @ sk_B_1 @ 
% 0.90/1.09            sk_A) @ 
% 0.90/1.09           (u1_struct_0 @ sk_B_1))
% 0.90/1.09          | (v2_struct_0 @ sk_A)
% 0.90/1.09          | (v2_struct_0 @ sk_B_1))),
% 0.90/1.09      inference('demod', [status(thm)], ['72', '77'])).
% 0.90/1.09  thf('79', plain, (~ (v2_struct_0 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('80', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         ((v2_struct_0 @ sk_B_1)
% 0.90/1.09          | (m1_subset_1 @ 
% 0.90/1.09             (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0 @ sk_B_1 @ 
% 0.90/1.09              sk_A) @ 
% 0.90/1.09             (u1_struct_0 @ sk_B_1)))),
% 0.90/1.09      inference('clc', [status(thm)], ['78', '79'])).
% 0.90/1.09  thf('81', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('82', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (m1_subset_1 @ 
% 0.90/1.09          (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.90/1.09          (u1_struct_0 @ sk_B_1))),
% 0.90/1.09      inference('clc', [status(thm)], ['80', '81'])).
% 0.90/1.09  thf('83', plain,
% 0.90/1.09      (![X9 : $i, X10 : $i, X13 : $i, X14 : $i]:
% 0.90/1.09         ((v2_struct_0 @ X9)
% 0.90/1.09          | ~ (l1_waybel_0 @ X9 @ X10)
% 0.90/1.09          | ~ (r2_waybel_0 @ X10 @ X9 @ X13)
% 0.90/1.09          | (r2_hidden @ 
% 0.90/1.09             (k2_waybel_0 @ X10 @ X9 @ (sk_E @ X14 @ X13 @ X9 @ X10)) @ X13)
% 0.90/1.09          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X9))
% 0.90/1.09          | ~ (l1_struct_0 @ X10)
% 0.90/1.09          | (v2_struct_0 @ X10))),
% 0.90/1.09      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.90/1.09  thf('84', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.09         ((v2_struct_0 @ X1)
% 0.90/1.09          | ~ (l1_struct_0 @ X1)
% 0.90/1.09          | (r2_hidden @ 
% 0.90/1.09             (k2_waybel_0 @ X1 @ sk_B_1 @ 
% 0.90/1.09              (sk_E @ 
% 0.90/1.09               (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0 @ 
% 0.90/1.09                sk_B_1 @ sk_A) @ 
% 0.90/1.09               X2 @ sk_B_1 @ X1)) @ 
% 0.90/1.09             X2)
% 0.90/1.09          | ~ (r2_waybel_0 @ X1 @ sk_B_1 @ X2)
% 0.90/1.09          | ~ (l1_waybel_0 @ sk_B_1 @ X1)
% 0.90/1.09          | (v2_struct_0 @ sk_B_1))),
% 0.90/1.09      inference('sup-', [status(thm)], ['82', '83'])).
% 0.90/1.09  thf('85', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]:
% 0.90/1.09         ((v2_struct_0 @ sk_B_1)
% 0.90/1.09          | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.90/1.09          | (r2_hidden @ 
% 0.90/1.09             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.90/1.09              (sk_E @ 
% 0.90/1.09               (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X1 @ 
% 0.90/1.09                sk_B_1 @ sk_A) @ 
% 0.90/1.09               X0 @ sk_B_1 @ sk_A)) @ 
% 0.90/1.09             X0)
% 0.90/1.09          | ~ (l1_struct_0 @ sk_A)
% 0.90/1.09          | (v2_struct_0 @ sk_A))),
% 0.90/1.09      inference('sup-', [status(thm)], ['58', '84'])).
% 0.90/1.09  thf('86', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('87', plain, ((l1_struct_0 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('88', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]:
% 0.90/1.09         ((v2_struct_0 @ sk_B_1)
% 0.90/1.09          | (r2_hidden @ 
% 0.90/1.09             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.90/1.09              (sk_E @ 
% 0.90/1.09               (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X1 @ 
% 0.90/1.09                sk_B_1 @ sk_A) @ 
% 0.90/1.09               X0 @ sk_B_1 @ sk_A)) @ 
% 0.90/1.09             X0)
% 0.90/1.09          | (v2_struct_0 @ sk_A))),
% 0.90/1.09      inference('demod', [status(thm)], ['85', '86', '87'])).
% 0.90/1.09  thf('89', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('90', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]:
% 0.90/1.09         ((v2_struct_0 @ sk_A)
% 0.90/1.09          | (r2_hidden @ 
% 0.90/1.09             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.90/1.09              (sk_E @ 
% 0.90/1.09               (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X1 @ 
% 0.90/1.09                sk_B_1 @ sk_A) @ 
% 0.90/1.09               X0 @ sk_B_1 @ sk_A)) @ 
% 0.90/1.09             X0))),
% 0.90/1.09      inference('clc', [status(thm)], ['88', '89'])).
% 0.90/1.09  thf('91', plain, (~ (v2_struct_0 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('92', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]:
% 0.90/1.09         (r2_hidden @ 
% 0.90/1.09          (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.90/1.09           (sk_E @ 
% 0.90/1.09            (sk_E @ (k4_yellow_6 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X1 @ sk_B_1 @ 
% 0.90/1.09             sk_A) @ 
% 0.90/1.09            X0 @ sk_B_1 @ sk_A)) @ 
% 0.90/1.09          X0)),
% 0.90/1.09      inference('clc', [status(thm)], ['90', '91'])).
% 0.90/1.09  thf('93', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k6_subset_1 @ X0 @ X0))),
% 0.90/1.09      inference('condensation', [status(thm)], ['24'])).
% 0.90/1.09  thf('94', plain, ($false), inference('sup-', [status(thm)], ['92', '93'])).
% 0.90/1.09  
% 0.90/1.09  % SZS output end Refutation
% 0.90/1.09  
% 0.90/1.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
