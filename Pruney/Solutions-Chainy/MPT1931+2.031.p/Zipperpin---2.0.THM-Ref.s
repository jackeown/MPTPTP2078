%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.u7tP8KzJdC

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:00 EST 2020

% Result     : Theorem 4.25s
% Output     : Refutation 4.25s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 196 expanded)
%              Number of leaves         :   25 (  69 expanded)
%              Depth                    :   18
%              Number of atoms          :  864 (2218 expanded)
%              Number of equality atoms :   32 ( 108 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(o_2_2_yellow_6_type,type,(
    o_2_2_yellow_6: $i > $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(r2_waybel_0_type,type,(
    r2_waybel_0: $i > $i > $i > $o )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

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
    ~ ( v2_struct_0 @ sk_B ) ),
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

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k6_subset_1 @ X6 @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('3',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k6_subset_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['3'])).

thf('5',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k6_subset_1 @ X6 @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('7',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k6_subset_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k6_subset_1 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['3'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k6_subset_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k6_subset_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('13',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('14',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k6_subset_1 @ X6 @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('15',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k6_subset_1 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k6_subset_1 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k6_subset_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k6_subset_1 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('19',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k6_subset_1 @ X6 @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('21',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k6_subset_1 @ X1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k6_subset_1 @ X1 @ X0 )
        = ( k6_subset_1 @ X2 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ ( k6_subset_1 @ X1 @ X0 ) @ X2 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k6_subset_1 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('24',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('25',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k6_subset_1 @ X6 @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('27',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k6_subset_1 @ X1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k6_subset_1 @ X1 @ X0 )
        = ( k6_subset_1 @ X2 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k6_subset_1 @ X1 @ X0 ) @ X2 @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_subset_1 @ X0 @ X0 )
        = ( k6_subset_1 @ X1 @ X1 ) )
      | ( ( k6_subset_1 @ X0 @ X0 )
        = ( k6_subset_1 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k6_subset_1 @ X1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k6_subset_1 @ X1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k6_subset_1 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k6_subset_1 @ X0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k6_subset_1 @ X1 @ ( k6_subset_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','33'])).

thf('35',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
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

thf('36',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( l1_waybel_0 @ X14 @ X15 )
      | ( r1_waybel_0 @ X15 @ X14 @ ( k6_subset_1 @ ( u1_struct_0 @ X15 ) @ X16 ) )
      | ( r2_waybel_0 @ X15 @ X14 @ X16 )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t10_waybel_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_0 @ sk_A @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r2_waybel_0 @ sk_A @ sk_B @ ( k6_subset_1 @ X0 @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['34','39'])).

thf('41',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_o_2_2_yellow_6,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ~ ( v2_struct_0 @ B )
        & ( v4_orders_2 @ B )
        & ( v7_waybel_0 @ B )
        & ( l1_waybel_0 @ B @ A ) )
     => ( m1_subset_1 @ ( o_2_2_yellow_6 @ A @ B ) @ ( u1_struct_0 @ B ) ) ) )).

thf('42',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( v2_struct_0 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v7_waybel_0 @ X19 )
      | ~ ( l1_waybel_0 @ X19 @ X18 )
      | ( m1_subset_1 @ ( o_2_2_yellow_6 @ X18 @ X19 ) @ ( u1_struct_0 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_o_2_2_yellow_6])).

thf('43',plain,
    ( ( m1_subset_1 @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( m1_subset_1 @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','44','45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['49','50'])).

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

thf('52',plain,(
    ! [X8: $i,X9: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( l1_waybel_0 @ X8 @ X9 )
      | ~ ( r2_waybel_0 @ X9 @ X8 @ X12 )
      | ( r2_hidden @ ( k2_waybel_0 @ X9 @ X8 @ ( sk_E @ X13 @ X12 @ X8 @ X9 ) ) @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( r2_hidden @ ( k2_waybel_0 @ X0 @ sk_B @ ( sk_E @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ X1 @ sk_B @ X0 ) ) @ X1 )
      | ~ ( r2_waybel_0 @ X0 @ sk_B @ X1 )
      | ~ ( l1_waybel_0 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B @ ( sk_E @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ ( k6_subset_1 @ X0 @ X0 ) @ sk_B @ sk_A ) ) @ ( k6_subset_1 @ X0 @ X0 ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','53'])).

thf('55',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B @ ( sk_E @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ ( k6_subset_1 @ X0 @ X0 ) @ sk_B @ sk_A ) ) @ ( k6_subset_1 @ X0 @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B @ ( sk_E @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ ( k6_subset_1 @ X0 @ X0 ) @ sk_B @ sk_A ) ) @ ( k6_subset_1 @ X0 @ X0 ) )
      | ( r1_waybel_0 @ sk_A @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k6_subset_1 @ X0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['32'])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_0 @ sk_A @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( r1_waybel_0 @ sk_A @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( r1_waybel_0 @ sk_A @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v2_struct_0 @ sk_B ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['0','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.u7tP8KzJdC
% 0.14/0.36  % Computer   : n024.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 18:48:06 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 4.25/4.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.25/4.48  % Solved by: fo/fo7.sh
% 4.25/4.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.25/4.48  % done 4021 iterations in 4.010s
% 4.25/4.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.25/4.48  % SZS output start Refutation
% 4.25/4.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.25/4.48  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 4.25/4.48  thf(o_2_2_yellow_6_type, type, o_2_2_yellow_6: $i > $i > $i).
% 4.25/4.48  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 4.25/4.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.25/4.48  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 4.25/4.48  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 4.25/4.48  thf(sk_A_type, type, sk_A: $i).
% 4.25/4.48  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 4.25/4.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.25/4.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 4.25/4.48  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 4.25/4.48  thf(sk_B_type, type, sk_B: $i).
% 4.25/4.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 4.25/4.48  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 4.25/4.48  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 4.25/4.48  thf(r2_waybel_0_type, type, r2_waybel_0: $i > $i > $i > $o).
% 4.25/4.48  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 4.25/4.48  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 4.25/4.48  thf(t29_yellow_6, conjecture,
% 4.25/4.48    (![A:$i]:
% 4.25/4.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 4.25/4.48       ( ![B:$i]:
% 4.25/4.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 4.25/4.48             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 4.25/4.48           ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ))).
% 4.25/4.48  thf(zf_stmt_0, negated_conjecture,
% 4.25/4.48    (~( ![A:$i]:
% 4.25/4.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 4.25/4.48          ( ![B:$i]:
% 4.25/4.48            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 4.25/4.48                ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 4.25/4.48              ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ) )),
% 4.25/4.48    inference('cnf.neg', [status(esa)], [t29_yellow_6])).
% 4.25/4.48  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 4.25/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.48  thf(d5_xboole_0, axiom,
% 4.25/4.48    (![A:$i,B:$i,C:$i]:
% 4.25/4.48     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 4.25/4.48       ( ![D:$i]:
% 4.25/4.48         ( ( r2_hidden @ D @ C ) <=>
% 4.25/4.48           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 4.25/4.48  thf('1', plain,
% 4.25/4.48      (![X1 : $i, X2 : $i, X5 : $i]:
% 4.25/4.48         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 4.25/4.48          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 4.25/4.48          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 4.25/4.48      inference('cnf', [status(esa)], [d5_xboole_0])).
% 4.25/4.48  thf(redefinition_k6_subset_1, axiom,
% 4.25/4.48    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 4.25/4.48  thf('2', plain,
% 4.25/4.48      (![X6 : $i, X7 : $i]: ((k6_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))),
% 4.25/4.48      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 4.25/4.48  thf('3', plain,
% 4.25/4.48      (![X1 : $i, X2 : $i, X5 : $i]:
% 4.25/4.48         (((X5) = (k6_subset_1 @ X1 @ X2))
% 4.25/4.48          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 4.25/4.48          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 4.25/4.48      inference('demod', [status(thm)], ['1', '2'])).
% 4.25/4.48  thf('4', plain,
% 4.25/4.48      (![X0 : $i, X1 : $i]:
% 4.25/4.48         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 4.25/4.48          | ((X0) = (k6_subset_1 @ X0 @ X1)))),
% 4.25/4.48      inference('eq_fact', [status(thm)], ['3'])).
% 4.25/4.48  thf('5', plain,
% 4.25/4.48      (![X1 : $i, X2 : $i, X5 : $i]:
% 4.25/4.48         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 4.25/4.48          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 4.25/4.48          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 4.25/4.48          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 4.25/4.48      inference('cnf', [status(esa)], [d5_xboole_0])).
% 4.25/4.48  thf('6', plain,
% 4.25/4.48      (![X6 : $i, X7 : $i]: ((k6_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))),
% 4.25/4.48      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 4.25/4.48  thf('7', plain,
% 4.25/4.48      (![X1 : $i, X2 : $i, X5 : $i]:
% 4.25/4.48         (((X5) = (k6_subset_1 @ X1 @ X2))
% 4.25/4.48          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 4.25/4.48          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 4.25/4.48          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 4.25/4.48      inference('demod', [status(thm)], ['5', '6'])).
% 4.25/4.48  thf('8', plain,
% 4.25/4.48      (![X0 : $i, X1 : $i]:
% 4.25/4.48         (((X0) = (k6_subset_1 @ X0 @ X1))
% 4.25/4.48          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 4.25/4.48          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 4.25/4.48          | ((X0) = (k6_subset_1 @ X0 @ X1)))),
% 4.25/4.48      inference('sup-', [status(thm)], ['4', '7'])).
% 4.25/4.48  thf('9', plain,
% 4.25/4.48      (![X0 : $i, X1 : $i]:
% 4.25/4.48         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 4.25/4.48          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 4.25/4.48          | ((X0) = (k6_subset_1 @ X0 @ X1)))),
% 4.25/4.48      inference('simplify', [status(thm)], ['8'])).
% 4.25/4.48  thf('10', plain,
% 4.25/4.48      (![X0 : $i, X1 : $i]:
% 4.25/4.48         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 4.25/4.48          | ((X0) = (k6_subset_1 @ X0 @ X1)))),
% 4.25/4.48      inference('eq_fact', [status(thm)], ['3'])).
% 4.25/4.48  thf('11', plain,
% 4.25/4.48      (![X0 : $i, X1 : $i]:
% 4.25/4.48         (((X0) = (k6_subset_1 @ X0 @ X1))
% 4.25/4.48          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 4.25/4.48      inference('clc', [status(thm)], ['9', '10'])).
% 4.25/4.48  thf('12', plain,
% 4.25/4.48      (![X1 : $i, X2 : $i, X5 : $i]:
% 4.25/4.48         (((X5) = (k6_subset_1 @ X1 @ X2))
% 4.25/4.48          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 4.25/4.48          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 4.25/4.48      inference('demod', [status(thm)], ['1', '2'])).
% 4.25/4.48  thf('13', plain,
% 4.25/4.48      (![X1 : $i, X2 : $i, X5 : $i]:
% 4.25/4.48         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 4.25/4.48          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 4.25/4.48          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 4.25/4.48      inference('cnf', [status(esa)], [d5_xboole_0])).
% 4.25/4.48  thf('14', plain,
% 4.25/4.48      (![X6 : $i, X7 : $i]: ((k6_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))),
% 4.25/4.48      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 4.25/4.48  thf('15', plain,
% 4.25/4.48      (![X1 : $i, X2 : $i, X5 : $i]:
% 4.25/4.48         (((X5) = (k6_subset_1 @ X1 @ X2))
% 4.25/4.48          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 4.25/4.48          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 4.25/4.48      inference('demod', [status(thm)], ['13', '14'])).
% 4.25/4.48  thf('16', plain,
% 4.25/4.48      (![X0 : $i, X1 : $i]:
% 4.25/4.48         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 4.25/4.48          | ((X1) = (k6_subset_1 @ X0 @ X0))
% 4.25/4.48          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 4.25/4.48          | ((X1) = (k6_subset_1 @ X0 @ X0)))),
% 4.25/4.48      inference('sup-', [status(thm)], ['12', '15'])).
% 4.25/4.48  thf('17', plain,
% 4.25/4.48      (![X0 : $i, X1 : $i]:
% 4.25/4.48         (((X1) = (k6_subset_1 @ X0 @ X0))
% 4.25/4.48          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 4.25/4.48      inference('simplify', [status(thm)], ['16'])).
% 4.25/4.48  thf('18', plain,
% 4.25/4.48      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.25/4.48         (~ (r2_hidden @ X4 @ X3)
% 4.25/4.48          | (r2_hidden @ X4 @ X1)
% 4.25/4.48          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 4.25/4.48      inference('cnf', [status(esa)], [d5_xboole_0])).
% 4.25/4.48  thf('19', plain,
% 4.25/4.48      (![X1 : $i, X2 : $i, X4 : $i]:
% 4.25/4.48         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 4.25/4.48      inference('simplify', [status(thm)], ['18'])).
% 4.25/4.48  thf('20', plain,
% 4.25/4.48      (![X6 : $i, X7 : $i]: ((k6_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))),
% 4.25/4.48      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 4.25/4.48  thf('21', plain,
% 4.25/4.48      (![X1 : $i, X2 : $i, X4 : $i]:
% 4.25/4.48         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k6_subset_1 @ X1 @ X2)))),
% 4.25/4.48      inference('demod', [status(thm)], ['19', '20'])).
% 4.25/4.48  thf('22', plain,
% 4.25/4.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.25/4.48         (((k6_subset_1 @ X1 @ X0) = (k6_subset_1 @ X2 @ X2))
% 4.25/4.48          | (r2_hidden @ (sk_D @ (k6_subset_1 @ X1 @ X0) @ X2 @ X2) @ X1))),
% 4.25/4.48      inference('sup-', [status(thm)], ['17', '21'])).
% 4.25/4.48  thf('23', plain,
% 4.25/4.48      (![X0 : $i, X1 : $i]:
% 4.25/4.48         (((X1) = (k6_subset_1 @ X0 @ X0))
% 4.25/4.48          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 4.25/4.48      inference('simplify', [status(thm)], ['16'])).
% 4.25/4.48  thf('24', plain,
% 4.25/4.48      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.25/4.48         (~ (r2_hidden @ X4 @ X3)
% 4.25/4.48          | ~ (r2_hidden @ X4 @ X2)
% 4.25/4.48          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 4.25/4.48      inference('cnf', [status(esa)], [d5_xboole_0])).
% 4.25/4.48  thf('25', plain,
% 4.25/4.48      (![X1 : $i, X2 : $i, X4 : $i]:
% 4.25/4.48         (~ (r2_hidden @ X4 @ X2)
% 4.25/4.48          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 4.25/4.48      inference('simplify', [status(thm)], ['24'])).
% 4.25/4.48  thf('26', plain,
% 4.25/4.48      (![X6 : $i, X7 : $i]: ((k6_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))),
% 4.25/4.48      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 4.25/4.48  thf('27', plain,
% 4.25/4.48      (![X1 : $i, X2 : $i, X4 : $i]:
% 4.25/4.48         (~ (r2_hidden @ X4 @ X2)
% 4.25/4.48          | ~ (r2_hidden @ X4 @ (k6_subset_1 @ X1 @ X2)))),
% 4.25/4.48      inference('demod', [status(thm)], ['25', '26'])).
% 4.25/4.48  thf('28', plain,
% 4.25/4.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.25/4.48         (((k6_subset_1 @ X1 @ X0) = (k6_subset_1 @ X2 @ X2))
% 4.25/4.48          | ~ (r2_hidden @ (sk_D @ (k6_subset_1 @ X1 @ X0) @ X2 @ X2) @ X0))),
% 4.25/4.48      inference('sup-', [status(thm)], ['23', '27'])).
% 4.25/4.48  thf('29', plain,
% 4.25/4.48      (![X0 : $i, X1 : $i]:
% 4.25/4.48         (((k6_subset_1 @ X0 @ X0) = (k6_subset_1 @ X1 @ X1))
% 4.25/4.48          | ((k6_subset_1 @ X0 @ X0) = (k6_subset_1 @ X1 @ X1)))),
% 4.25/4.48      inference('sup-', [status(thm)], ['22', '28'])).
% 4.25/4.48  thf('30', plain,
% 4.25/4.48      (![X0 : $i, X1 : $i]: ((k6_subset_1 @ X0 @ X0) = (k6_subset_1 @ X1 @ X1))),
% 4.25/4.48      inference('simplify', [status(thm)], ['29'])).
% 4.25/4.48  thf('31', plain,
% 4.25/4.48      (![X1 : $i, X2 : $i, X4 : $i]:
% 4.25/4.48         (~ (r2_hidden @ X4 @ X2)
% 4.25/4.48          | ~ (r2_hidden @ X4 @ (k6_subset_1 @ X1 @ X2)))),
% 4.25/4.48      inference('demod', [status(thm)], ['25', '26'])).
% 4.25/4.48  thf('32', plain,
% 4.25/4.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.25/4.48         (~ (r2_hidden @ X2 @ (k6_subset_1 @ X0 @ X0))
% 4.25/4.48          | ~ (r2_hidden @ X2 @ X1))),
% 4.25/4.48      inference('sup-', [status(thm)], ['30', '31'])).
% 4.25/4.48  thf('33', plain,
% 4.25/4.48      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k6_subset_1 @ X0 @ X0))),
% 4.25/4.48      inference('condensation', [status(thm)], ['32'])).
% 4.25/4.48  thf('34', plain,
% 4.25/4.48      (![X0 : $i, X1 : $i]:
% 4.25/4.48         ((X1) = (k6_subset_1 @ X1 @ (k6_subset_1 @ X0 @ X0)))),
% 4.25/4.48      inference('sup-', [status(thm)], ['11', '33'])).
% 4.25/4.48  thf('35', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 4.25/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.48  thf(t10_waybel_0, axiom,
% 4.25/4.48    (![A:$i]:
% 4.25/4.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 4.25/4.48       ( ![B:$i]:
% 4.25/4.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 4.25/4.48           ( ![C:$i]:
% 4.25/4.48             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 4.25/4.48               ( ~( r1_waybel_0 @
% 4.25/4.48                    A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ))).
% 4.25/4.48  thf('36', plain,
% 4.25/4.48      (![X14 : $i, X15 : $i, X16 : $i]:
% 4.25/4.48         ((v2_struct_0 @ X14)
% 4.25/4.48          | ~ (l1_waybel_0 @ X14 @ X15)
% 4.25/4.48          | (r1_waybel_0 @ X15 @ X14 @ 
% 4.25/4.48             (k6_subset_1 @ (u1_struct_0 @ X15) @ X16))
% 4.25/4.48          | (r2_waybel_0 @ X15 @ X14 @ X16)
% 4.25/4.48          | ~ (l1_struct_0 @ X15)
% 4.25/4.48          | (v2_struct_0 @ X15))),
% 4.25/4.48      inference('cnf', [status(esa)], [t10_waybel_0])).
% 4.25/4.48  thf('37', plain,
% 4.25/4.48      (![X0 : $i]:
% 4.25/4.48         ((v2_struct_0 @ sk_A)
% 4.25/4.48          | ~ (l1_struct_0 @ sk_A)
% 4.25/4.48          | (r2_waybel_0 @ sk_A @ sk_B @ X0)
% 4.25/4.48          | (r1_waybel_0 @ sk_A @ sk_B @ 
% 4.25/4.48             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 4.25/4.48          | (v2_struct_0 @ sk_B))),
% 4.25/4.48      inference('sup-', [status(thm)], ['35', '36'])).
% 4.25/4.48  thf('38', plain, ((l1_struct_0 @ sk_A)),
% 4.25/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.48  thf('39', plain,
% 4.25/4.48      (![X0 : $i]:
% 4.25/4.48         ((v2_struct_0 @ sk_A)
% 4.25/4.48          | (r2_waybel_0 @ sk_A @ sk_B @ X0)
% 4.25/4.48          | (r1_waybel_0 @ sk_A @ sk_B @ 
% 4.25/4.48             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 4.25/4.48          | (v2_struct_0 @ sk_B))),
% 4.25/4.48      inference('demod', [status(thm)], ['37', '38'])).
% 4.25/4.48  thf('40', plain,
% 4.25/4.48      (![X0 : $i]:
% 4.25/4.48         ((r1_waybel_0 @ sk_A @ sk_B @ (u1_struct_0 @ sk_A))
% 4.25/4.48          | (v2_struct_0 @ sk_B)
% 4.25/4.48          | (r2_waybel_0 @ sk_A @ sk_B @ (k6_subset_1 @ X0 @ X0))
% 4.25/4.48          | (v2_struct_0 @ sk_A))),
% 4.25/4.48      inference('sup+', [status(thm)], ['34', '39'])).
% 4.25/4.48  thf('41', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 4.25/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.48  thf(dt_o_2_2_yellow_6, axiom,
% 4.25/4.48    (![A:$i,B:$i]:
% 4.25/4.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 4.25/4.48         ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 4.25/4.48         ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 4.25/4.48       ( m1_subset_1 @ ( o_2_2_yellow_6 @ A @ B ) @ ( u1_struct_0 @ B ) ) ))).
% 4.25/4.48  thf('42', plain,
% 4.25/4.48      (![X18 : $i, X19 : $i]:
% 4.25/4.48         (~ (l1_struct_0 @ X18)
% 4.25/4.48          | (v2_struct_0 @ X18)
% 4.25/4.48          | (v2_struct_0 @ X19)
% 4.25/4.48          | ~ (v4_orders_2 @ X19)
% 4.25/4.48          | ~ (v7_waybel_0 @ X19)
% 4.25/4.48          | ~ (l1_waybel_0 @ X19 @ X18)
% 4.25/4.48          | (m1_subset_1 @ (o_2_2_yellow_6 @ X18 @ X19) @ (u1_struct_0 @ X19)))),
% 4.25/4.48      inference('cnf', [status(esa)], [dt_o_2_2_yellow_6])).
% 4.25/4.48  thf('43', plain,
% 4.25/4.48      (((m1_subset_1 @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))
% 4.25/4.48        | ~ (v7_waybel_0 @ sk_B)
% 4.25/4.48        | ~ (v4_orders_2 @ sk_B)
% 4.25/4.48        | (v2_struct_0 @ sk_B)
% 4.25/4.48        | (v2_struct_0 @ sk_A)
% 4.25/4.48        | ~ (l1_struct_0 @ sk_A))),
% 4.25/4.48      inference('sup-', [status(thm)], ['41', '42'])).
% 4.25/4.48  thf('44', plain, ((v7_waybel_0 @ sk_B)),
% 4.25/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.48  thf('45', plain, ((v4_orders_2 @ sk_B)),
% 4.25/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.48  thf('46', plain, ((l1_struct_0 @ sk_A)),
% 4.25/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.48  thf('47', plain,
% 4.25/4.48      (((m1_subset_1 @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))
% 4.25/4.48        | (v2_struct_0 @ sk_B)
% 4.25/4.48        | (v2_struct_0 @ sk_A))),
% 4.25/4.48      inference('demod', [status(thm)], ['43', '44', '45', '46'])).
% 4.25/4.48  thf('48', plain, (~ (v2_struct_0 @ sk_B)),
% 4.25/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.48  thf('49', plain,
% 4.25/4.48      (((v2_struct_0 @ sk_A)
% 4.25/4.48        | (m1_subset_1 @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)))),
% 4.25/4.48      inference('clc', [status(thm)], ['47', '48'])).
% 4.25/4.48  thf('50', plain, (~ (v2_struct_0 @ sk_A)),
% 4.25/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.49  thf('51', plain,
% 4.25/4.49      ((m1_subset_1 @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))),
% 4.25/4.49      inference('clc', [status(thm)], ['49', '50'])).
% 4.25/4.49  thf(d12_waybel_0, axiom,
% 4.25/4.49    (![A:$i]:
% 4.25/4.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 4.25/4.49       ( ![B:$i]:
% 4.25/4.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 4.25/4.49           ( ![C:$i]:
% 4.25/4.49             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 4.25/4.49               ( ![D:$i]:
% 4.25/4.49                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 4.25/4.49                   ( ?[E:$i]:
% 4.25/4.49                     ( ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) & 
% 4.25/4.49                       ( r1_orders_2 @ B @ D @ E ) & 
% 4.25/4.49                       ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ))).
% 4.25/4.49  thf('52', plain,
% 4.25/4.49      (![X8 : $i, X9 : $i, X12 : $i, X13 : $i]:
% 4.25/4.49         ((v2_struct_0 @ X8)
% 4.25/4.49          | ~ (l1_waybel_0 @ X8 @ X9)
% 4.25/4.49          | ~ (r2_waybel_0 @ X9 @ X8 @ X12)
% 4.25/4.49          | (r2_hidden @ 
% 4.25/4.49             (k2_waybel_0 @ X9 @ X8 @ (sk_E @ X13 @ X12 @ X8 @ X9)) @ X12)
% 4.25/4.49          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X8))
% 4.25/4.49          | ~ (l1_struct_0 @ X9)
% 4.25/4.49          | (v2_struct_0 @ X9))),
% 4.25/4.49      inference('cnf', [status(esa)], [d12_waybel_0])).
% 4.25/4.49  thf('53', plain,
% 4.25/4.49      (![X0 : $i, X1 : $i]:
% 4.25/4.49         ((v2_struct_0 @ X0)
% 4.25/4.49          | ~ (l1_struct_0 @ X0)
% 4.25/4.49          | (r2_hidden @ 
% 4.25/4.49             (k2_waybel_0 @ X0 @ sk_B @ 
% 4.25/4.49              (sk_E @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ X1 @ sk_B @ X0)) @ 
% 4.25/4.49             X1)
% 4.25/4.49          | ~ (r2_waybel_0 @ X0 @ sk_B @ X1)
% 4.25/4.49          | ~ (l1_waybel_0 @ sk_B @ X0)
% 4.25/4.49          | (v2_struct_0 @ sk_B))),
% 4.25/4.49      inference('sup-', [status(thm)], ['51', '52'])).
% 4.25/4.49  thf('54', plain,
% 4.25/4.49      (![X0 : $i]:
% 4.25/4.49         ((v2_struct_0 @ sk_A)
% 4.25/4.49          | (v2_struct_0 @ sk_B)
% 4.25/4.49          | (r1_waybel_0 @ sk_A @ sk_B @ (u1_struct_0 @ sk_A))
% 4.25/4.49          | (v2_struct_0 @ sk_B)
% 4.25/4.49          | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 4.25/4.49          | (r2_hidden @ 
% 4.25/4.49             (k2_waybel_0 @ sk_A @ sk_B @ 
% 4.25/4.49              (sk_E @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ 
% 4.25/4.49               (k6_subset_1 @ X0 @ X0) @ sk_B @ sk_A)) @ 
% 4.25/4.49             (k6_subset_1 @ X0 @ X0))
% 4.25/4.49          | ~ (l1_struct_0 @ sk_A)
% 4.25/4.49          | (v2_struct_0 @ sk_A))),
% 4.25/4.49      inference('sup-', [status(thm)], ['40', '53'])).
% 4.25/4.49  thf('55', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 4.25/4.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.49  thf('56', plain, ((l1_struct_0 @ sk_A)),
% 4.25/4.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.49  thf('57', plain,
% 4.25/4.49      (![X0 : $i]:
% 4.25/4.49         ((v2_struct_0 @ sk_A)
% 4.25/4.49          | (v2_struct_0 @ sk_B)
% 4.25/4.49          | (r1_waybel_0 @ sk_A @ sk_B @ (u1_struct_0 @ sk_A))
% 4.25/4.49          | (v2_struct_0 @ sk_B)
% 4.25/4.49          | (r2_hidden @ 
% 4.25/4.49             (k2_waybel_0 @ sk_A @ sk_B @ 
% 4.25/4.49              (sk_E @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ 
% 4.25/4.49               (k6_subset_1 @ X0 @ X0) @ sk_B @ sk_A)) @ 
% 4.25/4.49             (k6_subset_1 @ X0 @ X0))
% 4.25/4.49          | (v2_struct_0 @ sk_A))),
% 4.25/4.49      inference('demod', [status(thm)], ['54', '55', '56'])).
% 4.25/4.49  thf('58', plain,
% 4.25/4.49      (![X0 : $i]:
% 4.25/4.49         ((r2_hidden @ 
% 4.25/4.49           (k2_waybel_0 @ sk_A @ sk_B @ 
% 4.25/4.49            (sk_E @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ (k6_subset_1 @ X0 @ X0) @ 
% 4.25/4.49             sk_B @ sk_A)) @ 
% 4.25/4.49           (k6_subset_1 @ X0 @ X0))
% 4.25/4.49          | (r1_waybel_0 @ sk_A @ sk_B @ (u1_struct_0 @ sk_A))
% 4.25/4.49          | (v2_struct_0 @ sk_B)
% 4.25/4.49          | (v2_struct_0 @ sk_A))),
% 4.25/4.49      inference('simplify', [status(thm)], ['57'])).
% 4.25/4.49  thf('59', plain,
% 4.25/4.49      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k6_subset_1 @ X0 @ X0))),
% 4.25/4.49      inference('condensation', [status(thm)], ['32'])).
% 4.25/4.49  thf('60', plain,
% 4.25/4.49      (((v2_struct_0 @ sk_A)
% 4.25/4.49        | (v2_struct_0 @ sk_B)
% 4.25/4.49        | (r1_waybel_0 @ sk_A @ sk_B @ (u1_struct_0 @ sk_A)))),
% 4.25/4.49      inference('sup-', [status(thm)], ['58', '59'])).
% 4.25/4.49  thf('61', plain, (~ (v2_struct_0 @ sk_A)),
% 4.25/4.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.49  thf('62', plain,
% 4.25/4.49      (((r1_waybel_0 @ sk_A @ sk_B @ (u1_struct_0 @ sk_A))
% 4.25/4.49        | (v2_struct_0 @ sk_B))),
% 4.25/4.49      inference('clc', [status(thm)], ['60', '61'])).
% 4.25/4.49  thf('63', plain, (~ (r1_waybel_0 @ sk_A @ sk_B @ (u1_struct_0 @ sk_A))),
% 4.25/4.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.49  thf('64', plain, ((v2_struct_0 @ sk_B)),
% 4.25/4.49      inference('clc', [status(thm)], ['62', '63'])).
% 4.25/4.49  thf('65', plain, ($false), inference('demod', [status(thm)], ['0', '64'])).
% 4.25/4.49  
% 4.25/4.49  % SZS output end Refutation
% 4.25/4.49  
% 4.25/4.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
