%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ziH4xoa32i

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:03 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 269 expanded)
%              Number of leaves         :   31 (  92 expanded)
%              Depth                    :   23
%              Number of atoms          :  894 (2932 expanded)
%              Number of equality atoms :   20 (  79 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_waybel_0_type,type,(
    r2_waybel_0: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k6_subset_1 @ X12 @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('2',plain,(
    ! [X2: $i] :
      ( ( k6_subset_1 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(demod,[status(thm)],['0','1'])).

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

thf('3',plain,(
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

thf('4',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( l1_waybel_0 @ X20 @ X21 )
      | ( r1_waybel_0 @ X21 @ X20 @ ( k6_subset_1 @ ( u1_struct_0 @ X21 ) @ X22 ) )
      | ( r2_waybel_0 @ X21 @ X20 @ X22 )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t10_waybel_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['2','7'])).

thf('9',plain,(
    ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
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

thf('17',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( l1_waybel_0 @ X14 @ X15 )
      | ( m1_subset_1 @ ( sk_D @ X16 @ X14 @ X15 ) @ ( u1_struct_0 @ X14 ) )
      | ( r2_waybel_0 @ X15 @ X14 @ X16 )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X14: $i,X15: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( l1_waybel_0 @ X14 @ X15 )
      | ~ ( r2_waybel_0 @ X15 @ X14 @ X18 )
      | ( r2_hidden @ ( k2_waybel_0 @ X15 @ X14 @ ( sk_E @ X19 @ X18 @ X14 @ X15 ) ) @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ sk_B_1 @ ( sk_E @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ X2 @ sk_B_1 @ X1 ) ) @ X2 )
      | ~ ( r2_waybel_0 @ X1 @ sk_B_1 @ X2 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ X1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_waybel_0 @ sk_B_1 @ X1 )
      | ~ ( r2_waybel_0 @ X1 @ sk_B_1 @ X2 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ sk_B_1 @ ( sk_E @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ X2 @ sk_B_1 @ X1 ) ) @ X2 )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ X1 @ sk_B_1 @ sk_A ) ) @ X1 )
      | ~ ( r2_waybel_0 @ sk_A @ sk_B_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','23'])).

thf('25',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ X1 @ sk_B_1 @ sk_A ) ) @ X1 )
      | ~ ( r2_waybel_0 @ sk_A @ sk_B_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_waybel_0 @ sk_A @ sk_B_1 @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ X1 @ sk_B_1 @ sk_A ) ) @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ k1_xboole_0 @ sk_B_1 @ sk_A ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','27'])).

thf('29',plain,(
    ! [X2: $i] :
      ( ( k6_subset_1 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('30',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_xboole_0 @ X5 @ X7 )
      | ( ( k4_xboole_0 @ X5 @ X7 )
       != X5 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('31',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k6_subset_1 @ X12 @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('32',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_xboole_0 @ X5 @ X7 )
      | ( ( k6_subset_1 @ X5 @ X7 )
       != X5 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( X0 != X0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('38',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k6_subset_1 @ X12 @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('39',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k6_subset_1 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_xboole_0 @ X5 @ X6 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('41',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( ( k4_xboole_0 @ X9 @ ( k1_tarski @ X8 ) )
       != X9 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('42',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k6_subset_1 @ X12 @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('43',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( ( k6_subset_1 @ X9 @ ( k1_tarski @ X8 ) )
       != X9 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['28','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['48','49'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('52',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ ( sk_B @ X11 ) @ X11 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf('53',plain,(
    ! [X14: $i,X15: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( l1_waybel_0 @ X14 @ X15 )
      | ~ ( r2_waybel_0 @ X15 @ X14 @ X18 )
      | ( m1_subset_1 @ ( sk_E @ X19 @ X18 @ X14 @ X15 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X2 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_waybel_0 @ X1 @ X0 @ X2 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X14: $i,X15: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( l1_waybel_0 @ X14 @ X15 )
      | ~ ( r2_waybel_0 @ X15 @ X14 @ X18 )
      | ( r2_hidden @ ( k2_waybel_0 @ X15 @ X14 @ ( sk_E @ X19 @ X18 @ X14 @ X15 ) ) @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ X2 @ sk_B_1 @ X1 ) ) @ X2 )
      | ~ ( r2_waybel_0 @ X1 @ sk_B_1 @ X2 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ X1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X1 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','64'])).

thf('66',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X1 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X1 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X1 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('74',plain,(
    $false ),
    inference('sup-',[status(thm)],['72','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ziH4xoa32i
% 0.13/0.36  % Computer   : n013.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 14:15:40 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.36/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.54  % Solved by: fo/fo7.sh
% 0.36/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.54  % done 102 iterations in 0.064s
% 0.36/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.54  % SZS output start Refutation
% 0.36/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.54  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.36/0.54  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.36/0.54  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.36/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.54  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.36/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.36/0.54  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 0.36/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.36/0.54  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.36/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.54  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.36/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.36/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.54  thf(r2_waybel_0_type, type, r2_waybel_0: $i > $i > $i > $o).
% 0.36/0.54  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.36/0.54  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.36/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.54  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.36/0.54  thf(t3_boole, axiom,
% 0.36/0.54    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.36/0.54  thf('0', plain, (![X2 : $i]: ((k4_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.36/0.54      inference('cnf', [status(esa)], [t3_boole])).
% 0.36/0.54  thf(redefinition_k6_subset_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.36/0.54  thf('1', plain,
% 0.36/0.54      (![X12 : $i, X13 : $i]:
% 0.36/0.54         ((k6_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))),
% 0.36/0.54      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.36/0.54  thf('2', plain, (![X2 : $i]: ((k6_subset_1 @ X2 @ k1_xboole_0) = (X2))),
% 0.36/0.54      inference('demod', [status(thm)], ['0', '1'])).
% 0.36/0.54  thf(t29_yellow_6, conjecture,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.36/0.54             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.36/0.54           ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.36/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.54    (~( ![A:$i]:
% 0.36/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.36/0.54          ( ![B:$i]:
% 0.36/0.54            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.36/0.54                ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.36/0.54              ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ) )),
% 0.36/0.54    inference('cnf.neg', [status(esa)], [t29_yellow_6])).
% 0.36/0.54  thf('3', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(t10_waybel_0, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.36/0.54           ( ![C:$i]:
% 0.36/0.54             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.36/0.54               ( ~( r1_waybel_0 @
% 0.36/0.54                    A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ))).
% 0.36/0.54  thf('4', plain,
% 0.36/0.54      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.36/0.54         ((v2_struct_0 @ X20)
% 0.36/0.54          | ~ (l1_waybel_0 @ X20 @ X21)
% 0.36/0.54          | (r1_waybel_0 @ X21 @ X20 @ 
% 0.36/0.54             (k6_subset_1 @ (u1_struct_0 @ X21) @ X22))
% 0.36/0.54          | (r2_waybel_0 @ X21 @ X20 @ X22)
% 0.36/0.54          | ~ (l1_struct_0 @ X21)
% 0.36/0.54          | (v2_struct_0 @ X21))),
% 0.36/0.54      inference('cnf', [status(esa)], [t10_waybel_0])).
% 0.36/0.54  thf('5', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((v2_struct_0 @ sk_A)
% 0.36/0.54          | ~ (l1_struct_0 @ sk_A)
% 0.36/0.54          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.36/0.54          | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.36/0.54             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.36/0.54          | (v2_struct_0 @ sk_B_1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.36/0.54  thf('6', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('7', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((v2_struct_0 @ sk_A)
% 0.36/0.54          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.36/0.54          | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.36/0.54             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.36/0.54          | (v2_struct_0 @ sk_B_1))),
% 0.36/0.54      inference('demod', [status(thm)], ['5', '6'])).
% 0.36/0.54  thf('8', plain,
% 0.36/0.54      (((r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.36/0.54        | (v2_struct_0 @ sk_B_1)
% 0.36/0.54        | (r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0)
% 0.36/0.54        | (v2_struct_0 @ sk_A))),
% 0.36/0.54      inference('sup+', [status(thm)], ['2', '7'])).
% 0.36/0.54  thf('9', plain, (~ (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('10', plain,
% 0.36/0.54      (((v2_struct_0 @ sk_A)
% 0.36/0.54        | (r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0)
% 0.36/0.54        | (v2_struct_0 @ sk_B_1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.36/0.54  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('12', plain,
% 0.36/0.54      (((v2_struct_0 @ sk_B_1) | (r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0))),
% 0.36/0.54      inference('clc', [status(thm)], ['10', '11'])).
% 0.36/0.54  thf('13', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('14', plain, ((r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0)),
% 0.36/0.54      inference('clc', [status(thm)], ['12', '13'])).
% 0.36/0.54  thf('15', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('16', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(d12_waybel_0, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.36/0.54           ( ![C:$i]:
% 0.36/0.54             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.36/0.54               ( ![D:$i]:
% 0.36/0.54                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.36/0.54                   ( ?[E:$i]:
% 0.36/0.54                     ( ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) & 
% 0.36/0.54                       ( r1_orders_2 @ B @ D @ E ) & 
% 0.36/0.54                       ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.54  thf('17', plain,
% 0.36/0.54      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.36/0.54         ((v2_struct_0 @ X14)
% 0.36/0.54          | ~ (l1_waybel_0 @ X14 @ X15)
% 0.36/0.54          | (m1_subset_1 @ (sk_D @ X16 @ X14 @ X15) @ (u1_struct_0 @ X14))
% 0.36/0.54          | (r2_waybel_0 @ X15 @ X14 @ X16)
% 0.36/0.54          | ~ (l1_struct_0 @ X15)
% 0.36/0.54          | (v2_struct_0 @ X15))),
% 0.36/0.54      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.36/0.54  thf('18', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((v2_struct_0 @ sk_A)
% 0.36/0.54          | ~ (l1_struct_0 @ sk_A)
% 0.36/0.54          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.36/0.54          | (m1_subset_1 @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_B_1))
% 0.36/0.54          | (v2_struct_0 @ sk_B_1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.54  thf('19', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('20', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((v2_struct_0 @ sk_A)
% 0.36/0.54          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.36/0.54          | (m1_subset_1 @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_B_1))
% 0.36/0.54          | (v2_struct_0 @ sk_B_1))),
% 0.36/0.54      inference('demod', [status(thm)], ['18', '19'])).
% 0.36/0.54  thf('21', plain,
% 0.36/0.54      (![X14 : $i, X15 : $i, X18 : $i, X19 : $i]:
% 0.36/0.54         ((v2_struct_0 @ X14)
% 0.36/0.54          | ~ (l1_waybel_0 @ X14 @ X15)
% 0.36/0.54          | ~ (r2_waybel_0 @ X15 @ X14 @ X18)
% 0.36/0.54          | (r2_hidden @ 
% 0.36/0.54             (k2_waybel_0 @ X15 @ X14 @ (sk_E @ X19 @ X18 @ X14 @ X15)) @ X18)
% 0.36/0.54          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X14))
% 0.36/0.54          | ~ (l1_struct_0 @ X15)
% 0.36/0.54          | (v2_struct_0 @ X15))),
% 0.36/0.54      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.36/0.54  thf('22', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.54         ((v2_struct_0 @ sk_B_1)
% 0.36/0.54          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.36/0.54          | (v2_struct_0 @ sk_A)
% 0.36/0.54          | (v2_struct_0 @ X1)
% 0.36/0.54          | ~ (l1_struct_0 @ X1)
% 0.36/0.54          | (r2_hidden @ 
% 0.36/0.54             (k2_waybel_0 @ X1 @ sk_B_1 @ 
% 0.36/0.54              (sk_E @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ X2 @ sk_B_1 @ X1)) @ 
% 0.36/0.54             X2)
% 0.36/0.54          | ~ (r2_waybel_0 @ X1 @ sk_B_1 @ X2)
% 0.36/0.54          | ~ (l1_waybel_0 @ sk_B_1 @ X1)
% 0.36/0.54          | (v2_struct_0 @ sk_B_1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.36/0.54  thf('23', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.54         (~ (l1_waybel_0 @ sk_B_1 @ X1)
% 0.36/0.54          | ~ (r2_waybel_0 @ X1 @ sk_B_1 @ X2)
% 0.36/0.54          | (r2_hidden @ 
% 0.36/0.54             (k2_waybel_0 @ X1 @ sk_B_1 @ 
% 0.36/0.54              (sk_E @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ X2 @ sk_B_1 @ X1)) @ 
% 0.36/0.54             X2)
% 0.36/0.54          | ~ (l1_struct_0 @ X1)
% 0.36/0.54          | (v2_struct_0 @ X1)
% 0.36/0.54          | (v2_struct_0 @ sk_A)
% 0.36/0.54          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.36/0.54          | (v2_struct_0 @ sk_B_1))),
% 0.36/0.54      inference('simplify', [status(thm)], ['22'])).
% 0.36/0.54  thf('24', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((v2_struct_0 @ sk_B_1)
% 0.36/0.54          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.36/0.54          | (v2_struct_0 @ sk_A)
% 0.36/0.54          | (v2_struct_0 @ sk_A)
% 0.36/0.54          | ~ (l1_struct_0 @ sk_A)
% 0.36/0.54          | (r2_hidden @ 
% 0.36/0.54             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.36/0.54              (sk_E @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ X1 @ sk_B_1 @ sk_A)) @ 
% 0.36/0.54             X1)
% 0.36/0.54          | ~ (r2_waybel_0 @ sk_A @ sk_B_1 @ X1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['15', '23'])).
% 0.36/0.54  thf('25', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('26', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((v2_struct_0 @ sk_B_1)
% 0.36/0.54          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.36/0.54          | (v2_struct_0 @ sk_A)
% 0.36/0.54          | (v2_struct_0 @ sk_A)
% 0.36/0.54          | (r2_hidden @ 
% 0.36/0.54             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.36/0.54              (sk_E @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ X1 @ sk_B_1 @ sk_A)) @ 
% 0.36/0.54             X1)
% 0.36/0.54          | ~ (r2_waybel_0 @ sk_A @ sk_B_1 @ X1))),
% 0.36/0.54      inference('demod', [status(thm)], ['24', '25'])).
% 0.36/0.54  thf('27', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         (~ (r2_waybel_0 @ sk_A @ sk_B_1 @ X1)
% 0.36/0.54          | (r2_hidden @ 
% 0.36/0.54             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.36/0.54              (sk_E @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ X1 @ sk_B_1 @ sk_A)) @ 
% 0.36/0.54             X1)
% 0.36/0.54          | (v2_struct_0 @ sk_A)
% 0.36/0.54          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.36/0.54          | (v2_struct_0 @ sk_B_1))),
% 0.36/0.54      inference('simplify', [status(thm)], ['26'])).
% 0.36/0.54  thf('28', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((v2_struct_0 @ sk_B_1)
% 0.36/0.54          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.36/0.54          | (v2_struct_0 @ sk_A)
% 0.36/0.54          | (r2_hidden @ 
% 0.36/0.54             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.36/0.54              (sk_E @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ k1_xboole_0 @ sk_B_1 @ sk_A)) @ 
% 0.36/0.54             k1_xboole_0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['14', '27'])).
% 0.36/0.54  thf('29', plain, (![X2 : $i]: ((k6_subset_1 @ X2 @ k1_xboole_0) = (X2))),
% 0.36/0.54      inference('demod', [status(thm)], ['0', '1'])).
% 0.36/0.54  thf(t83_xboole_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.36/0.54  thf('30', plain,
% 0.36/0.54      (![X5 : $i, X7 : $i]:
% 0.36/0.54         ((r1_xboole_0 @ X5 @ X7) | ((k4_xboole_0 @ X5 @ X7) != (X5)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.36/0.54  thf('31', plain,
% 0.36/0.54      (![X12 : $i, X13 : $i]:
% 0.36/0.54         ((k6_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))),
% 0.36/0.54      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.36/0.54  thf('32', plain,
% 0.36/0.54      (![X5 : $i, X7 : $i]:
% 0.36/0.54         ((r1_xboole_0 @ X5 @ X7) | ((k6_subset_1 @ X5 @ X7) != (X5)))),
% 0.36/0.54      inference('demod', [status(thm)], ['30', '31'])).
% 0.36/0.54  thf('33', plain,
% 0.36/0.54      (![X0 : $i]: (((X0) != (X0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['29', '32'])).
% 0.36/0.54  thf('34', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.36/0.54      inference('simplify', [status(thm)], ['33'])).
% 0.36/0.54  thf(symmetry_r1_xboole_0, axiom,
% 0.36/0.54    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.36/0.54  thf('35', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.36/0.54      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.36/0.54  thf('36', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.36/0.54      inference('sup-', [status(thm)], ['34', '35'])).
% 0.36/0.54  thf('37', plain,
% 0.36/0.54      (![X5 : $i, X6 : $i]:
% 0.36/0.54         (((k4_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_xboole_0 @ X5 @ X6))),
% 0.36/0.54      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.36/0.54  thf('38', plain,
% 0.36/0.54      (![X12 : $i, X13 : $i]:
% 0.36/0.54         ((k6_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))),
% 0.36/0.54      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.36/0.54  thf('39', plain,
% 0.36/0.54      (![X5 : $i, X6 : $i]:
% 0.36/0.54         (((k6_subset_1 @ X5 @ X6) = (X5)) | ~ (r1_xboole_0 @ X5 @ X6))),
% 0.36/0.54      inference('demod', [status(thm)], ['37', '38'])).
% 0.36/0.54  thf('40', plain,
% 0.36/0.54      (![X0 : $i]: ((k6_subset_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['36', '39'])).
% 0.36/0.54  thf(t65_zfmisc_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.36/0.54       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.36/0.54  thf('41', plain,
% 0.36/0.54      (![X8 : $i, X9 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X8 @ X9)
% 0.36/0.54          | ((k4_xboole_0 @ X9 @ (k1_tarski @ X8)) != (X9)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.36/0.54  thf('42', plain,
% 0.36/0.54      (![X12 : $i, X13 : $i]:
% 0.36/0.54         ((k6_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))),
% 0.36/0.54      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.36/0.54  thf('43', plain,
% 0.36/0.54      (![X8 : $i, X9 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X8 @ X9)
% 0.36/0.54          | ((k6_subset_1 @ X9 @ (k1_tarski @ X8)) != (X9)))),
% 0.36/0.54      inference('demod', [status(thm)], ['41', '42'])).
% 0.36/0.54  thf('44', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['40', '43'])).
% 0.36/0.54  thf('45', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.36/0.54      inference('simplify', [status(thm)], ['44'])).
% 0.36/0.54  thf('46', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((v2_struct_0 @ sk_A)
% 0.36/0.54          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.36/0.54          | (v2_struct_0 @ sk_B_1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['28', '45'])).
% 0.36/0.54  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('48', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((v2_struct_0 @ sk_B_1) | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0))),
% 0.36/0.54      inference('clc', [status(thm)], ['46', '47'])).
% 0.36/0.54  thf('49', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('50', plain, (![X0 : $i]: (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)),
% 0.36/0.54      inference('clc', [status(thm)], ['48', '49'])).
% 0.36/0.54  thf('51', plain, (![X0 : $i]: (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)),
% 0.36/0.54      inference('clc', [status(thm)], ['48', '49'])).
% 0.36/0.54  thf(existence_m1_subset_1, axiom,
% 0.36/0.54    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.36/0.54  thf('52', plain, (![X11 : $i]: (m1_subset_1 @ (sk_B @ X11) @ X11)),
% 0.36/0.54      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.36/0.54  thf('53', plain,
% 0.36/0.54      (![X14 : $i, X15 : $i, X18 : $i, X19 : $i]:
% 0.36/0.54         ((v2_struct_0 @ X14)
% 0.36/0.54          | ~ (l1_waybel_0 @ X14 @ X15)
% 0.36/0.54          | ~ (r2_waybel_0 @ X15 @ X14 @ X18)
% 0.36/0.54          | (m1_subset_1 @ (sk_E @ X19 @ X18 @ X14 @ X15) @ (u1_struct_0 @ X14))
% 0.36/0.54          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X14))
% 0.36/0.54          | ~ (l1_struct_0 @ X15)
% 0.36/0.54          | (v2_struct_0 @ X15))),
% 0.36/0.54      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.36/0.54  thf('54', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.54         ((v2_struct_0 @ X1)
% 0.36/0.54          | ~ (l1_struct_0 @ X1)
% 0.36/0.54          | (m1_subset_1 @ 
% 0.36/0.54             (sk_E @ (sk_B @ (u1_struct_0 @ X0)) @ X2 @ X0 @ X1) @ 
% 0.36/0.54             (u1_struct_0 @ X0))
% 0.36/0.54          | ~ (r2_waybel_0 @ X1 @ X0 @ X2)
% 0.36/0.54          | ~ (l1_waybel_0 @ X0 @ X1)
% 0.36/0.54          | (v2_struct_0 @ X0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['52', '53'])).
% 0.36/0.54  thf('55', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((v2_struct_0 @ sk_B_1)
% 0.36/0.54          | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.36/0.54          | (m1_subset_1 @ 
% 0.36/0.54             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.36/0.54             (u1_struct_0 @ sk_B_1))
% 0.36/0.54          | ~ (l1_struct_0 @ sk_A)
% 0.36/0.54          | (v2_struct_0 @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['51', '54'])).
% 0.36/0.54  thf('56', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('57', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('58', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((v2_struct_0 @ sk_B_1)
% 0.36/0.54          | (m1_subset_1 @ 
% 0.36/0.54             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.36/0.54             (u1_struct_0 @ sk_B_1))
% 0.36/0.54          | (v2_struct_0 @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.36/0.54  thf('59', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('60', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((v2_struct_0 @ sk_A)
% 0.36/0.54          | (m1_subset_1 @ 
% 0.36/0.54             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.36/0.54             (u1_struct_0 @ sk_B_1)))),
% 0.36/0.54      inference('clc', [status(thm)], ['58', '59'])).
% 0.36/0.54  thf('61', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('62', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (m1_subset_1 @ 
% 0.36/0.54          (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.36/0.54          (u1_struct_0 @ sk_B_1))),
% 0.36/0.54      inference('clc', [status(thm)], ['60', '61'])).
% 0.36/0.54  thf('63', plain,
% 0.36/0.54      (![X14 : $i, X15 : $i, X18 : $i, X19 : $i]:
% 0.36/0.54         ((v2_struct_0 @ X14)
% 0.36/0.54          | ~ (l1_waybel_0 @ X14 @ X15)
% 0.36/0.54          | ~ (r2_waybel_0 @ X15 @ X14 @ X18)
% 0.36/0.54          | (r2_hidden @ 
% 0.36/0.54             (k2_waybel_0 @ X15 @ X14 @ (sk_E @ X19 @ X18 @ X14 @ X15)) @ X18)
% 0.36/0.54          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X14))
% 0.36/0.54          | ~ (l1_struct_0 @ X15)
% 0.36/0.54          | (v2_struct_0 @ X15))),
% 0.36/0.54      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.36/0.54  thf('64', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.54         ((v2_struct_0 @ X1)
% 0.36/0.54          | ~ (l1_struct_0 @ X1)
% 0.36/0.54          | (r2_hidden @ 
% 0.36/0.54             (k2_waybel_0 @ X1 @ sk_B_1 @ 
% 0.36/0.54              (sk_E @ 
% 0.36/0.54               (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.36/0.54               X2 @ sk_B_1 @ X1)) @ 
% 0.36/0.54             X2)
% 0.36/0.54          | ~ (r2_waybel_0 @ X1 @ sk_B_1 @ X2)
% 0.36/0.54          | ~ (l1_waybel_0 @ sk_B_1 @ X1)
% 0.36/0.54          | (v2_struct_0 @ sk_B_1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['62', '63'])).
% 0.36/0.54  thf('65', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((v2_struct_0 @ sk_B_1)
% 0.36/0.54          | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.36/0.54          | (r2_hidden @ 
% 0.36/0.54             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.36/0.54              (sk_E @ 
% 0.36/0.54               (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X1 @ sk_B_1 @ sk_A) @ 
% 0.36/0.54               X0 @ sk_B_1 @ sk_A)) @ 
% 0.36/0.54             X0)
% 0.36/0.54          | ~ (l1_struct_0 @ sk_A)
% 0.36/0.54          | (v2_struct_0 @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['50', '64'])).
% 0.36/0.54  thf('66', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('67', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('68', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((v2_struct_0 @ sk_B_1)
% 0.36/0.54          | (r2_hidden @ 
% 0.36/0.54             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.36/0.54              (sk_E @ 
% 0.36/0.54               (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X1 @ sk_B_1 @ sk_A) @ 
% 0.36/0.54               X0 @ sk_B_1 @ sk_A)) @ 
% 0.36/0.54             X0)
% 0.36/0.54          | (v2_struct_0 @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.36/0.54  thf('69', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('70', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((v2_struct_0 @ sk_A)
% 0.36/0.54          | (r2_hidden @ 
% 0.36/0.54             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.36/0.54              (sk_E @ 
% 0.36/0.54               (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X1 @ sk_B_1 @ sk_A) @ 
% 0.36/0.54               X0 @ sk_B_1 @ sk_A)) @ 
% 0.36/0.54             X0))),
% 0.36/0.54      inference('clc', [status(thm)], ['68', '69'])).
% 0.36/0.54  thf('71', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('72', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         (r2_hidden @ 
% 0.36/0.54          (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.36/0.54           (sk_E @ 
% 0.36/0.54            (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X1 @ sk_B_1 @ sk_A) @ 
% 0.36/0.54            X0 @ sk_B_1 @ sk_A)) @ 
% 0.36/0.54          X0)),
% 0.36/0.54      inference('clc', [status(thm)], ['70', '71'])).
% 0.36/0.54  thf('73', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.36/0.54      inference('simplify', [status(thm)], ['44'])).
% 0.36/0.54  thf('74', plain, ($false), inference('sup-', [status(thm)], ['72', '73'])).
% 0.36/0.54  
% 0.36/0.54  % SZS output end Refutation
% 0.36/0.54  
% 0.38/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
