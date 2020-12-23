%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xnZgluBSjd

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 278 expanded)
%              Number of leaves         :   33 (  97 expanded)
%              Depth                    :   15
%              Number of atoms          : 1078 (3923 expanded)
%              Number of equality atoms :   16 ( 124 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(a_2_2_lattice3_type,type,(
    a_2_2_lattice3: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(r4_lattice3_type,type,(
    r4_lattice3: $i > $i > $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(t41_lattice3,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v4_lattice3 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ( r2_hidden @ B @ C )
                & ( r4_lattice3 @ A @ B @ C ) )
             => ( ( k15_lattice3 @ A @ C )
                = B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v4_lattice3 @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( ( r2_hidden @ B @ C )
                  & ( r4_lattice3 @ A @ B @ C ) )
               => ( ( k15_lattice3 @ A @ C )
                  = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t41_lattice3])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t37_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v4_lattice3 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( k15_lattice3 @ A @ B )
          = ( k16_lattice3 @ A @ ( a_2_2_lattice3 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k15_lattice3 @ X14 @ X15 )
        = ( k16_lattice3 @ X14 @ ( a_2_2_lattice3 @ X14 @ X15 ) ) )
      | ~ ( l3_lattices @ X14 )
      | ~ ( v4_lattice3 @ X14 )
      | ~ ( v10_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t37_lattice3])).

thf('2',plain,(
    r4_lattice3 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fraenkel_a_2_2_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( v10_lattices @ B )
        & ( v4_lattice3 @ B )
        & ( l3_lattices @ B ) )
     => ( ( r2_hidden @ A @ ( a_2_2_lattice3 @ B @ C ) )
      <=> ? [D: $i] :
            ( ( r4_lattice3 @ B @ D @ C )
            & ( A = D )
            & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( l3_lattices @ X10 )
      | ~ ( v4_lattice3 @ X10 )
      | ~ ( v10_lattices @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( r2_hidden @ X12 @ ( a_2_2_lattice3 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X10 ) )
      | ( X12 != X13 )
      | ~ ( r4_lattice3 @ X10 @ X13 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_2_lattice3])).

thf('5',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ~ ( r4_lattice3 @ X10 @ X13 @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X10 ) )
      | ( r2_hidden @ X13 @ ( a_2_2_lattice3 @ X10 @ X11 ) )
      | ( v2_struct_0 @ X10 )
      | ~ ( v10_lattices @ X10 )
      | ~ ( v4_lattice3 @ X10 )
      | ~ ( l3_lattices @ X10 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_B @ ( a_2_2_lattice3 @ sk_A @ X0 ) )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_B @ ( a_2_2_lattice3 @ sk_A @ X0 ) )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ ( a_2_2_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    r2_hidden @ sk_B @ ( a_2_2_lattice3 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['2','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v4_lattice3 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( r2_hidden @ B @ C )
             => ( ( r3_lattices @ A @ B @ ( k15_lattice3 @ A @ C ) )
                & ( r3_lattices @ A @ ( k16_lattice3 @ A @ C ) @ B ) ) ) ) ) )).

thf('15',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ( r3_lattices @ X17 @ ( k16_lattice3 @ X17 @ X18 ) @ X16 )
      | ~ ( r2_hidden @ X16 @ X18 )
      | ~ ( l3_lattices @ X17 )
      | ~ ( v4_lattice3 @ X17 )
      | ~ ( v10_lattices @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t38_lattice3])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17','18','19'])).

thf('21',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ sk_C ) ) @ sk_B ),
    inference('sup-',[status(thm)],['13','22'])).

thf('24',plain,
    ( ( r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_C ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup+',[status(thm)],['1','23'])).

thf('25',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_C ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','26','27'])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_C ) @ sk_B ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k15_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('32',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l3_lattices @ X8 )
      | ( v2_struct_0 @ X8 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X8 @ X9 ) @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf(redefinition_r3_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v6_lattices @ A )
        & ( v8_lattices @ A )
        & ( v9_lattices @ A )
        & ( l3_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_lattices @ A @ B @ C )
      <=> ( r1_lattices @ A @ B @ C ) ) ) )).

thf('33',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X3 ) )
      | ~ ( l3_lattices @ X3 )
      | ~ ( v9_lattices @ X3 )
      | ~ ( v8_lattices @ X3 )
      | ~ ( v6_lattices @ X3 )
      | ( v2_struct_0 @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ( r1_lattices @ X3 @ X2 @ X4 )
      | ~ ( r3_lattices @ X3 @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','35'])).

thf('37',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A ) )
       => ( ~ ( v2_struct_0 @ A )
          & ( v4_lattices @ A )
          & ( v5_lattices @ A )
          & ( v6_lattices @ A )
          & ( v7_lattices @ A )
          & ( v8_lattices @ A )
          & ( v9_lattices @ A ) ) ) ) )).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','37','43','49','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ~ ( r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['30','58'])).

thf('60',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l3_lattices @ X8 )
      | ( v2_struct_0 @ X8 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X8 @ X9 ) @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('61',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v4_lattices @ A )
        & ( l2_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( r1_lattices @ A @ B @ C )
                  & ( r1_lattices @ A @ C @ B ) )
               => ( B = C ) ) ) ) ) )).

thf('62',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ~ ( r1_lattices @ X6 @ X5 @ X7 )
      | ~ ( r1_lattices @ X6 @ X7 @ X5 )
      | ( X5 = X7 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l2_lattices @ X6 )
      | ~ ( v4_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t26_lattices])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B = X0 )
      | ~ ( r1_lattices @ sk_A @ X0 @ sk_B )
      | ~ ( r1_lattices @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v4_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v4_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('71',plain,(
    ! [X1: $i] :
      ( ( l2_lattices @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('72',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B = X0 )
      | ~ ( r1_lattices @ sk_A @ X0 @ sk_B )
      | ~ ( r1_lattices @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['63','69','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r1_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) )
      | ~ ( r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','73'])).

thf('75',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r1_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) )
      | ~ ( r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k15_lattice3 @ sk_A @ X0 ) )
      | ~ ( r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ~ ( r1_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( r1_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) )
    | ( sk_B
      = ( k15_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['59','77'])).

thf('79',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l3_lattices @ X8 )
      | ( v2_struct_0 @ X8 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X8 @ X9 ) @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('80',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ( r3_lattices @ X17 @ X16 @ ( k15_lattice3 @ X17 @ X18 ) )
      | ~ ( r2_hidden @ X16 @ X18 )
      | ~ ( l3_lattices @ X17 )
      | ~ ( v4_lattice3 @ X17 )
      | ~ ( v10_lattices @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t38_lattice3])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['83','84','85','86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,(
    r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['80','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X3 ) )
      | ~ ( l3_lattices @ X3 )
      | ~ ( v9_lattices @ X3 )
      | ~ ( v8_lattices @ X3 )
      | ~ ( v6_lattices @ X3 )
      | ( v2_struct_0 @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ( r1_lattices @ X3 @ X2 @ X4 )
      | ~ ( r3_lattices @ X3 @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattices @ sk_A @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('95',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('96',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('97',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattices @ sk_A @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['93','94','95','96','97'])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k15_lattice3 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['90','98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( r1_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) )
    | ~ ( m1_subset_1 @ ( k15_lattice3 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( r1_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['79','101'])).

thf('103',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    r1_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k15_lattice3 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['78','106'])).

thf('108',plain,(
    ( k15_lattice3 @ sk_A @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['107','108'])).

thf('110',plain,(
    $false ),
    inference(demod,[status(thm)],['0','109'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xnZgluBSjd
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:40:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 67 iterations in 0.040s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.21/0.50  thf(a_2_2_lattice3_type, type, a_2_2_lattice3: $i > $i > $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.21/0.50  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.50  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.21/0.50  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.21/0.50  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.50  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 0.21/0.50  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 0.21/0.50  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.21/0.50  thf(r4_lattice3_type, type, r4_lattice3: $i > $i > $i > $o).
% 0.21/0.50  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.21/0.50  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 0.21/0.50  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.21/0.50  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 0.21/0.50  thf(t41_lattice3, conjecture,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.50         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( ( r2_hidden @ B @ C ) & ( r4_lattice3 @ A @ B @ C ) ) =>
% 0.21/0.50               ( ( k15_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]:
% 0.21/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.50            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.50          ( ![B:$i]:
% 0.21/0.50            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.50              ( ![C:$i]:
% 0.21/0.50                ( ( ( r2_hidden @ B @ C ) & ( r4_lattice3 @ A @ B @ C ) ) =>
% 0.21/0.50                  ( ( k15_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t41_lattice3])).
% 0.21/0.50  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t37_lattice3, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.50         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( k15_lattice3 @ A @ B ) =
% 0.21/0.50           ( k16_lattice3 @ A @ ( a_2_2_lattice3 @ A @ B ) ) ) ) ))).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (![X14 : $i, X15 : $i]:
% 0.21/0.50         (((k15_lattice3 @ X14 @ X15)
% 0.21/0.50            = (k16_lattice3 @ X14 @ (a_2_2_lattice3 @ X14 @ X15)))
% 0.21/0.50          | ~ (l3_lattices @ X14)
% 0.21/0.50          | ~ (v4_lattice3 @ X14)
% 0.21/0.50          | ~ (v10_lattices @ X14)
% 0.21/0.50          | (v2_struct_0 @ X14))),
% 0.21/0.50      inference('cnf', [status(esa)], [t37_lattice3])).
% 0.21/0.50  thf('2', plain, ((r4_lattice3 @ sk_A @ sk_B @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('3', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(fraenkel_a_2_2_lattice3, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ B ) ) & ( v10_lattices @ B ) & 
% 0.21/0.50         ( v4_lattice3 @ B ) & ( l3_lattices @ B ) ) =>
% 0.21/0.50       ( ( r2_hidden @ A @ ( a_2_2_lattice3 @ B @ C ) ) <=>
% 0.21/0.50         ( ?[D:$i]:
% 0.21/0.50           ( ( r4_lattice3 @ B @ D @ C ) & ( ( A ) = ( D ) ) & 
% 0.21/0.50             ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.50         (~ (l3_lattices @ X10)
% 0.21/0.50          | ~ (v4_lattice3 @ X10)
% 0.21/0.50          | ~ (v10_lattices @ X10)
% 0.21/0.50          | (v2_struct_0 @ X10)
% 0.21/0.50          | (r2_hidden @ X12 @ (a_2_2_lattice3 @ X10 @ X11))
% 0.21/0.50          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X10))
% 0.21/0.50          | ((X12) != (X13))
% 0.21/0.50          | ~ (r4_lattice3 @ X10 @ X13 @ X11))),
% 0.21/0.50      inference('cnf', [status(esa)], [fraenkel_a_2_2_lattice3])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.21/0.50         (~ (r4_lattice3 @ X10 @ X13 @ X11)
% 0.21/0.50          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X10))
% 0.21/0.50          | (r2_hidden @ X13 @ (a_2_2_lattice3 @ X10 @ X11))
% 0.21/0.50          | (v2_struct_0 @ X10)
% 0.21/0.50          | ~ (v10_lattices @ X10)
% 0.21/0.50          | ~ (v4_lattice3 @ X10)
% 0.21/0.50          | ~ (l3_lattices @ X10))),
% 0.21/0.50      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (l3_lattices @ sk_A)
% 0.21/0.50          | ~ (v4_lattice3 @ sk_A)
% 0.21/0.50          | ~ (v10_lattices @ sk_A)
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | (r2_hidden @ sk_B @ (a_2_2_lattice3 @ sk_A @ X0))
% 0.21/0.50          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['3', '5'])).
% 0.21/0.50  thf('7', plain, ((l3_lattices @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('8', plain, ((v4_lattice3 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('9', plain, ((v10_lattices @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_A)
% 0.21/0.50          | (r2_hidden @ sk_B @ (a_2_2_lattice3 @ sk_A @ X0))
% 0.21/0.50          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.21/0.50  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.21/0.50          | (r2_hidden @ sk_B @ (a_2_2_lattice3 @ sk_A @ X0)))),
% 0.21/0.50      inference('clc', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('13', plain, ((r2_hidden @ sk_B @ (a_2_2_lattice3 @ sk_A @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['2', '12'])).
% 0.21/0.50  thf('14', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t38_lattice3, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.50         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( r2_hidden @ B @ C ) =>
% 0.21/0.50               ( ( r3_lattices @ A @ B @ ( k15_lattice3 @ A @ C ) ) & 
% 0.21/0.50                 ( r3_lattices @ A @ ( k16_lattice3 @ A @ C ) @ B ) ) ) ) ) ) ))).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.21/0.50          | (r3_lattices @ X17 @ (k16_lattice3 @ X17 @ X18) @ X16)
% 0.21/0.50          | ~ (r2_hidden @ X16 @ X18)
% 0.21/0.50          | ~ (l3_lattices @ X17)
% 0.21/0.50          | ~ (v4_lattice3 @ X17)
% 0.21/0.50          | ~ (v10_lattices @ X17)
% 0.21/0.50          | (v2_struct_0 @ X17))),
% 0.21/0.50      inference('cnf', [status(esa)], [t38_lattice3])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_A)
% 0.21/0.50          | ~ (v10_lattices @ sk_A)
% 0.21/0.50          | ~ (v4_lattice3 @ sk_A)
% 0.21/0.50          | ~ (l3_lattices @ sk_A)
% 0.21/0.50          | ~ (r2_hidden @ sk_B @ X0)
% 0.21/0.50          | (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.50  thf('17', plain, ((v10_lattices @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('18', plain, ((v4_lattice3 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('19', plain, ((l3_lattices @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_A)
% 0.21/0.50          | ~ (r2_hidden @ sk_B @ X0)
% 0.21/0.50          | (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['16', '17', '18', '19'])).
% 0.21/0.50  thf('21', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.21/0.50          | ~ (r2_hidden @ sk_B @ X0))),
% 0.21/0.50      inference('clc', [status(thm)], ['20', '21'])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      ((r3_lattices @ sk_A @ 
% 0.21/0.50        (k16_lattice3 @ sk_A @ (a_2_2_lattice3 @ sk_A @ sk_C)) @ sk_B)),
% 0.21/0.50      inference('sup-', [status(thm)], ['13', '22'])).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      (((r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_C) @ sk_B)
% 0.21/0.50        | (v2_struct_0 @ sk_A)
% 0.21/0.50        | ~ (v10_lattices @ sk_A)
% 0.21/0.50        | ~ (v4_lattice3 @ sk_A)
% 0.21/0.50        | ~ (l3_lattices @ sk_A))),
% 0.21/0.50      inference('sup+', [status(thm)], ['1', '23'])).
% 0.21/0.50  thf('25', plain, ((v10_lattices @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('26', plain, ((v4_lattice3 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('27', plain, ((l3_lattices @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      (((r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_C) @ sk_B)
% 0.21/0.50        | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 0.21/0.50  thf('29', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      ((r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_C) @ sk_B)),
% 0.21/0.50      inference('clc', [status(thm)], ['28', '29'])).
% 0.21/0.50  thf('31', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(dt_k15_lattice3, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.21/0.50       ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      (![X8 : $i, X9 : $i]:
% 0.21/0.50         (~ (l3_lattices @ X8)
% 0.21/0.50          | (v2_struct_0 @ X8)
% 0.21/0.50          | (m1_subset_1 @ (k15_lattice3 @ X8 @ X9) @ (u1_struct_0 @ X8)))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.21/0.50  thf(redefinition_r3_lattices, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.21/0.50         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 0.21/0.50         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.50         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X3))
% 0.21/0.50          | ~ (l3_lattices @ X3)
% 0.21/0.50          | ~ (v9_lattices @ X3)
% 0.21/0.50          | ~ (v8_lattices @ X3)
% 0.21/0.50          | ~ (v6_lattices @ X3)
% 0.21/0.50          | (v2_struct_0 @ X3)
% 0.21/0.50          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 0.21/0.50          | (r1_lattices @ X3 @ X2 @ X4)
% 0.21/0.50          | ~ (r3_lattices @ X3 @ X2 @ X4))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X0)
% 0.21/0.50          | ~ (l3_lattices @ X0)
% 0.21/0.50          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.21/0.50          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.21/0.50          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.50          | (v2_struct_0 @ X0)
% 0.21/0.50          | ~ (v6_lattices @ X0)
% 0.21/0.50          | ~ (v8_lattices @ X0)
% 0.21/0.50          | ~ (v9_lattices @ X0)
% 0.21/0.50          | ~ (l3_lattices @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (v9_lattices @ X0)
% 0.21/0.50          | ~ (v8_lattices @ X0)
% 0.21/0.50          | ~ (v6_lattices @ X0)
% 0.21/0.50          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.50          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.21/0.50          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.21/0.50          | ~ (l3_lattices @ X0)
% 0.21/0.50          | (v2_struct_0 @ X0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['34'])).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_A)
% 0.21/0.50          | ~ (l3_lattices @ sk_A)
% 0.21/0.50          | ~ (r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B)
% 0.21/0.50          | (r1_lattices @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B)
% 0.21/0.50          | ~ (v6_lattices @ sk_A)
% 0.21/0.50          | ~ (v8_lattices @ sk_A)
% 0.21/0.50          | ~ (v9_lattices @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['31', '35'])).
% 0.21/0.50  thf('37', plain, ((l3_lattices @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(cc1_lattices, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l3_lattices @ A ) =>
% 0.21/0.50       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.21/0.50         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.21/0.50           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.21/0.50           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X0)
% 0.21/0.50          | ~ (v10_lattices @ X0)
% 0.21/0.50          | (v6_lattices @ X0)
% 0.21/0.50          | ~ (l3_lattices @ X0))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.50  thf('39', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('40', plain,
% 0.21/0.50      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.50  thf('41', plain, ((l3_lattices @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('42', plain, ((v10_lattices @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('43', plain, ((v6_lattices @ sk_A)),
% 0.21/0.50      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.21/0.50  thf('44', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X0)
% 0.21/0.50          | ~ (v10_lattices @ X0)
% 0.21/0.50          | (v8_lattices @ X0)
% 0.21/0.50          | ~ (l3_lattices @ X0))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.50  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('46', plain,
% 0.21/0.50      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.50  thf('47', plain, ((l3_lattices @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('48', plain, ((v10_lattices @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('49', plain, ((v8_lattices @ sk_A)),
% 0.21/0.50      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.21/0.50  thf('50', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X0)
% 0.21/0.50          | ~ (v10_lattices @ X0)
% 0.21/0.50          | (v9_lattices @ X0)
% 0.21/0.50          | ~ (l3_lattices @ X0))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.50  thf('51', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('52', plain,
% 0.21/0.50      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.50  thf('53', plain, ((l3_lattices @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('54', plain, ((v10_lattices @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('55', plain, ((v9_lattices @ sk_A)),
% 0.21/0.50      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.21/0.50  thf('56', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_A)
% 0.21/0.50          | ~ (r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B)
% 0.21/0.50          | (r1_lattices @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['36', '37', '43', '49', '55'])).
% 0.21/0.50  thf('57', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('58', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r1_lattices @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B)
% 0.21/0.50          | ~ (r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B))),
% 0.21/0.50      inference('clc', [status(thm)], ['56', '57'])).
% 0.21/0.50  thf('59', plain,
% 0.21/0.50      ((r1_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_C) @ sk_B)),
% 0.21/0.50      inference('sup-', [status(thm)], ['30', '58'])).
% 0.21/0.50  thf('60', plain,
% 0.21/0.50      (![X8 : $i, X9 : $i]:
% 0.21/0.50         (~ (l3_lattices @ X8)
% 0.21/0.50          | (v2_struct_0 @ X8)
% 0.21/0.50          | (m1_subset_1 @ (k15_lattice3 @ X8 @ X9) @ (u1_struct_0 @ X8)))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.21/0.50  thf('61', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t26_lattices, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & ( l2_lattices @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.50               ( ( ( r1_lattices @ A @ B @ C ) & ( r1_lattices @ A @ C @ B ) ) =>
% 0.21/0.50                 ( ( B ) = ( C ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('62', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 0.21/0.50          | ~ (r1_lattices @ X6 @ X5 @ X7)
% 0.21/0.50          | ~ (r1_lattices @ X6 @ X7 @ X5)
% 0.21/0.50          | ((X5) = (X7))
% 0.21/0.50          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 0.21/0.50          | ~ (l2_lattices @ X6)
% 0.21/0.50          | ~ (v4_lattices @ X6)
% 0.21/0.50          | (v2_struct_0 @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [t26_lattices])).
% 0.21/0.50  thf('63', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_A)
% 0.21/0.50          | ~ (v4_lattices @ sk_A)
% 0.21/0.50          | ~ (l2_lattices @ sk_A)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50          | ((sk_B) = (X0))
% 0.21/0.50          | ~ (r1_lattices @ sk_A @ X0 @ sk_B)
% 0.21/0.50          | ~ (r1_lattices @ sk_A @ sk_B @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['61', '62'])).
% 0.21/0.50  thf('64', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X0)
% 0.21/0.50          | ~ (v10_lattices @ X0)
% 0.21/0.50          | (v4_lattices @ X0)
% 0.21/0.50          | ~ (l3_lattices @ X0))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.50  thf('65', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('66', plain,
% 0.21/0.50      ((~ (l3_lattices @ sk_A) | (v4_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.50  thf('67', plain, ((l3_lattices @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('68', plain, ((v10_lattices @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('69', plain, ((v4_lattices @ sk_A)),
% 0.21/0.50      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.21/0.50  thf('70', plain, ((l3_lattices @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(dt_l3_lattices, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 0.21/0.50  thf('71', plain, (![X1 : $i]: ((l2_lattices @ X1) | ~ (l3_lattices @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.21/0.50  thf('72', plain, ((l2_lattices @ sk_A)),
% 0.21/0.50      inference('sup-', [status(thm)], ['70', '71'])).
% 0.21/0.50  thf('73', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_A)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50          | ((sk_B) = (X0))
% 0.21/0.50          | ~ (r1_lattices @ sk_A @ X0 @ sk_B)
% 0.21/0.50          | ~ (r1_lattices @ sk_A @ sk_B @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['63', '69', '72'])).
% 0.21/0.50  thf('74', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_A)
% 0.21/0.50          | ~ (l3_lattices @ sk_A)
% 0.21/0.50          | ~ (r1_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ X0))
% 0.21/0.50          | ~ (r1_lattices @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B)
% 0.21/0.50          | ((sk_B) = (k15_lattice3 @ sk_A @ X0))
% 0.21/0.50          | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['60', '73'])).
% 0.21/0.50  thf('75', plain, ((l3_lattices @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('76', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_A)
% 0.21/0.50          | ~ (r1_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ X0))
% 0.21/0.50          | ~ (r1_lattices @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B)
% 0.21/0.50          | ((sk_B) = (k15_lattice3 @ sk_A @ X0))
% 0.21/0.50          | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['74', '75'])).
% 0.21/0.50  thf('77', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((sk_B) = (k15_lattice3 @ sk_A @ X0))
% 0.21/0.50          | ~ (r1_lattices @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B)
% 0.21/0.50          | ~ (r1_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ X0))
% 0.21/0.50          | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('simplify', [status(thm)], ['76'])).
% 0.21/0.50  thf('78', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_A)
% 0.21/0.50        | ~ (r1_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C))
% 0.21/0.50        | ((sk_B) = (k15_lattice3 @ sk_A @ sk_C)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['59', '77'])).
% 0.21/0.50  thf('79', plain,
% 0.21/0.50      (![X8 : $i, X9 : $i]:
% 0.21/0.50         (~ (l3_lattices @ X8)
% 0.21/0.50          | (v2_struct_0 @ X8)
% 0.21/0.50          | (m1_subset_1 @ (k15_lattice3 @ X8 @ X9) @ (u1_struct_0 @ X8)))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.21/0.50  thf('80', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('81', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('82', plain,
% 0.21/0.50      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.21/0.50          | (r3_lattices @ X17 @ X16 @ (k15_lattice3 @ X17 @ X18))
% 0.21/0.50          | ~ (r2_hidden @ X16 @ X18)
% 0.21/0.50          | ~ (l3_lattices @ X17)
% 0.21/0.50          | ~ (v4_lattice3 @ X17)
% 0.21/0.50          | ~ (v10_lattices @ X17)
% 0.21/0.50          | (v2_struct_0 @ X17))),
% 0.21/0.50      inference('cnf', [status(esa)], [t38_lattice3])).
% 0.21/0.50  thf('83', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_A)
% 0.21/0.50          | ~ (v10_lattices @ sk_A)
% 0.21/0.50          | ~ (v4_lattice3 @ sk_A)
% 0.21/0.50          | ~ (l3_lattices @ sk_A)
% 0.21/0.50          | ~ (r2_hidden @ sk_B @ X0)
% 0.21/0.50          | (r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['81', '82'])).
% 0.21/0.50  thf('84', plain, ((v10_lattices @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('85', plain, ((v4_lattice3 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('86', plain, ((l3_lattices @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('87', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_A)
% 0.21/0.50          | ~ (r2_hidden @ sk_B @ X0)
% 0.21/0.50          | (r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ X0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['83', '84', '85', '86'])).
% 0.21/0.50  thf('88', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('89', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ X0))
% 0.21/0.50          | ~ (r2_hidden @ sk_B @ X0))),
% 0.21/0.50      inference('clc', [status(thm)], ['87', '88'])).
% 0.21/0.50  thf('90', plain,
% 0.21/0.50      ((r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['80', '89'])).
% 0.21/0.50  thf('91', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('92', plain,
% 0.21/0.50      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X3))
% 0.21/0.50          | ~ (l3_lattices @ X3)
% 0.21/0.50          | ~ (v9_lattices @ X3)
% 0.21/0.50          | ~ (v8_lattices @ X3)
% 0.21/0.50          | ~ (v6_lattices @ X3)
% 0.21/0.50          | (v2_struct_0 @ X3)
% 0.21/0.50          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 0.21/0.50          | (r1_lattices @ X3 @ X2 @ X4)
% 0.21/0.50          | ~ (r3_lattices @ X3 @ X2 @ X4))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.21/0.50  thf('93', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (r3_lattices @ sk_A @ sk_B @ X0)
% 0.21/0.50          | (r1_lattices @ sk_A @ sk_B @ X0)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | ~ (v6_lattices @ sk_A)
% 0.21/0.50          | ~ (v8_lattices @ sk_A)
% 0.21/0.50          | ~ (v9_lattices @ sk_A)
% 0.21/0.50          | ~ (l3_lattices @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['91', '92'])).
% 0.21/0.50  thf('94', plain, ((v6_lattices @ sk_A)),
% 0.21/0.50      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.21/0.50  thf('95', plain, ((v8_lattices @ sk_A)),
% 0.21/0.50      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.21/0.50  thf('96', plain, ((v9_lattices @ sk_A)),
% 0.21/0.50      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.21/0.50  thf('97', plain, ((l3_lattices @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('98', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (r3_lattices @ sk_A @ sk_B @ X0)
% 0.21/0.50          | (r1_lattices @ sk_A @ sk_B @ X0)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50          | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['93', '94', '95', '96', '97'])).
% 0.21/0.50  thf('99', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_A)
% 0.21/0.50        | ~ (m1_subset_1 @ (k15_lattice3 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.21/0.50        | (r1_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['90', '98'])).
% 0.21/0.50  thf('100', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('101', plain,
% 0.21/0.50      (((r1_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C))
% 0.21/0.50        | ~ (m1_subset_1 @ (k15_lattice3 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('clc', [status(thm)], ['99', '100'])).
% 0.21/0.50  thf('102', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_A)
% 0.21/0.50        | ~ (l3_lattices @ sk_A)
% 0.21/0.50        | (r1_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['79', '101'])).
% 0.21/0.50  thf('103', plain, ((l3_lattices @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('104', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_A)
% 0.21/0.50        | (r1_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C)))),
% 0.21/0.50      inference('demod', [status(thm)], ['102', '103'])).
% 0.21/0.50  thf('105', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('106', plain,
% 0.21/0.50      ((r1_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C))),
% 0.21/0.50      inference('clc', [status(thm)], ['104', '105'])).
% 0.21/0.50  thf('107', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_A) | ((sk_B) = (k15_lattice3 @ sk_A @ sk_C)))),
% 0.21/0.50      inference('demod', [status(thm)], ['78', '106'])).
% 0.21/0.50  thf('108', plain, (((k15_lattice3 @ sk_A @ sk_C) != (sk_B))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('109', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['107', '108'])).
% 0.21/0.50  thf('110', plain, ($false), inference('demod', [status(thm)], ['0', '109'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
