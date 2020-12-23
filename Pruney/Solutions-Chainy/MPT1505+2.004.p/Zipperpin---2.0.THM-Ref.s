%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GD4u0KcgWi

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:28 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 235 expanded)
%              Number of leaves         :   31 (  81 expanded)
%              Depth                    :   18
%              Number of atoms          : 1195 (3605 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r3_lattice3_type,type,(
    r3_lattice3: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r4_lattice3_type,type,(
    r4_lattice3: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t38_lattice3,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v4_lattice3 @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( r2_hidden @ B @ C )
               => ( ( r3_lattices @ A @ B @ ( k15_lattice3 @ A @ C ) )
                  & ( r3_lattices @ A @ ( k16_lattice3 @ A @ C ) @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_lattice3])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k15_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('2',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf(d21_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v4_lattice3 @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i,C: $i] :
            ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
           => ( ( C
                = ( k15_lattice3 @ A @ B ) )
            <=> ( ( r4_lattice3 @ A @ C @ B )
                & ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r4_lattice3 @ A @ D @ B )
                     => ( r1_lattices @ A @ C @ D ) ) ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( v10_lattices @ X14 )
      | ~ ( v4_lattice3 @ X14 )
      | ~ ( l3_lattices @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( X15
       != ( k15_lattice3 @ X14 @ X16 ) )
      | ( r4_lattice3 @ X14 @ X15 @ X16 )
      | ~ ( l3_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('6',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r4_lattice3 @ X14 @ ( k15_lattice3 @ X14 @ X16 ) @ X16 )
      | ~ ( m1_subset_1 @ ( k15_lattice3 @ X14 @ X16 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( l3_lattices @ X14 )
      | ~ ( v4_lattice3 @ X14 )
      | ~ ( v10_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X1 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf(d17_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( r4_lattice3 @ A @ B @ C )
            <=> ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( r2_hidden @ D @ C )
                   => ( r1_lattices @ A @ D @ B ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( r4_lattice3 @ X10 @ X9 @ X11 )
      | ~ ( r2_hidden @ X12 @ X11 )
      | ( r1_lattices @ X10 @ X12 @ X9 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X3 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ( r1_lattices @ X0 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r1_lattices @ X1 @ X2 @ ( k15_lattice3 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r1_lattices @ X1 @ X2 @ ( k15_lattice3 @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ( r1_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','14'])).

thf('16',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16','17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    r1_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['2','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('24',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l3_lattices @ X2 )
      | ~ ( v9_lattices @ X2 )
      | ~ ( v8_lattices @ X2 )
      | ~ ( v6_lattices @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( r3_lattices @ X2 @ X1 @ X3 )
      | ~ ( r1_lattices @ X2 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ sk_B @ X0 )
      | ( r3_lattices @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

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

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ sk_B @ X0 )
      | ( r3_lattices @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','31','37','43','44'])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k15_lattice3 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) )
    | ~ ( m1_subset_1 @ ( k15_lattice3 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) )
    | ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ~ ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) )
   <= ~ ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['49'])).

thf('51',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k16_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( m1_subset_1 @ ( k16_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('53',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf(t34_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v4_lattice3 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( B
                = ( k16_lattice3 @ A @ C ) )
            <=> ( ( r3_lattice3 @ A @ B @ C )
                & ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r3_lattice3 @ A @ D @ C )
                     => ( r3_lattices @ A @ D @ B ) ) ) ) ) ) ) )).

thf('54',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( X22
       != ( k16_lattice3 @ X23 @ X24 ) )
      | ( r3_lattice3 @ X23 @ X22 @ X24 )
      | ~ ( l3_lattices @ X23 )
      | ~ ( v4_lattice3 @ X23 )
      | ~ ( v10_lattices @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('55',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v10_lattices @ X23 )
      | ~ ( v4_lattice3 @ X23 )
      | ~ ( l3_lattices @ X23 )
      | ( r3_lattice3 @ X23 @ ( k16_lattice3 @ X23 @ X24 ) @ X24 )
      | ~ ( m1_subset_1 @ ( k16_lattice3 @ X23 @ X24 ) @ ( u1_struct_0 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf(d16_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( r3_lattice3 @ A @ B @ C )
            <=> ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( r2_hidden @ D @ C )
                   => ( r1_lattices @ A @ B @ D ) ) ) ) ) ) )).

thf('59',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r3_lattice3 @ X5 @ X4 @ X6 )
      | ~ ( r2_hidden @ X7 @ X6 )
      | ( r1_lattices @ X5 @ X4 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X3 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r1_lattices @ X1 @ ( k16_lattice3 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r1_lattices @ X1 @ ( k16_lattice3 @ X1 @ X0 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','63'])).

thf('65',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65','66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['51','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf('74',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l3_lattices @ X2 )
      | ~ ( v9_lattices @ X2 )
      | ~ ( v8_lattices @ X2 )
      | ~ ( v6_lattices @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( r3_lattices @ X2 @ X1 @ X3 )
      | ~ ( r1_lattices @ X2 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','76'])).

thf('78',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('80',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('81',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['77','78','79','80','81'])).

thf('83',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ~ ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,(
    r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['71','84'])).

thf('86',plain,
    ( ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C ) @ sk_B )
   <= ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(split,[status(esa)],['49'])).

thf('87',plain,(
    r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ~ ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) )
    | ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(split,[status(esa)],['49'])).

thf('89',plain,(
    ~ ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['87','88'])).

thf('90',plain,(
    ~ ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['50','89'])).

thf('91',plain,(
    ~ ( m1_subset_1 @ ( k15_lattice3 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['48','90'])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['1','91'])).

thf('93',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    $false ),
    inference(demod,[status(thm)],['0','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GD4u0KcgWi
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:34:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.43/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.43/0.64  % Solved by: fo/fo7.sh
% 0.43/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.64  % done 155 iterations in 0.186s
% 0.43/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.43/0.64  % SZS output start Refutation
% 0.43/0.64  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.43/0.64  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.43/0.64  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.43/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.64  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.43/0.64  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 0.43/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.43/0.64  thf(r3_lattice3_type, type, r3_lattice3: $i > $i > $i > $o).
% 0.43/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.64  thf(r4_lattice3_type, type, r4_lattice3: $i > $i > $i > $o).
% 0.43/0.64  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.43/0.64  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.43/0.64  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.43/0.64  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 0.43/0.64  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 0.43/0.64  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 0.43/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.64  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.43/0.64  thf(sk_C_type, type, sk_C: $i).
% 0.43/0.64  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.43/0.64  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.43/0.64  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.43/0.64  thf(t38_lattice3, conjecture,
% 0.43/0.64    (![A:$i]:
% 0.43/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.43/0.64         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.43/0.64       ( ![B:$i]:
% 0.43/0.64         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.64           ( ![C:$i]:
% 0.43/0.64             ( ( r2_hidden @ B @ C ) =>
% 0.43/0.64               ( ( r3_lattices @ A @ B @ ( k15_lattice3 @ A @ C ) ) & 
% 0.43/0.64                 ( r3_lattices @ A @ ( k16_lattice3 @ A @ C ) @ B ) ) ) ) ) ) ))).
% 0.43/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.64    (~( ![A:$i]:
% 0.43/0.64        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.43/0.64            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.43/0.64          ( ![B:$i]:
% 0.43/0.64            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.64              ( ![C:$i]:
% 0.43/0.64                ( ( r2_hidden @ B @ C ) =>
% 0.43/0.64                  ( ( r3_lattices @ A @ B @ ( k15_lattice3 @ A @ C ) ) & 
% 0.43/0.64                    ( r3_lattices @ A @ ( k16_lattice3 @ A @ C ) @ B ) ) ) ) ) ) ) )),
% 0.43/0.64    inference('cnf.neg', [status(esa)], [t38_lattice3])).
% 0.43/0.64  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.64  thf(dt_k15_lattice3, axiom,
% 0.43/0.64    (![A:$i,B:$i]:
% 0.43/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.43/0.64       ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.43/0.64  thf('1', plain,
% 0.43/0.64      (![X18 : $i, X19 : $i]:
% 0.43/0.64         (~ (l3_lattices @ X18)
% 0.43/0.64          | (v2_struct_0 @ X18)
% 0.43/0.64          | (m1_subset_1 @ (k15_lattice3 @ X18 @ X19) @ (u1_struct_0 @ X18)))),
% 0.43/0.64      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.43/0.64  thf('2', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.43/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.64  thf('3', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.43/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.64  thf('4', plain,
% 0.43/0.64      (![X18 : $i, X19 : $i]:
% 0.43/0.64         (~ (l3_lattices @ X18)
% 0.43/0.64          | (v2_struct_0 @ X18)
% 0.43/0.64          | (m1_subset_1 @ (k15_lattice3 @ X18 @ X19) @ (u1_struct_0 @ X18)))),
% 0.43/0.64      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.43/0.64  thf(d21_lattice3, axiom,
% 0.43/0.64    (![A:$i]:
% 0.43/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.43/0.64       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.43/0.64           ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.43/0.64         ( ![B:$i,C:$i]:
% 0.43/0.64           ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.64             ( ( ( C ) = ( k15_lattice3 @ A @ B ) ) <=>
% 0.43/0.64               ( ( r4_lattice3 @ A @ C @ B ) & 
% 0.43/0.64                 ( ![D:$i]:
% 0.43/0.64                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.64                     ( ( r4_lattice3 @ A @ D @ B ) =>
% 0.43/0.64                       ( r1_lattices @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.43/0.64  thf('5', plain,
% 0.43/0.64      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.43/0.64         ((v2_struct_0 @ X14)
% 0.43/0.64          | ~ (v10_lattices @ X14)
% 0.43/0.64          | ~ (v4_lattice3 @ X14)
% 0.43/0.64          | ~ (l3_lattices @ X14)
% 0.43/0.64          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.43/0.64          | ((X15) != (k15_lattice3 @ X14 @ X16))
% 0.43/0.64          | (r4_lattice3 @ X14 @ X15 @ X16)
% 0.43/0.64          | ~ (l3_lattices @ X14)
% 0.43/0.64          | (v2_struct_0 @ X14))),
% 0.43/0.64      inference('cnf', [status(esa)], [d21_lattice3])).
% 0.43/0.64  thf('6', plain,
% 0.43/0.64      (![X14 : $i, X16 : $i]:
% 0.43/0.64         ((r4_lattice3 @ X14 @ (k15_lattice3 @ X14 @ X16) @ X16)
% 0.43/0.64          | ~ (m1_subset_1 @ (k15_lattice3 @ X14 @ X16) @ (u1_struct_0 @ X14))
% 0.43/0.64          | ~ (l3_lattices @ X14)
% 0.43/0.64          | ~ (v4_lattice3 @ X14)
% 0.43/0.64          | ~ (v10_lattices @ X14)
% 0.43/0.64          | (v2_struct_0 @ X14))),
% 0.43/0.64      inference('simplify', [status(thm)], ['5'])).
% 0.43/0.64  thf('7', plain,
% 0.43/0.64      (![X0 : $i, X1 : $i]:
% 0.43/0.64         ((v2_struct_0 @ X0)
% 0.43/0.64          | ~ (l3_lattices @ X0)
% 0.43/0.64          | (v2_struct_0 @ X0)
% 0.43/0.64          | ~ (v10_lattices @ X0)
% 0.43/0.64          | ~ (v4_lattice3 @ X0)
% 0.43/0.64          | ~ (l3_lattices @ X0)
% 0.43/0.64          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X1))),
% 0.43/0.64      inference('sup-', [status(thm)], ['4', '6'])).
% 0.43/0.64  thf('8', plain,
% 0.43/0.64      (![X0 : $i, X1 : $i]:
% 0.43/0.64         ((r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X1)
% 0.43/0.64          | ~ (v4_lattice3 @ X0)
% 0.43/0.64          | ~ (v10_lattices @ X0)
% 0.43/0.64          | ~ (l3_lattices @ X0)
% 0.43/0.64          | (v2_struct_0 @ X0))),
% 0.43/0.64      inference('simplify', [status(thm)], ['7'])).
% 0.43/0.64  thf('9', plain,
% 0.43/0.64      (![X18 : $i, X19 : $i]:
% 0.43/0.64         (~ (l3_lattices @ X18)
% 0.43/0.64          | (v2_struct_0 @ X18)
% 0.43/0.64          | (m1_subset_1 @ (k15_lattice3 @ X18 @ X19) @ (u1_struct_0 @ X18)))),
% 0.43/0.64      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.43/0.64  thf(d17_lattice3, axiom,
% 0.43/0.64    (![A:$i]:
% 0.43/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.43/0.64       ( ![B:$i]:
% 0.43/0.64         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.64           ( ![C:$i]:
% 0.43/0.64             ( ( r4_lattice3 @ A @ B @ C ) <=>
% 0.43/0.64               ( ![D:$i]:
% 0.43/0.64                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.64                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ))).
% 0.43/0.64  thf('10', plain,
% 0.43/0.64      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.43/0.64         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.43/0.64          | ~ (r4_lattice3 @ X10 @ X9 @ X11)
% 0.46/0.64          | ~ (r2_hidden @ X12 @ X11)
% 0.46/0.64          | (r1_lattices @ X10 @ X12 @ X9)
% 0.46/0.64          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X10))
% 0.46/0.64          | ~ (l3_lattices @ X10)
% 0.46/0.64          | (v2_struct_0 @ X10))),
% 0.46/0.64      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.46/0.64  thf('11', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.64         ((v2_struct_0 @ X0)
% 0.46/0.64          | ~ (l3_lattices @ X0)
% 0.46/0.64          | (v2_struct_0 @ X0)
% 0.46/0.64          | ~ (l3_lattices @ X0)
% 0.46/0.64          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.46/0.64          | (r1_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))
% 0.46/0.64          | ~ (r2_hidden @ X2 @ X3)
% 0.46/0.64          | ~ (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X3))),
% 0.46/0.64      inference('sup-', [status(thm)], ['9', '10'])).
% 0.46/0.64  thf('12', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.64         (~ (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X3)
% 0.46/0.64          | ~ (r2_hidden @ X2 @ X3)
% 0.46/0.64          | (r1_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))
% 0.46/0.64          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.46/0.64          | ~ (l3_lattices @ X0)
% 0.46/0.64          | (v2_struct_0 @ X0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['11'])).
% 0.46/0.64  thf('13', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         ((v2_struct_0 @ X1)
% 0.46/0.64          | ~ (l3_lattices @ X1)
% 0.46/0.64          | ~ (v10_lattices @ X1)
% 0.46/0.64          | ~ (v4_lattice3 @ X1)
% 0.46/0.64          | (v2_struct_0 @ X1)
% 0.46/0.64          | ~ (l3_lattices @ X1)
% 0.46/0.64          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.46/0.64          | (r1_lattices @ X1 @ X2 @ (k15_lattice3 @ X1 @ X0))
% 0.46/0.64          | ~ (r2_hidden @ X2 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['8', '12'])).
% 0.46/0.64  thf('14', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X2 @ X0)
% 0.46/0.64          | (r1_lattices @ X1 @ X2 @ (k15_lattice3 @ X1 @ X0))
% 0.46/0.64          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.46/0.64          | ~ (v4_lattice3 @ X1)
% 0.46/0.64          | ~ (v10_lattices @ X1)
% 0.46/0.64          | ~ (l3_lattices @ X1)
% 0.46/0.64          | (v2_struct_0 @ X1))),
% 0.46/0.64      inference('simplify', [status(thm)], ['13'])).
% 0.46/0.64  thf('15', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v2_struct_0 @ sk_A)
% 0.46/0.64          | ~ (l3_lattices @ sk_A)
% 0.46/0.64          | ~ (v10_lattices @ sk_A)
% 0.46/0.64          | ~ (v4_lattice3 @ sk_A)
% 0.46/0.64          | (r1_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ X0))
% 0.46/0.64          | ~ (r2_hidden @ sk_B @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['3', '14'])).
% 0.46/0.64  thf('16', plain, ((l3_lattices @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('17', plain, ((v10_lattices @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('18', plain, ((v4_lattice3 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('19', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v2_struct_0 @ sk_A)
% 0.46/0.64          | (r1_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ X0))
% 0.46/0.64          | ~ (r2_hidden @ sk_B @ X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['15', '16', '17', '18'])).
% 0.46/0.64  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('21', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (r2_hidden @ sk_B @ X0)
% 0.46/0.64          | (r1_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ X0)))),
% 0.46/0.64      inference('clc', [status(thm)], ['19', '20'])).
% 0.46/0.64  thf('22', plain,
% 0.46/0.64      ((r1_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['2', '21'])).
% 0.46/0.64  thf('23', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(redefinition_r3_lattices, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.46/0.64         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 0.46/0.64         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.46/0.64         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.64       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 0.46/0.64  thf('24', plain,
% 0.46/0.64      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.46/0.64          | ~ (l3_lattices @ X2)
% 0.46/0.64          | ~ (v9_lattices @ X2)
% 0.46/0.64          | ~ (v8_lattices @ X2)
% 0.46/0.64          | ~ (v6_lattices @ X2)
% 0.46/0.64          | (v2_struct_0 @ X2)
% 0.46/0.64          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.46/0.64          | (r3_lattices @ X2 @ X1 @ X3)
% 0.46/0.64          | ~ (r1_lattices @ X2 @ X1 @ X3))),
% 0.46/0.64      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.46/0.64  thf('25', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (r1_lattices @ sk_A @ sk_B @ X0)
% 0.46/0.64          | (r3_lattices @ sk_A @ sk_B @ X0)
% 0.46/0.64          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.46/0.64          | (v2_struct_0 @ sk_A)
% 0.46/0.64          | ~ (v6_lattices @ sk_A)
% 0.46/0.64          | ~ (v8_lattices @ sk_A)
% 0.46/0.64          | ~ (v9_lattices @ sk_A)
% 0.46/0.64          | ~ (l3_lattices @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['23', '24'])).
% 0.46/0.64  thf(cc1_lattices, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( l3_lattices @ A ) =>
% 0.46/0.64       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.46/0.64         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.46/0.64           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.46/0.64           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.46/0.64  thf('26', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v2_struct_0 @ X0)
% 0.46/0.64          | ~ (v10_lattices @ X0)
% 0.46/0.64          | (v6_lattices @ X0)
% 0.46/0.64          | ~ (l3_lattices @ X0))),
% 0.46/0.64      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.46/0.64  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('28', plain,
% 0.46/0.64      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['26', '27'])).
% 0.46/0.64  thf('29', plain, ((l3_lattices @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('30', plain, ((v10_lattices @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('31', plain, ((v6_lattices @ sk_A)),
% 0.46/0.64      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.46/0.64  thf('32', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v2_struct_0 @ X0)
% 0.46/0.64          | ~ (v10_lattices @ X0)
% 0.46/0.64          | (v8_lattices @ X0)
% 0.46/0.64          | ~ (l3_lattices @ X0))),
% 0.46/0.64      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.46/0.64  thf('33', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('34', plain,
% 0.46/0.64      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['32', '33'])).
% 0.46/0.64  thf('35', plain, ((l3_lattices @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('36', plain, ((v10_lattices @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('37', plain, ((v8_lattices @ sk_A)),
% 0.46/0.64      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.46/0.64  thf('38', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v2_struct_0 @ X0)
% 0.46/0.64          | ~ (v10_lattices @ X0)
% 0.46/0.64          | (v9_lattices @ X0)
% 0.46/0.64          | ~ (l3_lattices @ X0))),
% 0.46/0.64      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.46/0.64  thf('39', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('40', plain,
% 0.46/0.64      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['38', '39'])).
% 0.46/0.64  thf('41', plain, ((l3_lattices @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('42', plain, ((v10_lattices @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('43', plain, ((v9_lattices @ sk_A)),
% 0.46/0.64      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.46/0.64  thf('44', plain, ((l3_lattices @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('45', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (r1_lattices @ sk_A @ sk_B @ X0)
% 0.46/0.64          | (r3_lattices @ sk_A @ sk_B @ X0)
% 0.46/0.64          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.46/0.64          | (v2_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['25', '31', '37', '43', '44'])).
% 0.46/0.64  thf('46', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_A)
% 0.46/0.64        | ~ (m1_subset_1 @ (k15_lattice3 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.46/0.64        | (r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['22', '45'])).
% 0.46/0.64  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('48', plain,
% 0.46/0.64      (((r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C))
% 0.46/0.64        | ~ (m1_subset_1 @ (k15_lattice3 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A)))),
% 0.46/0.64      inference('clc', [status(thm)], ['46', '47'])).
% 0.46/0.64  thf('49', plain,
% 0.46/0.64      ((~ (r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C))
% 0.46/0.64        | ~ (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C) @ sk_B))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('50', plain,
% 0.46/0.64      ((~ (r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C)))
% 0.46/0.64         <= (~ ((r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C))))),
% 0.46/0.64      inference('split', [status(esa)], ['49'])).
% 0.46/0.64  thf('51', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('52', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(dt_k16_lattice3, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.46/0.64       ( m1_subset_1 @ ( k16_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.46/0.64  thf('53', plain,
% 0.46/0.64      (![X20 : $i, X21 : $i]:
% 0.46/0.64         (~ (l3_lattices @ X20)
% 0.46/0.64          | (v2_struct_0 @ X20)
% 0.46/0.64          | (m1_subset_1 @ (k16_lattice3 @ X20 @ X21) @ (u1_struct_0 @ X20)))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.46/0.64  thf(t34_lattice3, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.46/0.64         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.64           ( ![C:$i]:
% 0.46/0.64             ( ( ( B ) = ( k16_lattice3 @ A @ C ) ) <=>
% 0.46/0.64               ( ( r3_lattice3 @ A @ B @ C ) & 
% 0.46/0.64                 ( ![D:$i]:
% 0.46/0.64                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.64                     ( ( r3_lattice3 @ A @ D @ C ) =>
% 0.46/0.64                       ( r3_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.64  thf('54', plain,
% 0.46/0.64      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 0.46/0.64          | ((X22) != (k16_lattice3 @ X23 @ X24))
% 0.46/0.64          | (r3_lattice3 @ X23 @ X22 @ X24)
% 0.46/0.64          | ~ (l3_lattices @ X23)
% 0.46/0.64          | ~ (v4_lattice3 @ X23)
% 0.46/0.64          | ~ (v10_lattices @ X23)
% 0.46/0.64          | (v2_struct_0 @ X23))),
% 0.46/0.64      inference('cnf', [status(esa)], [t34_lattice3])).
% 0.46/0.64  thf('55', plain,
% 0.46/0.64      (![X23 : $i, X24 : $i]:
% 0.46/0.64         ((v2_struct_0 @ X23)
% 0.46/0.64          | ~ (v10_lattices @ X23)
% 0.46/0.64          | ~ (v4_lattice3 @ X23)
% 0.46/0.64          | ~ (l3_lattices @ X23)
% 0.46/0.64          | (r3_lattice3 @ X23 @ (k16_lattice3 @ X23 @ X24) @ X24)
% 0.46/0.64          | ~ (m1_subset_1 @ (k16_lattice3 @ X23 @ X24) @ (u1_struct_0 @ X23)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['54'])).
% 0.46/0.64  thf('56', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((v2_struct_0 @ X0)
% 0.46/0.64          | ~ (l3_lattices @ X0)
% 0.46/0.64          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X1)
% 0.46/0.64          | ~ (l3_lattices @ X0)
% 0.46/0.64          | ~ (v4_lattice3 @ X0)
% 0.46/0.64          | ~ (v10_lattices @ X0)
% 0.46/0.64          | (v2_struct_0 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['53', '55'])).
% 0.46/0.64  thf('57', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (v10_lattices @ X0)
% 0.46/0.64          | ~ (v4_lattice3 @ X0)
% 0.46/0.64          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X1)
% 0.46/0.64          | ~ (l3_lattices @ X0)
% 0.46/0.64          | (v2_struct_0 @ X0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['56'])).
% 0.46/0.64  thf('58', plain,
% 0.46/0.64      (![X20 : $i, X21 : $i]:
% 0.46/0.64         (~ (l3_lattices @ X20)
% 0.46/0.64          | (v2_struct_0 @ X20)
% 0.46/0.64          | (m1_subset_1 @ (k16_lattice3 @ X20 @ X21) @ (u1_struct_0 @ X20)))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.46/0.64  thf(d16_lattice3, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.64           ( ![C:$i]:
% 0.46/0.64             ( ( r3_lattice3 @ A @ B @ C ) <=>
% 0.46/0.64               ( ![D:$i]:
% 0.46/0.64                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.64                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 0.46/0.64  thf('59', plain,
% 0.46/0.64      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.46/0.64          | ~ (r3_lattice3 @ X5 @ X4 @ X6)
% 0.46/0.64          | ~ (r2_hidden @ X7 @ X6)
% 0.46/0.64          | (r1_lattices @ X5 @ X4 @ X7)
% 0.46/0.64          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X5))
% 0.46/0.64          | ~ (l3_lattices @ X5)
% 0.46/0.64          | (v2_struct_0 @ X5))),
% 0.46/0.64      inference('cnf', [status(esa)], [d16_lattice3])).
% 0.46/0.64  thf('60', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.64         ((v2_struct_0 @ X0)
% 0.46/0.64          | ~ (l3_lattices @ X0)
% 0.46/0.64          | (v2_struct_0 @ X0)
% 0.46/0.64          | ~ (l3_lattices @ X0)
% 0.46/0.64          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.46/0.64          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.46/0.64          | ~ (r2_hidden @ X2 @ X3)
% 0.46/0.64          | ~ (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X3))),
% 0.46/0.64      inference('sup-', [status(thm)], ['58', '59'])).
% 0.46/0.64  thf('61', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.64         (~ (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X3)
% 0.46/0.64          | ~ (r2_hidden @ X2 @ X3)
% 0.46/0.64          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.46/0.64          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.46/0.64          | ~ (l3_lattices @ X0)
% 0.46/0.64          | (v2_struct_0 @ X0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['60'])).
% 0.46/0.64  thf('62', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         ((v2_struct_0 @ X1)
% 0.46/0.64          | ~ (l3_lattices @ X1)
% 0.46/0.64          | ~ (v4_lattice3 @ X1)
% 0.46/0.64          | ~ (v10_lattices @ X1)
% 0.46/0.64          | (v2_struct_0 @ X1)
% 0.46/0.64          | ~ (l3_lattices @ X1)
% 0.46/0.64          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.46/0.64          | (r1_lattices @ X1 @ (k16_lattice3 @ X1 @ X0) @ X2)
% 0.46/0.64          | ~ (r2_hidden @ X2 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['57', '61'])).
% 0.46/0.64  thf('63', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X2 @ X0)
% 0.46/0.64          | (r1_lattices @ X1 @ (k16_lattice3 @ X1 @ X0) @ X2)
% 0.46/0.64          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.46/0.64          | ~ (v10_lattices @ X1)
% 0.46/0.64          | ~ (v4_lattice3 @ X1)
% 0.46/0.64          | ~ (l3_lattices @ X1)
% 0.46/0.64          | (v2_struct_0 @ X1))),
% 0.46/0.64      inference('simplify', [status(thm)], ['62'])).
% 0.46/0.64  thf('64', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v2_struct_0 @ sk_A)
% 0.46/0.64          | ~ (l3_lattices @ sk_A)
% 0.46/0.64          | ~ (v4_lattice3 @ sk_A)
% 0.46/0.64          | ~ (v10_lattices @ sk_A)
% 0.46/0.64          | (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.46/0.64          | ~ (r2_hidden @ sk_B @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['52', '63'])).
% 0.46/0.64  thf('65', plain, ((l3_lattices @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('66', plain, ((v4_lattice3 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('67', plain, ((v10_lattices @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('68', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v2_struct_0 @ sk_A)
% 0.46/0.64          | (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.46/0.64          | ~ (r2_hidden @ sk_B @ X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['64', '65', '66', '67'])).
% 0.46/0.64  thf('69', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('70', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (r2_hidden @ sk_B @ X0)
% 0.46/0.64          | (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B))),
% 0.46/0.64      inference('clc', [status(thm)], ['68', '69'])).
% 0.46/0.64  thf('71', plain,
% 0.46/0.64      ((r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C) @ sk_B)),
% 0.46/0.64      inference('sup-', [status(thm)], ['51', '70'])).
% 0.46/0.64  thf('72', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('73', plain,
% 0.46/0.64      (![X20 : $i, X21 : $i]:
% 0.46/0.64         (~ (l3_lattices @ X20)
% 0.46/0.64          | (v2_struct_0 @ X20)
% 0.46/0.64          | (m1_subset_1 @ (k16_lattice3 @ X20 @ X21) @ (u1_struct_0 @ X20)))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.46/0.64  thf('74', plain,
% 0.46/0.64      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.46/0.64          | ~ (l3_lattices @ X2)
% 0.46/0.64          | ~ (v9_lattices @ X2)
% 0.46/0.64          | ~ (v8_lattices @ X2)
% 0.46/0.64          | ~ (v6_lattices @ X2)
% 0.46/0.64          | (v2_struct_0 @ X2)
% 0.46/0.64          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.46/0.64          | (r3_lattices @ X2 @ X1 @ X3)
% 0.46/0.64          | ~ (r1_lattices @ X2 @ X1 @ X3))),
% 0.46/0.64      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.46/0.64  thf('75', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         ((v2_struct_0 @ X0)
% 0.46/0.64          | ~ (l3_lattices @ X0)
% 0.46/0.64          | ~ (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.46/0.64          | (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.46/0.64          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.46/0.64          | (v2_struct_0 @ X0)
% 0.46/0.64          | ~ (v6_lattices @ X0)
% 0.46/0.64          | ~ (v8_lattices @ X0)
% 0.46/0.64          | ~ (v9_lattices @ X0)
% 0.46/0.64          | ~ (l3_lattices @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['73', '74'])).
% 0.46/0.64  thf('76', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (v9_lattices @ X0)
% 0.46/0.64          | ~ (v8_lattices @ X0)
% 0.46/0.64          | ~ (v6_lattices @ X0)
% 0.46/0.64          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.46/0.64          | (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.46/0.64          | ~ (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.46/0.64          | ~ (l3_lattices @ X0)
% 0.46/0.64          | (v2_struct_0 @ X0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['75'])).
% 0.46/0.64  thf('77', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v2_struct_0 @ sk_A)
% 0.46/0.64          | ~ (l3_lattices @ sk_A)
% 0.46/0.64          | ~ (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.46/0.64          | (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.46/0.64          | ~ (v6_lattices @ sk_A)
% 0.46/0.64          | ~ (v8_lattices @ sk_A)
% 0.46/0.64          | ~ (v9_lattices @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['72', '76'])).
% 0.46/0.64  thf('78', plain, ((l3_lattices @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('79', plain, ((v6_lattices @ sk_A)),
% 0.46/0.64      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.46/0.64  thf('80', plain, ((v8_lattices @ sk_A)),
% 0.46/0.64      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.46/0.64  thf('81', plain, ((v9_lattices @ sk_A)),
% 0.46/0.64      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.46/0.64  thf('82', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v2_struct_0 @ sk_A)
% 0.46/0.64          | ~ (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.46/0.64          | (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['77', '78', '79', '80', '81'])).
% 0.46/0.64  thf('83', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('84', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.46/0.64          | ~ (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B))),
% 0.46/0.64      inference('clc', [status(thm)], ['82', '83'])).
% 0.46/0.64  thf('85', plain,
% 0.46/0.64      ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C) @ sk_B)),
% 0.46/0.64      inference('sup-', [status(thm)], ['71', '84'])).
% 0.46/0.64  thf('86', plain,
% 0.46/0.64      ((~ (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C) @ sk_B))
% 0.46/0.64         <= (~ ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C) @ sk_B)))),
% 0.46/0.64      inference('split', [status(esa)], ['49'])).
% 0.46/0.64  thf('87', plain,
% 0.46/0.64      (((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C) @ sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['85', '86'])).
% 0.46/0.64  thf('88', plain,
% 0.46/0.64      (~ ((r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C))) | 
% 0.46/0.64       ~ ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C) @ sk_B))),
% 0.46/0.64      inference('split', [status(esa)], ['49'])).
% 0.46/0.64  thf('89', plain,
% 0.46/0.64      (~ ((r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C)))),
% 0.46/0.64      inference('sat_resolution*', [status(thm)], ['87', '88'])).
% 0.46/0.64  thf('90', plain,
% 0.46/0.64      (~ (r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C))),
% 0.46/0.64      inference('simpl_trail', [status(thm)], ['50', '89'])).
% 0.46/0.64  thf('91', plain,
% 0.46/0.64      (~ (m1_subset_1 @ (k15_lattice3 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.46/0.64      inference('clc', [status(thm)], ['48', '90'])).
% 0.46/0.64  thf('92', plain, (((v2_struct_0 @ sk_A) | ~ (l3_lattices @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['1', '91'])).
% 0.46/0.64  thf('93', plain, ((l3_lattices @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('94', plain, ((v2_struct_0 @ sk_A)),
% 0.46/0.64      inference('demod', [status(thm)], ['92', '93'])).
% 0.46/0.64  thf('95', plain, ($false), inference('demod', [status(thm)], ['0', '94'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.46/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
