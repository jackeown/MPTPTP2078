%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.c62mBOawbK

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:28 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 254 expanded)
%              Number of leaves         :   32 (  87 expanded)
%              Depth                    :   18
%              Number of atoms          : 1283 (3935 expanded)
%              Number of equality atoms :    6 (  10 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

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

thf(a_2_2_lattice3_type,type,(
    a_2_2_lattice3: $i > $i > $i )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

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
    ! [X25: $i,X26: $i] :
      ( ( ( k15_lattice3 @ X25 @ X26 )
        = ( k16_lattice3 @ X25 @ ( a_2_2_lattice3 @ X25 @ X26 ) ) )
      | ~ ( l3_lattices @ X25 )
      | ~ ( v4_lattice3 @ X25 )
      | ~ ( v10_lattices @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t37_lattice3])).

thf(dt_k16_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( m1_subset_1 @ ( k16_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k15_lattice3 @ X1 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X1 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X1 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

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

thf('8',plain,(
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

thf('9',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r4_lattice3 @ X14 @ ( k15_lattice3 @ X14 @ X16 ) @ X16 )
      | ~ ( m1_subset_1 @ ( k15_lattice3 @ X14 @ X16 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( l3_lattices @ X14 )
      | ~ ( v4_lattice3 @ X14 )
      | ~ ( v10_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X1 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

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

thf('13',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( r4_lattice3 @ X10 @ X9 @ X11 )
      | ~ ( r2_hidden @ X12 @ X11 )
      | ( r1_lattices @ X10 @ X12 @ X9 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X3 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ( r1_lattices @ X0 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r1_lattices @ X1 @ X2 @ ( k15_lattice3 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r1_lattices @ X1 @ X2 @ ( k15_lattice3 @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r1_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf('19',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19','20','21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    r1_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['5','24'])).

thf('26',plain,(
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

thf('27',plain,(
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

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ sk_B @ X0 )
      | ( r3_lattices @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

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

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ sk_B @ X0 )
      | ( r3_lattices @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','34','40','46','47'])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k15_lattice3 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['25','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) )
    | ~ ( m1_subset_1 @ ( k15_lattice3 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) )
    | ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ~ ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) )
   <= ~ ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['52'])).

thf('54',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) ),
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

thf('57',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( X20
       != ( k16_lattice3 @ X21 @ X22 ) )
      | ( r3_lattice3 @ X21 @ X20 @ X22 )
      | ~ ( l3_lattices @ X21 )
      | ~ ( v4_lattice3 @ X21 )
      | ~ ( v10_lattices @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('58',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v10_lattices @ X21 )
      | ~ ( v4_lattice3 @ X21 )
      | ~ ( l3_lattices @ X21 )
      | ( r3_lattice3 @ X21 @ ( k16_lattice3 @ X21 @ X22 ) @ X22 )
      | ~ ( m1_subset_1 @ ( k16_lattice3 @ X21 @ X22 ) @ ( u1_struct_0 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) ),
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

thf('62',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r3_lattice3 @ X5 @ X4 @ X6 )
      | ~ ( r2_hidden @ X7 @ X6 )
      | ( r1_lattices @ X5 @ X4 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X3 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
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
    inference('sup-',[status(thm)],['60','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r1_lattices @ X1 @ ( k16_lattice3 @ X1 @ X0 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','66'])).

thf('68',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68','69','70'])).

thf('72',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,(
    r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['54','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf('77',plain,(
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

thf('78',plain,(
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
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','79'])).

thf('81',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('83',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('84',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['80','81','82','83','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ~ ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['74','87'])).

thf('89',plain,
    ( ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C ) @ sk_B )
   <= ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(split,[status(esa)],['52'])).

thf('90',plain,(
    r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ~ ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) )
    | ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(split,[status(esa)],['52'])).

thf('92',plain,(
    ~ ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['53','92'])).

thf('94',plain,(
    ~ ( m1_subset_1 @ ( k15_lattice3 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['51','93'])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['4','94'])).

thf('96',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['95','96','97','98'])).

thf('100',plain,(
    $false ),
    inference(demod,[status(thm)],['0','99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.c62mBOawbK
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:34:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.43/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.61  % Solved by: fo/fo7.sh
% 0.43/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.61  % done 155 iterations in 0.141s
% 0.43/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.61  % SZS output start Refutation
% 0.43/0.61  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 0.43/0.61  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.43/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.61  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.43/0.61  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.43/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.43/0.61  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.43/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.43/0.61  thf(r3_lattice3_type, type, r3_lattice3: $i > $i > $i > $o).
% 0.43/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.61  thf(r4_lattice3_type, type, r4_lattice3: $i > $i > $i > $o).
% 0.43/0.61  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.43/0.61  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.43/0.61  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.43/0.61  thf(a_2_2_lattice3_type, type, a_2_2_lattice3: $i > $i > $i).
% 0.43/0.61  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 0.43/0.61  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 0.43/0.61  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 0.43/0.61  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.43/0.61  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.43/0.61  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.43/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.43/0.61  thf(t38_lattice3, conjecture,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.43/0.61         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.43/0.61       ( ![B:$i]:
% 0.43/0.61         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.61           ( ![C:$i]:
% 0.43/0.61             ( ( r2_hidden @ B @ C ) =>
% 0.43/0.61               ( ( r3_lattices @ A @ B @ ( k15_lattice3 @ A @ C ) ) & 
% 0.43/0.61                 ( r3_lattices @ A @ ( k16_lattice3 @ A @ C ) @ B ) ) ) ) ) ) ))).
% 0.43/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.61    (~( ![A:$i]:
% 0.43/0.61        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.43/0.61            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.43/0.61          ( ![B:$i]:
% 0.43/0.61            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.61              ( ![C:$i]:
% 0.43/0.61                ( ( r2_hidden @ B @ C ) =>
% 0.43/0.61                  ( ( r3_lattices @ A @ B @ ( k15_lattice3 @ A @ C ) ) & 
% 0.43/0.61                    ( r3_lattices @ A @ ( k16_lattice3 @ A @ C ) @ B ) ) ) ) ) ) ) )),
% 0.43/0.61    inference('cnf.neg', [status(esa)], [t38_lattice3])).
% 0.43/0.61  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(t37_lattice3, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.43/0.61         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.43/0.61       ( ![B:$i]:
% 0.43/0.61         ( ( k15_lattice3 @ A @ B ) =
% 0.43/0.61           ( k16_lattice3 @ A @ ( a_2_2_lattice3 @ A @ B ) ) ) ) ))).
% 0.43/0.61  thf('1', plain,
% 0.43/0.61      (![X25 : $i, X26 : $i]:
% 0.43/0.61         (((k15_lattice3 @ X25 @ X26)
% 0.43/0.61            = (k16_lattice3 @ X25 @ (a_2_2_lattice3 @ X25 @ X26)))
% 0.43/0.61          | ~ (l3_lattices @ X25)
% 0.43/0.61          | ~ (v4_lattice3 @ X25)
% 0.43/0.61          | ~ (v10_lattices @ X25)
% 0.43/0.61          | (v2_struct_0 @ X25))),
% 0.43/0.61      inference('cnf', [status(esa)], [t37_lattice3])).
% 0.43/0.61  thf(dt_k16_lattice3, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.43/0.61       ( m1_subset_1 @ ( k16_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.43/0.61  thf('2', plain,
% 0.43/0.61      (![X18 : $i, X19 : $i]:
% 0.43/0.61         (~ (l3_lattices @ X18)
% 0.43/0.61          | (v2_struct_0 @ X18)
% 0.43/0.61          | (m1_subset_1 @ (k16_lattice3 @ X18 @ X19) @ (u1_struct_0 @ X18)))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.43/0.61  thf('3', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         ((m1_subset_1 @ (k15_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1))
% 0.43/0.61          | (v2_struct_0 @ X1)
% 0.43/0.61          | ~ (v10_lattices @ X1)
% 0.43/0.61          | ~ (v4_lattice3 @ X1)
% 0.43/0.61          | ~ (l3_lattices @ X1)
% 0.43/0.61          | (v2_struct_0 @ X1)
% 0.43/0.61          | ~ (l3_lattices @ X1))),
% 0.43/0.61      inference('sup+', [status(thm)], ['1', '2'])).
% 0.43/0.61  thf('4', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (~ (l3_lattices @ X1)
% 0.43/0.61          | ~ (v4_lattice3 @ X1)
% 0.43/0.61          | ~ (v10_lattices @ X1)
% 0.43/0.61          | (v2_struct_0 @ X1)
% 0.43/0.61          | (m1_subset_1 @ (k15_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1)))),
% 0.43/0.61      inference('simplify', [status(thm)], ['3'])).
% 0.43/0.61  thf('5', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('6', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('7', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (~ (l3_lattices @ X1)
% 0.43/0.61          | ~ (v4_lattice3 @ X1)
% 0.43/0.61          | ~ (v10_lattices @ X1)
% 0.43/0.61          | (v2_struct_0 @ X1)
% 0.43/0.61          | (m1_subset_1 @ (k15_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1)))),
% 0.43/0.61      inference('simplify', [status(thm)], ['3'])).
% 0.43/0.61  thf(d21_lattice3, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.43/0.61       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.43/0.61           ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.43/0.61         ( ![B:$i,C:$i]:
% 0.43/0.61           ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.61             ( ( ( C ) = ( k15_lattice3 @ A @ B ) ) <=>
% 0.43/0.61               ( ( r4_lattice3 @ A @ C @ B ) & 
% 0.43/0.61                 ( ![D:$i]:
% 0.43/0.61                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.61                     ( ( r4_lattice3 @ A @ D @ B ) =>
% 0.43/0.61                       ( r1_lattices @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.43/0.61  thf('8', plain,
% 0.43/0.61      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.43/0.61         ((v2_struct_0 @ X14)
% 0.43/0.61          | ~ (v10_lattices @ X14)
% 0.43/0.61          | ~ (v4_lattice3 @ X14)
% 0.43/0.61          | ~ (l3_lattices @ X14)
% 0.43/0.61          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.43/0.61          | ((X15) != (k15_lattice3 @ X14 @ X16))
% 0.43/0.61          | (r4_lattice3 @ X14 @ X15 @ X16)
% 0.43/0.61          | ~ (l3_lattices @ X14)
% 0.43/0.61          | (v2_struct_0 @ X14))),
% 0.43/0.61      inference('cnf', [status(esa)], [d21_lattice3])).
% 0.43/0.61  thf('9', plain,
% 0.43/0.61      (![X14 : $i, X16 : $i]:
% 0.43/0.61         ((r4_lattice3 @ X14 @ (k15_lattice3 @ X14 @ X16) @ X16)
% 0.43/0.61          | ~ (m1_subset_1 @ (k15_lattice3 @ X14 @ X16) @ (u1_struct_0 @ X14))
% 0.43/0.61          | ~ (l3_lattices @ X14)
% 0.43/0.61          | ~ (v4_lattice3 @ X14)
% 0.43/0.61          | ~ (v10_lattices @ X14)
% 0.43/0.61          | (v2_struct_0 @ X14))),
% 0.43/0.61      inference('simplify', [status(thm)], ['8'])).
% 0.43/0.61  thf('10', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         ((v2_struct_0 @ X0)
% 0.43/0.61          | ~ (v10_lattices @ X0)
% 0.43/0.61          | ~ (v4_lattice3 @ X0)
% 0.43/0.61          | ~ (l3_lattices @ X0)
% 0.43/0.61          | (v2_struct_0 @ X0)
% 0.43/0.61          | ~ (v10_lattices @ X0)
% 0.43/0.61          | ~ (v4_lattice3 @ X0)
% 0.43/0.61          | ~ (l3_lattices @ X0)
% 0.43/0.61          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X1))),
% 0.43/0.61      inference('sup-', [status(thm)], ['7', '9'])).
% 0.43/0.61  thf('11', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         ((r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X1)
% 0.43/0.61          | ~ (l3_lattices @ X0)
% 0.43/0.61          | ~ (v4_lattice3 @ X0)
% 0.43/0.61          | ~ (v10_lattices @ X0)
% 0.43/0.61          | (v2_struct_0 @ X0))),
% 0.43/0.61      inference('simplify', [status(thm)], ['10'])).
% 0.43/0.61  thf('12', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (~ (l3_lattices @ X1)
% 0.43/0.61          | ~ (v4_lattice3 @ X1)
% 0.43/0.61          | ~ (v10_lattices @ X1)
% 0.43/0.61          | (v2_struct_0 @ X1)
% 0.43/0.61          | (m1_subset_1 @ (k15_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1)))),
% 0.43/0.61      inference('simplify', [status(thm)], ['3'])).
% 0.43/0.61  thf(d17_lattice3, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.43/0.61       ( ![B:$i]:
% 0.43/0.61         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.61           ( ![C:$i]:
% 0.43/0.61             ( ( r4_lattice3 @ A @ B @ C ) <=>
% 0.43/0.61               ( ![D:$i]:
% 0.43/0.61                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.61                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ))).
% 0.43/0.61  thf('13', plain,
% 0.43/0.61      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.43/0.61          | ~ (r4_lattice3 @ X10 @ X9 @ X11)
% 0.43/0.61          | ~ (r2_hidden @ X12 @ X11)
% 0.43/0.61          | (r1_lattices @ X10 @ X12 @ X9)
% 0.43/0.61          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X10))
% 0.43/0.61          | ~ (l3_lattices @ X10)
% 0.43/0.61          | (v2_struct_0 @ X10))),
% 0.43/0.61      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.43/0.61  thf('14', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.61         ((v2_struct_0 @ X0)
% 0.43/0.61          | ~ (v10_lattices @ X0)
% 0.43/0.61          | ~ (v4_lattice3 @ X0)
% 0.43/0.61          | ~ (l3_lattices @ X0)
% 0.43/0.61          | (v2_struct_0 @ X0)
% 0.43/0.61          | ~ (l3_lattices @ X0)
% 0.43/0.61          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.43/0.61          | (r1_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))
% 0.43/0.61          | ~ (r2_hidden @ X2 @ X3)
% 0.43/0.61          | ~ (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X3))),
% 0.43/0.61      inference('sup-', [status(thm)], ['12', '13'])).
% 0.43/0.61  thf('15', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.61         (~ (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X3)
% 0.43/0.61          | ~ (r2_hidden @ X2 @ X3)
% 0.43/0.61          | (r1_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))
% 0.43/0.61          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.43/0.61          | ~ (l3_lattices @ X0)
% 0.43/0.61          | ~ (v4_lattice3 @ X0)
% 0.43/0.61          | ~ (v10_lattices @ X0)
% 0.43/0.61          | (v2_struct_0 @ X0))),
% 0.43/0.61      inference('simplify', [status(thm)], ['14'])).
% 0.43/0.61  thf('16', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.61         ((v2_struct_0 @ X1)
% 0.43/0.61          | ~ (v10_lattices @ X1)
% 0.43/0.61          | ~ (v4_lattice3 @ X1)
% 0.43/0.61          | ~ (l3_lattices @ X1)
% 0.43/0.61          | (v2_struct_0 @ X1)
% 0.43/0.61          | ~ (v10_lattices @ X1)
% 0.43/0.61          | ~ (v4_lattice3 @ X1)
% 0.43/0.61          | ~ (l3_lattices @ X1)
% 0.43/0.61          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.43/0.61          | (r1_lattices @ X1 @ X2 @ (k15_lattice3 @ X1 @ X0))
% 0.43/0.61          | ~ (r2_hidden @ X2 @ X0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['11', '15'])).
% 0.43/0.61  thf('17', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.61         (~ (r2_hidden @ X2 @ X0)
% 0.43/0.61          | (r1_lattices @ X1 @ X2 @ (k15_lattice3 @ X1 @ X0))
% 0.43/0.61          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.43/0.61          | ~ (l3_lattices @ X1)
% 0.43/0.61          | ~ (v4_lattice3 @ X1)
% 0.43/0.61          | ~ (v10_lattices @ X1)
% 0.43/0.61          | (v2_struct_0 @ X1))),
% 0.43/0.61      inference('simplify', [status(thm)], ['16'])).
% 0.43/0.61  thf('18', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((v2_struct_0 @ sk_A)
% 0.43/0.61          | ~ (v10_lattices @ sk_A)
% 0.43/0.61          | ~ (v4_lattice3 @ sk_A)
% 0.43/0.61          | ~ (l3_lattices @ sk_A)
% 0.43/0.61          | (r1_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ X0))
% 0.43/0.61          | ~ (r2_hidden @ sk_B @ X0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['6', '17'])).
% 0.43/0.61  thf('19', plain, ((v10_lattices @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('20', plain, ((v4_lattice3 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('21', plain, ((l3_lattices @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('22', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((v2_struct_0 @ sk_A)
% 0.43/0.61          | (r1_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ X0))
% 0.43/0.61          | ~ (r2_hidden @ sk_B @ X0))),
% 0.43/0.61      inference('demod', [status(thm)], ['18', '19', '20', '21'])).
% 0.43/0.61  thf('23', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('24', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (r2_hidden @ sk_B @ X0)
% 0.43/0.61          | (r1_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ X0)))),
% 0.43/0.61      inference('clc', [status(thm)], ['22', '23'])).
% 0.43/0.61  thf('25', plain,
% 0.43/0.61      ((r1_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C))),
% 0.43/0.61      inference('sup-', [status(thm)], ['5', '24'])).
% 0.43/0.61  thf('26', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(redefinition_r3_lattices, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i]:
% 0.43/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.43/0.61         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 0.43/0.61         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.43/0.61         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.61       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 0.43/0.61  thf('27', plain,
% 0.43/0.61      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.43/0.61          | ~ (l3_lattices @ X2)
% 0.43/0.61          | ~ (v9_lattices @ X2)
% 0.43/0.61          | ~ (v8_lattices @ X2)
% 0.43/0.61          | ~ (v6_lattices @ X2)
% 0.43/0.61          | (v2_struct_0 @ X2)
% 0.43/0.61          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.43/0.61          | (r3_lattices @ X2 @ X1 @ X3)
% 0.43/0.61          | ~ (r1_lattices @ X2 @ X1 @ X3))),
% 0.43/0.61      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.43/0.61  thf('28', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (r1_lattices @ sk_A @ sk_B @ X0)
% 0.43/0.61          | (r3_lattices @ sk_A @ sk_B @ X0)
% 0.43/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.43/0.61          | (v2_struct_0 @ sk_A)
% 0.43/0.61          | ~ (v6_lattices @ sk_A)
% 0.43/0.61          | ~ (v8_lattices @ sk_A)
% 0.43/0.61          | ~ (v9_lattices @ sk_A)
% 0.43/0.61          | ~ (l3_lattices @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['26', '27'])).
% 0.43/0.61  thf(cc1_lattices, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( l3_lattices @ A ) =>
% 0.43/0.61       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.43/0.61         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.43/0.61           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.43/0.61           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.43/0.61  thf('29', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((v2_struct_0 @ X0)
% 0.43/0.61          | ~ (v10_lattices @ X0)
% 0.43/0.61          | (v6_lattices @ X0)
% 0.43/0.61          | ~ (l3_lattices @ X0))),
% 0.43/0.61      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.43/0.61  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('31', plain,
% 0.43/0.61      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['29', '30'])).
% 0.43/0.61  thf('32', plain, ((l3_lattices @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('33', plain, ((v10_lattices @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('34', plain, ((v6_lattices @ sk_A)),
% 0.43/0.61      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.43/0.61  thf('35', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((v2_struct_0 @ X0)
% 0.43/0.61          | ~ (v10_lattices @ X0)
% 0.43/0.61          | (v8_lattices @ X0)
% 0.43/0.61          | ~ (l3_lattices @ X0))),
% 0.43/0.61      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.43/0.61  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('37', plain,
% 0.43/0.61      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['35', '36'])).
% 0.43/0.61  thf('38', plain, ((l3_lattices @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('39', plain, ((v10_lattices @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('40', plain, ((v8_lattices @ sk_A)),
% 0.43/0.61      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.43/0.61  thf('41', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((v2_struct_0 @ X0)
% 0.43/0.61          | ~ (v10_lattices @ X0)
% 0.43/0.61          | (v9_lattices @ X0)
% 0.43/0.61          | ~ (l3_lattices @ X0))),
% 0.43/0.61      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.43/0.61  thf('42', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('43', plain,
% 0.43/0.61      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['41', '42'])).
% 0.43/0.61  thf('44', plain, ((l3_lattices @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('45', plain, ((v10_lattices @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('46', plain, ((v9_lattices @ sk_A)),
% 0.43/0.61      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.43/0.61  thf('47', plain, ((l3_lattices @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('48', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (r1_lattices @ sk_A @ sk_B @ X0)
% 0.43/0.61          | (r3_lattices @ sk_A @ sk_B @ X0)
% 0.43/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.43/0.61          | (v2_struct_0 @ sk_A))),
% 0.43/0.61      inference('demod', [status(thm)], ['28', '34', '40', '46', '47'])).
% 0.43/0.61  thf('49', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | ~ (m1_subset_1 @ (k15_lattice3 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.43/0.61        | (r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['25', '48'])).
% 0.43/0.61  thf('50', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('51', plain,
% 0.43/0.61      (((r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C))
% 0.43/0.61        | ~ (m1_subset_1 @ (k15_lattice3 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('clc', [status(thm)], ['49', '50'])).
% 0.43/0.61  thf('52', plain,
% 0.43/0.61      ((~ (r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C))
% 0.43/0.61        | ~ (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C) @ sk_B))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('53', plain,
% 0.43/0.61      ((~ (r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C)))
% 0.43/0.61         <= (~ ((r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C))))),
% 0.43/0.61      inference('split', [status(esa)], ['52'])).
% 0.43/0.61  thf('54', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('55', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('56', plain,
% 0.43/0.61      (![X18 : $i, X19 : $i]:
% 0.43/0.61         (~ (l3_lattices @ X18)
% 0.43/0.61          | (v2_struct_0 @ X18)
% 0.43/0.61          | (m1_subset_1 @ (k16_lattice3 @ X18 @ X19) @ (u1_struct_0 @ X18)))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.43/0.61  thf(t34_lattice3, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.43/0.61         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.43/0.61       ( ![B:$i]:
% 0.43/0.61         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.61           ( ![C:$i]:
% 0.43/0.61             ( ( ( B ) = ( k16_lattice3 @ A @ C ) ) <=>
% 0.43/0.61               ( ( r3_lattice3 @ A @ B @ C ) & 
% 0.43/0.61                 ( ![D:$i]:
% 0.43/0.61                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.61                     ( ( r3_lattice3 @ A @ D @ C ) =>
% 0.43/0.61                       ( r3_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.43/0.61  thf('57', plain,
% 0.43/0.61      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.43/0.61          | ((X20) != (k16_lattice3 @ X21 @ X22))
% 0.43/0.61          | (r3_lattice3 @ X21 @ X20 @ X22)
% 0.43/0.61          | ~ (l3_lattices @ X21)
% 0.43/0.61          | ~ (v4_lattice3 @ X21)
% 0.43/0.61          | ~ (v10_lattices @ X21)
% 0.43/0.61          | (v2_struct_0 @ X21))),
% 0.43/0.61      inference('cnf', [status(esa)], [t34_lattice3])).
% 0.43/0.61  thf('58', plain,
% 0.43/0.61      (![X21 : $i, X22 : $i]:
% 0.43/0.61         ((v2_struct_0 @ X21)
% 0.43/0.61          | ~ (v10_lattices @ X21)
% 0.43/0.61          | ~ (v4_lattice3 @ X21)
% 0.43/0.61          | ~ (l3_lattices @ X21)
% 0.43/0.61          | (r3_lattice3 @ X21 @ (k16_lattice3 @ X21 @ X22) @ X22)
% 0.43/0.61          | ~ (m1_subset_1 @ (k16_lattice3 @ X21 @ X22) @ (u1_struct_0 @ X21)))),
% 0.43/0.61      inference('simplify', [status(thm)], ['57'])).
% 0.43/0.61  thf('59', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         ((v2_struct_0 @ X0)
% 0.43/0.61          | ~ (l3_lattices @ X0)
% 0.43/0.61          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X1)
% 0.43/0.61          | ~ (l3_lattices @ X0)
% 0.43/0.61          | ~ (v4_lattice3 @ X0)
% 0.43/0.61          | ~ (v10_lattices @ X0)
% 0.43/0.61          | (v2_struct_0 @ X0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['56', '58'])).
% 0.43/0.61  thf('60', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (~ (v10_lattices @ X0)
% 0.43/0.61          | ~ (v4_lattice3 @ X0)
% 0.43/0.61          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X1)
% 0.43/0.61          | ~ (l3_lattices @ X0)
% 0.43/0.61          | (v2_struct_0 @ X0))),
% 0.43/0.61      inference('simplify', [status(thm)], ['59'])).
% 0.43/0.61  thf('61', plain,
% 0.43/0.61      (![X18 : $i, X19 : $i]:
% 0.43/0.61         (~ (l3_lattices @ X18)
% 0.43/0.61          | (v2_struct_0 @ X18)
% 0.43/0.61          | (m1_subset_1 @ (k16_lattice3 @ X18 @ X19) @ (u1_struct_0 @ X18)))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.43/0.61  thf(d16_lattice3, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.43/0.61       ( ![B:$i]:
% 0.43/0.61         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.61           ( ![C:$i]:
% 0.43/0.61             ( ( r3_lattice3 @ A @ B @ C ) <=>
% 0.43/0.61               ( ![D:$i]:
% 0.43/0.61                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.61                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 0.43/0.61  thf('62', plain,
% 0.43/0.61      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.43/0.61          | ~ (r3_lattice3 @ X5 @ X4 @ X6)
% 0.43/0.61          | ~ (r2_hidden @ X7 @ X6)
% 0.43/0.61          | (r1_lattices @ X5 @ X4 @ X7)
% 0.43/0.61          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X5))
% 0.43/0.61          | ~ (l3_lattices @ X5)
% 0.43/0.61          | (v2_struct_0 @ X5))),
% 0.43/0.61      inference('cnf', [status(esa)], [d16_lattice3])).
% 0.43/0.61  thf('63', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.61         ((v2_struct_0 @ X0)
% 0.43/0.61          | ~ (l3_lattices @ X0)
% 0.43/0.61          | (v2_struct_0 @ X0)
% 0.43/0.61          | ~ (l3_lattices @ X0)
% 0.43/0.61          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.43/0.61          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.43/0.61          | ~ (r2_hidden @ X2 @ X3)
% 0.43/0.61          | ~ (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X3))),
% 0.43/0.61      inference('sup-', [status(thm)], ['61', '62'])).
% 0.43/0.61  thf('64', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.61         (~ (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X3)
% 0.43/0.61          | ~ (r2_hidden @ X2 @ X3)
% 0.43/0.61          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.43/0.61          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.43/0.61          | ~ (l3_lattices @ X0)
% 0.43/0.61          | (v2_struct_0 @ X0))),
% 0.43/0.61      inference('simplify', [status(thm)], ['63'])).
% 0.43/0.61  thf('65', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.61         ((v2_struct_0 @ X1)
% 0.43/0.61          | ~ (l3_lattices @ X1)
% 0.43/0.61          | ~ (v4_lattice3 @ X1)
% 0.43/0.61          | ~ (v10_lattices @ X1)
% 0.43/0.61          | (v2_struct_0 @ X1)
% 0.43/0.61          | ~ (l3_lattices @ X1)
% 0.43/0.61          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.43/0.61          | (r1_lattices @ X1 @ (k16_lattice3 @ X1 @ X0) @ X2)
% 0.43/0.61          | ~ (r2_hidden @ X2 @ X0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['60', '64'])).
% 0.43/0.61  thf('66', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.61         (~ (r2_hidden @ X2 @ X0)
% 0.43/0.61          | (r1_lattices @ X1 @ (k16_lattice3 @ X1 @ X0) @ X2)
% 0.43/0.61          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.43/0.61          | ~ (v10_lattices @ X1)
% 0.43/0.61          | ~ (v4_lattice3 @ X1)
% 0.43/0.61          | ~ (l3_lattices @ X1)
% 0.43/0.61          | (v2_struct_0 @ X1))),
% 0.43/0.61      inference('simplify', [status(thm)], ['65'])).
% 0.43/0.61  thf('67', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((v2_struct_0 @ sk_A)
% 0.43/0.61          | ~ (l3_lattices @ sk_A)
% 0.43/0.61          | ~ (v4_lattice3 @ sk_A)
% 0.43/0.61          | ~ (v10_lattices @ sk_A)
% 0.43/0.61          | (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.43/0.61          | ~ (r2_hidden @ sk_B @ X0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['55', '66'])).
% 0.43/0.61  thf('68', plain, ((l3_lattices @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('69', plain, ((v4_lattice3 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('70', plain, ((v10_lattices @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('71', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((v2_struct_0 @ sk_A)
% 0.43/0.61          | (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.43/0.61          | ~ (r2_hidden @ sk_B @ X0))),
% 0.43/0.61      inference('demod', [status(thm)], ['67', '68', '69', '70'])).
% 0.43/0.61  thf('72', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('73', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (r2_hidden @ sk_B @ X0)
% 0.43/0.61          | (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B))),
% 0.43/0.61      inference('clc', [status(thm)], ['71', '72'])).
% 0.43/0.61  thf('74', plain,
% 0.43/0.61      ((r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C) @ sk_B)),
% 0.43/0.61      inference('sup-', [status(thm)], ['54', '73'])).
% 0.43/0.61  thf('75', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('76', plain,
% 0.43/0.61      (![X18 : $i, X19 : $i]:
% 0.43/0.61         (~ (l3_lattices @ X18)
% 0.43/0.61          | (v2_struct_0 @ X18)
% 0.43/0.61          | (m1_subset_1 @ (k16_lattice3 @ X18 @ X19) @ (u1_struct_0 @ X18)))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.43/0.61  thf('77', plain,
% 0.43/0.61      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.43/0.61          | ~ (l3_lattices @ X2)
% 0.43/0.61          | ~ (v9_lattices @ X2)
% 0.43/0.61          | ~ (v8_lattices @ X2)
% 0.43/0.61          | ~ (v6_lattices @ X2)
% 0.43/0.61          | (v2_struct_0 @ X2)
% 0.43/0.61          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.43/0.61          | (r3_lattices @ X2 @ X1 @ X3)
% 0.43/0.61          | ~ (r1_lattices @ X2 @ X1 @ X3))),
% 0.43/0.61      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.43/0.61  thf('78', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.61         ((v2_struct_0 @ X0)
% 0.43/0.61          | ~ (l3_lattices @ X0)
% 0.43/0.61          | ~ (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.43/0.61          | (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.43/0.61          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.43/0.61          | (v2_struct_0 @ X0)
% 0.43/0.61          | ~ (v6_lattices @ X0)
% 0.43/0.61          | ~ (v8_lattices @ X0)
% 0.43/0.61          | ~ (v9_lattices @ X0)
% 0.43/0.61          | ~ (l3_lattices @ X0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['76', '77'])).
% 0.43/0.61  thf('79', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.61         (~ (v9_lattices @ X0)
% 0.43/0.61          | ~ (v8_lattices @ X0)
% 0.43/0.61          | ~ (v6_lattices @ X0)
% 0.43/0.61          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.43/0.61          | (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.43/0.61          | ~ (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.43/0.61          | ~ (l3_lattices @ X0)
% 0.43/0.61          | (v2_struct_0 @ X0))),
% 0.43/0.61      inference('simplify', [status(thm)], ['78'])).
% 0.43/0.61  thf('80', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((v2_struct_0 @ sk_A)
% 0.43/0.61          | ~ (l3_lattices @ sk_A)
% 0.43/0.61          | ~ (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.43/0.61          | (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.43/0.61          | ~ (v6_lattices @ sk_A)
% 0.43/0.61          | ~ (v8_lattices @ sk_A)
% 0.43/0.61          | ~ (v9_lattices @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['75', '79'])).
% 0.43/0.61  thf('81', plain, ((l3_lattices @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('82', plain, ((v6_lattices @ sk_A)),
% 0.43/0.61      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.43/0.61  thf('83', plain, ((v8_lattices @ sk_A)),
% 0.43/0.61      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.43/0.61  thf('84', plain, ((v9_lattices @ sk_A)),
% 0.43/0.61      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.43/0.61  thf('85', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((v2_struct_0 @ sk_A)
% 0.43/0.61          | ~ (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.43/0.61          | (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B))),
% 0.43/0.61      inference('demod', [status(thm)], ['80', '81', '82', '83', '84'])).
% 0.43/0.61  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('87', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.43/0.61          | ~ (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B))),
% 0.43/0.61      inference('clc', [status(thm)], ['85', '86'])).
% 0.43/0.61  thf('88', plain,
% 0.43/0.61      ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C) @ sk_B)),
% 0.43/0.61      inference('sup-', [status(thm)], ['74', '87'])).
% 0.43/0.61  thf('89', plain,
% 0.43/0.61      ((~ (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C) @ sk_B))
% 0.43/0.61         <= (~ ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C) @ sk_B)))),
% 0.43/0.61      inference('split', [status(esa)], ['52'])).
% 0.43/0.61  thf('90', plain,
% 0.43/0.61      (((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C) @ sk_B))),
% 0.43/0.61      inference('sup-', [status(thm)], ['88', '89'])).
% 0.43/0.61  thf('91', plain,
% 0.43/0.61      (~ ((r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C))) | 
% 0.43/0.61       ~ ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C) @ sk_B))),
% 0.43/0.61      inference('split', [status(esa)], ['52'])).
% 0.43/0.61  thf('92', plain,
% 0.43/0.61      (~ ((r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C)))),
% 0.43/0.61      inference('sat_resolution*', [status(thm)], ['90', '91'])).
% 0.43/0.61  thf('93', plain,
% 0.43/0.61      (~ (r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C))),
% 0.43/0.61      inference('simpl_trail', [status(thm)], ['53', '92'])).
% 0.43/0.61  thf('94', plain,
% 0.43/0.61      (~ (m1_subset_1 @ (k15_lattice3 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.43/0.61      inference('clc', [status(thm)], ['51', '93'])).
% 0.43/0.61  thf('95', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | ~ (v10_lattices @ sk_A)
% 0.43/0.61        | ~ (v4_lattice3 @ sk_A)
% 0.43/0.61        | ~ (l3_lattices @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['4', '94'])).
% 0.43/0.61  thf('96', plain, ((v10_lattices @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('97', plain, ((v4_lattice3 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('98', plain, ((l3_lattices @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('99', plain, ((v2_struct_0 @ sk_A)),
% 0.43/0.61      inference('demod', [status(thm)], ['95', '96', '97', '98'])).
% 0.43/0.61  thf('100', plain, ($false), inference('demod', [status(thm)], ['0', '99'])).
% 0.43/0.61  
% 0.43/0.61  % SZS output end Refutation
% 0.43/0.61  
% 0.43/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
