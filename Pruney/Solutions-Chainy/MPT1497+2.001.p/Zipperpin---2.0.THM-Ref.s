%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LT7B6ACSD2

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:26 EST 2020

% Result     : Theorem 1.93s
% Output     : Refutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :  363 (4537 expanded)
%              Number of leaves         :   44 (1275 expanded)
%              Depth                    :   55
%              Number of atoms          : 4329 (70118 expanded)
%              Number of equality atoms :   36 ( 420 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k4_lattice3_type,type,(
    k4_lattice3: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(r4_lattice3_type,type,(
    r4_lattice3: $i > $i > $i > $o )).

thf(k5_lattice3_type,type,(
    k5_lattice3: $i > $i > $i )).

thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(t30_lattice3,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( v10_lattices @ B )
        & ( l3_lattices @ B ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
         => ( ( r4_lattice3 @ B @ C @ A )
          <=> ( r2_lattice3 @ ( k3_lattice3 @ B ) @ A @ ( k4_lattice3 @ B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ~ ( v2_struct_0 @ B )
          & ( v10_lattices @ B )
          & ( l3_lattices @ B ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
           => ( ( r4_lattice3 @ B @ C @ A )
            <=> ( r2_lattice3 @ ( k3_lattice3 @ B ) @ A @ ( k4_lattice3 @ B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t30_lattice3])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A ) )
     => ( ( v1_orders_2 @ ( k3_lattice3 @ A ) )
        & ( v3_orders_2 @ ( k3_lattice3 @ A ) )
        & ( v4_orders_2 @ ( k3_lattice3 @ A ) )
        & ( v5_orders_2 @ ( k3_lattice3 @ A ) )
        & ( l1_orders_2 @ ( k3_lattice3 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X20: $i] :
      ( ( l1_orders_2 @ ( k3_lattice3 @ X20 ) )
      | ~ ( l3_lattices @ X20 )
      | ~ ( v10_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_lattice3])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k4_lattice3 @ A @ B ) @ ( u1_struct_0 @ ( k3_lattice3 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l3_lattices @ X21 )
      | ~ ( v10_lattices @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ( m1_subset_1 @ ( k4_lattice3 @ X21 @ X22 ) @ ( u1_struct_0 @ ( k3_lattice3 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_lattice3])).

thf('4',plain,
    ( ( m1_subset_1 @ ( k4_lattice3 @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v10_lattices @ sk_B )
    | ~ ( l3_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k4_lattice3 @ A @ B )
            = B ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ( ( k4_lattice3 @ X13 @ X12 )
        = X12 )
      | ~ ( l3_lattices @ X13 )
      | ~ ( v10_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_lattice3])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v10_lattices @ sk_B )
    | ~ ( l3_lattices @ sk_B )
    | ( ( k4_lattice3 @ sk_B @ sk_C )
      = sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k4_lattice3 @ sk_B @ sk_C )
      = sk_C ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( k4_lattice3 @ sk_B @ sk_C )
    = sk_C ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['4','12','13','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf(d9_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ( ( r2_lattice3 @ A @ B @ C )
          <=> ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ D @ B )
                 => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) )).

thf('18',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X16 @ X18 @ X17 ) @ ( u1_struct_0 @ X17 ) )
      | ( r2_lattice3 @ X17 @ X18 @ X16 )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ ( k3_lattice3 @ sk_B ) )
      | ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','19'])).

thf('21',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf(d4_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k3_lattice3 @ A ) ) )
         => ( ( k5_lattice3 @ A @ B )
            = B ) ) ) )).

thf('26',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ ( k3_lattice3 @ X15 ) ) )
      | ( ( k5_lattice3 @ X15 @ X14 )
        = X14 )
      | ~ ( l3_lattices @ X15 )
      | ~ ( v10_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_lattice3])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ( ( k5_lattice3 @ sk_B @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) )
        = ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( ( k5_lattice3 @ sk_B @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) )
        = ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k5_lattice3 @ sk_B @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) )
        = ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf(dt_k5_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k3_lattice3 @ A ) ) ) )
     => ( m1_subset_1 @ ( k5_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('34',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l3_lattices @ X23 )
      | ~ ( v10_lattices @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ ( k3_lattice3 @ X23 ) ) )
      | ( m1_subset_1 @ ( k5_lattice3 @ X23 @ X24 ) @ ( u1_struct_0 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattice3])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ( m1_subset_1 @ ( k5_lattice3 @ sk_B @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ( m1_subset_1 @ ( k5_lattice3 @ sk_B @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_lattice3 @ sk_B @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['32','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ( ( k4_lattice3 @ X13 @ X12 )
        = X12 )
      | ~ ( l3_lattices @ X13 )
      | ~ ( v10_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_lattice3])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ( ( k4_lattice3 @ sk_B @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) )
        = ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( ( k4_lattice3 @ sk_B @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) )
        = ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattice3 @ sk_B @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) )
        = ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) )
    | ( r4_lattice3 @ sk_B @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( r4_lattice3 @ sk_B @ sk_C @ sk_A )
   <= ( r4_lattice3 @ sk_B @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['50'])).

thf('52',plain,(
    ! [X20: $i] :
      ( ( l1_orders_2 @ ( k3_lattice3 @ X20 ) )
      | ~ ( l3_lattices @ X20 )
      | ~ ( v10_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_lattice3])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('54',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ( r2_hidden @ ( sk_D_1 @ X16 @ X18 @ X17 ) @ X18 )
      | ( r2_lattice3 @ X17 @ X18 @ X16 )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ ( k3_lattice3 @ sk_B ) )
      | ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ X0 )
      | ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ X0 )
      | ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('64',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r4_lattice3 @ X8 @ X7 @ X9 )
      | ~ ( r2_hidden @ X10 @ X9 )
      | ( r1_lattices @ X8 @ X10 @ X7 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l3_lattices @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_lattices @ sk_B @ X0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r4_lattice3 @ sk_B @ sk_C @ X1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_lattices @ sk_B @ X0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r4_lattice3 @ sk_B @ sk_C @ X1 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ~ ( r4_lattice3 @ sk_B @ sk_C @ X1 )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ X1 )
      | ( r1_lattices @ sk_B @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ sk_C )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['62','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( r1_lattices @ sk_B @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ sk_C )
      | ~ ( r4_lattice3 @ sk_B @ sk_C @ X0 )
      | ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['61','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r4_lattice3 @ sk_B @ sk_C @ X0 )
      | ( r1_lattices @ sk_B @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ( ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( r1_lattices @ sk_B @ ( sk_D_1 @ sk_C @ sk_A @ ( k3_lattice3 @ sk_B ) ) @ sk_C ) )
   <= ( r4_lattice3 @ sk_B @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['51','70'])).

thf('72',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( r1_lattices @ sk_B @ ( sk_D_1 @ sk_C @ sk_A @ ( k3_lattice3 @ sk_B ) ) @ sk_C )
      | ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C ) )
   <= ( r4_lattice3 @ sk_B @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

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

thf('75',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l3_lattices @ X5 )
      | ~ ( v9_lattices @ X5 )
      | ~ ( v8_lattices @ X5 )
      | ~ ( v6_lattices @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ( r3_lattices @ X5 @ X4 @ X6 )
      | ~ ( r1_lattices @ X5 @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ~ ( r1_lattices @ sk_B @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ X1 )
      | ( r3_lattices @ sk_B @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v6_lattices @ sk_B )
      | ~ ( v8_lattices @ sk_B )
      | ~ ( v9_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

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

thf('77',plain,(
    ! [X3: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( v10_lattices @ X3 )
      | ( v6_lattices @ X3 )
      | ~ ( l3_lattices @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ~ ( l3_lattices @ sk_B )
    | ( v6_lattices @ sk_B )
    | ~ ( v10_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v6_lattices @ sk_B ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,(
    ! [X3: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( v10_lattices @ X3 )
      | ( v8_lattices @ X3 )
      | ~ ( l3_lattices @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ~ ( l3_lattices @ sk_B )
    | ( v8_lattices @ sk_B )
    | ~ ( v10_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v8_lattices @ sk_B ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,(
    ! [X3: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( v10_lattices @ X3 )
      | ( v9_lattices @ X3 )
      | ~ ( l3_lattices @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ~ ( l3_lattices @ sk_B )
    | ( v9_lattices @ sk_B )
    | ~ ( v10_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v9_lattices @ sk_B ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ~ ( r1_lattices @ sk_B @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ X1 )
      | ( r3_lattices @ sk_B @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['76','82','88','94','95'])).

thf('97',plain,
    ( ( ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) )
      | ( r3_lattices @ sk_B @ ( sk_D_1 @ sk_C @ sk_A @ ( k3_lattice3 @ sk_B ) ) @ sk_C )
      | ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C ) )
   <= ( r4_lattice3 @ sk_B @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['73','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( r3_lattices @ sk_B @ ( sk_D_1 @ sk_C @ sk_A @ ( k3_lattice3 @ sk_B ) ) @ sk_C )
      | ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C ) )
   <= ( r4_lattice3 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ( r3_lattices @ sk_B @ ( sk_D_1 @ sk_C @ sk_A @ ( k3_lattice3 @ sk_B ) ) @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C ) )
   <= ( r4_lattice3 @ sk_B @ sk_C @ sk_A ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C )
      | ( r3_lattices @ sk_B @ ( sk_D_1 @ sk_C @ sk_A @ ( k3_lattice3 @ sk_B ) ) @ sk_C ) )
   <= ( r4_lattice3 @ sk_B @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,
    ( ~ ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) )
    | ~ ( r4_lattice3 @ sk_B @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ~ ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) )
    | ~ ( r4_lattice3 @ sk_B @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['103'])).

thf('105',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ( m1_subset_1 @ ( sk_D @ X11 @ X7 @ X8 ) @ ( u1_struct_0 @ X8 ) )
      | ( r4_lattice3 @ X8 @ X7 @ X11 )
      | ~ ( l3_lattices @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ( r4_lattice3 @ sk_B @ sk_C @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r4_lattice3 @ sk_B @ sk_C @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
      | ( r4_lattice3 @ sk_B @ sk_C @ X0 ) ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ( ( k4_lattice3 @ X13 @ X12 )
        = X12 )
      | ~ ( l3_lattices @ X13 )
      | ~ ( v10_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_lattice3])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_B @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ( ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) )
        = ( sk_D @ X0 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_B @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) )
        = ( sk_D @ X0 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) )
        = ( sk_D @ X0 @ sk_C @ sk_B ) )
      | ( r4_lattice3 @ sk_B @ sk_C @ X0 ) ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('119',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X7 @ X8 ) @ X11 )
      | ( r4_lattice3 @ X8 @ X7 @ X11 )
      | ~ ( l3_lattices @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ( r4_lattice3 @ sk_B @ sk_C @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_C @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r4_lattice3 @ sk_B @ sk_C @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_C @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ sk_C @ sk_B ) @ X0 )
      | ( r4_lattice3 @ sk_B @ sk_C @ X0 ) ) ),
    inference(clc,[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) )
        = ( sk_D @ X0 @ sk_C @ sk_B ) )
      | ( r4_lattice3 @ sk_B @ sk_C @ X0 ) ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
      | ( r4_lattice3 @ sk_B @ sk_C @ X0 ) ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('128',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l3_lattices @ X21 )
      | ~ ( v10_lattices @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ( m1_subset_1 @ ( k4_lattice3 @ X21 @ X22 ) @ ( u1_struct_0 @ ( k3_lattice3 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_lattice3])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_B @ sk_C @ X0 )
      | ( m1_subset_1 @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_B @ sk_C @ X0 )
      | ( m1_subset_1 @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( r4_lattice3 @ sk_B @ sk_C @ X0 ) ) ),
    inference(clc,[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ sk_B ) @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( r4_lattice3 @ sk_B @ sk_C @ X0 )
      | ( r4_lattice3 @ sk_B @ sk_C @ X0 ) ) ),
    inference('sup+',[status(thm)],['126','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_B @ sk_C @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ sk_B ) @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,
    ( ( k4_lattice3 @ sk_B @ sk_C )
    = sk_C ),
    inference(clc,[status(thm)],['10','11'])).

thf('138',plain,
    ( ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) )
   <= ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['50'])).

thf('139',plain,
    ( ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C )
   <= ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X20: $i] :
      ( ( l1_orders_2 @ ( k3_lattice3 @ X20 ) )
      | ~ ( l3_lattices @ X20 )
      | ~ ( v10_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_lattice3])).

thf('141',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('142',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ~ ( r2_lattice3 @ X17 @ X18 @ X16 )
      | ~ ( r2_hidden @ X19 @ X18 )
      | ( r1_orders_2 @ X17 @ X19 @ X16 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ ( k3_lattice3 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ~ ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['140','143'])).

thf('145',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['144','145','146'])).

thf('148',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
        | ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['139','147'])).

thf('149',plain,
    ( ! [X0: $i] :
        ( ( r4_lattice3 @ sk_B @ sk_C @ X0 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( r2_hidden @ ( sk_D @ X0 @ sk_C @ sk_B ) @ sk_A )
        | ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D @ X0 @ sk_C @ sk_B ) @ sk_C ) )
   <= ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['136','148'])).

thf('150',plain,
    ( ( ( r4_lattice3 @ sk_B @ sk_C @ sk_A )
      | ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D @ sk_A @ sk_C @ sk_B ) @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( r4_lattice3 @ sk_B @ sk_C @ sk_A ) )
   <= ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['125','149'])).

thf('151',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D @ sk_A @ sk_C @ sk_B ) @ sk_C )
      | ( r4_lattice3 @ sk_B @ sk_C @ sk_A ) )
   <= ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( ( r4_lattice3 @ sk_B @ sk_C @ sk_A )
      | ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D @ sk_A @ sk_C @ sk_B ) @ sk_C ) )
   <= ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X20: $i] :
      ( ( l1_orders_2 @ ( k3_lattice3 @ X20 ) )
      | ~ ( l3_lattices @ X20 )
      | ~ ( v10_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_lattice3])).

thf('155',plain,(
    ! [X20: $i] :
      ( ( v3_orders_2 @ ( k3_lattice3 @ X20 ) )
      | ~ ( l3_lattices @ X20 )
      | ~ ( v10_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_lattice3])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_B @ sk_C @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ sk_B ) @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf(redefinition_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_orders_2 @ A @ B @ C )
      <=> ( r1_orders_2 @ A @ B @ C ) ) ) )).

thf('157',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r3_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( r1_orders_2 @ X1 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_B @ sk_C @ X0 )
      | ~ ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D @ X0 @ sk_C @ sk_B ) @ X1 )
      | ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D @ X0 @ sk_C @ sk_B ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ~ ( v3_orders_2 @ ( k3_lattice3 @ sk_B ) )
      | ~ ( l1_orders_2 @ ( k3_lattice3 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ~ ( l1_orders_2 @ ( k3_lattice3 @ sk_B ) )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D @ X1 @ sk_C @ sk_B ) @ X0 )
      | ~ ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D @ X1 @ sk_C @ sk_B ) @ X0 )
      | ( r4_lattice3 @ sk_B @ sk_C @ X1 ) ) ),
    inference('sup-',[status(thm)],['155','158'])).

thf('160',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( l1_orders_2 @ ( k3_lattice3 @ sk_B ) )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D @ X1 @ sk_C @ sk_B ) @ X0 )
      | ~ ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D @ X1 @ sk_C @ sk_B ) @ X0 )
      | ( r4_lattice3 @ sk_B @ sk_C @ X1 ) ) ),
    inference(demod,[status(thm)],['159','160','161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ( r4_lattice3 @ sk_B @ sk_C @ X0 )
      | ~ ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D @ X0 @ sk_C @ sk_B ) @ X1 )
      | ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D @ X0 @ sk_C @ sk_B ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['154','162'])).

thf('164',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r4_lattice3 @ sk_B @ sk_C @ X0 )
      | ~ ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D @ X0 @ sk_C @ sk_B ) @ X1 )
      | ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D @ X0 @ sk_C @ sk_B ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['163','164','165'])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D @ X0 @ sk_C @ sk_B ) @ X1 )
      | ~ ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D @ X0 @ sk_C @ sk_B ) @ X1 )
      | ( r4_lattice3 @ sk_B @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,
    ( ( ( r4_lattice3 @ sk_B @ sk_C @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r4_lattice3 @ sk_B @ sk_C @ sk_A )
      | ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D @ sk_A @ sk_C @ sk_B ) @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
   <= ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['153','167'])).

thf('169',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('170',plain,
    ( ( ( r4_lattice3 @ sk_B @ sk_C @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r4_lattice3 @ sk_B @ sk_C @ sk_A )
      | ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D @ sk_A @ sk_C @ sk_B ) @ sk_C )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
   <= ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('171',plain,
    ( ( ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D @ sk_A @ sk_C @ sk_B ) @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( r4_lattice3 @ sk_B @ sk_C @ sk_A ) )
   <= ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( r4_lattice3 @ sk_B @ sk_C @ X0 ) ) ),
    inference(clc,[status(thm)],['132','133'])).

thf('173',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ ( k3_lattice3 @ X15 ) ) )
      | ( ( k5_lattice3 @ X15 @ X14 )
        = X14 )
      | ~ ( l3_lattices @ X15 )
      | ~ ( v10_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_lattice3])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_B @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ( ( k5_lattice3 @ sk_B @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) )
        = ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_B @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( ( k5_lattice3 @ sk_B @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) )
        = ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['174','175','176'])).

thf('178',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( ( k5_lattice3 @ sk_B @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) )
        = ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) )
      | ( r4_lattice3 @ sk_B @ sk_C @ X0 ) ) ),
    inference(clc,[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( r4_lattice3 @ sk_B @ sk_C @ X0 ) ) ),
    inference(clc,[status(thm)],['132','133'])).

thf('181',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l3_lattices @ X23 )
      | ~ ( v10_lattices @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ ( k3_lattice3 @ X23 ) ) )
      | ( m1_subset_1 @ ( k5_lattice3 @ X23 @ X24 ) @ ( u1_struct_0 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattice3])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_B @ sk_C @ X0 )
      | ( m1_subset_1 @ ( k5_lattice3 @ sk_B @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_B @ sk_C @ X0 )
      | ( m1_subset_1 @ ( k5_lattice3 @ sk_B @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['182','183','184'])).

thf('186',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_lattice3 @ sk_B @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) ) @ ( u1_struct_0 @ sk_B ) )
      | ( r4_lattice3 @ sk_B @ sk_C @ X0 ) ) ),
    inference(clc,[status(thm)],['185','186'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) )
      | ( r4_lattice3 @ sk_B @ sk_C @ X0 )
      | ( r4_lattice3 @ sk_B @ sk_C @ X0 ) ) ),
    inference('sup+',[status(thm)],['179','187'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_B @ sk_C @ X0 )
      | ( m1_subset_1 @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['188'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) )
        = ( sk_D @ X0 @ sk_C @ sk_B ) )
      | ( r4_lattice3 @ sk_B @ sk_C @ X0 ) ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('191',plain,(
    ! [X0: $i] :
      ( ( ( k5_lattice3 @ sk_B @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) )
        = ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) )
      | ( r4_lattice3 @ sk_B @ sk_C @ X0 ) ) ),
    inference(clc,[status(thm)],['177','178'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( ( k5_lattice3 @ sk_B @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) )
        = ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) )
      | ( r4_lattice3 @ sk_B @ sk_C @ X0 ) ) ),
    inference(clc,[status(thm)],['177','178'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_lattice3 @ sk_B @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) ) @ ( u1_struct_0 @ sk_B ) )
      | ( r4_lattice3 @ sk_B @ sk_C @ X0 ) ) ),
    inference(clc,[status(thm)],['185','186'])).

thf('194',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ( ( k4_lattice3 @ X13 @ X12 )
        = X12 )
      | ~ ( l3_lattices @ X13 )
      | ~ ( v10_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_lattice3])).

thf('195',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_B @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ( ( k4_lattice3 @ sk_B @ ( k5_lattice3 @ sk_B @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) ) )
        = ( k5_lattice3 @ sk_B @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_B @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( ( k4_lattice3 @ sk_B @ ( k5_lattice3 @ sk_B @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) ) )
        = ( k5_lattice3 @ sk_B @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['195','196','197'])).

thf('199',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattice3 @ sk_B @ ( k5_lattice3 @ sk_B @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) ) )
        = ( k5_lattice3 @ sk_B @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) ) )
      | ( r4_lattice3 @ sk_B @ sk_C @ X0 ) ) ),
    inference(clc,[status(thm)],['198','199'])).

thf('201',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattice3 @ sk_B @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) )
        = ( k5_lattice3 @ sk_B @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) ) )
      | ( r4_lattice3 @ sk_B @ sk_C @ X0 )
      | ( r4_lattice3 @ sk_B @ sk_C @ X0 ) ) ),
    inference('sup+',[status(thm)],['192','200'])).

thf('202',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_B @ sk_C @ X0 )
      | ( ( k4_lattice3 @ sk_B @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) )
        = ( k5_lattice3 @ sk_B @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) ) ) ) ),
    inference(simplify,[status(thm)],['201'])).

thf('203',plain,
    ( ( k4_lattice3 @ sk_B @ sk_C )
    = sk_C ),
    inference(clc,[status(thm)],['10','11'])).

thf(t7_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r3_lattices @ A @ B @ C )
              <=> ( r3_orders_2 @ ( k3_lattice3 @ A ) @ ( k4_lattice3 @ A @ B ) @ ( k4_lattice3 @ A @ C ) ) ) ) ) ) )).

thf('204',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ~ ( r3_orders_2 @ ( k3_lattice3 @ X27 ) @ ( k4_lattice3 @ X27 @ X26 ) @ ( k4_lattice3 @ X27 @ X28 ) )
      | ( r3_lattices @ X27 @ X26 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X27 ) )
      | ~ ( l3_lattices @ X27 )
      | ~ ( v10_lattices @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_lattice3])).

thf('205',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( k4_lattice3 @ sk_B @ X0 ) @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) )
      | ( r3_lattices @ sk_B @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( k4_lattice3 @ sk_B @ X0 ) @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( r3_lattices @ sk_B @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['205','206','207','208'])).

thf('210',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( k5_lattice3 @ sk_B @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) ) @ sk_C )
      | ( r4_lattice3 @ sk_B @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) )
      | ( r3_lattices @ sk_B @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) @ sk_C )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['202','209'])).

thf('211',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) @ sk_C )
      | ( r4_lattice3 @ sk_B @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( r3_lattices @ sk_B @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) @ sk_C )
      | ~ ( m1_subset_1 @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) )
      | ( r4_lattice3 @ sk_B @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['191','210'])).

thf('212',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) )
      | ( r3_lattices @ sk_B @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( r4_lattice3 @ sk_B @ sk_C @ X0 )
      | ~ ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) @ sk_C ) ) ),
    inference(simplify,[status(thm)],['211'])).

thf('213',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D @ X0 @ sk_C @ sk_B ) @ sk_C )
      | ( r4_lattice3 @ sk_B @ sk_C @ X0 )
      | ( r4_lattice3 @ sk_B @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( r3_lattices @ sk_B @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) @ sk_C )
      | ~ ( m1_subset_1 @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['190','212'])).

thf('214',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) )
      | ( r3_lattices @ sk_B @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( r4_lattice3 @ sk_B @ sk_C @ X0 )
      | ~ ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D @ X0 @ sk_C @ sk_B ) @ sk_C ) ) ),
    inference(simplify,[status(thm)],['213'])).

thf('215',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_B @ sk_C @ X0 )
      | ~ ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D @ X0 @ sk_C @ sk_B ) @ sk_C )
      | ( r4_lattice3 @ sk_B @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( r3_lattices @ sk_B @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['189','214'])).

thf('216',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_B @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D @ X0 @ sk_C @ sk_B ) @ sk_C )
      | ( r4_lattice3 @ sk_B @ sk_C @ X0 ) ) ),
    inference(simplify,[status(thm)],['215'])).

thf('217',plain,
    ( ( ( r4_lattice3 @ sk_B @ sk_C @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ( r4_lattice3 @ sk_B @ sk_C @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_lattices @ sk_B @ ( k4_lattice3 @ sk_B @ ( sk_D @ sk_A @ sk_C @ sk_B ) ) @ sk_C ) )
   <= ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['171','216'])).

thf('218',plain,
    ( ( ( r3_lattices @ sk_B @ ( k4_lattice3 @ sk_B @ ( sk_D @ sk_A @ sk_C @ sk_B ) ) @ sk_C )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( r4_lattice3 @ sk_B @ sk_C @ sk_A ) )
   <= ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['217'])).

thf('219',plain,
    ( ( ( r3_lattices @ sk_B @ ( sk_D @ sk_A @ sk_C @ sk_B ) @ sk_C )
      | ( r4_lattice3 @ sk_B @ sk_C @ sk_A )
      | ( r4_lattice3 @ sk_B @ sk_C @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
   <= ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['118','218'])).

thf('220',plain,
    ( ( ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( r4_lattice3 @ sk_B @ sk_C @ sk_A )
      | ( r3_lattices @ sk_B @ ( sk_D @ sk_A @ sk_C @ sk_B ) @ sk_C ) )
   <= ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['219'])).

thf('221',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
      | ( r4_lattice3 @ sk_B @ sk_C @ X0 ) ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('222',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l3_lattices @ X5 )
      | ~ ( v9_lattices @ X5 )
      | ~ ( v8_lattices @ X5 )
      | ~ ( v6_lattices @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ( r1_lattices @ X5 @ X4 @ X6 )
      | ~ ( r3_lattices @ X5 @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('223',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_B @ sk_C @ X0 )
      | ~ ( r3_lattices @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) @ X1 )
      | ( r1_lattices @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v6_lattices @ sk_B )
      | ~ ( v8_lattices @ sk_B )
      | ~ ( v9_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B ) ) ),
    inference('sup-',[status(thm)],['221','222'])).

thf('224',plain,(
    v6_lattices @ sk_B ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('225',plain,(
    v8_lattices @ sk_B ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('226',plain,(
    v9_lattices @ sk_B ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('227',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_B @ sk_C @ X0 )
      | ~ ( r3_lattices @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) @ X1 )
      | ( r1_lattices @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['223','224','225','226','227'])).

thf('229',plain,
    ( ( ( r4_lattice3 @ sk_B @ sk_C @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) )
      | ( r1_lattices @ sk_B @ ( sk_D @ sk_A @ sk_C @ sk_B ) @ sk_C )
      | ( r4_lattice3 @ sk_B @ sk_C @ sk_A ) )
   <= ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['220','228'])).

thf('230',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,
    ( ( ( r4_lattice3 @ sk_B @ sk_C @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_lattices @ sk_B @ ( sk_D @ sk_A @ sk_C @ sk_B ) @ sk_C )
      | ( r4_lattice3 @ sk_B @ sk_C @ sk_A ) )
   <= ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['229','230'])).

thf('232',plain,
    ( ( ( r1_lattices @ sk_B @ ( sk_D @ sk_A @ sk_C @ sk_B ) @ sk_C )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( r4_lattice3 @ sk_B @ sk_C @ sk_A ) )
   <= ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['231'])).

thf('233',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r1_lattices @ X8 @ ( sk_D @ X11 @ X7 @ X8 ) @ X7 )
      | ( r4_lattice3 @ X8 @ X7 @ X11 )
      | ~ ( l3_lattices @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('235',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ( r4_lattice3 @ sk_B @ sk_C @ X0 )
      | ~ ( r1_lattices @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['233','234'])).

thf('236',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r4_lattice3 @ sk_B @ sk_C @ X0 )
      | ~ ( r1_lattices @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['235','236'])).

thf('238',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) @ sk_C )
      | ( r4_lattice3 @ sk_B @ sk_C @ X0 ) ) ),
    inference(clc,[status(thm)],['237','238'])).

thf('240',plain,
    ( ( ( r4_lattice3 @ sk_B @ sk_C @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ( r4_lattice3 @ sk_B @ sk_C @ sk_A ) )
   <= ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['232','239'])).

thf('241',plain,
    ( ( ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( r4_lattice3 @ sk_B @ sk_C @ sk_A ) )
   <= ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['240'])).

thf('242',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,
    ( ( ( r4_lattice3 @ sk_B @ sk_C @ sk_A )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
   <= ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['241','242'])).

thf('244',plain,
    ( ~ ( r4_lattice3 @ sk_B @ sk_C @ sk_A )
   <= ~ ( r4_lattice3 @ sk_B @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['103'])).

thf('245',plain,
    ( ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
   <= ( ~ ( r4_lattice3 @ sk_B @ sk_C @ sk_A )
      & ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['243','244'])).

thf(fc4_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A ) )
     => ( ~ ( v2_struct_0 @ ( k3_lattice3 @ A ) )
        & ( v1_orders_2 @ ( k3_lattice3 @ A ) )
        & ( v3_orders_2 @ ( k3_lattice3 @ A ) )
        & ( v4_orders_2 @ ( k3_lattice3 @ A ) )
        & ( v5_orders_2 @ ( k3_lattice3 @ A ) ) ) ) )).

thf('246',plain,(
    ! [X25: $i] :
      ( ~ ( v2_struct_0 @ ( k3_lattice3 @ X25 ) )
      | ~ ( l3_lattices @ X25 )
      | ~ ( v10_lattices @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc4_lattice3])).

thf('247',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B ) )
   <= ( ~ ( r4_lattice3 @ sk_B @ sk_C @ sk_A )
      & ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['245','246'])).

thf('248',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('250',plain,
    ( ( v2_struct_0 @ sk_B )
   <= ( ~ ( r4_lattice3 @ sk_B @ sk_C @ sk_A )
      & ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['247','248','249'])).

thf('251',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,
    ( ( r4_lattice3 @ sk_B @ sk_C @ sk_A )
    | ~ ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['250','251'])).

thf('253',plain,
    ( ( r4_lattice3 @ sk_B @ sk_C @ sk_A )
    | ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['50'])).

thf('254',plain,(
    r4_lattice3 @ sk_B @ sk_C @ sk_A ),
    inference('sat_resolution*',[status(thm)],['104','252','253'])).

thf('255',plain,
    ( ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C )
    | ( r3_lattices @ sk_B @ ( sk_D_1 @ sk_C @ sk_A @ ( k3_lattice3 @ sk_B ) ) @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['102','254'])).

thf('256',plain,
    ( ~ ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) )
   <= ~ ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['103'])).

thf('257',plain,
    ( ( k4_lattice3 @ sk_B @ sk_C )
    = sk_C ),
    inference(clc,[status(thm)],['10','11'])).

thf('258',plain,
    ( ~ ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C )
   <= ~ ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['256','257'])).

thf('259',plain,(
    ~ ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['104','252'])).

thf('260',plain,(
    ~ ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['258','259'])).

thf('261',plain,(
    r3_lattices @ sk_B @ ( sk_D_1 @ sk_C @ sk_A @ ( k3_lattice3 @ sk_B ) ) @ sk_C ),
    inference(clc,[status(thm)],['255','260'])).

thf('262',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('263',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ~ ( r3_lattices @ X27 @ X26 @ X28 )
      | ( r3_orders_2 @ ( k3_lattice3 @ X27 ) @ ( k4_lattice3 @ X27 @ X26 ) @ ( k4_lattice3 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X27 ) )
      | ~ ( l3_lattices @ X27 )
      | ~ ( v10_lattices @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_lattice3])).

thf('264',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( k4_lattice3 @ sk_B @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) ) @ ( k4_lattice3 @ sk_B @ X1 ) )
      | ~ ( r3_lattices @ sk_B @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['262','263'])).

thf('265',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('266',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( k4_lattice3 @ sk_B @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) ) @ ( k4_lattice3 @ sk_B @ X1 ) )
      | ~ ( r3_lattices @ sk_B @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['264','265','266'])).

thf('268',plain,
    ( ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( k4_lattice3 @ sk_B @ ( sk_D_1 @ sk_C @ sk_A @ ( k3_lattice3 @ sk_B ) ) ) @ ( k4_lattice3 @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['261','267'])).

thf('269',plain,
    ( ( k4_lattice3 @ sk_B @ sk_C )
    = sk_C ),
    inference(clc,[status(thm)],['10','11'])).

thf('270',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('271',plain,
    ( ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( k4_lattice3 @ sk_B @ ( sk_D_1 @ sk_C @ sk_A @ ( k3_lattice3 @ sk_B ) ) ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['268','269','270'])).

thf('272',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('273',plain,
    ( ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C )
    | ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( k4_lattice3 @ sk_B @ ( sk_D_1 @ sk_C @ sk_A @ ( k3_lattice3 @ sk_B ) ) ) @ sk_C ) ),
    inference(clc,[status(thm)],['271','272'])).

thf('274',plain,(
    ~ ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['258','259'])).

thf('275',plain,(
    r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( k4_lattice3 @ sk_B @ ( sk_D_1 @ sk_C @ sk_A @ ( k3_lattice3 @ sk_B ) ) ) @ sk_C ),
    inference(clc,[status(thm)],['273','274'])).

thf('276',plain,
    ( ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D_1 @ sk_C @ sk_A @ ( k3_lattice3 @ sk_B ) ) @ sk_C )
    | ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['49','275'])).

thf('277',plain,(
    ~ ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['258','259'])).

thf('278',plain,(
    r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D_1 @ sk_C @ sk_A @ ( k3_lattice3 @ sk_B ) ) @ sk_C ),
    inference(clc,[status(thm)],['276','277'])).

thf('279',plain,(
    ! [X20: $i] :
      ( ( l1_orders_2 @ ( k3_lattice3 @ X20 ) )
      | ~ ( l3_lattices @ X20 )
      | ~ ( v10_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_lattice3])).

thf('280',plain,(
    ! [X20: $i] :
      ( ( v3_orders_2 @ ( k3_lattice3 @ X20 ) )
      | ~ ( l3_lattices @ X20 )
      | ~ ( v10_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_lattice3])).

thf('281',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('282',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r1_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( r3_orders_2 @ X1 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('283',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ~ ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ X1 )
      | ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ~ ( v3_orders_2 @ ( k3_lattice3 @ sk_B ) )
      | ~ ( l1_orders_2 @ ( k3_lattice3 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['281','282'])).

thf('284',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ~ ( l1_orders_2 @ ( k3_lattice3 @ sk_B ) )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D_1 @ sk_C @ X1 @ ( k3_lattice3 @ sk_B ) ) @ X0 )
      | ~ ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D_1 @ sk_C @ X1 @ ( k3_lattice3 @ sk_B ) ) @ X0 )
      | ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['280','283'])).

thf('285',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('286',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('287',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( l1_orders_2 @ ( k3_lattice3 @ sk_B ) )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D_1 @ sk_C @ X1 @ ( k3_lattice3 @ sk_B ) ) @ X0 )
      | ~ ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D_1 @ sk_C @ X1 @ ( k3_lattice3 @ sk_B ) ) @ X0 )
      | ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['284','285','286'])).

thf('288',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ~ ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ X1 )
      | ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['279','287'])).

thf('289',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('290',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('291',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ~ ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ X1 )
      | ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['288','289','290'])).

thf('292',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ X1 )
      | ~ ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ X1 )
      | ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['291'])).

thf('293',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C )
    | ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D_1 @ sk_C @ sk_A @ ( k3_lattice3 @ sk_B ) ) @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
    | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['278','292'])).

thf('294',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('295',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C )
    | ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D_1 @ sk_C @ sk_A @ ( k3_lattice3 @ sk_B ) ) @ sk_C )
    | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) ) ),
    inference(demod,[status(thm)],['293','294'])).

thf('296',plain,(
    ! [X20: $i] :
      ( ( l1_orders_2 @ ( k3_lattice3 @ X20 ) )
      | ~ ( l3_lattices @ X20 )
      | ~ ( v10_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_lattice3])).

thf('297',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('298',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ~ ( r1_orders_2 @ X17 @ ( sk_D_1 @ X16 @ X18 @ X17 ) @ X16 )
      | ( r2_lattice3 @ X17 @ X18 @ X16 )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('299',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ ( k3_lattice3 @ sk_B ) )
      | ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ~ ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['297','298'])).

thf('300',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ~ ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ sk_C )
      | ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['296','299'])).

thf('301',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('302',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('303',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ sk_C )
      | ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['300','301','302'])).

thf('304',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('305',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ~ ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['303','304'])).

thf('306',plain,
    ( ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
    | ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['295','305'])).

thf('307',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C )
    | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['306'])).

thf('308',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('309',plain,
    ( ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
    | ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['307','308'])).

thf('310',plain,(
    ~ ( r2_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['258','259'])).

thf('311',plain,(
    v2_struct_0 @ ( k3_lattice3 @ sk_B ) ),
    inference(clc,[status(thm)],['309','310'])).

thf('312',plain,(
    ! [X25: $i] :
      ( ~ ( v2_struct_0 @ ( k3_lattice3 @ X25 ) )
      | ~ ( l3_lattices @ X25 )
      | ~ ( v10_lattices @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc4_lattice3])).

thf('313',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v10_lattices @ sk_B )
    | ~ ( l3_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['311','312'])).

thf('314',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('315',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('316',plain,(
    v2_struct_0 @ sk_B ),
    inference(demod,[status(thm)],['313','314','315'])).

thf('317',plain,(
    $false ),
    inference(demod,[status(thm)],['0','316'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LT7B6ACSD2
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:31:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.93/2.14  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.93/2.14  % Solved by: fo/fo7.sh
% 1.93/2.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.93/2.14  % done 2868 iterations in 1.647s
% 1.93/2.14  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.93/2.14  % SZS output start Refutation
% 1.93/2.14  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 1.93/2.14  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.93/2.14  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 1.93/2.14  thf(sk_A_type, type, sk_A: $i).
% 1.93/2.14  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.93/2.14  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 1.93/2.14  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 1.93/2.14  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 1.93/2.14  thf(sk_C_type, type, sk_C: $i).
% 1.93/2.14  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.93/2.14  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 1.93/2.14  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.93/2.14  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 1.93/2.14  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 1.93/2.14  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 1.93/2.14  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 1.93/2.14  thf(k4_lattice3_type, type, k4_lattice3: $i > $i > $i).
% 1.93/2.14  thf(sk_B_type, type, sk_B: $i).
% 1.93/2.14  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 1.93/2.14  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 1.93/2.14  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 1.93/2.14  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 1.93/2.14  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.93/2.14  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 1.93/2.14  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 1.93/2.14  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 1.93/2.14  thf(r4_lattice3_type, type, r4_lattice3: $i > $i > $i > $o).
% 1.93/2.14  thf(k5_lattice3_type, type, k5_lattice3: $i > $i > $i).
% 1.93/2.14  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 1.93/2.14  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 1.93/2.14  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 1.93/2.14  thf(t30_lattice3, conjecture,
% 1.93/2.14    (![A:$i,B:$i]:
% 1.93/2.14     ( ( ( ~( v2_struct_0 @ B ) ) & ( v10_lattices @ B ) & ( l3_lattices @ B ) ) =>
% 1.93/2.14       ( ![C:$i]:
% 1.93/2.14         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 1.93/2.14           ( ( r4_lattice3 @ B @ C @ A ) <=>
% 1.93/2.14             ( r2_lattice3 @ ( k3_lattice3 @ B ) @ A @ ( k4_lattice3 @ B @ C ) ) ) ) ) ))).
% 1.93/2.14  thf(zf_stmt_0, negated_conjecture,
% 1.93/2.14    (~( ![A:$i,B:$i]:
% 1.93/2.14        ( ( ( ~( v2_struct_0 @ B ) ) & ( v10_lattices @ B ) & 
% 1.93/2.14            ( l3_lattices @ B ) ) =>
% 1.93/2.14          ( ![C:$i]:
% 1.93/2.14            ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 1.93/2.14              ( ( r4_lattice3 @ B @ C @ A ) <=>
% 1.93/2.14                ( r2_lattice3 @
% 1.93/2.14                  ( k3_lattice3 @ B ) @ A @ ( k4_lattice3 @ B @ C ) ) ) ) ) ) )),
% 1.93/2.14    inference('cnf.neg', [status(esa)], [t30_lattice3])).
% 1.93/2.14  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf(dt_k3_lattice3, axiom,
% 1.93/2.14    (![A:$i]:
% 1.93/2.14     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 1.93/2.14       ( ( v1_orders_2 @ ( k3_lattice3 @ A ) ) & 
% 1.93/2.14         ( v3_orders_2 @ ( k3_lattice3 @ A ) ) & 
% 1.93/2.14         ( v4_orders_2 @ ( k3_lattice3 @ A ) ) & 
% 1.93/2.14         ( v5_orders_2 @ ( k3_lattice3 @ A ) ) & 
% 1.93/2.14         ( l1_orders_2 @ ( k3_lattice3 @ A ) ) ) ))).
% 1.93/2.14  thf('1', plain,
% 1.93/2.14      (![X20 : $i]:
% 1.93/2.14         ((l1_orders_2 @ (k3_lattice3 @ X20))
% 1.93/2.14          | ~ (l3_lattices @ X20)
% 1.93/2.14          | ~ (v10_lattices @ X20)
% 1.93/2.14          | (v2_struct_0 @ X20))),
% 1.93/2.14      inference('cnf', [status(esa)], [dt_k3_lattice3])).
% 1.93/2.14  thf('2', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_B))),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf(dt_k4_lattice3, axiom,
% 1.93/2.14    (![A:$i,B:$i]:
% 1.93/2.14     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 1.93/2.14         ( l3_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 1.93/2.14       ( m1_subset_1 @
% 1.93/2.14         ( k4_lattice3 @ A @ B ) @ ( u1_struct_0 @ ( k3_lattice3 @ A ) ) ) ))).
% 1.93/2.14  thf('3', plain,
% 1.93/2.14      (![X21 : $i, X22 : $i]:
% 1.93/2.14         (~ (l3_lattices @ X21)
% 1.93/2.14          | ~ (v10_lattices @ X21)
% 1.93/2.14          | (v2_struct_0 @ X21)
% 1.93/2.14          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 1.93/2.14          | (m1_subset_1 @ (k4_lattice3 @ X21 @ X22) @ 
% 1.93/2.14             (u1_struct_0 @ (k3_lattice3 @ X21))))),
% 1.93/2.14      inference('cnf', [status(esa)], [dt_k4_lattice3])).
% 1.93/2.14  thf('4', plain,
% 1.93/2.14      (((m1_subset_1 @ (k4_lattice3 @ sk_B @ sk_C) @ 
% 1.93/2.14         (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 1.93/2.14        | (v2_struct_0 @ sk_B)
% 1.93/2.14        | ~ (v10_lattices @ sk_B)
% 1.93/2.14        | ~ (l3_lattices @ sk_B))),
% 1.93/2.14      inference('sup-', [status(thm)], ['2', '3'])).
% 1.93/2.14  thf('5', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_B))),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf(d3_lattice3, axiom,
% 1.93/2.14    (![A:$i]:
% 1.93/2.14     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 1.93/2.14       ( ![B:$i]:
% 1.93/2.14         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.93/2.14           ( ( k4_lattice3 @ A @ B ) = ( B ) ) ) ) ))).
% 1.93/2.14  thf('6', plain,
% 1.93/2.14      (![X12 : $i, X13 : $i]:
% 1.93/2.14         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 1.93/2.14          | ((k4_lattice3 @ X13 @ X12) = (X12))
% 1.93/2.14          | ~ (l3_lattices @ X13)
% 1.93/2.14          | ~ (v10_lattices @ X13)
% 1.93/2.14          | (v2_struct_0 @ X13))),
% 1.93/2.14      inference('cnf', [status(esa)], [d3_lattice3])).
% 1.93/2.14  thf('7', plain,
% 1.93/2.14      (((v2_struct_0 @ sk_B)
% 1.93/2.14        | ~ (v10_lattices @ sk_B)
% 1.93/2.14        | ~ (l3_lattices @ sk_B)
% 1.93/2.14        | ((k4_lattice3 @ sk_B @ sk_C) = (sk_C)))),
% 1.93/2.14      inference('sup-', [status(thm)], ['5', '6'])).
% 1.93/2.14  thf('8', plain, ((v10_lattices @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('9', plain, ((l3_lattices @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('10', plain,
% 1.93/2.14      (((v2_struct_0 @ sk_B) | ((k4_lattice3 @ sk_B @ sk_C) = (sk_C)))),
% 1.93/2.14      inference('demod', [status(thm)], ['7', '8', '9'])).
% 1.93/2.14  thf('11', plain, (~ (v2_struct_0 @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('12', plain, (((k4_lattice3 @ sk_B @ sk_C) = (sk_C))),
% 1.93/2.14      inference('clc', [status(thm)], ['10', '11'])).
% 1.93/2.14  thf('13', plain, ((v10_lattices @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('14', plain, ((l3_lattices @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('15', plain,
% 1.93/2.14      (((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 1.93/2.14        | (v2_struct_0 @ sk_B))),
% 1.93/2.14      inference('demod', [status(thm)], ['4', '12', '13', '14'])).
% 1.93/2.14  thf('16', plain, (~ (v2_struct_0 @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('17', plain,
% 1.93/2.14      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))),
% 1.93/2.14      inference('clc', [status(thm)], ['15', '16'])).
% 1.93/2.14  thf(d9_lattice3, axiom,
% 1.93/2.14    (![A:$i]:
% 1.93/2.14     ( ( l1_orders_2 @ A ) =>
% 1.93/2.14       ( ![B:$i,C:$i]:
% 1.93/2.14         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.93/2.14           ( ( r2_lattice3 @ A @ B @ C ) <=>
% 1.93/2.14             ( ![D:$i]:
% 1.93/2.14               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 1.93/2.14                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ))).
% 1.93/2.14  thf('18', plain,
% 1.93/2.14      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.93/2.14         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 1.93/2.14          | (m1_subset_1 @ (sk_D_1 @ X16 @ X18 @ X17) @ (u1_struct_0 @ X17))
% 1.93/2.14          | (r2_lattice3 @ X17 @ X18 @ X16)
% 1.93/2.14          | ~ (l1_orders_2 @ X17))),
% 1.93/2.14      inference('cnf', [status(esa)], [d9_lattice3])).
% 1.93/2.14  thf('19', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         (~ (l1_orders_2 @ (k3_lattice3 @ sk_B))
% 1.93/2.14          | (r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 1.93/2.14          | (m1_subset_1 @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ 
% 1.93/2.14             (u1_struct_0 @ (k3_lattice3 @ sk_B))))),
% 1.93/2.14      inference('sup-', [status(thm)], ['17', '18'])).
% 1.93/2.14  thf('20', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((v2_struct_0 @ sk_B)
% 1.93/2.14          | ~ (v10_lattices @ sk_B)
% 1.93/2.14          | ~ (l3_lattices @ sk_B)
% 1.93/2.14          | (m1_subset_1 @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ 
% 1.93/2.14             (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 1.93/2.14          | (r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C))),
% 1.93/2.14      inference('sup-', [status(thm)], ['1', '19'])).
% 1.93/2.14  thf('21', plain, ((v10_lattices @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('22', plain, ((l3_lattices @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('23', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((v2_struct_0 @ sk_B)
% 1.93/2.14          | (m1_subset_1 @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ 
% 1.93/2.14             (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 1.93/2.14          | (r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C))),
% 1.93/2.14      inference('demod', [status(thm)], ['20', '21', '22'])).
% 1.93/2.14  thf('24', plain, (~ (v2_struct_0 @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('25', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 1.93/2.14          | (m1_subset_1 @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ 
% 1.93/2.14             (u1_struct_0 @ (k3_lattice3 @ sk_B))))),
% 1.93/2.14      inference('clc', [status(thm)], ['23', '24'])).
% 1.93/2.14  thf(d4_lattice3, axiom,
% 1.93/2.14    (![A:$i]:
% 1.93/2.14     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 1.93/2.14       ( ![B:$i]:
% 1.93/2.14         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k3_lattice3 @ A ) ) ) =>
% 1.93/2.14           ( ( k5_lattice3 @ A @ B ) = ( B ) ) ) ) ))).
% 1.93/2.14  thf('26', plain,
% 1.93/2.14      (![X14 : $i, X15 : $i]:
% 1.93/2.14         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ (k3_lattice3 @ X15)))
% 1.93/2.14          | ((k5_lattice3 @ X15 @ X14) = (X14))
% 1.93/2.14          | ~ (l3_lattices @ X15)
% 1.93/2.14          | ~ (v10_lattices @ X15)
% 1.93/2.14          | (v2_struct_0 @ X15))),
% 1.93/2.14      inference('cnf', [status(esa)], [d4_lattice3])).
% 1.93/2.14  thf('27', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 1.93/2.14          | (v2_struct_0 @ sk_B)
% 1.93/2.14          | ~ (v10_lattices @ sk_B)
% 1.93/2.14          | ~ (l3_lattices @ sk_B)
% 1.93/2.14          | ((k5_lattice3 @ sk_B @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)))
% 1.93/2.14              = (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B))))),
% 1.93/2.14      inference('sup-', [status(thm)], ['25', '26'])).
% 1.93/2.14  thf('28', plain, ((v10_lattices @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('29', plain, ((l3_lattices @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('30', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 1.93/2.14          | (v2_struct_0 @ sk_B)
% 1.93/2.14          | ((k5_lattice3 @ sk_B @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)))
% 1.93/2.14              = (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B))))),
% 1.93/2.14      inference('demod', [status(thm)], ['27', '28', '29'])).
% 1.93/2.14  thf('31', plain, (~ (v2_struct_0 @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('32', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         (((k5_lattice3 @ sk_B @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)))
% 1.93/2.14            = (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)))
% 1.93/2.14          | (r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C))),
% 1.93/2.14      inference('clc', [status(thm)], ['30', '31'])).
% 1.93/2.14  thf('33', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 1.93/2.14          | (m1_subset_1 @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ 
% 1.93/2.14             (u1_struct_0 @ (k3_lattice3 @ sk_B))))),
% 1.93/2.14      inference('clc', [status(thm)], ['23', '24'])).
% 1.93/2.14  thf(dt_k5_lattice3, axiom,
% 1.93/2.14    (![A:$i,B:$i]:
% 1.93/2.14     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 1.93/2.14         ( l3_lattices @ A ) & 
% 1.93/2.14         ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k3_lattice3 @ A ) ) ) ) =>
% 1.93/2.14       ( m1_subset_1 @ ( k5_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 1.93/2.14  thf('34', plain,
% 1.93/2.14      (![X23 : $i, X24 : $i]:
% 1.93/2.14         (~ (l3_lattices @ X23)
% 1.93/2.14          | ~ (v10_lattices @ X23)
% 1.93/2.14          | (v2_struct_0 @ X23)
% 1.93/2.14          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ (k3_lattice3 @ X23)))
% 1.93/2.14          | (m1_subset_1 @ (k5_lattice3 @ X23 @ X24) @ (u1_struct_0 @ X23)))),
% 1.93/2.14      inference('cnf', [status(esa)], [dt_k5_lattice3])).
% 1.93/2.14  thf('35', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 1.93/2.14          | (m1_subset_1 @ 
% 1.93/2.14             (k5_lattice3 @ sk_B @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B))) @ 
% 1.93/2.14             (u1_struct_0 @ sk_B))
% 1.93/2.14          | (v2_struct_0 @ sk_B)
% 1.93/2.14          | ~ (v10_lattices @ sk_B)
% 1.93/2.14          | ~ (l3_lattices @ sk_B))),
% 1.93/2.14      inference('sup-', [status(thm)], ['33', '34'])).
% 1.93/2.14  thf('36', plain, ((v10_lattices @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('37', plain, ((l3_lattices @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('38', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 1.93/2.14          | (m1_subset_1 @ 
% 1.93/2.14             (k5_lattice3 @ sk_B @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B))) @ 
% 1.93/2.14             (u1_struct_0 @ sk_B))
% 1.93/2.14          | (v2_struct_0 @ sk_B))),
% 1.93/2.14      inference('demod', [status(thm)], ['35', '36', '37'])).
% 1.93/2.14  thf('39', plain, (~ (v2_struct_0 @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('40', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((m1_subset_1 @ 
% 1.93/2.14           (k5_lattice3 @ sk_B @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B))) @ 
% 1.93/2.14           (u1_struct_0 @ sk_B))
% 1.93/2.14          | (r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C))),
% 1.93/2.14      inference('clc', [status(thm)], ['38', '39'])).
% 1.93/2.14  thf('41', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((m1_subset_1 @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ 
% 1.93/2.14           (u1_struct_0 @ sk_B))
% 1.93/2.14          | (r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 1.93/2.14          | (r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C))),
% 1.93/2.14      inference('sup+', [status(thm)], ['32', '40'])).
% 1.93/2.14  thf('42', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 1.93/2.14          | (m1_subset_1 @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ 
% 1.93/2.14             (u1_struct_0 @ sk_B)))),
% 1.93/2.14      inference('simplify', [status(thm)], ['41'])).
% 1.93/2.14  thf('43', plain,
% 1.93/2.14      (![X12 : $i, X13 : $i]:
% 1.93/2.14         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 1.93/2.14          | ((k4_lattice3 @ X13 @ X12) = (X12))
% 1.93/2.14          | ~ (l3_lattices @ X13)
% 1.93/2.14          | ~ (v10_lattices @ X13)
% 1.93/2.14          | (v2_struct_0 @ X13))),
% 1.93/2.14      inference('cnf', [status(esa)], [d3_lattice3])).
% 1.93/2.14  thf('44', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 1.93/2.14          | (v2_struct_0 @ sk_B)
% 1.93/2.14          | ~ (v10_lattices @ sk_B)
% 1.93/2.14          | ~ (l3_lattices @ sk_B)
% 1.93/2.14          | ((k4_lattice3 @ sk_B @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)))
% 1.93/2.14              = (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B))))),
% 1.93/2.14      inference('sup-', [status(thm)], ['42', '43'])).
% 1.93/2.14  thf('45', plain, ((v10_lattices @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('46', plain, ((l3_lattices @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('47', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 1.93/2.14          | (v2_struct_0 @ sk_B)
% 1.93/2.14          | ((k4_lattice3 @ sk_B @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)))
% 1.93/2.14              = (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B))))),
% 1.93/2.14      inference('demod', [status(thm)], ['44', '45', '46'])).
% 1.93/2.14  thf('48', plain, (~ (v2_struct_0 @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('49', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         (((k4_lattice3 @ sk_B @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)))
% 1.93/2.14            = (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)))
% 1.93/2.14          | (r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C))),
% 1.93/2.14      inference('clc', [status(thm)], ['47', '48'])).
% 1.93/2.14  thf('50', plain,
% 1.93/2.14      (((r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 1.93/2.14         (k4_lattice3 @ sk_B @ sk_C))
% 1.93/2.14        | (r4_lattice3 @ sk_B @ sk_C @ sk_A))),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('51', plain,
% 1.93/2.14      (((r4_lattice3 @ sk_B @ sk_C @ sk_A))
% 1.93/2.14         <= (((r4_lattice3 @ sk_B @ sk_C @ sk_A)))),
% 1.93/2.14      inference('split', [status(esa)], ['50'])).
% 1.93/2.14  thf('52', plain,
% 1.93/2.14      (![X20 : $i]:
% 1.93/2.14         ((l1_orders_2 @ (k3_lattice3 @ X20))
% 1.93/2.14          | ~ (l3_lattices @ X20)
% 1.93/2.14          | ~ (v10_lattices @ X20)
% 1.93/2.14          | (v2_struct_0 @ X20))),
% 1.93/2.14      inference('cnf', [status(esa)], [dt_k3_lattice3])).
% 1.93/2.14  thf('53', plain,
% 1.93/2.14      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))),
% 1.93/2.14      inference('clc', [status(thm)], ['15', '16'])).
% 1.93/2.14  thf('54', plain,
% 1.93/2.14      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.93/2.14         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 1.93/2.14          | (r2_hidden @ (sk_D_1 @ X16 @ X18 @ X17) @ X18)
% 1.93/2.14          | (r2_lattice3 @ X17 @ X18 @ X16)
% 1.93/2.14          | ~ (l1_orders_2 @ X17))),
% 1.93/2.14      inference('cnf', [status(esa)], [d9_lattice3])).
% 1.93/2.14  thf('55', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         (~ (l1_orders_2 @ (k3_lattice3 @ sk_B))
% 1.93/2.14          | (r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 1.93/2.14          | (r2_hidden @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ X0))),
% 1.93/2.14      inference('sup-', [status(thm)], ['53', '54'])).
% 1.93/2.14  thf('56', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((v2_struct_0 @ sk_B)
% 1.93/2.14          | ~ (v10_lattices @ sk_B)
% 1.93/2.14          | ~ (l3_lattices @ sk_B)
% 1.93/2.14          | (r2_hidden @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ X0)
% 1.93/2.14          | (r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C))),
% 1.93/2.14      inference('sup-', [status(thm)], ['52', '55'])).
% 1.93/2.14  thf('57', plain, ((v10_lattices @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('58', plain, ((l3_lattices @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('59', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((v2_struct_0 @ sk_B)
% 1.93/2.14          | (r2_hidden @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ X0)
% 1.93/2.14          | (r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C))),
% 1.93/2.14      inference('demod', [status(thm)], ['56', '57', '58'])).
% 1.93/2.14  thf('60', plain, (~ (v2_struct_0 @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('61', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 1.93/2.14          | (r2_hidden @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ X0))),
% 1.93/2.14      inference('clc', [status(thm)], ['59', '60'])).
% 1.93/2.14  thf('62', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 1.93/2.14          | (m1_subset_1 @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ 
% 1.93/2.14             (u1_struct_0 @ sk_B)))),
% 1.93/2.14      inference('simplify', [status(thm)], ['41'])).
% 1.93/2.14  thf('63', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_B))),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf(d17_lattice3, axiom,
% 1.93/2.14    (![A:$i]:
% 1.93/2.14     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 1.93/2.14       ( ![B:$i]:
% 1.93/2.14         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.93/2.14           ( ![C:$i]:
% 1.93/2.14             ( ( r4_lattice3 @ A @ B @ C ) <=>
% 1.93/2.14               ( ![D:$i]:
% 1.93/2.14                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 1.93/2.14                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ))).
% 1.93/2.14  thf('64', plain,
% 1.93/2.14      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.93/2.14         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 1.93/2.14          | ~ (r4_lattice3 @ X8 @ X7 @ X9)
% 1.93/2.14          | ~ (r2_hidden @ X10 @ X9)
% 1.93/2.14          | (r1_lattices @ X8 @ X10 @ X7)
% 1.93/2.14          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X8))
% 1.93/2.14          | ~ (l3_lattices @ X8)
% 1.93/2.14          | (v2_struct_0 @ X8))),
% 1.93/2.14      inference('cnf', [status(esa)], [d17_lattice3])).
% 1.93/2.14  thf('65', plain,
% 1.93/2.14      (![X0 : $i, X1 : $i]:
% 1.93/2.14         ((v2_struct_0 @ sk_B)
% 1.93/2.14          | ~ (l3_lattices @ sk_B)
% 1.93/2.14          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 1.93/2.14          | (r1_lattices @ sk_B @ X0 @ sk_C)
% 1.93/2.14          | ~ (r2_hidden @ X0 @ X1)
% 1.93/2.14          | ~ (r4_lattice3 @ sk_B @ sk_C @ X1))),
% 1.93/2.14      inference('sup-', [status(thm)], ['63', '64'])).
% 1.93/2.14  thf('66', plain, ((l3_lattices @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('67', plain,
% 1.93/2.14      (![X0 : $i, X1 : $i]:
% 1.93/2.14         ((v2_struct_0 @ sk_B)
% 1.93/2.14          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 1.93/2.14          | (r1_lattices @ sk_B @ X0 @ sk_C)
% 1.93/2.14          | ~ (r2_hidden @ X0 @ X1)
% 1.93/2.14          | ~ (r4_lattice3 @ sk_B @ sk_C @ X1))),
% 1.93/2.14      inference('demod', [status(thm)], ['65', '66'])).
% 1.93/2.14  thf('68', plain,
% 1.93/2.14      (![X0 : $i, X1 : $i]:
% 1.93/2.14         ((r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 1.93/2.14          | ~ (r4_lattice3 @ sk_B @ sk_C @ X1)
% 1.93/2.14          | ~ (r2_hidden @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ X1)
% 1.93/2.14          | (r1_lattices @ sk_B @ 
% 1.93/2.14             (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ sk_C)
% 1.93/2.14          | (v2_struct_0 @ sk_B))),
% 1.93/2.14      inference('sup-', [status(thm)], ['62', '67'])).
% 1.93/2.14  thf('69', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 1.93/2.14          | (v2_struct_0 @ sk_B)
% 1.93/2.14          | (r1_lattices @ sk_B @ 
% 1.93/2.14             (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ sk_C)
% 1.93/2.14          | ~ (r4_lattice3 @ sk_B @ sk_C @ X0)
% 1.93/2.14          | (r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C))),
% 1.93/2.14      inference('sup-', [status(thm)], ['61', '68'])).
% 1.93/2.14  thf('70', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         (~ (r4_lattice3 @ sk_B @ sk_C @ X0)
% 1.93/2.14          | (r1_lattices @ sk_B @ 
% 1.93/2.14             (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ sk_C)
% 1.93/2.14          | (v2_struct_0 @ sk_B)
% 1.93/2.14          | (r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C))),
% 1.93/2.14      inference('simplify', [status(thm)], ['69'])).
% 1.93/2.14  thf('71', plain,
% 1.93/2.14      ((((r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ sk_C)
% 1.93/2.14         | (v2_struct_0 @ sk_B)
% 1.93/2.14         | (r1_lattices @ sk_B @ 
% 1.93/2.14            (sk_D_1 @ sk_C @ sk_A @ (k3_lattice3 @ sk_B)) @ sk_C)))
% 1.93/2.14         <= (((r4_lattice3 @ sk_B @ sk_C @ sk_A)))),
% 1.93/2.14      inference('sup-', [status(thm)], ['51', '70'])).
% 1.93/2.14  thf('72', plain, (~ (v2_struct_0 @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('73', plain,
% 1.93/2.14      ((((r1_lattices @ sk_B @ (sk_D_1 @ sk_C @ sk_A @ (k3_lattice3 @ sk_B)) @ 
% 1.93/2.14          sk_C)
% 1.93/2.14         | (r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ sk_C)))
% 1.93/2.14         <= (((r4_lattice3 @ sk_B @ sk_C @ sk_A)))),
% 1.93/2.14      inference('clc', [status(thm)], ['71', '72'])).
% 1.93/2.14  thf('74', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 1.93/2.14          | (m1_subset_1 @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ 
% 1.93/2.14             (u1_struct_0 @ sk_B)))),
% 1.93/2.14      inference('simplify', [status(thm)], ['41'])).
% 1.93/2.14  thf(redefinition_r3_lattices, axiom,
% 1.93/2.14    (![A:$i,B:$i,C:$i]:
% 1.93/2.14     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 1.93/2.14         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 1.93/2.14         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 1.93/2.14         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 1.93/2.14       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 1.93/2.14  thf('75', plain,
% 1.93/2.14      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.93/2.14         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 1.93/2.14          | ~ (l3_lattices @ X5)
% 1.93/2.14          | ~ (v9_lattices @ X5)
% 1.93/2.14          | ~ (v8_lattices @ X5)
% 1.93/2.14          | ~ (v6_lattices @ X5)
% 1.93/2.14          | (v2_struct_0 @ X5)
% 1.93/2.14          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 1.93/2.14          | (r3_lattices @ X5 @ X4 @ X6)
% 1.93/2.14          | ~ (r1_lattices @ X5 @ X4 @ X6))),
% 1.93/2.14      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 1.93/2.14  thf('76', plain,
% 1.93/2.14      (![X0 : $i, X1 : $i]:
% 1.93/2.14         ((r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 1.93/2.14          | ~ (r1_lattices @ sk_B @ 
% 1.93/2.14               (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ X1)
% 1.93/2.14          | (r3_lattices @ sk_B @ 
% 1.93/2.14             (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ X1)
% 1.93/2.14          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 1.93/2.14          | (v2_struct_0 @ sk_B)
% 1.93/2.14          | ~ (v6_lattices @ sk_B)
% 1.93/2.14          | ~ (v8_lattices @ sk_B)
% 1.93/2.14          | ~ (v9_lattices @ sk_B)
% 1.93/2.14          | ~ (l3_lattices @ sk_B))),
% 1.93/2.14      inference('sup-', [status(thm)], ['74', '75'])).
% 1.93/2.14  thf(cc1_lattices, axiom,
% 1.93/2.14    (![A:$i]:
% 1.93/2.14     ( ( l3_lattices @ A ) =>
% 1.93/2.14       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 1.93/2.14         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 1.93/2.14           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 1.93/2.14           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 1.93/2.14  thf('77', plain,
% 1.93/2.14      (![X3 : $i]:
% 1.93/2.14         ((v2_struct_0 @ X3)
% 1.93/2.14          | ~ (v10_lattices @ X3)
% 1.93/2.14          | (v6_lattices @ X3)
% 1.93/2.14          | ~ (l3_lattices @ X3))),
% 1.93/2.14      inference('cnf', [status(esa)], [cc1_lattices])).
% 1.93/2.14  thf('78', plain, (~ (v2_struct_0 @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('79', plain,
% 1.93/2.14      ((~ (l3_lattices @ sk_B) | (v6_lattices @ sk_B) | ~ (v10_lattices @ sk_B))),
% 1.93/2.14      inference('sup-', [status(thm)], ['77', '78'])).
% 1.93/2.14  thf('80', plain, ((l3_lattices @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('81', plain, ((v10_lattices @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('82', plain, ((v6_lattices @ sk_B)),
% 1.93/2.14      inference('demod', [status(thm)], ['79', '80', '81'])).
% 1.93/2.14  thf('83', plain,
% 1.93/2.14      (![X3 : $i]:
% 1.93/2.14         ((v2_struct_0 @ X3)
% 1.93/2.14          | ~ (v10_lattices @ X3)
% 1.93/2.14          | (v8_lattices @ X3)
% 1.93/2.14          | ~ (l3_lattices @ X3))),
% 1.93/2.14      inference('cnf', [status(esa)], [cc1_lattices])).
% 1.93/2.14  thf('84', plain, (~ (v2_struct_0 @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('85', plain,
% 1.93/2.14      ((~ (l3_lattices @ sk_B) | (v8_lattices @ sk_B) | ~ (v10_lattices @ sk_B))),
% 1.93/2.14      inference('sup-', [status(thm)], ['83', '84'])).
% 1.93/2.14  thf('86', plain, ((l3_lattices @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('87', plain, ((v10_lattices @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('88', plain, ((v8_lattices @ sk_B)),
% 1.93/2.14      inference('demod', [status(thm)], ['85', '86', '87'])).
% 1.93/2.14  thf('89', plain,
% 1.93/2.14      (![X3 : $i]:
% 1.93/2.14         ((v2_struct_0 @ X3)
% 1.93/2.14          | ~ (v10_lattices @ X3)
% 1.93/2.14          | (v9_lattices @ X3)
% 1.93/2.14          | ~ (l3_lattices @ X3))),
% 1.93/2.14      inference('cnf', [status(esa)], [cc1_lattices])).
% 1.93/2.14  thf('90', plain, (~ (v2_struct_0 @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('91', plain,
% 1.93/2.14      ((~ (l3_lattices @ sk_B) | (v9_lattices @ sk_B) | ~ (v10_lattices @ sk_B))),
% 1.93/2.14      inference('sup-', [status(thm)], ['89', '90'])).
% 1.93/2.14  thf('92', plain, ((l3_lattices @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('93', plain, ((v10_lattices @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('94', plain, ((v9_lattices @ sk_B)),
% 1.93/2.14      inference('demod', [status(thm)], ['91', '92', '93'])).
% 1.93/2.14  thf('95', plain, ((l3_lattices @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('96', plain,
% 1.93/2.14      (![X0 : $i, X1 : $i]:
% 1.93/2.14         ((r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 1.93/2.14          | ~ (r1_lattices @ sk_B @ 
% 1.93/2.14               (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ X1)
% 1.93/2.14          | (r3_lattices @ sk_B @ 
% 1.93/2.14             (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ X1)
% 1.93/2.14          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 1.93/2.14          | (v2_struct_0 @ sk_B))),
% 1.93/2.14      inference('demod', [status(thm)], ['76', '82', '88', '94', '95'])).
% 1.93/2.14  thf('97', plain,
% 1.93/2.14      ((((r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ sk_C)
% 1.93/2.14         | (v2_struct_0 @ sk_B)
% 1.93/2.14         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_B))
% 1.93/2.14         | (r3_lattices @ sk_B @ 
% 1.93/2.14            (sk_D_1 @ sk_C @ sk_A @ (k3_lattice3 @ sk_B)) @ sk_C)
% 1.93/2.14         | (r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ sk_C)))
% 1.93/2.14         <= (((r4_lattice3 @ sk_B @ sk_C @ sk_A)))),
% 1.93/2.14      inference('sup-', [status(thm)], ['73', '96'])).
% 1.93/2.14  thf('98', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_B))),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('99', plain,
% 1.93/2.14      ((((r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ sk_C)
% 1.93/2.14         | (v2_struct_0 @ sk_B)
% 1.93/2.14         | (r3_lattices @ sk_B @ 
% 1.93/2.14            (sk_D_1 @ sk_C @ sk_A @ (k3_lattice3 @ sk_B)) @ sk_C)
% 1.93/2.14         | (r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ sk_C)))
% 1.93/2.14         <= (((r4_lattice3 @ sk_B @ sk_C @ sk_A)))),
% 1.93/2.14      inference('demod', [status(thm)], ['97', '98'])).
% 1.93/2.14  thf('100', plain,
% 1.93/2.14      ((((r3_lattices @ sk_B @ (sk_D_1 @ sk_C @ sk_A @ (k3_lattice3 @ sk_B)) @ 
% 1.93/2.14          sk_C)
% 1.93/2.14         | (v2_struct_0 @ sk_B)
% 1.93/2.14         | (r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ sk_C)))
% 1.93/2.14         <= (((r4_lattice3 @ sk_B @ sk_C @ sk_A)))),
% 1.93/2.14      inference('simplify', [status(thm)], ['99'])).
% 1.93/2.14  thf('101', plain, (~ (v2_struct_0 @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('102', plain,
% 1.93/2.14      ((((r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ sk_C)
% 1.93/2.14         | (r3_lattices @ sk_B @ 
% 1.93/2.14            (sk_D_1 @ sk_C @ sk_A @ (k3_lattice3 @ sk_B)) @ sk_C)))
% 1.93/2.14         <= (((r4_lattice3 @ sk_B @ sk_C @ sk_A)))),
% 1.93/2.14      inference('clc', [status(thm)], ['100', '101'])).
% 1.93/2.14  thf('103', plain,
% 1.93/2.14      ((~ (r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 1.93/2.14           (k4_lattice3 @ sk_B @ sk_C))
% 1.93/2.14        | ~ (r4_lattice3 @ sk_B @ sk_C @ sk_A))),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('104', plain,
% 1.93/2.14      (~
% 1.93/2.14       ((r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 1.93/2.14         (k4_lattice3 @ sk_B @ sk_C))) | 
% 1.93/2.14       ~ ((r4_lattice3 @ sk_B @ sk_C @ sk_A))),
% 1.93/2.14      inference('split', [status(esa)], ['103'])).
% 1.93/2.14  thf('105', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_B))),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('106', plain,
% 1.93/2.14      (![X7 : $i, X8 : $i, X11 : $i]:
% 1.93/2.14         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 1.93/2.14          | (m1_subset_1 @ (sk_D @ X11 @ X7 @ X8) @ (u1_struct_0 @ X8))
% 1.93/2.14          | (r4_lattice3 @ X8 @ X7 @ X11)
% 1.93/2.14          | ~ (l3_lattices @ X8)
% 1.93/2.14          | (v2_struct_0 @ X8))),
% 1.93/2.14      inference('cnf', [status(esa)], [d17_lattice3])).
% 1.93/2.14  thf('107', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((v2_struct_0 @ sk_B)
% 1.93/2.14          | ~ (l3_lattices @ sk_B)
% 1.93/2.14          | (r4_lattice3 @ sk_B @ sk_C @ X0)
% 1.93/2.14          | (m1_subset_1 @ (sk_D @ X0 @ sk_C @ sk_B) @ (u1_struct_0 @ sk_B)))),
% 1.93/2.14      inference('sup-', [status(thm)], ['105', '106'])).
% 1.93/2.14  thf('108', plain, ((l3_lattices @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('109', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((v2_struct_0 @ sk_B)
% 1.93/2.14          | (r4_lattice3 @ sk_B @ sk_C @ X0)
% 1.93/2.14          | (m1_subset_1 @ (sk_D @ X0 @ sk_C @ sk_B) @ (u1_struct_0 @ sk_B)))),
% 1.93/2.14      inference('demod', [status(thm)], ['107', '108'])).
% 1.93/2.14  thf('110', plain, (~ (v2_struct_0 @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('111', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((m1_subset_1 @ (sk_D @ X0 @ sk_C @ sk_B) @ (u1_struct_0 @ sk_B))
% 1.93/2.14          | (r4_lattice3 @ sk_B @ sk_C @ X0))),
% 1.93/2.14      inference('clc', [status(thm)], ['109', '110'])).
% 1.93/2.14  thf('112', plain,
% 1.93/2.14      (![X12 : $i, X13 : $i]:
% 1.93/2.14         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 1.93/2.14          | ((k4_lattice3 @ X13 @ X12) = (X12))
% 1.93/2.14          | ~ (l3_lattices @ X13)
% 1.93/2.14          | ~ (v10_lattices @ X13)
% 1.93/2.14          | (v2_struct_0 @ X13))),
% 1.93/2.14      inference('cnf', [status(esa)], [d3_lattice3])).
% 1.93/2.14  thf('113', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((r4_lattice3 @ sk_B @ sk_C @ X0)
% 1.93/2.14          | (v2_struct_0 @ sk_B)
% 1.93/2.14          | ~ (v10_lattices @ sk_B)
% 1.93/2.14          | ~ (l3_lattices @ sk_B)
% 1.93/2.14          | ((k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B))
% 1.93/2.14              = (sk_D @ X0 @ sk_C @ sk_B)))),
% 1.93/2.14      inference('sup-', [status(thm)], ['111', '112'])).
% 1.93/2.14  thf('114', plain, ((v10_lattices @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('115', plain, ((l3_lattices @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('116', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((r4_lattice3 @ sk_B @ sk_C @ X0)
% 1.93/2.14          | (v2_struct_0 @ sk_B)
% 1.93/2.14          | ((k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B))
% 1.93/2.14              = (sk_D @ X0 @ sk_C @ sk_B)))),
% 1.93/2.14      inference('demod', [status(thm)], ['113', '114', '115'])).
% 1.93/2.14  thf('117', plain, (~ (v2_struct_0 @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('118', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         (((k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B))
% 1.93/2.14            = (sk_D @ X0 @ sk_C @ sk_B))
% 1.93/2.14          | (r4_lattice3 @ sk_B @ sk_C @ X0))),
% 1.93/2.14      inference('clc', [status(thm)], ['116', '117'])).
% 1.93/2.14  thf('119', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_B))),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('120', plain,
% 1.93/2.14      (![X7 : $i, X8 : $i, X11 : $i]:
% 1.93/2.14         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 1.93/2.14          | (r2_hidden @ (sk_D @ X11 @ X7 @ X8) @ X11)
% 1.93/2.14          | (r4_lattice3 @ X8 @ X7 @ X11)
% 1.93/2.14          | ~ (l3_lattices @ X8)
% 1.93/2.14          | (v2_struct_0 @ X8))),
% 1.93/2.14      inference('cnf', [status(esa)], [d17_lattice3])).
% 1.93/2.14  thf('121', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((v2_struct_0 @ sk_B)
% 1.93/2.14          | ~ (l3_lattices @ sk_B)
% 1.93/2.14          | (r4_lattice3 @ sk_B @ sk_C @ X0)
% 1.93/2.14          | (r2_hidden @ (sk_D @ X0 @ sk_C @ sk_B) @ X0))),
% 1.93/2.14      inference('sup-', [status(thm)], ['119', '120'])).
% 1.93/2.14  thf('122', plain, ((l3_lattices @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('123', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((v2_struct_0 @ sk_B)
% 1.93/2.14          | (r4_lattice3 @ sk_B @ sk_C @ X0)
% 1.93/2.14          | (r2_hidden @ (sk_D @ X0 @ sk_C @ sk_B) @ X0))),
% 1.93/2.14      inference('demod', [status(thm)], ['121', '122'])).
% 1.93/2.14  thf('124', plain, (~ (v2_struct_0 @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('125', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((r2_hidden @ (sk_D @ X0 @ sk_C @ sk_B) @ X0)
% 1.93/2.14          | (r4_lattice3 @ sk_B @ sk_C @ X0))),
% 1.93/2.14      inference('clc', [status(thm)], ['123', '124'])).
% 1.93/2.14  thf('126', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         (((k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B))
% 1.93/2.14            = (sk_D @ X0 @ sk_C @ sk_B))
% 1.93/2.14          | (r4_lattice3 @ sk_B @ sk_C @ X0))),
% 1.93/2.14      inference('clc', [status(thm)], ['116', '117'])).
% 1.93/2.14  thf('127', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((m1_subset_1 @ (sk_D @ X0 @ sk_C @ sk_B) @ (u1_struct_0 @ sk_B))
% 1.93/2.14          | (r4_lattice3 @ sk_B @ sk_C @ X0))),
% 1.93/2.14      inference('clc', [status(thm)], ['109', '110'])).
% 1.93/2.14  thf('128', plain,
% 1.93/2.14      (![X21 : $i, X22 : $i]:
% 1.93/2.14         (~ (l3_lattices @ X21)
% 1.93/2.14          | ~ (v10_lattices @ X21)
% 1.93/2.14          | (v2_struct_0 @ X21)
% 1.93/2.14          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 1.93/2.14          | (m1_subset_1 @ (k4_lattice3 @ X21 @ X22) @ 
% 1.93/2.14             (u1_struct_0 @ (k3_lattice3 @ X21))))),
% 1.93/2.14      inference('cnf', [status(esa)], [dt_k4_lattice3])).
% 1.93/2.14  thf('129', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((r4_lattice3 @ sk_B @ sk_C @ X0)
% 1.93/2.14          | (m1_subset_1 @ (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B)) @ 
% 1.93/2.14             (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 1.93/2.14          | (v2_struct_0 @ sk_B)
% 1.93/2.14          | ~ (v10_lattices @ sk_B)
% 1.93/2.14          | ~ (l3_lattices @ sk_B))),
% 1.93/2.14      inference('sup-', [status(thm)], ['127', '128'])).
% 1.93/2.14  thf('130', plain, ((v10_lattices @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('131', plain, ((l3_lattices @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('132', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((r4_lattice3 @ sk_B @ sk_C @ X0)
% 1.93/2.14          | (m1_subset_1 @ (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B)) @ 
% 1.93/2.14             (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 1.93/2.14          | (v2_struct_0 @ sk_B))),
% 1.93/2.14      inference('demod', [status(thm)], ['129', '130', '131'])).
% 1.93/2.14  thf('133', plain, (~ (v2_struct_0 @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('134', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((m1_subset_1 @ (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B)) @ 
% 1.93/2.14           (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 1.93/2.14          | (r4_lattice3 @ sk_B @ sk_C @ X0))),
% 1.93/2.14      inference('clc', [status(thm)], ['132', '133'])).
% 1.93/2.14  thf('135', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((m1_subset_1 @ (sk_D @ X0 @ sk_C @ sk_B) @ 
% 1.93/2.14           (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 1.93/2.14          | (r4_lattice3 @ sk_B @ sk_C @ X0)
% 1.93/2.14          | (r4_lattice3 @ sk_B @ sk_C @ X0))),
% 1.93/2.14      inference('sup+', [status(thm)], ['126', '134'])).
% 1.93/2.14  thf('136', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((r4_lattice3 @ sk_B @ sk_C @ X0)
% 1.93/2.14          | (m1_subset_1 @ (sk_D @ X0 @ sk_C @ sk_B) @ 
% 1.93/2.14             (u1_struct_0 @ (k3_lattice3 @ sk_B))))),
% 1.93/2.14      inference('simplify', [status(thm)], ['135'])).
% 1.93/2.14  thf('137', plain, (((k4_lattice3 @ sk_B @ sk_C) = (sk_C))),
% 1.93/2.14      inference('clc', [status(thm)], ['10', '11'])).
% 1.93/2.14  thf('138', plain,
% 1.93/2.14      (((r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 1.93/2.14         (k4_lattice3 @ sk_B @ sk_C)))
% 1.93/2.14         <= (((r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 1.93/2.14               (k4_lattice3 @ sk_B @ sk_C))))),
% 1.93/2.14      inference('split', [status(esa)], ['50'])).
% 1.93/2.14  thf('139', plain,
% 1.93/2.14      (((r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ sk_C))
% 1.93/2.14         <= (((r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 1.93/2.14               (k4_lattice3 @ sk_B @ sk_C))))),
% 1.93/2.14      inference('sup+', [status(thm)], ['137', '138'])).
% 1.93/2.14  thf('140', plain,
% 1.93/2.14      (![X20 : $i]:
% 1.93/2.14         ((l1_orders_2 @ (k3_lattice3 @ X20))
% 1.93/2.14          | ~ (l3_lattices @ X20)
% 1.93/2.14          | ~ (v10_lattices @ X20)
% 1.93/2.14          | (v2_struct_0 @ X20))),
% 1.93/2.14      inference('cnf', [status(esa)], [dt_k3_lattice3])).
% 1.93/2.14  thf('141', plain,
% 1.93/2.14      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))),
% 1.93/2.14      inference('clc', [status(thm)], ['15', '16'])).
% 1.93/2.14  thf('142', plain,
% 1.93/2.14      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 1.93/2.14         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 1.93/2.14          | ~ (r2_lattice3 @ X17 @ X18 @ X16)
% 1.93/2.14          | ~ (r2_hidden @ X19 @ X18)
% 1.93/2.14          | (r1_orders_2 @ X17 @ X19 @ X16)
% 1.93/2.14          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 1.93/2.14          | ~ (l1_orders_2 @ X17))),
% 1.93/2.14      inference('cnf', [status(esa)], [d9_lattice3])).
% 1.93/2.14  thf('143', plain,
% 1.93/2.14      (![X0 : $i, X1 : $i]:
% 1.93/2.14         (~ (l1_orders_2 @ (k3_lattice3 @ sk_B))
% 1.93/2.14          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 1.93/2.14          | (r1_orders_2 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 1.93/2.14          | ~ (r2_hidden @ X0 @ X1)
% 1.93/2.14          | ~ (r2_lattice3 @ (k3_lattice3 @ sk_B) @ X1 @ sk_C))),
% 1.93/2.14      inference('sup-', [status(thm)], ['141', '142'])).
% 1.93/2.14  thf('144', plain,
% 1.93/2.14      (![X0 : $i, X1 : $i]:
% 1.93/2.14         ((v2_struct_0 @ sk_B)
% 1.93/2.14          | ~ (v10_lattices @ sk_B)
% 1.93/2.14          | ~ (l3_lattices @ sk_B)
% 1.93/2.14          | ~ (r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 1.93/2.14          | ~ (r2_hidden @ X1 @ X0)
% 1.93/2.14          | (r1_orders_2 @ (k3_lattice3 @ sk_B) @ X1 @ sk_C)
% 1.93/2.14          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k3_lattice3 @ sk_B))))),
% 1.93/2.14      inference('sup-', [status(thm)], ['140', '143'])).
% 1.93/2.14  thf('145', plain, ((v10_lattices @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('146', plain, ((l3_lattices @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('147', plain,
% 1.93/2.14      (![X0 : $i, X1 : $i]:
% 1.93/2.14         ((v2_struct_0 @ sk_B)
% 1.93/2.14          | ~ (r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 1.93/2.14          | ~ (r2_hidden @ X1 @ X0)
% 1.93/2.14          | (r1_orders_2 @ (k3_lattice3 @ sk_B) @ X1 @ sk_C)
% 1.93/2.14          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k3_lattice3 @ sk_B))))),
% 1.93/2.14      inference('demod', [status(thm)], ['144', '145', '146'])).
% 1.93/2.14  thf('148', plain,
% 1.93/2.14      ((![X0 : $i]:
% 1.93/2.14          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 1.93/2.14           | (r1_orders_2 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 1.93/2.14           | ~ (r2_hidden @ X0 @ sk_A)
% 1.93/2.14           | (v2_struct_0 @ sk_B)))
% 1.93/2.14         <= (((r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 1.93/2.14               (k4_lattice3 @ sk_B @ sk_C))))),
% 1.93/2.14      inference('sup-', [status(thm)], ['139', '147'])).
% 1.93/2.14  thf('149', plain,
% 1.93/2.14      ((![X0 : $i]:
% 1.93/2.14          ((r4_lattice3 @ sk_B @ sk_C @ X0)
% 1.93/2.14           | (v2_struct_0 @ sk_B)
% 1.93/2.14           | ~ (r2_hidden @ (sk_D @ X0 @ sk_C @ sk_B) @ sk_A)
% 1.93/2.14           | (r1_orders_2 @ (k3_lattice3 @ sk_B) @ (sk_D @ X0 @ sk_C @ sk_B) @ 
% 1.93/2.14              sk_C)))
% 1.93/2.14         <= (((r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 1.93/2.14               (k4_lattice3 @ sk_B @ sk_C))))),
% 1.93/2.14      inference('sup-', [status(thm)], ['136', '148'])).
% 1.93/2.14  thf('150', plain,
% 1.93/2.14      ((((r4_lattice3 @ sk_B @ sk_C @ sk_A)
% 1.93/2.14         | (r1_orders_2 @ (k3_lattice3 @ sk_B) @ (sk_D @ sk_A @ sk_C @ sk_B) @ 
% 1.93/2.14            sk_C)
% 1.93/2.14         | (v2_struct_0 @ sk_B)
% 1.93/2.14         | (r4_lattice3 @ sk_B @ sk_C @ sk_A)))
% 1.93/2.14         <= (((r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 1.93/2.14               (k4_lattice3 @ sk_B @ sk_C))))),
% 1.93/2.14      inference('sup-', [status(thm)], ['125', '149'])).
% 1.93/2.14  thf('151', plain,
% 1.93/2.14      ((((v2_struct_0 @ sk_B)
% 1.93/2.14         | (r1_orders_2 @ (k3_lattice3 @ sk_B) @ (sk_D @ sk_A @ sk_C @ sk_B) @ 
% 1.93/2.14            sk_C)
% 1.93/2.14         | (r4_lattice3 @ sk_B @ sk_C @ sk_A)))
% 1.93/2.14         <= (((r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 1.93/2.14               (k4_lattice3 @ sk_B @ sk_C))))),
% 1.93/2.14      inference('simplify', [status(thm)], ['150'])).
% 1.93/2.14  thf('152', plain, (~ (v2_struct_0 @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('153', plain,
% 1.93/2.14      ((((r4_lattice3 @ sk_B @ sk_C @ sk_A)
% 1.93/2.14         | (r1_orders_2 @ (k3_lattice3 @ sk_B) @ (sk_D @ sk_A @ sk_C @ sk_B) @ 
% 1.93/2.14            sk_C)))
% 1.93/2.14         <= (((r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 1.93/2.14               (k4_lattice3 @ sk_B @ sk_C))))),
% 1.93/2.14      inference('clc', [status(thm)], ['151', '152'])).
% 1.93/2.14  thf('154', plain,
% 1.93/2.14      (![X20 : $i]:
% 1.93/2.14         ((l1_orders_2 @ (k3_lattice3 @ X20))
% 1.93/2.14          | ~ (l3_lattices @ X20)
% 1.93/2.14          | ~ (v10_lattices @ X20)
% 1.93/2.14          | (v2_struct_0 @ X20))),
% 1.93/2.14      inference('cnf', [status(esa)], [dt_k3_lattice3])).
% 1.93/2.14  thf('155', plain,
% 1.93/2.14      (![X20 : $i]:
% 1.93/2.14         ((v3_orders_2 @ (k3_lattice3 @ X20))
% 1.93/2.14          | ~ (l3_lattices @ X20)
% 1.93/2.14          | ~ (v10_lattices @ X20)
% 1.93/2.14          | (v2_struct_0 @ X20))),
% 1.93/2.14      inference('cnf', [status(esa)], [dt_k3_lattice3])).
% 1.93/2.14  thf('156', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((r4_lattice3 @ sk_B @ sk_C @ X0)
% 1.93/2.14          | (m1_subset_1 @ (sk_D @ X0 @ sk_C @ sk_B) @ 
% 1.93/2.14             (u1_struct_0 @ (k3_lattice3 @ sk_B))))),
% 1.93/2.14      inference('simplify', [status(thm)], ['135'])).
% 1.93/2.14  thf(redefinition_r3_orders_2, axiom,
% 1.93/2.14    (![A:$i,B:$i,C:$i]:
% 1.93/2.14     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.93/2.14         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 1.93/2.14         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 1.93/2.14       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 1.93/2.14  thf('157', plain,
% 1.93/2.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.93/2.14         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 1.93/2.14          | ~ (l1_orders_2 @ X1)
% 1.93/2.14          | ~ (v3_orders_2 @ X1)
% 1.93/2.14          | (v2_struct_0 @ X1)
% 1.93/2.14          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 1.93/2.14          | (r3_orders_2 @ X1 @ X0 @ X2)
% 1.93/2.14          | ~ (r1_orders_2 @ X1 @ X0 @ X2))),
% 1.93/2.14      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 1.93/2.14  thf('158', plain,
% 1.93/2.14      (![X0 : $i, X1 : $i]:
% 1.93/2.14         ((r4_lattice3 @ sk_B @ sk_C @ X0)
% 1.93/2.14          | ~ (r1_orders_2 @ (k3_lattice3 @ sk_B) @ 
% 1.93/2.14               (sk_D @ X0 @ sk_C @ sk_B) @ X1)
% 1.93/2.14          | (r3_orders_2 @ (k3_lattice3 @ sk_B) @ (sk_D @ X0 @ sk_C @ sk_B) @ 
% 1.93/2.14             X1)
% 1.93/2.14          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 1.93/2.14          | (v2_struct_0 @ (k3_lattice3 @ sk_B))
% 1.93/2.14          | ~ (v3_orders_2 @ (k3_lattice3 @ sk_B))
% 1.93/2.14          | ~ (l1_orders_2 @ (k3_lattice3 @ sk_B)))),
% 1.93/2.14      inference('sup-', [status(thm)], ['156', '157'])).
% 1.93/2.14  thf('159', plain,
% 1.93/2.14      (![X0 : $i, X1 : $i]:
% 1.93/2.14         ((v2_struct_0 @ sk_B)
% 1.93/2.14          | ~ (v10_lattices @ sk_B)
% 1.93/2.14          | ~ (l3_lattices @ sk_B)
% 1.93/2.14          | ~ (l1_orders_2 @ (k3_lattice3 @ sk_B))
% 1.93/2.14          | (v2_struct_0 @ (k3_lattice3 @ sk_B))
% 1.93/2.14          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 1.93/2.14          | (r3_orders_2 @ (k3_lattice3 @ sk_B) @ (sk_D @ X1 @ sk_C @ sk_B) @ 
% 1.93/2.14             X0)
% 1.93/2.14          | ~ (r1_orders_2 @ (k3_lattice3 @ sk_B) @ 
% 1.93/2.14               (sk_D @ X1 @ sk_C @ sk_B) @ X0)
% 1.93/2.14          | (r4_lattice3 @ sk_B @ sk_C @ X1))),
% 1.93/2.14      inference('sup-', [status(thm)], ['155', '158'])).
% 1.93/2.14  thf('160', plain, ((v10_lattices @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('161', plain, ((l3_lattices @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('162', plain,
% 1.93/2.14      (![X0 : $i, X1 : $i]:
% 1.93/2.14         ((v2_struct_0 @ sk_B)
% 1.93/2.14          | ~ (l1_orders_2 @ (k3_lattice3 @ sk_B))
% 1.93/2.14          | (v2_struct_0 @ (k3_lattice3 @ sk_B))
% 1.93/2.14          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 1.93/2.14          | (r3_orders_2 @ (k3_lattice3 @ sk_B) @ (sk_D @ X1 @ sk_C @ sk_B) @ 
% 1.93/2.14             X0)
% 1.93/2.14          | ~ (r1_orders_2 @ (k3_lattice3 @ sk_B) @ 
% 1.93/2.14               (sk_D @ X1 @ sk_C @ sk_B) @ X0)
% 1.93/2.14          | (r4_lattice3 @ sk_B @ sk_C @ X1))),
% 1.93/2.14      inference('demod', [status(thm)], ['159', '160', '161'])).
% 1.93/2.14  thf('163', plain,
% 1.93/2.14      (![X0 : $i, X1 : $i]:
% 1.93/2.14         ((v2_struct_0 @ sk_B)
% 1.93/2.14          | ~ (v10_lattices @ sk_B)
% 1.93/2.14          | ~ (l3_lattices @ sk_B)
% 1.93/2.14          | (r4_lattice3 @ sk_B @ sk_C @ X0)
% 1.93/2.14          | ~ (r1_orders_2 @ (k3_lattice3 @ sk_B) @ 
% 1.93/2.14               (sk_D @ X0 @ sk_C @ sk_B) @ X1)
% 1.93/2.14          | (r3_orders_2 @ (k3_lattice3 @ sk_B) @ (sk_D @ X0 @ sk_C @ sk_B) @ 
% 1.93/2.14             X1)
% 1.93/2.14          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 1.93/2.14          | (v2_struct_0 @ (k3_lattice3 @ sk_B))
% 1.93/2.14          | (v2_struct_0 @ sk_B))),
% 1.93/2.14      inference('sup-', [status(thm)], ['154', '162'])).
% 1.93/2.14  thf('164', plain, ((v10_lattices @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('165', plain, ((l3_lattices @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('166', plain,
% 1.93/2.14      (![X0 : $i, X1 : $i]:
% 1.93/2.14         ((v2_struct_0 @ sk_B)
% 1.93/2.14          | (r4_lattice3 @ sk_B @ sk_C @ X0)
% 1.93/2.14          | ~ (r1_orders_2 @ (k3_lattice3 @ sk_B) @ 
% 1.93/2.14               (sk_D @ X0 @ sk_C @ sk_B) @ X1)
% 1.93/2.14          | (r3_orders_2 @ (k3_lattice3 @ sk_B) @ (sk_D @ X0 @ sk_C @ sk_B) @ 
% 1.93/2.14             X1)
% 1.93/2.14          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 1.93/2.14          | (v2_struct_0 @ (k3_lattice3 @ sk_B))
% 1.93/2.14          | (v2_struct_0 @ sk_B))),
% 1.93/2.14      inference('demod', [status(thm)], ['163', '164', '165'])).
% 1.93/2.14  thf('167', plain,
% 1.93/2.14      (![X0 : $i, X1 : $i]:
% 1.93/2.14         ((v2_struct_0 @ (k3_lattice3 @ sk_B))
% 1.93/2.14          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 1.93/2.14          | (r3_orders_2 @ (k3_lattice3 @ sk_B) @ (sk_D @ X0 @ sk_C @ sk_B) @ 
% 1.93/2.14             X1)
% 1.93/2.14          | ~ (r1_orders_2 @ (k3_lattice3 @ sk_B) @ 
% 1.93/2.14               (sk_D @ X0 @ sk_C @ sk_B) @ X1)
% 1.93/2.14          | (r4_lattice3 @ sk_B @ sk_C @ X0)
% 1.93/2.14          | (v2_struct_0 @ sk_B))),
% 1.93/2.14      inference('simplify', [status(thm)], ['166'])).
% 1.93/2.14  thf('168', plain,
% 1.93/2.14      ((((r4_lattice3 @ sk_B @ sk_C @ sk_A)
% 1.93/2.14         | (v2_struct_0 @ sk_B)
% 1.93/2.14         | (r4_lattice3 @ sk_B @ sk_C @ sk_A)
% 1.93/2.14         | (r3_orders_2 @ (k3_lattice3 @ sk_B) @ (sk_D @ sk_A @ sk_C @ sk_B) @ 
% 1.93/2.14            sk_C)
% 1.93/2.14         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 1.93/2.14         | (v2_struct_0 @ (k3_lattice3 @ sk_B))))
% 1.93/2.14         <= (((r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 1.93/2.14               (k4_lattice3 @ sk_B @ sk_C))))),
% 1.93/2.14      inference('sup-', [status(thm)], ['153', '167'])).
% 1.93/2.14  thf('169', plain,
% 1.93/2.14      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))),
% 1.93/2.14      inference('clc', [status(thm)], ['15', '16'])).
% 1.93/2.14  thf('170', plain,
% 1.93/2.14      ((((r4_lattice3 @ sk_B @ sk_C @ sk_A)
% 1.93/2.14         | (v2_struct_0 @ sk_B)
% 1.93/2.14         | (r4_lattice3 @ sk_B @ sk_C @ sk_A)
% 1.93/2.14         | (r3_orders_2 @ (k3_lattice3 @ sk_B) @ (sk_D @ sk_A @ sk_C @ sk_B) @ 
% 1.93/2.14            sk_C)
% 1.93/2.14         | (v2_struct_0 @ (k3_lattice3 @ sk_B))))
% 1.93/2.14         <= (((r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 1.93/2.14               (k4_lattice3 @ sk_B @ sk_C))))),
% 1.93/2.14      inference('demod', [status(thm)], ['168', '169'])).
% 1.93/2.14  thf('171', plain,
% 1.93/2.14      ((((v2_struct_0 @ (k3_lattice3 @ sk_B))
% 1.93/2.14         | (r3_orders_2 @ (k3_lattice3 @ sk_B) @ (sk_D @ sk_A @ sk_C @ sk_B) @ 
% 1.93/2.14            sk_C)
% 1.93/2.14         | (v2_struct_0 @ sk_B)
% 1.93/2.14         | (r4_lattice3 @ sk_B @ sk_C @ sk_A)))
% 1.93/2.14         <= (((r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 1.93/2.14               (k4_lattice3 @ sk_B @ sk_C))))),
% 1.93/2.14      inference('simplify', [status(thm)], ['170'])).
% 1.93/2.14  thf('172', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((m1_subset_1 @ (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B)) @ 
% 1.93/2.14           (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 1.93/2.14          | (r4_lattice3 @ sk_B @ sk_C @ X0))),
% 1.93/2.14      inference('clc', [status(thm)], ['132', '133'])).
% 1.93/2.14  thf('173', plain,
% 1.93/2.14      (![X14 : $i, X15 : $i]:
% 1.93/2.14         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ (k3_lattice3 @ X15)))
% 1.93/2.14          | ((k5_lattice3 @ X15 @ X14) = (X14))
% 1.93/2.14          | ~ (l3_lattices @ X15)
% 1.93/2.14          | ~ (v10_lattices @ X15)
% 1.93/2.14          | (v2_struct_0 @ X15))),
% 1.93/2.14      inference('cnf', [status(esa)], [d4_lattice3])).
% 1.93/2.14  thf('174', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((r4_lattice3 @ sk_B @ sk_C @ X0)
% 1.93/2.14          | (v2_struct_0 @ sk_B)
% 1.93/2.14          | ~ (v10_lattices @ sk_B)
% 1.93/2.14          | ~ (l3_lattices @ sk_B)
% 1.93/2.14          | ((k5_lattice3 @ sk_B @ 
% 1.93/2.14              (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B)))
% 1.93/2.14              = (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B))))),
% 1.93/2.14      inference('sup-', [status(thm)], ['172', '173'])).
% 1.93/2.14  thf('175', plain, ((v10_lattices @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('176', plain, ((l3_lattices @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('177', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((r4_lattice3 @ sk_B @ sk_C @ X0)
% 1.93/2.14          | (v2_struct_0 @ sk_B)
% 1.93/2.14          | ((k5_lattice3 @ sk_B @ 
% 1.93/2.14              (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B)))
% 1.93/2.14              = (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B))))),
% 1.93/2.14      inference('demod', [status(thm)], ['174', '175', '176'])).
% 1.93/2.14  thf('178', plain, (~ (v2_struct_0 @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('179', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         (((k5_lattice3 @ sk_B @ 
% 1.93/2.14            (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B)))
% 1.93/2.14            = (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B)))
% 1.93/2.14          | (r4_lattice3 @ sk_B @ sk_C @ X0))),
% 1.93/2.14      inference('clc', [status(thm)], ['177', '178'])).
% 1.93/2.14  thf('180', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((m1_subset_1 @ (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B)) @ 
% 1.93/2.14           (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 1.93/2.14          | (r4_lattice3 @ sk_B @ sk_C @ X0))),
% 1.93/2.14      inference('clc', [status(thm)], ['132', '133'])).
% 1.93/2.14  thf('181', plain,
% 1.93/2.14      (![X23 : $i, X24 : $i]:
% 1.93/2.14         (~ (l3_lattices @ X23)
% 1.93/2.14          | ~ (v10_lattices @ X23)
% 1.93/2.14          | (v2_struct_0 @ X23)
% 1.93/2.14          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ (k3_lattice3 @ X23)))
% 1.93/2.14          | (m1_subset_1 @ (k5_lattice3 @ X23 @ X24) @ (u1_struct_0 @ X23)))),
% 1.93/2.14      inference('cnf', [status(esa)], [dt_k5_lattice3])).
% 1.93/2.14  thf('182', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((r4_lattice3 @ sk_B @ sk_C @ X0)
% 1.93/2.14          | (m1_subset_1 @ 
% 1.93/2.14             (k5_lattice3 @ sk_B @ 
% 1.93/2.14              (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B))) @ 
% 1.93/2.14             (u1_struct_0 @ sk_B))
% 1.93/2.14          | (v2_struct_0 @ sk_B)
% 1.93/2.14          | ~ (v10_lattices @ sk_B)
% 1.93/2.14          | ~ (l3_lattices @ sk_B))),
% 1.93/2.14      inference('sup-', [status(thm)], ['180', '181'])).
% 1.93/2.14  thf('183', plain, ((v10_lattices @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('184', plain, ((l3_lattices @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('185', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((r4_lattice3 @ sk_B @ sk_C @ X0)
% 1.93/2.14          | (m1_subset_1 @ 
% 1.93/2.14             (k5_lattice3 @ sk_B @ 
% 1.93/2.14              (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B))) @ 
% 1.93/2.14             (u1_struct_0 @ sk_B))
% 1.93/2.14          | (v2_struct_0 @ sk_B))),
% 1.93/2.14      inference('demod', [status(thm)], ['182', '183', '184'])).
% 1.93/2.14  thf('186', plain, (~ (v2_struct_0 @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('187', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((m1_subset_1 @ 
% 1.93/2.14           (k5_lattice3 @ sk_B @ 
% 1.93/2.14            (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B))) @ 
% 1.93/2.14           (u1_struct_0 @ sk_B))
% 1.93/2.14          | (r4_lattice3 @ sk_B @ sk_C @ X0))),
% 1.93/2.14      inference('clc', [status(thm)], ['185', '186'])).
% 1.93/2.14  thf('188', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((m1_subset_1 @ (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B)) @ 
% 1.93/2.14           (u1_struct_0 @ sk_B))
% 1.93/2.14          | (r4_lattice3 @ sk_B @ sk_C @ X0)
% 1.93/2.14          | (r4_lattice3 @ sk_B @ sk_C @ X0))),
% 1.93/2.14      inference('sup+', [status(thm)], ['179', '187'])).
% 1.93/2.14  thf('189', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((r4_lattice3 @ sk_B @ sk_C @ X0)
% 1.93/2.14          | (m1_subset_1 @ (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B)) @ 
% 1.93/2.14             (u1_struct_0 @ sk_B)))),
% 1.93/2.14      inference('simplify', [status(thm)], ['188'])).
% 1.93/2.14  thf('190', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         (((k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B))
% 1.93/2.14            = (sk_D @ X0 @ sk_C @ sk_B))
% 1.93/2.14          | (r4_lattice3 @ sk_B @ sk_C @ X0))),
% 1.93/2.14      inference('clc', [status(thm)], ['116', '117'])).
% 1.93/2.14  thf('191', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         (((k5_lattice3 @ sk_B @ 
% 1.93/2.14            (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B)))
% 1.93/2.14            = (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B)))
% 1.93/2.14          | (r4_lattice3 @ sk_B @ sk_C @ X0))),
% 1.93/2.14      inference('clc', [status(thm)], ['177', '178'])).
% 1.93/2.14  thf('192', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         (((k5_lattice3 @ sk_B @ 
% 1.93/2.14            (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B)))
% 1.93/2.14            = (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B)))
% 1.93/2.14          | (r4_lattice3 @ sk_B @ sk_C @ X0))),
% 1.93/2.14      inference('clc', [status(thm)], ['177', '178'])).
% 1.93/2.14  thf('193', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((m1_subset_1 @ 
% 1.93/2.14           (k5_lattice3 @ sk_B @ 
% 1.93/2.14            (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B))) @ 
% 1.93/2.14           (u1_struct_0 @ sk_B))
% 1.93/2.14          | (r4_lattice3 @ sk_B @ sk_C @ X0))),
% 1.93/2.14      inference('clc', [status(thm)], ['185', '186'])).
% 1.93/2.14  thf('194', plain,
% 1.93/2.14      (![X12 : $i, X13 : $i]:
% 1.93/2.14         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 1.93/2.14          | ((k4_lattice3 @ X13 @ X12) = (X12))
% 1.93/2.14          | ~ (l3_lattices @ X13)
% 1.93/2.14          | ~ (v10_lattices @ X13)
% 1.93/2.14          | (v2_struct_0 @ X13))),
% 1.93/2.14      inference('cnf', [status(esa)], [d3_lattice3])).
% 1.93/2.14  thf('195', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((r4_lattice3 @ sk_B @ sk_C @ X0)
% 1.93/2.14          | (v2_struct_0 @ sk_B)
% 1.93/2.14          | ~ (v10_lattices @ sk_B)
% 1.93/2.14          | ~ (l3_lattices @ sk_B)
% 1.93/2.14          | ((k4_lattice3 @ sk_B @ 
% 1.93/2.14              (k5_lattice3 @ sk_B @ 
% 1.93/2.14               (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B))))
% 1.93/2.14              = (k5_lattice3 @ sk_B @ 
% 1.93/2.14                 (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B)))))),
% 1.93/2.14      inference('sup-', [status(thm)], ['193', '194'])).
% 1.93/2.14  thf('196', plain, ((v10_lattices @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('197', plain, ((l3_lattices @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('198', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((r4_lattice3 @ sk_B @ sk_C @ X0)
% 1.93/2.14          | (v2_struct_0 @ sk_B)
% 1.93/2.14          | ((k4_lattice3 @ sk_B @ 
% 1.93/2.14              (k5_lattice3 @ sk_B @ 
% 1.93/2.14               (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B))))
% 1.93/2.14              = (k5_lattice3 @ sk_B @ 
% 1.93/2.14                 (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B)))))),
% 1.93/2.14      inference('demod', [status(thm)], ['195', '196', '197'])).
% 1.93/2.14  thf('199', plain, (~ (v2_struct_0 @ sk_B)),
% 1.93/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.14  thf('200', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         (((k4_lattice3 @ sk_B @ 
% 1.93/2.14            (k5_lattice3 @ sk_B @ 
% 1.93/2.14             (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B))))
% 1.93/2.14            = (k5_lattice3 @ sk_B @ 
% 1.93/2.14               (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B))))
% 1.93/2.14          | (r4_lattice3 @ sk_B @ sk_C @ X0))),
% 1.93/2.14      inference('clc', [status(thm)], ['198', '199'])).
% 1.93/2.14  thf('201', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         (((k4_lattice3 @ sk_B @ 
% 1.93/2.14            (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B)))
% 1.93/2.14            = (k5_lattice3 @ sk_B @ 
% 1.93/2.14               (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B))))
% 1.93/2.14          | (r4_lattice3 @ sk_B @ sk_C @ X0)
% 1.93/2.14          | (r4_lattice3 @ sk_B @ sk_C @ X0))),
% 1.93/2.14      inference('sup+', [status(thm)], ['192', '200'])).
% 1.93/2.14  thf('202', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         ((r4_lattice3 @ sk_B @ sk_C @ X0)
% 1.93/2.14          | ((k4_lattice3 @ sk_B @ 
% 1.93/2.14              (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B)))
% 1.93/2.14              = (k5_lattice3 @ sk_B @ 
% 1.93/2.14                 (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B)))))),
% 1.93/2.14      inference('simplify', [status(thm)], ['201'])).
% 1.93/2.14  thf('203', plain, (((k4_lattice3 @ sk_B @ sk_C) = (sk_C))),
% 1.93/2.14      inference('clc', [status(thm)], ['10', '11'])).
% 1.93/2.14  thf(t7_lattice3, axiom,
% 1.93/2.14    (![A:$i]:
% 1.93/2.14     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 1.93/2.14       ( ![B:$i]:
% 1.93/2.14         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.93/2.14           ( ![C:$i]:
% 1.93/2.14             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.93/2.14               ( ( r3_lattices @ A @ B @ C ) <=>
% 1.93/2.14                 ( r3_orders_2 @
% 1.93/2.14                   ( k3_lattice3 @ A ) @ ( k4_lattice3 @ A @ B ) @ 
% 1.93/2.14                   ( k4_lattice3 @ A @ C ) ) ) ) ) ) ) ))).
% 1.93/2.14  thf('204', plain,
% 1.93/2.14      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.93/2.14         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 1.93/2.14          | ~ (r3_orders_2 @ (k3_lattice3 @ X27) @ (k4_lattice3 @ X27 @ X26) @ 
% 1.93/2.14               (k4_lattice3 @ X27 @ X28))
% 1.93/2.14          | (r3_lattices @ X27 @ X26 @ X28)
% 1.93/2.14          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X27))
% 1.93/2.14          | ~ (l3_lattices @ X27)
% 1.93/2.14          | ~ (v10_lattices @ X27)
% 1.93/2.14          | (v2_struct_0 @ X27))),
% 1.93/2.14      inference('cnf', [status(esa)], [t7_lattice3])).
% 1.93/2.14  thf('205', plain,
% 1.93/2.14      (![X0 : $i]:
% 1.93/2.14         (~ (r3_orders_2 @ (k3_lattice3 @ sk_B) @ (k4_lattice3 @ sk_B @ X0) @ 
% 1.93/2.14             sk_C)
% 1.93/2.14          | (v2_struct_0 @ sk_B)
% 1.93/2.14          | ~ (v10_lattices @ sk_B)
% 1.93/2.15          | ~ (l3_lattices @ sk_B)
% 1.93/2.15          | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_B))
% 1.93/2.15          | (r3_lattices @ sk_B @ X0 @ sk_C)
% 1.93/2.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 1.93/2.15      inference('sup-', [status(thm)], ['203', '204'])).
% 1.93/2.15  thf('206', plain, ((v10_lattices @ sk_B)),
% 1.93/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.15  thf('207', plain, ((l3_lattices @ sk_B)),
% 1.93/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.15  thf('208', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_B))),
% 1.93/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.15  thf('209', plain,
% 1.93/2.15      (![X0 : $i]:
% 1.93/2.15         (~ (r3_orders_2 @ (k3_lattice3 @ sk_B) @ (k4_lattice3 @ sk_B @ X0) @ 
% 1.93/2.15             sk_C)
% 1.93/2.15          | (v2_struct_0 @ sk_B)
% 1.93/2.15          | (r3_lattices @ sk_B @ X0 @ sk_C)
% 1.93/2.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 1.93/2.15      inference('demod', [status(thm)], ['205', '206', '207', '208'])).
% 1.93/2.15  thf('210', plain,
% 1.93/2.15      (![X0 : $i]:
% 1.93/2.15         (~ (r3_orders_2 @ (k3_lattice3 @ sk_B) @ 
% 1.93/2.15             (k5_lattice3 @ sk_B @ 
% 1.93/2.15              (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B))) @ 
% 1.93/2.15             sk_C)
% 1.93/2.15          | (r4_lattice3 @ sk_B @ sk_C @ X0)
% 1.93/2.15          | ~ (m1_subset_1 @ 
% 1.93/2.15               (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B)) @ 
% 1.93/2.15               (u1_struct_0 @ sk_B))
% 1.93/2.15          | (r3_lattices @ sk_B @ 
% 1.93/2.15             (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B)) @ sk_C)
% 1.93/2.15          | (v2_struct_0 @ sk_B))),
% 1.93/2.15      inference('sup-', [status(thm)], ['202', '209'])).
% 1.93/2.15  thf('211', plain,
% 1.93/2.15      (![X0 : $i]:
% 1.93/2.15         (~ (r3_orders_2 @ (k3_lattice3 @ sk_B) @ 
% 1.93/2.15             (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B)) @ sk_C)
% 1.93/2.15          | (r4_lattice3 @ sk_B @ sk_C @ X0)
% 1.93/2.15          | (v2_struct_0 @ sk_B)
% 1.93/2.15          | (r3_lattices @ sk_B @ 
% 1.93/2.15             (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B)) @ sk_C)
% 1.93/2.15          | ~ (m1_subset_1 @ 
% 1.93/2.15               (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B)) @ 
% 1.93/2.15               (u1_struct_0 @ sk_B))
% 1.93/2.15          | (r4_lattice3 @ sk_B @ sk_C @ X0))),
% 1.93/2.15      inference('sup-', [status(thm)], ['191', '210'])).
% 1.93/2.15  thf('212', plain,
% 1.93/2.15      (![X0 : $i]:
% 1.93/2.15         (~ (m1_subset_1 @ (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B)) @ 
% 1.93/2.15             (u1_struct_0 @ sk_B))
% 1.93/2.15          | (r3_lattices @ sk_B @ 
% 1.93/2.15             (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B)) @ sk_C)
% 1.93/2.15          | (v2_struct_0 @ sk_B)
% 1.93/2.15          | (r4_lattice3 @ sk_B @ sk_C @ X0)
% 1.93/2.15          | ~ (r3_orders_2 @ (k3_lattice3 @ sk_B) @ 
% 1.93/2.15               (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B)) @ sk_C))),
% 1.93/2.15      inference('simplify', [status(thm)], ['211'])).
% 1.93/2.15  thf('213', plain,
% 1.93/2.15      (![X0 : $i]:
% 1.93/2.15         (~ (r3_orders_2 @ (k3_lattice3 @ sk_B) @ (sk_D @ X0 @ sk_C @ sk_B) @ 
% 1.93/2.15             sk_C)
% 1.93/2.15          | (r4_lattice3 @ sk_B @ sk_C @ X0)
% 1.93/2.15          | (r4_lattice3 @ sk_B @ sk_C @ X0)
% 1.93/2.15          | (v2_struct_0 @ sk_B)
% 1.93/2.15          | (r3_lattices @ sk_B @ 
% 1.93/2.15             (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B)) @ sk_C)
% 1.93/2.15          | ~ (m1_subset_1 @ 
% 1.93/2.15               (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B)) @ 
% 1.93/2.15               (u1_struct_0 @ sk_B)))),
% 1.93/2.15      inference('sup-', [status(thm)], ['190', '212'])).
% 1.93/2.15  thf('214', plain,
% 1.93/2.15      (![X0 : $i]:
% 1.93/2.15         (~ (m1_subset_1 @ (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B)) @ 
% 1.93/2.15             (u1_struct_0 @ sk_B))
% 1.93/2.15          | (r3_lattices @ sk_B @ 
% 1.93/2.15             (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B)) @ sk_C)
% 1.93/2.15          | (v2_struct_0 @ sk_B)
% 1.93/2.15          | (r4_lattice3 @ sk_B @ sk_C @ X0)
% 1.93/2.15          | ~ (r3_orders_2 @ (k3_lattice3 @ sk_B) @ 
% 1.93/2.15               (sk_D @ X0 @ sk_C @ sk_B) @ sk_C))),
% 1.93/2.15      inference('simplify', [status(thm)], ['213'])).
% 1.93/2.15  thf('215', plain,
% 1.93/2.15      (![X0 : $i]:
% 1.93/2.15         ((r4_lattice3 @ sk_B @ sk_C @ X0)
% 1.93/2.15          | ~ (r3_orders_2 @ (k3_lattice3 @ sk_B) @ 
% 1.93/2.15               (sk_D @ X0 @ sk_C @ sk_B) @ sk_C)
% 1.93/2.15          | (r4_lattice3 @ sk_B @ sk_C @ X0)
% 1.93/2.15          | (v2_struct_0 @ sk_B)
% 1.93/2.15          | (r3_lattices @ sk_B @ 
% 1.93/2.15             (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B)) @ sk_C))),
% 1.93/2.15      inference('sup-', [status(thm)], ['189', '214'])).
% 1.93/2.15  thf('216', plain,
% 1.93/2.15      (![X0 : $i]:
% 1.93/2.15         ((r3_lattices @ sk_B @ 
% 1.93/2.15           (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B)) @ sk_C)
% 1.93/2.15          | (v2_struct_0 @ sk_B)
% 1.93/2.15          | ~ (r3_orders_2 @ (k3_lattice3 @ sk_B) @ 
% 1.93/2.15               (sk_D @ X0 @ sk_C @ sk_B) @ sk_C)
% 1.93/2.15          | (r4_lattice3 @ sk_B @ sk_C @ X0))),
% 1.93/2.15      inference('simplify', [status(thm)], ['215'])).
% 1.93/2.15  thf('217', plain,
% 1.93/2.15      ((((r4_lattice3 @ sk_B @ sk_C @ sk_A)
% 1.93/2.15         | (v2_struct_0 @ sk_B)
% 1.93/2.15         | (v2_struct_0 @ (k3_lattice3 @ sk_B))
% 1.93/2.15         | (r4_lattice3 @ sk_B @ sk_C @ sk_A)
% 1.93/2.15         | (v2_struct_0 @ sk_B)
% 1.93/2.15         | (r3_lattices @ sk_B @ 
% 1.93/2.15            (k4_lattice3 @ sk_B @ (sk_D @ sk_A @ sk_C @ sk_B)) @ sk_C)))
% 1.93/2.15         <= (((r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 1.93/2.15               (k4_lattice3 @ sk_B @ sk_C))))),
% 1.93/2.15      inference('sup-', [status(thm)], ['171', '216'])).
% 1.93/2.15  thf('218', plain,
% 1.93/2.15      ((((r3_lattices @ sk_B @ 
% 1.93/2.15          (k4_lattice3 @ sk_B @ (sk_D @ sk_A @ sk_C @ sk_B)) @ sk_C)
% 1.93/2.15         | (v2_struct_0 @ (k3_lattice3 @ sk_B))
% 1.93/2.15         | (v2_struct_0 @ sk_B)
% 1.93/2.15         | (r4_lattice3 @ sk_B @ sk_C @ sk_A)))
% 1.93/2.15         <= (((r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 1.93/2.15               (k4_lattice3 @ sk_B @ sk_C))))),
% 1.93/2.15      inference('simplify', [status(thm)], ['217'])).
% 1.93/2.15  thf('219', plain,
% 1.93/2.15      ((((r3_lattices @ sk_B @ (sk_D @ sk_A @ sk_C @ sk_B) @ sk_C)
% 1.93/2.15         | (r4_lattice3 @ sk_B @ sk_C @ sk_A)
% 1.93/2.15         | (r4_lattice3 @ sk_B @ sk_C @ sk_A)
% 1.93/2.15         | (v2_struct_0 @ sk_B)
% 1.93/2.15         | (v2_struct_0 @ (k3_lattice3 @ sk_B))))
% 1.93/2.15         <= (((r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 1.93/2.15               (k4_lattice3 @ sk_B @ sk_C))))),
% 1.93/2.15      inference('sup+', [status(thm)], ['118', '218'])).
% 1.93/2.15  thf('220', plain,
% 1.93/2.15      ((((v2_struct_0 @ (k3_lattice3 @ sk_B))
% 1.93/2.15         | (v2_struct_0 @ sk_B)
% 1.93/2.15         | (r4_lattice3 @ sk_B @ sk_C @ sk_A)
% 1.93/2.15         | (r3_lattices @ sk_B @ (sk_D @ sk_A @ sk_C @ sk_B) @ sk_C)))
% 1.93/2.15         <= (((r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 1.93/2.15               (k4_lattice3 @ sk_B @ sk_C))))),
% 1.93/2.15      inference('simplify', [status(thm)], ['219'])).
% 1.93/2.15  thf('221', plain,
% 1.93/2.15      (![X0 : $i]:
% 1.93/2.15         ((m1_subset_1 @ (sk_D @ X0 @ sk_C @ sk_B) @ (u1_struct_0 @ sk_B))
% 1.93/2.15          | (r4_lattice3 @ sk_B @ sk_C @ X0))),
% 1.93/2.15      inference('clc', [status(thm)], ['109', '110'])).
% 1.93/2.15  thf('222', plain,
% 1.93/2.15      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.93/2.15         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 1.93/2.15          | ~ (l3_lattices @ X5)
% 1.93/2.15          | ~ (v9_lattices @ X5)
% 1.93/2.15          | ~ (v8_lattices @ X5)
% 1.93/2.15          | ~ (v6_lattices @ X5)
% 1.93/2.15          | (v2_struct_0 @ X5)
% 1.93/2.15          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 1.93/2.15          | (r1_lattices @ X5 @ X4 @ X6)
% 1.93/2.15          | ~ (r3_lattices @ X5 @ X4 @ X6))),
% 1.93/2.15      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 1.93/2.15  thf('223', plain,
% 1.93/2.15      (![X0 : $i, X1 : $i]:
% 1.93/2.15         ((r4_lattice3 @ sk_B @ sk_C @ X0)
% 1.93/2.15          | ~ (r3_lattices @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B) @ X1)
% 1.93/2.15          | (r1_lattices @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B) @ X1)
% 1.93/2.15          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 1.93/2.15          | (v2_struct_0 @ sk_B)
% 1.93/2.15          | ~ (v6_lattices @ sk_B)
% 1.93/2.15          | ~ (v8_lattices @ sk_B)
% 1.93/2.15          | ~ (v9_lattices @ sk_B)
% 1.93/2.15          | ~ (l3_lattices @ sk_B))),
% 1.93/2.15      inference('sup-', [status(thm)], ['221', '222'])).
% 1.93/2.15  thf('224', plain, ((v6_lattices @ sk_B)),
% 1.93/2.15      inference('demod', [status(thm)], ['79', '80', '81'])).
% 1.93/2.15  thf('225', plain, ((v8_lattices @ sk_B)),
% 1.93/2.15      inference('demod', [status(thm)], ['85', '86', '87'])).
% 1.93/2.15  thf('226', plain, ((v9_lattices @ sk_B)),
% 1.93/2.15      inference('demod', [status(thm)], ['91', '92', '93'])).
% 1.93/2.15  thf('227', plain, ((l3_lattices @ sk_B)),
% 1.93/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.15  thf('228', plain,
% 1.93/2.15      (![X0 : $i, X1 : $i]:
% 1.93/2.15         ((r4_lattice3 @ sk_B @ sk_C @ X0)
% 1.93/2.15          | ~ (r3_lattices @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B) @ X1)
% 1.93/2.15          | (r1_lattices @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B) @ X1)
% 1.93/2.15          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 1.93/2.15          | (v2_struct_0 @ sk_B))),
% 1.93/2.15      inference('demod', [status(thm)], ['223', '224', '225', '226', '227'])).
% 1.93/2.15  thf('229', plain,
% 1.93/2.15      ((((r4_lattice3 @ sk_B @ sk_C @ sk_A)
% 1.93/2.15         | (v2_struct_0 @ sk_B)
% 1.93/2.15         | (v2_struct_0 @ (k3_lattice3 @ sk_B))
% 1.93/2.15         | (v2_struct_0 @ sk_B)
% 1.93/2.15         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_B))
% 1.93/2.15         | (r1_lattices @ sk_B @ (sk_D @ sk_A @ sk_C @ sk_B) @ sk_C)
% 1.93/2.15         | (r4_lattice3 @ sk_B @ sk_C @ sk_A)))
% 1.93/2.15         <= (((r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 1.93/2.15               (k4_lattice3 @ sk_B @ sk_C))))),
% 1.93/2.15      inference('sup-', [status(thm)], ['220', '228'])).
% 1.93/2.15  thf('230', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_B))),
% 1.93/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.15  thf('231', plain,
% 1.93/2.15      ((((r4_lattice3 @ sk_B @ sk_C @ sk_A)
% 1.93/2.15         | (v2_struct_0 @ sk_B)
% 1.93/2.15         | (v2_struct_0 @ (k3_lattice3 @ sk_B))
% 1.93/2.15         | (v2_struct_0 @ sk_B)
% 1.93/2.15         | (r1_lattices @ sk_B @ (sk_D @ sk_A @ sk_C @ sk_B) @ sk_C)
% 1.93/2.15         | (r4_lattice3 @ sk_B @ sk_C @ sk_A)))
% 1.93/2.15         <= (((r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 1.93/2.15               (k4_lattice3 @ sk_B @ sk_C))))),
% 1.93/2.15      inference('demod', [status(thm)], ['229', '230'])).
% 1.93/2.15  thf('232', plain,
% 1.93/2.15      ((((r1_lattices @ sk_B @ (sk_D @ sk_A @ sk_C @ sk_B) @ sk_C)
% 1.93/2.15         | (v2_struct_0 @ (k3_lattice3 @ sk_B))
% 1.93/2.15         | (v2_struct_0 @ sk_B)
% 1.93/2.15         | (r4_lattice3 @ sk_B @ sk_C @ sk_A)))
% 1.93/2.15         <= (((r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 1.93/2.15               (k4_lattice3 @ sk_B @ sk_C))))),
% 1.93/2.15      inference('simplify', [status(thm)], ['231'])).
% 1.93/2.15  thf('233', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_B))),
% 1.93/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.15  thf('234', plain,
% 1.93/2.15      (![X7 : $i, X8 : $i, X11 : $i]:
% 1.93/2.15         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 1.93/2.15          | ~ (r1_lattices @ X8 @ (sk_D @ X11 @ X7 @ X8) @ X7)
% 1.93/2.15          | (r4_lattice3 @ X8 @ X7 @ X11)
% 1.93/2.15          | ~ (l3_lattices @ X8)
% 1.93/2.15          | (v2_struct_0 @ X8))),
% 1.93/2.15      inference('cnf', [status(esa)], [d17_lattice3])).
% 1.93/2.15  thf('235', plain,
% 1.93/2.15      (![X0 : $i]:
% 1.93/2.15         ((v2_struct_0 @ sk_B)
% 1.93/2.15          | ~ (l3_lattices @ sk_B)
% 1.93/2.15          | (r4_lattice3 @ sk_B @ sk_C @ X0)
% 1.93/2.15          | ~ (r1_lattices @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B) @ sk_C))),
% 1.93/2.15      inference('sup-', [status(thm)], ['233', '234'])).
% 1.93/2.15  thf('236', plain, ((l3_lattices @ sk_B)),
% 1.93/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.15  thf('237', plain,
% 1.93/2.15      (![X0 : $i]:
% 1.93/2.15         ((v2_struct_0 @ sk_B)
% 1.93/2.15          | (r4_lattice3 @ sk_B @ sk_C @ X0)
% 1.93/2.15          | ~ (r1_lattices @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B) @ sk_C))),
% 1.93/2.15      inference('demod', [status(thm)], ['235', '236'])).
% 1.93/2.15  thf('238', plain, (~ (v2_struct_0 @ sk_B)),
% 1.93/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.15  thf('239', plain,
% 1.93/2.15      (![X0 : $i]:
% 1.93/2.15         (~ (r1_lattices @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B) @ sk_C)
% 1.93/2.15          | (r4_lattice3 @ sk_B @ sk_C @ X0))),
% 1.93/2.15      inference('clc', [status(thm)], ['237', '238'])).
% 1.93/2.15  thf('240', plain,
% 1.93/2.15      ((((r4_lattice3 @ sk_B @ sk_C @ sk_A)
% 1.93/2.15         | (v2_struct_0 @ sk_B)
% 1.93/2.15         | (v2_struct_0 @ (k3_lattice3 @ sk_B))
% 1.93/2.15         | (r4_lattice3 @ sk_B @ sk_C @ sk_A)))
% 1.93/2.15         <= (((r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 1.93/2.15               (k4_lattice3 @ sk_B @ sk_C))))),
% 1.93/2.15      inference('sup-', [status(thm)], ['232', '239'])).
% 1.93/2.15  thf('241', plain,
% 1.93/2.15      ((((v2_struct_0 @ (k3_lattice3 @ sk_B))
% 1.93/2.15         | (v2_struct_0 @ sk_B)
% 1.93/2.15         | (r4_lattice3 @ sk_B @ sk_C @ sk_A)))
% 1.93/2.15         <= (((r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 1.93/2.15               (k4_lattice3 @ sk_B @ sk_C))))),
% 1.93/2.15      inference('simplify', [status(thm)], ['240'])).
% 1.93/2.15  thf('242', plain, (~ (v2_struct_0 @ sk_B)),
% 1.93/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.15  thf('243', plain,
% 1.93/2.15      ((((r4_lattice3 @ sk_B @ sk_C @ sk_A)
% 1.93/2.15         | (v2_struct_0 @ (k3_lattice3 @ sk_B))))
% 1.93/2.15         <= (((r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 1.93/2.15               (k4_lattice3 @ sk_B @ sk_C))))),
% 1.93/2.15      inference('clc', [status(thm)], ['241', '242'])).
% 1.93/2.15  thf('244', plain,
% 1.93/2.15      ((~ (r4_lattice3 @ sk_B @ sk_C @ sk_A))
% 1.93/2.15         <= (~ ((r4_lattice3 @ sk_B @ sk_C @ sk_A)))),
% 1.93/2.15      inference('split', [status(esa)], ['103'])).
% 1.93/2.15  thf('245', plain,
% 1.93/2.15      (((v2_struct_0 @ (k3_lattice3 @ sk_B)))
% 1.93/2.15         <= (~ ((r4_lattice3 @ sk_B @ sk_C @ sk_A)) & 
% 1.93/2.15             ((r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 1.93/2.15               (k4_lattice3 @ sk_B @ sk_C))))),
% 1.93/2.15      inference('sup-', [status(thm)], ['243', '244'])).
% 1.93/2.15  thf(fc4_lattice3, axiom,
% 1.93/2.15    (![A:$i]:
% 1.93/2.15     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 1.93/2.15       ( ( ~( v2_struct_0 @ ( k3_lattice3 @ A ) ) ) & 
% 1.93/2.15         ( v1_orders_2 @ ( k3_lattice3 @ A ) ) & 
% 1.93/2.15         ( v3_orders_2 @ ( k3_lattice3 @ A ) ) & 
% 1.93/2.15         ( v4_orders_2 @ ( k3_lattice3 @ A ) ) & 
% 1.93/2.15         ( v5_orders_2 @ ( k3_lattice3 @ A ) ) ) ))).
% 1.93/2.15  thf('246', plain,
% 1.93/2.15      (![X25 : $i]:
% 1.93/2.15         (~ (v2_struct_0 @ (k3_lattice3 @ X25))
% 1.93/2.15          | ~ (l3_lattices @ X25)
% 1.93/2.15          | ~ (v10_lattices @ X25)
% 1.93/2.15          | (v2_struct_0 @ X25))),
% 1.93/2.15      inference('cnf', [status(esa)], [fc4_lattice3])).
% 1.93/2.15  thf('247', plain,
% 1.93/2.15      ((((v2_struct_0 @ sk_B)
% 1.93/2.15         | ~ (v10_lattices @ sk_B)
% 1.93/2.15         | ~ (l3_lattices @ sk_B)))
% 1.93/2.15         <= (~ ((r4_lattice3 @ sk_B @ sk_C @ sk_A)) & 
% 1.93/2.15             ((r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 1.93/2.15               (k4_lattice3 @ sk_B @ sk_C))))),
% 1.93/2.15      inference('sup-', [status(thm)], ['245', '246'])).
% 1.93/2.15  thf('248', plain, ((v10_lattices @ sk_B)),
% 1.93/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.15  thf('249', plain, ((l3_lattices @ sk_B)),
% 1.93/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.15  thf('250', plain,
% 1.93/2.15      (((v2_struct_0 @ sk_B))
% 1.93/2.15         <= (~ ((r4_lattice3 @ sk_B @ sk_C @ sk_A)) & 
% 1.93/2.15             ((r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 1.93/2.15               (k4_lattice3 @ sk_B @ sk_C))))),
% 1.93/2.15      inference('demod', [status(thm)], ['247', '248', '249'])).
% 1.93/2.15  thf('251', plain, (~ (v2_struct_0 @ sk_B)),
% 1.93/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.15  thf('252', plain,
% 1.93/2.15      (((r4_lattice3 @ sk_B @ sk_C @ sk_A)) | 
% 1.93/2.15       ~
% 1.93/2.15       ((r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 1.93/2.15         (k4_lattice3 @ sk_B @ sk_C)))),
% 1.93/2.15      inference('sup-', [status(thm)], ['250', '251'])).
% 1.93/2.15  thf('253', plain,
% 1.93/2.15      (((r4_lattice3 @ sk_B @ sk_C @ sk_A)) | 
% 1.93/2.15       ((r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 1.93/2.15         (k4_lattice3 @ sk_B @ sk_C)))),
% 1.93/2.15      inference('split', [status(esa)], ['50'])).
% 1.93/2.15  thf('254', plain, (((r4_lattice3 @ sk_B @ sk_C @ sk_A))),
% 1.93/2.15      inference('sat_resolution*', [status(thm)], ['104', '252', '253'])).
% 1.93/2.15  thf('255', plain,
% 1.93/2.15      (((r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ sk_C)
% 1.93/2.15        | (r3_lattices @ sk_B @ 
% 1.93/2.15           (sk_D_1 @ sk_C @ sk_A @ (k3_lattice3 @ sk_B)) @ sk_C))),
% 1.93/2.15      inference('simpl_trail', [status(thm)], ['102', '254'])).
% 1.93/2.15  thf('256', plain,
% 1.93/2.15      ((~ (r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 1.93/2.15           (k4_lattice3 @ sk_B @ sk_C)))
% 1.93/2.15         <= (~
% 1.93/2.15             ((r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 1.93/2.15               (k4_lattice3 @ sk_B @ sk_C))))),
% 1.93/2.15      inference('split', [status(esa)], ['103'])).
% 1.93/2.15  thf('257', plain, (((k4_lattice3 @ sk_B @ sk_C) = (sk_C))),
% 1.93/2.15      inference('clc', [status(thm)], ['10', '11'])).
% 1.93/2.15  thf('258', plain,
% 1.93/2.15      ((~ (r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ sk_C))
% 1.93/2.15         <= (~
% 1.93/2.15             ((r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 1.93/2.15               (k4_lattice3 @ sk_B @ sk_C))))),
% 1.93/2.15      inference('demod', [status(thm)], ['256', '257'])).
% 1.93/2.15  thf('259', plain,
% 1.93/2.15      (~
% 1.93/2.15       ((r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 1.93/2.15         (k4_lattice3 @ sk_B @ sk_C)))),
% 1.93/2.15      inference('sat_resolution*', [status(thm)], ['104', '252'])).
% 1.93/2.15  thf('260', plain, (~ (r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ sk_C)),
% 1.93/2.15      inference('simpl_trail', [status(thm)], ['258', '259'])).
% 1.93/2.15  thf('261', plain,
% 1.93/2.15      ((r3_lattices @ sk_B @ (sk_D_1 @ sk_C @ sk_A @ (k3_lattice3 @ sk_B)) @ 
% 1.93/2.15        sk_C)),
% 1.93/2.15      inference('clc', [status(thm)], ['255', '260'])).
% 1.93/2.15  thf('262', plain,
% 1.93/2.15      (![X0 : $i]:
% 1.93/2.15         ((r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 1.93/2.15          | (m1_subset_1 @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ 
% 1.93/2.15             (u1_struct_0 @ sk_B)))),
% 1.93/2.15      inference('simplify', [status(thm)], ['41'])).
% 1.93/2.15  thf('263', plain,
% 1.93/2.15      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.93/2.15         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 1.93/2.15          | ~ (r3_lattices @ X27 @ X26 @ X28)
% 1.93/2.15          | (r3_orders_2 @ (k3_lattice3 @ X27) @ (k4_lattice3 @ X27 @ X26) @ 
% 1.93/2.15             (k4_lattice3 @ X27 @ X28))
% 1.93/2.15          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X27))
% 1.93/2.15          | ~ (l3_lattices @ X27)
% 1.93/2.15          | ~ (v10_lattices @ X27)
% 1.93/2.15          | (v2_struct_0 @ X27))),
% 1.93/2.15      inference('cnf', [status(esa)], [t7_lattice3])).
% 1.93/2.15  thf('264', plain,
% 1.93/2.15      (![X0 : $i, X1 : $i]:
% 1.93/2.15         ((r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 1.93/2.15          | (v2_struct_0 @ sk_B)
% 1.93/2.15          | ~ (v10_lattices @ sk_B)
% 1.93/2.15          | ~ (l3_lattices @ sk_B)
% 1.93/2.15          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 1.93/2.15          | (r3_orders_2 @ (k3_lattice3 @ sk_B) @ 
% 1.93/2.15             (k4_lattice3 @ sk_B @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B))) @ 
% 1.93/2.15             (k4_lattice3 @ sk_B @ X1))
% 1.93/2.15          | ~ (r3_lattices @ sk_B @ 
% 1.93/2.15               (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ X1))),
% 1.93/2.15      inference('sup-', [status(thm)], ['262', '263'])).
% 1.93/2.15  thf('265', plain, ((v10_lattices @ sk_B)),
% 1.93/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.15  thf('266', plain, ((l3_lattices @ sk_B)),
% 1.93/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.15  thf('267', plain,
% 1.93/2.15      (![X0 : $i, X1 : $i]:
% 1.93/2.15         ((r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 1.93/2.15          | (v2_struct_0 @ sk_B)
% 1.93/2.15          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 1.93/2.15          | (r3_orders_2 @ (k3_lattice3 @ sk_B) @ 
% 1.93/2.15             (k4_lattice3 @ sk_B @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B))) @ 
% 1.93/2.15             (k4_lattice3 @ sk_B @ X1))
% 1.93/2.15          | ~ (r3_lattices @ sk_B @ 
% 1.93/2.15               (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ X1))),
% 1.93/2.15      inference('demod', [status(thm)], ['264', '265', '266'])).
% 1.93/2.15  thf('268', plain,
% 1.93/2.15      (((r3_orders_2 @ (k3_lattice3 @ sk_B) @ 
% 1.93/2.15         (k4_lattice3 @ sk_B @ (sk_D_1 @ sk_C @ sk_A @ (k3_lattice3 @ sk_B))) @ 
% 1.93/2.15         (k4_lattice3 @ sk_B @ sk_C))
% 1.93/2.15        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_B))
% 1.93/2.15        | (v2_struct_0 @ sk_B)
% 1.93/2.15        | (r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ sk_C))),
% 1.93/2.15      inference('sup-', [status(thm)], ['261', '267'])).
% 1.93/2.15  thf('269', plain, (((k4_lattice3 @ sk_B @ sk_C) = (sk_C))),
% 1.93/2.15      inference('clc', [status(thm)], ['10', '11'])).
% 1.93/2.15  thf('270', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_B))),
% 1.93/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.15  thf('271', plain,
% 1.93/2.15      (((r3_orders_2 @ (k3_lattice3 @ sk_B) @ 
% 1.93/2.15         (k4_lattice3 @ sk_B @ (sk_D_1 @ sk_C @ sk_A @ (k3_lattice3 @ sk_B))) @ 
% 1.93/2.15         sk_C)
% 1.93/2.15        | (v2_struct_0 @ sk_B)
% 1.93/2.15        | (r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ sk_C))),
% 1.93/2.15      inference('demod', [status(thm)], ['268', '269', '270'])).
% 1.93/2.15  thf('272', plain, (~ (v2_struct_0 @ sk_B)),
% 1.93/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.15  thf('273', plain,
% 1.93/2.15      (((r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ sk_C)
% 1.93/2.15        | (r3_orders_2 @ (k3_lattice3 @ sk_B) @ 
% 1.93/2.15           (k4_lattice3 @ sk_B @ (sk_D_1 @ sk_C @ sk_A @ (k3_lattice3 @ sk_B))) @ 
% 1.93/2.15           sk_C))),
% 1.93/2.15      inference('clc', [status(thm)], ['271', '272'])).
% 1.93/2.15  thf('274', plain, (~ (r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ sk_C)),
% 1.93/2.15      inference('simpl_trail', [status(thm)], ['258', '259'])).
% 1.93/2.15  thf('275', plain,
% 1.93/2.15      ((r3_orders_2 @ (k3_lattice3 @ sk_B) @ 
% 1.93/2.15        (k4_lattice3 @ sk_B @ (sk_D_1 @ sk_C @ sk_A @ (k3_lattice3 @ sk_B))) @ 
% 1.93/2.15        sk_C)),
% 1.93/2.15      inference('clc', [status(thm)], ['273', '274'])).
% 1.93/2.15  thf('276', plain,
% 1.93/2.15      (((r3_orders_2 @ (k3_lattice3 @ sk_B) @ 
% 1.93/2.15         (sk_D_1 @ sk_C @ sk_A @ (k3_lattice3 @ sk_B)) @ sk_C)
% 1.93/2.15        | (r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ sk_C))),
% 1.93/2.15      inference('sup+', [status(thm)], ['49', '275'])).
% 1.93/2.15  thf('277', plain, (~ (r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ sk_C)),
% 1.93/2.15      inference('simpl_trail', [status(thm)], ['258', '259'])).
% 1.93/2.15  thf('278', plain,
% 1.93/2.15      ((r3_orders_2 @ (k3_lattice3 @ sk_B) @ 
% 1.93/2.15        (sk_D_1 @ sk_C @ sk_A @ (k3_lattice3 @ sk_B)) @ sk_C)),
% 1.93/2.15      inference('clc', [status(thm)], ['276', '277'])).
% 1.93/2.15  thf('279', plain,
% 1.93/2.15      (![X20 : $i]:
% 1.93/2.15         ((l1_orders_2 @ (k3_lattice3 @ X20))
% 1.93/2.15          | ~ (l3_lattices @ X20)
% 1.93/2.15          | ~ (v10_lattices @ X20)
% 1.93/2.15          | (v2_struct_0 @ X20))),
% 1.93/2.15      inference('cnf', [status(esa)], [dt_k3_lattice3])).
% 1.93/2.15  thf('280', plain,
% 1.93/2.15      (![X20 : $i]:
% 1.93/2.15         ((v3_orders_2 @ (k3_lattice3 @ X20))
% 1.93/2.15          | ~ (l3_lattices @ X20)
% 1.93/2.15          | ~ (v10_lattices @ X20)
% 1.93/2.15          | (v2_struct_0 @ X20))),
% 1.93/2.15      inference('cnf', [status(esa)], [dt_k3_lattice3])).
% 1.93/2.15  thf('281', plain,
% 1.93/2.15      (![X0 : $i]:
% 1.93/2.15         ((r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 1.93/2.15          | (m1_subset_1 @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ 
% 1.93/2.15             (u1_struct_0 @ (k3_lattice3 @ sk_B))))),
% 1.93/2.15      inference('clc', [status(thm)], ['23', '24'])).
% 1.93/2.15  thf('282', plain,
% 1.93/2.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.93/2.15         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 1.93/2.15          | ~ (l1_orders_2 @ X1)
% 1.93/2.15          | ~ (v3_orders_2 @ X1)
% 1.93/2.15          | (v2_struct_0 @ X1)
% 1.93/2.15          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 1.93/2.15          | (r1_orders_2 @ X1 @ X0 @ X2)
% 1.93/2.15          | ~ (r3_orders_2 @ X1 @ X0 @ X2))),
% 1.93/2.15      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 1.93/2.15  thf('283', plain,
% 1.93/2.15      (![X0 : $i, X1 : $i]:
% 1.93/2.15         ((r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 1.93/2.15          | ~ (r3_orders_2 @ (k3_lattice3 @ sk_B) @ 
% 1.93/2.15               (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ X1)
% 1.93/2.15          | (r1_orders_2 @ (k3_lattice3 @ sk_B) @ 
% 1.93/2.15             (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ X1)
% 1.93/2.15          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 1.93/2.15          | (v2_struct_0 @ (k3_lattice3 @ sk_B))
% 1.93/2.15          | ~ (v3_orders_2 @ (k3_lattice3 @ sk_B))
% 1.93/2.15          | ~ (l1_orders_2 @ (k3_lattice3 @ sk_B)))),
% 1.93/2.15      inference('sup-', [status(thm)], ['281', '282'])).
% 1.93/2.15  thf('284', plain,
% 1.93/2.15      (![X0 : $i, X1 : $i]:
% 1.93/2.15         ((v2_struct_0 @ sk_B)
% 1.93/2.15          | ~ (v10_lattices @ sk_B)
% 1.93/2.15          | ~ (l3_lattices @ sk_B)
% 1.93/2.15          | ~ (l1_orders_2 @ (k3_lattice3 @ sk_B))
% 1.93/2.15          | (v2_struct_0 @ (k3_lattice3 @ sk_B))
% 1.93/2.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 1.93/2.15          | (r1_orders_2 @ (k3_lattice3 @ sk_B) @ 
% 1.93/2.15             (sk_D_1 @ sk_C @ X1 @ (k3_lattice3 @ sk_B)) @ X0)
% 1.93/2.15          | ~ (r3_orders_2 @ (k3_lattice3 @ sk_B) @ 
% 1.93/2.15               (sk_D_1 @ sk_C @ X1 @ (k3_lattice3 @ sk_B)) @ X0)
% 1.93/2.15          | (r2_lattice3 @ (k3_lattice3 @ sk_B) @ X1 @ sk_C))),
% 1.93/2.15      inference('sup-', [status(thm)], ['280', '283'])).
% 1.93/2.15  thf('285', plain, ((v10_lattices @ sk_B)),
% 1.93/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.15  thf('286', plain, ((l3_lattices @ sk_B)),
% 1.93/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.15  thf('287', plain,
% 1.93/2.15      (![X0 : $i, X1 : $i]:
% 1.93/2.15         ((v2_struct_0 @ sk_B)
% 1.93/2.15          | ~ (l1_orders_2 @ (k3_lattice3 @ sk_B))
% 1.93/2.15          | (v2_struct_0 @ (k3_lattice3 @ sk_B))
% 1.93/2.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 1.93/2.15          | (r1_orders_2 @ (k3_lattice3 @ sk_B) @ 
% 1.93/2.15             (sk_D_1 @ sk_C @ X1 @ (k3_lattice3 @ sk_B)) @ X0)
% 1.93/2.15          | ~ (r3_orders_2 @ (k3_lattice3 @ sk_B) @ 
% 1.93/2.15               (sk_D_1 @ sk_C @ X1 @ (k3_lattice3 @ sk_B)) @ X0)
% 1.93/2.15          | (r2_lattice3 @ (k3_lattice3 @ sk_B) @ X1 @ sk_C))),
% 1.93/2.15      inference('demod', [status(thm)], ['284', '285', '286'])).
% 1.93/2.15  thf('288', plain,
% 1.93/2.15      (![X0 : $i, X1 : $i]:
% 1.93/2.15         ((v2_struct_0 @ sk_B)
% 1.93/2.15          | ~ (v10_lattices @ sk_B)
% 1.93/2.15          | ~ (l3_lattices @ sk_B)
% 1.93/2.15          | (r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 1.93/2.15          | ~ (r3_orders_2 @ (k3_lattice3 @ sk_B) @ 
% 1.93/2.15               (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ X1)
% 1.93/2.15          | (r1_orders_2 @ (k3_lattice3 @ sk_B) @ 
% 1.93/2.15             (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ X1)
% 1.93/2.15          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 1.93/2.15          | (v2_struct_0 @ (k3_lattice3 @ sk_B))
% 1.93/2.15          | (v2_struct_0 @ sk_B))),
% 1.93/2.15      inference('sup-', [status(thm)], ['279', '287'])).
% 1.93/2.15  thf('289', plain, ((v10_lattices @ sk_B)),
% 1.93/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.15  thf('290', plain, ((l3_lattices @ sk_B)),
% 1.93/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.15  thf('291', plain,
% 1.93/2.15      (![X0 : $i, X1 : $i]:
% 1.93/2.15         ((v2_struct_0 @ sk_B)
% 1.93/2.15          | (r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 1.93/2.15          | ~ (r3_orders_2 @ (k3_lattice3 @ sk_B) @ 
% 1.93/2.15               (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ X1)
% 1.93/2.15          | (r1_orders_2 @ (k3_lattice3 @ sk_B) @ 
% 1.93/2.15             (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ X1)
% 1.93/2.15          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 1.93/2.15          | (v2_struct_0 @ (k3_lattice3 @ sk_B))
% 1.93/2.15          | (v2_struct_0 @ sk_B))),
% 1.93/2.15      inference('demod', [status(thm)], ['288', '289', '290'])).
% 1.93/2.15  thf('292', plain,
% 1.93/2.15      (![X0 : $i, X1 : $i]:
% 1.93/2.15         ((v2_struct_0 @ (k3_lattice3 @ sk_B))
% 1.93/2.15          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 1.93/2.15          | (r1_orders_2 @ (k3_lattice3 @ sk_B) @ 
% 1.93/2.15             (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ X1)
% 1.93/2.15          | ~ (r3_orders_2 @ (k3_lattice3 @ sk_B) @ 
% 1.93/2.15               (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ X1)
% 1.93/2.15          | (r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 1.93/2.15          | (v2_struct_0 @ sk_B))),
% 1.93/2.15      inference('simplify', [status(thm)], ['291'])).
% 1.93/2.15  thf('293', plain,
% 1.93/2.15      (((v2_struct_0 @ sk_B)
% 1.93/2.15        | (r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ sk_C)
% 1.93/2.15        | (r1_orders_2 @ (k3_lattice3 @ sk_B) @ 
% 1.93/2.15           (sk_D_1 @ sk_C @ sk_A @ (k3_lattice3 @ sk_B)) @ sk_C)
% 1.93/2.15        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 1.93/2.15        | (v2_struct_0 @ (k3_lattice3 @ sk_B)))),
% 1.93/2.15      inference('sup-', [status(thm)], ['278', '292'])).
% 1.93/2.15  thf('294', plain,
% 1.93/2.15      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))),
% 1.93/2.15      inference('clc', [status(thm)], ['15', '16'])).
% 1.93/2.15  thf('295', plain,
% 1.93/2.15      (((v2_struct_0 @ sk_B)
% 1.93/2.15        | (r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ sk_C)
% 1.93/2.15        | (r1_orders_2 @ (k3_lattice3 @ sk_B) @ 
% 1.93/2.15           (sk_D_1 @ sk_C @ sk_A @ (k3_lattice3 @ sk_B)) @ sk_C)
% 1.93/2.15        | (v2_struct_0 @ (k3_lattice3 @ sk_B)))),
% 1.93/2.15      inference('demod', [status(thm)], ['293', '294'])).
% 1.93/2.15  thf('296', plain,
% 1.93/2.15      (![X20 : $i]:
% 1.93/2.15         ((l1_orders_2 @ (k3_lattice3 @ X20))
% 1.93/2.15          | ~ (l3_lattices @ X20)
% 1.93/2.15          | ~ (v10_lattices @ X20)
% 1.93/2.15          | (v2_struct_0 @ X20))),
% 1.93/2.15      inference('cnf', [status(esa)], [dt_k3_lattice3])).
% 1.93/2.15  thf('297', plain,
% 1.93/2.15      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))),
% 1.93/2.15      inference('clc', [status(thm)], ['15', '16'])).
% 1.93/2.15  thf('298', plain,
% 1.93/2.15      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.93/2.15         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 1.93/2.15          | ~ (r1_orders_2 @ X17 @ (sk_D_1 @ X16 @ X18 @ X17) @ X16)
% 1.93/2.15          | (r2_lattice3 @ X17 @ X18 @ X16)
% 1.93/2.15          | ~ (l1_orders_2 @ X17))),
% 1.93/2.15      inference('cnf', [status(esa)], [d9_lattice3])).
% 1.93/2.15  thf('299', plain,
% 1.93/2.15      (![X0 : $i]:
% 1.93/2.15         (~ (l1_orders_2 @ (k3_lattice3 @ sk_B))
% 1.93/2.15          | (r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 1.93/2.15          | ~ (r1_orders_2 @ (k3_lattice3 @ sk_B) @ 
% 1.93/2.15               (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ sk_C))),
% 1.93/2.15      inference('sup-', [status(thm)], ['297', '298'])).
% 1.93/2.15  thf('300', plain,
% 1.93/2.15      (![X0 : $i]:
% 1.93/2.15         ((v2_struct_0 @ sk_B)
% 1.93/2.15          | ~ (v10_lattices @ sk_B)
% 1.93/2.15          | ~ (l3_lattices @ sk_B)
% 1.93/2.15          | ~ (r1_orders_2 @ (k3_lattice3 @ sk_B) @ 
% 1.93/2.15               (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ sk_C)
% 1.93/2.15          | (r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C))),
% 1.93/2.15      inference('sup-', [status(thm)], ['296', '299'])).
% 1.93/2.15  thf('301', plain, ((v10_lattices @ sk_B)),
% 1.93/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.15  thf('302', plain, ((l3_lattices @ sk_B)),
% 1.93/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.15  thf('303', plain,
% 1.93/2.15      (![X0 : $i]:
% 1.93/2.15         ((v2_struct_0 @ sk_B)
% 1.93/2.15          | ~ (r1_orders_2 @ (k3_lattice3 @ sk_B) @ 
% 1.93/2.15               (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ sk_C)
% 1.93/2.15          | (r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C))),
% 1.93/2.15      inference('demod', [status(thm)], ['300', '301', '302'])).
% 1.93/2.15  thf('304', plain, (~ (v2_struct_0 @ sk_B)),
% 1.93/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.15  thf('305', plain,
% 1.93/2.15      (![X0 : $i]:
% 1.93/2.15         ((r2_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 1.93/2.15          | ~ (r1_orders_2 @ (k3_lattice3 @ sk_B) @ 
% 1.93/2.15               (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ sk_C))),
% 1.93/2.15      inference('clc', [status(thm)], ['303', '304'])).
% 1.93/2.15  thf('306', plain,
% 1.93/2.15      (((v2_struct_0 @ (k3_lattice3 @ sk_B))
% 1.93/2.15        | (r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ sk_C)
% 1.93/2.15        | (v2_struct_0 @ sk_B)
% 1.93/2.15        | (r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ sk_C))),
% 1.93/2.15      inference('sup-', [status(thm)], ['295', '305'])).
% 1.93/2.15  thf('307', plain,
% 1.93/2.15      (((v2_struct_0 @ sk_B)
% 1.93/2.15        | (r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ sk_C)
% 1.93/2.15        | (v2_struct_0 @ (k3_lattice3 @ sk_B)))),
% 1.93/2.15      inference('simplify', [status(thm)], ['306'])).
% 1.93/2.15  thf('308', plain, (~ (v2_struct_0 @ sk_B)),
% 1.93/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.15  thf('309', plain,
% 1.93/2.15      (((v2_struct_0 @ (k3_lattice3 @ sk_B))
% 1.93/2.15        | (r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ sk_C))),
% 1.93/2.15      inference('clc', [status(thm)], ['307', '308'])).
% 1.93/2.15  thf('310', plain, (~ (r2_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ sk_C)),
% 1.93/2.15      inference('simpl_trail', [status(thm)], ['258', '259'])).
% 1.93/2.15  thf('311', plain, ((v2_struct_0 @ (k3_lattice3 @ sk_B))),
% 1.93/2.15      inference('clc', [status(thm)], ['309', '310'])).
% 1.93/2.15  thf('312', plain,
% 1.93/2.15      (![X25 : $i]:
% 1.93/2.15         (~ (v2_struct_0 @ (k3_lattice3 @ X25))
% 1.93/2.15          | ~ (l3_lattices @ X25)
% 1.93/2.15          | ~ (v10_lattices @ X25)
% 1.93/2.15          | (v2_struct_0 @ X25))),
% 1.93/2.15      inference('cnf', [status(esa)], [fc4_lattice3])).
% 1.93/2.15  thf('313', plain,
% 1.93/2.15      (((v2_struct_0 @ sk_B) | ~ (v10_lattices @ sk_B) | ~ (l3_lattices @ sk_B))),
% 1.93/2.15      inference('sup-', [status(thm)], ['311', '312'])).
% 1.93/2.15  thf('314', plain, ((v10_lattices @ sk_B)),
% 1.93/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.15  thf('315', plain, ((l3_lattices @ sk_B)),
% 1.93/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.15  thf('316', plain, ((v2_struct_0 @ sk_B)),
% 1.93/2.15      inference('demod', [status(thm)], ['313', '314', '315'])).
% 1.93/2.15  thf('317', plain, ($false), inference('demod', [status(thm)], ['0', '316'])).
% 1.93/2.15  
% 1.93/2.15  % SZS output end Refutation
% 1.93/2.15  
% 1.93/2.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
