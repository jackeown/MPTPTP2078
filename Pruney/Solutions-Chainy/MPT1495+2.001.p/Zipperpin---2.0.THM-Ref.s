%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LQFhMF1qnR

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:26 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :  329 (3781 expanded)
%              Number of leaves         :   44 (1066 expanded)
%              Depth                    :   54
%              Number of atoms          : 3484 (56993 expanded)
%              Number of equality atoms :   23 ( 325 expanded)
%              Maximal formula depth    :   16 (   6 average)

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

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(r3_lattice3_type,type,(
    r3_lattice3: $i > $i > $i > $o )).

thf(k5_lattice3_type,type,(
    k5_lattice3: $i > $i > $i )).

thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(t28_lattice3,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( v10_lattices @ B )
        & ( l3_lattices @ B ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
         => ( ( r3_lattice3 @ B @ C @ A )
          <=> ( r1_lattice3 @ ( k3_lattice3 @ B ) @ A @ ( k4_lattice3 @ B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ~ ( v2_struct_0 @ B )
          & ( v10_lattices @ B )
          & ( l3_lattices @ B ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
           => ( ( r3_lattice3 @ B @ C @ A )
            <=> ( r1_lattice3 @ ( k3_lattice3 @ B ) @ A @ ( k4_lattice3 @ B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_lattice3])).

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

thf(d8_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ( ( r1_lattice3 @ A @ B @ C )
          <=> ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ D @ B )
                 => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) )).

thf('18',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X16 @ X18 @ X17 ) @ ( u1_struct_0 @ X17 ) )
      | ( r1_lattice3 @ X17 @ X18 @ X16 )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ ( k3_lattice3 @ sk_B ) )
      | ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C ) ) ),
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
      | ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
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
      ( ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
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
      ( ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
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
      | ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
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
      ( ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
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
      ( ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ( m1_subset_1 @ ( k5_lattice3 @ sk_B @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_lattice3 @ sk_B @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) ) @ ( u1_struct_0 @ sk_B ) )
      | ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) )
      | ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['32','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
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
      ( ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
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
      ( ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
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
      | ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('51',plain,
    ( ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) )
    | ( r3_lattice3 @ sk_B @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( r3_lattice3 @ sk_B @ sk_C @ sk_A )
   <= ( r3_lattice3 @ sk_B @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['51'])).

thf('53',plain,
    ( ~ ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) )
    | ~ ( r3_lattice3 @ sk_B @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ~ ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) )
    | ~ ( r3_lattice3 @ sk_B @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['53'])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('56',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ( m1_subset_1 @ ( sk_D @ X11 @ X7 @ X8 ) @ ( u1_struct_0 @ X8 ) )
      | ( r3_lattice3 @ X8 @ X7 @ X11 )
      | ~ ( l3_lattices @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ( r3_lattice3 @ sk_B @ sk_C @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r3_lattice3 @ sk_B @ sk_C @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
      | ( r3_lattice3 @ sk_B @ sk_C @ X0 ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
      | ( r3_lattice3 @ sk_B @ sk_C @ X0 ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X7 @ X8 ) @ X11 )
      | ( r3_lattice3 @ X8 @ X7 @ X11 )
      | ~ ( l3_lattices @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ( r3_lattice3 @ sk_B @ sk_C @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_C @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r3_lattice3 @ sk_B @ sk_C @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_C @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ sk_C @ sk_B ) @ X0 )
      | ( r3_lattice3 @ sk_B @ sk_C @ X0 ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
      | ( r3_lattice3 @ sk_B @ sk_C @ X0 ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('71',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ( ( k4_lattice3 @ X13 @ X12 )
        = X12 )
      | ~ ( l3_lattices @ X13 )
      | ~ ( v10_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_lattice3])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r3_lattice3 @ sk_B @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ( ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) )
        = ( sk_D @ X0 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( r3_lattice3 @ sk_B @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) )
        = ( sk_D @ X0 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) )
        = ( sk_D @ X0 @ sk_C @ sk_B ) )
      | ( r3_lattice3 @ sk_B @ sk_C @ X0 ) ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
      | ( r3_lattice3 @ sk_B @ sk_C @ X0 ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('79',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l3_lattices @ X21 )
      | ~ ( v10_lattices @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ( m1_subset_1 @ ( k4_lattice3 @ X21 @ X22 ) @ ( u1_struct_0 @ ( k3_lattice3 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_lattice3])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( r3_lattice3 @ sk_B @ sk_C @ X0 )
      | ( m1_subset_1 @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r3_lattice3 @ sk_B @ sk_C @ X0 )
      | ( m1_subset_1 @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) ) @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( r3_lattice3 @ sk_B @ sk_C @ X0 ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ sk_B ) @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( r3_lattice3 @ sk_B @ sk_C @ X0 )
      | ( r3_lattice3 @ sk_B @ sk_C @ X0 ) ) ),
    inference('sup+',[status(thm)],['77','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( r3_lattice3 @ sk_B @ sk_C @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ sk_B ) @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ( k4_lattice3 @ sk_B @ sk_C )
    = sk_C ),
    inference(clc,[status(thm)],['10','11'])).

thf('89',plain,
    ( ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) )
   <= ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['51'])).

thf('90',plain,
    ( ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C )
   <= ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X20: $i] :
      ( ( l1_orders_2 @ ( k3_lattice3 @ X20 ) )
      | ~ ( l3_lattices @ X20 )
      | ~ ( v10_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_lattice3])).

thf('92',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('93',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ~ ( r1_lattice3 @ X17 @ X18 @ X16 )
      | ~ ( r2_hidden @ X19 @ X18 )
      | ( r1_orders_2 @ X17 @ X16 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ ( k3_lattice3 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ~ ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['91','94'])).

thf('96',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
        | ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ X0 )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['90','98'])).

thf('100',plain,
    ( ! [X0: $i] :
        ( ( r3_lattice3 @ sk_B @ sk_C @ X0 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( r2_hidden @ ( sk_D @ X0 @ sk_C @ sk_B ) @ sk_A )
        | ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_B ) ) )
   <= ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['87','99'])).

thf('101',plain,
    ( ( ( r3_lattice3 @ sk_B @ sk_C @ sk_A )
      | ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ ( sk_D @ sk_A @ sk_C @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( r3_lattice3 @ sk_B @ sk_C @ sk_A ) )
   <= ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['69','100'])).

thf('102',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ ( sk_D @ sk_A @ sk_C @ sk_B ) )
      | ( r3_lattice3 @ sk_B @ sk_C @ sk_A ) )
   <= ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( ( r3_lattice3 @ sk_B @ sk_C @ sk_A )
      | ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ ( sk_D @ sk_A @ sk_C @ sk_B ) ) )
   <= ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( r3_lattice3 @ sk_B @ sk_C @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ sk_B ) @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('106',plain,(
    ! [X20: $i] :
      ( ( l1_orders_2 @ ( k3_lattice3 @ X20 ) )
      | ~ ( l3_lattices @ X20 )
      | ~ ( v10_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_lattice3])).

thf('107',plain,(
    ! [X20: $i] :
      ( ( v3_orders_2 @ ( k3_lattice3 @ X20 ) )
      | ~ ( l3_lattices @ X20 )
      | ~ ( v10_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_lattice3])).

thf('108',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf(redefinition_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_orders_2 @ A @ B @ C )
      <=> ( r1_orders_2 @ A @ B @ C ) ) ) )).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r3_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( r1_orders_2 @ X1 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ X0 )
      | ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ~ ( v3_orders_2 @ ( k3_lattice3 @ sk_B ) )
      | ~ ( l1_orders_2 @ ( k3_lattice3 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ~ ( l1_orders_2 @ ( k3_lattice3 @ sk_B ) )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ X0 )
      | ~ ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['107','110'])).

thf('112',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( l1_orders_2 @ ( k3_lattice3 @ sk_B ) )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ X0 )
      | ~ ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ~ ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ X0 )
      | ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['106','114'])).

thf('116',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ X0 )
      | ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['115','116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ X0 )
      | ~ ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( r3_lattice3 @ sk_B @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_B ) )
      | ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_B ) )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['105','119'])).

thf('121',plain,
    ( ( ( r3_lattice3 @ sk_B @ sk_C @ sk_A )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ ( sk_D @ sk_A @ sk_C @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( r3_lattice3 @ sk_B @ sk_C @ sk_A ) )
   <= ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['104','120'])).

thf('122',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ ( sk_D @ sk_A @ sk_C @ sk_B ) )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ( r3_lattice3 @ sk_B @ sk_C @ sk_A ) )
   <= ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattice3 @ sk_B @ ( sk_D @ X0 @ sk_C @ sk_B ) )
        = ( sk_D @ X0 @ sk_C @ sk_B ) )
      | ( r3_lattice3 @ sk_B @ sk_C @ X0 ) ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('124',plain,
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

thf('125',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ~ ( r3_orders_2 @ ( k3_lattice3 @ X27 ) @ ( k4_lattice3 @ X27 @ X26 ) @ ( k4_lattice3 @ X27 @ X28 ) )
      | ( r3_lattices @ X27 @ X26 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X27 ) )
      | ~ ( l3_lattices @ X27 )
      | ~ ( v10_lattices @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_lattice3])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ ( k4_lattice3 @ sk_B @ X0 ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( r3_lattices @ sk_B @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ ( k4_lattice3 @ sk_B @ X0 ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( r3_lattices @ sk_B @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['126','127','128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_B ) )
      | ( r3_lattice3 @ sk_B @ sk_C @ X0 )
      | ( r3_lattices @ sk_B @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_B ) )
      | ~ ( m1_subset_1 @ ( sk_D @ X0 @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['123','130'])).

thf('132',plain,
    ( ( ( r3_lattice3 @ sk_B @ sk_C @ sk_A )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
      | ( r3_lattices @ sk_B @ sk_C @ ( sk_D @ sk_A @ sk_C @ sk_B ) )
      | ( r3_lattice3 @ sk_B @ sk_C @ sk_A ) )
   <= ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['122','131'])).

thf('133',plain,
    ( ( ( r3_lattices @ sk_B @ sk_C @ ( sk_D @ sk_A @ sk_C @ sk_B ) )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ( r3_lattice3 @ sk_B @ sk_C @ sk_A ) )
   <= ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,
    ( ( ( r3_lattice3 @ sk_B @ sk_C @ sk_A )
      | ( r3_lattice3 @ sk_B @ sk_C @ sk_A )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( r3_lattices @ sk_B @ sk_C @ ( sk_D @ sk_A @ sk_C @ sk_B ) ) )
   <= ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['62','133'])).

thf('135',plain,
    ( ( ( r3_lattices @ sk_B @ sk_C @ ( sk_D @ sk_A @ sk_C @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ( r3_lattice3 @ sk_B @ sk_C @ sk_A ) )
   <= ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ),
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

thf('137',plain,(
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

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattices @ sk_B @ sk_C @ X0 )
      | ( r1_lattices @ sk_B @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v6_lattices @ sk_B )
      | ~ ( v8_lattices @ sk_B )
      | ~ ( v9_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

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

thf('139',plain,(
    ! [X3: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( v10_lattices @ X3 )
      | ( v6_lattices @ X3 )
      | ~ ( l3_lattices @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('140',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ~ ( l3_lattices @ sk_B )
    | ( v6_lattices @ sk_B )
    | ~ ( v10_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v6_lattices @ sk_B ),
    inference(demod,[status(thm)],['141','142','143'])).

thf('145',plain,(
    ! [X3: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( v10_lattices @ X3 )
      | ( v8_lattices @ X3 )
      | ~ ( l3_lattices @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('146',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ~ ( l3_lattices @ sk_B )
    | ( v8_lattices @ sk_B )
    | ~ ( v10_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v8_lattices @ sk_B ),
    inference(demod,[status(thm)],['147','148','149'])).

thf('151',plain,(
    ! [X3: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( v10_lattices @ X3 )
      | ( v9_lattices @ X3 )
      | ~ ( l3_lattices @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('152',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ~ ( l3_lattices @ sk_B )
    | ( v9_lattices @ sk_B )
    | ~ ( v10_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v9_lattices @ sk_B ),
    inference(demod,[status(thm)],['153','154','155'])).

thf('157',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattices @ sk_B @ sk_C @ X0 )
      | ( r1_lattices @ sk_B @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['138','144','150','156','157'])).

thf('159',plain,
    ( ( ( r3_lattice3 @ sk_B @ sk_C @ sk_A )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
      | ( r1_lattices @ sk_B @ sk_C @ ( sk_D @ sk_A @ sk_C @ sk_B ) ) )
   <= ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['135','158'])).

thf('160',plain,
    ( ( ( r1_lattices @ sk_B @ sk_C @ ( sk_D @ sk_A @ sk_C @ sk_B ) )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ( r3_lattice3 @ sk_B @ sk_C @ sk_A ) )
   <= ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,
    ( ( ( r3_lattice3 @ sk_B @ sk_C @ sk_A )
      | ( r3_lattice3 @ sk_B @ sk_C @ sk_A )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_lattices @ sk_B @ sk_C @ ( sk_D @ sk_A @ sk_C @ sk_B ) ) )
   <= ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['61','160'])).

thf('162',plain,
    ( ( ( r1_lattices @ sk_B @ sk_C @ ( sk_D @ sk_A @ sk_C @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ( r3_lattice3 @ sk_B @ sk_C @ sk_A ) )
   <= ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r1_lattices @ X8 @ X7 @ ( sk_D @ X11 @ X7 @ X8 ) )
      | ( r3_lattice3 @ X8 @ X7 @ X11 )
      | ~ ( l3_lattices @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ( r3_lattice3 @ sk_B @ sk_C @ X0 )
      | ~ ( r1_lattices @ sk_B @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r3_lattice3 @ sk_B @ sk_C @ X0 )
      | ~ ( r1_lattices @ sk_B @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_B @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_B ) )
      | ( r3_lattice3 @ sk_B @ sk_C @ X0 ) ) ),
    inference(clc,[status(thm)],['167','168'])).

thf('170',plain,
    ( ( ( r3_lattice3 @ sk_B @ sk_C @ sk_A )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( r3_lattice3 @ sk_B @ sk_C @ sk_A ) )
   <= ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['162','169'])).

thf('171',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ( r3_lattice3 @ sk_B @ sk_C @ sk_A ) )
   <= ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,
    ( ( ( r3_lattice3 @ sk_B @ sk_C @ sk_A )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
   <= ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['171','172'])).

thf('174',plain,
    ( ~ ( r3_lattice3 @ sk_B @ sk_C @ sk_A )
   <= ~ ( r3_lattice3 @ sk_B @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['53'])).

thf('175',plain,
    ( ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
   <= ( ~ ( r3_lattice3 @ sk_B @ sk_C @ sk_A )
      & ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['173','174'])).

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

thf('176',plain,(
    ! [X25: $i] :
      ( ~ ( v2_struct_0 @ ( k3_lattice3 @ X25 ) )
      | ~ ( l3_lattices @ X25 )
      | ~ ( v10_lattices @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc4_lattice3])).

thf('177',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B ) )
   <= ( ~ ( r3_lattice3 @ sk_B @ sk_C @ sk_A )
      & ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,
    ( ( v2_struct_0 @ sk_B )
   <= ( ~ ( r3_lattice3 @ sk_B @ sk_C @ sk_A )
      & ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['177','178','179'])).

thf('181',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ( r3_lattice3 @ sk_B @ sk_C @ sk_A )
    | ~ ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,
    ( ( r3_lattice3 @ sk_B @ sk_C @ sk_A )
    | ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['51'])).

thf('184',plain,(
    r3_lattice3 @ sk_B @ sk_C @ sk_A ),
    inference('sat_resolution*',[status(thm)],['54','182','183'])).

thf('185',plain,(
    r3_lattice3 @ sk_B @ sk_C @ sk_A ),
    inference(simpl_trail,[status(thm)],['52','184'])).

thf('186',plain,(
    ! [X20: $i] :
      ( ( l1_orders_2 @ ( k3_lattice3 @ X20 ) )
      | ~ ( l3_lattices @ X20 )
      | ~ ( v10_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_lattice3])).

thf('187',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('188',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ( r2_hidden @ ( sk_D_1 @ X16 @ X18 @ X17 ) @ X18 )
      | ( r1_lattice3 @ X17 @ X18 @ X16 )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('189',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ ( k3_lattice3 @ sk_B ) )
      | ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ X0 )
      | ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['186','189'])).

thf('191',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ X0 )
      | ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['190','191','192'])).

thf('194',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('197',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r3_lattice3 @ X8 @ X7 @ X9 )
      | ~ ( r2_hidden @ X10 @ X9 )
      | ( r1_lattices @ X8 @ X7 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l3_lattices @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('199',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_lattices @ sk_B @ sk_C @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r3_lattice3 @ sk_B @ sk_C @ X1 ) ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_lattices @ sk_B @ sk_C @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r3_lattice3 @ sk_B @ sk_C @ X1 ) ) ),
    inference(demod,[status(thm)],['199','200'])).

thf('202',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ~ ( r3_lattice3 @ sk_B @ sk_C @ X1 )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ X1 )
      | ( r1_lattices @ sk_B @ sk_C @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['196','201'])).

thf('203',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( r1_lattices @ sk_B @ sk_C @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) )
      | ~ ( r3_lattice3 @ sk_B @ sk_C @ X0 )
      | ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['195','202'])).

thf('204',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattice3 @ sk_B @ sk_C @ X0 )
      | ( r1_lattices @ sk_B @ sk_C @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['203'])).

thf('205',plain,
    ( ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( r1_lattices @ sk_B @ sk_C @ ( sk_D_1 @ sk_C @ sk_A @ ( k3_lattice3 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['185','204'])).

thf('206',plain,
    ( ~ ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) )
   <= ~ ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['53'])).

thf('207',plain,
    ( ( k4_lattice3 @ sk_B @ sk_C )
    = sk_C ),
    inference(clc,[status(thm)],['10','11'])).

thf('208',plain,
    ( ~ ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C )
   <= ~ ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['206','207'])).

thf('209',plain,(
    ~ ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ ( k4_lattice3 @ sk_B @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['54','182'])).

thf('210',plain,(
    ~ ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['208','209'])).

thf('211',plain,
    ( ( r1_lattices @ sk_B @ sk_C @ ( sk_D_1 @ sk_C @ sk_A @ ( k3_lattice3 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['205','210'])).

thf('212',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    r1_lattices @ sk_B @ sk_C @ ( sk_D_1 @ sk_C @ sk_A @ ( k3_lattice3 @ sk_B ) ) ),
    inference(clc,[status(thm)],['211','212'])).

thf('214',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
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

thf('216',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_B @ sk_C @ X0 )
      | ( r3_lattices @ sk_B @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v6_lattices @ sk_B )
      | ~ ( v8_lattices @ sk_B )
      | ~ ( v9_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B ) ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('217',plain,(
    v6_lattices @ sk_B ),
    inference(demod,[status(thm)],['141','142','143'])).

thf('218',plain,(
    v8_lattices @ sk_B ),
    inference(demod,[status(thm)],['147','148','149'])).

thf('219',plain,(
    v9_lattices @ sk_B ),
    inference(demod,[status(thm)],['153','154','155'])).

thf('220',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_B @ sk_C @ X0 )
      | ( r3_lattices @ sk_B @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['216','217','218','219','220'])).

thf('222',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_A @ ( k3_lattice3 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) )
    | ( r3_lattices @ sk_B @ sk_C @ ( sk_D_1 @ sk_C @ sk_A @ ( k3_lattice3 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['213','221'])).

thf('223',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,
    ( ( r3_lattices @ sk_B @ sk_C @ ( sk_D_1 @ sk_C @ sk_A @ ( k3_lattice3 @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_A @ ( k3_lattice3 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['222','223'])).

thf('225',plain,
    ( ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C )
    | ( r3_lattices @ sk_B @ sk_C @ ( sk_D_1 @ sk_C @ sk_A @ ( k3_lattice3 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['50','224'])).

thf('226',plain,(
    ~ ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['208','209'])).

thf('227',plain,(
    r3_lattices @ sk_B @ sk_C @ ( sk_D_1 @ sk_C @ sk_A @ ( k3_lattice3 @ sk_B ) ) ),
    inference(clc,[status(thm)],['225','226'])).

thf('228',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('229',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ~ ( r3_lattices @ X27 @ X26 @ X28 )
      | ( r3_orders_2 @ ( k3_lattice3 @ X27 ) @ ( k4_lattice3 @ X27 @ X26 ) @ ( k4_lattice3 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X27 ) )
      | ~ ( l3_lattices @ X27 )
      | ~ ( v10_lattices @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_lattice3])).

thf('231',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ ( k4_lattice3 @ sk_B @ sk_C ) @ ( k4_lattice3 @ sk_B @ X0 ) )
      | ~ ( r3_lattices @ sk_B @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['229','230'])).

thf('232',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,
    ( ( k4_lattice3 @ sk_B @ sk_C )
    = sk_C ),
    inference(clc,[status(thm)],['10','11'])).

thf('235',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ ( k4_lattice3 @ sk_B @ X0 ) )
      | ~ ( r3_lattices @ sk_B @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['231','232','233','234'])).

thf('236',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ~ ( r3_lattices @ sk_B @ sk_C @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ ( k4_lattice3 @ sk_B @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['228','235'])).

thf('237',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ ( k4_lattice3 @ sk_B @ ( sk_D_1 @ sk_C @ sk_A @ ( k3_lattice3 @ sk_B ) ) ) )
    | ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['227','236'])).

thf('238',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,
    ( ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C )
    | ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ ( k4_lattice3 @ sk_B @ ( sk_D_1 @ sk_C @ sk_A @ ( k3_lattice3 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['237','238'])).

thf('240',plain,(
    ~ ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['208','209'])).

thf('241',plain,(
    r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ ( k4_lattice3 @ sk_B @ ( sk_D_1 @ sk_C @ sk_A @ ( k3_lattice3 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['239','240'])).

thf('242',plain,
    ( ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ ( sk_D_1 @ sk_C @ sk_A @ ( k3_lattice3 @ sk_B ) ) )
    | ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['49','241'])).

thf('243',plain,(
    ~ ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['208','209'])).

thf('244',plain,(
    r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ ( sk_D_1 @ sk_C @ sk_A @ ( k3_lattice3 @ sk_B ) ) ),
    inference(clc,[status(thm)],['242','243'])).

thf('245',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('246',plain,(
    ! [X20: $i] :
      ( ( l1_orders_2 @ ( k3_lattice3 @ X20 ) )
      | ~ ( l3_lattices @ X20 )
      | ~ ( v10_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_lattice3])).

thf('247',plain,(
    ! [X20: $i] :
      ( ( v3_orders_2 @ ( k3_lattice3 @ X20 ) )
      | ~ ( l3_lattices @ X20 )
      | ~ ( v10_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_lattice3])).

thf('248',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('249',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r1_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( r3_orders_2 @ X1 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('250',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ X0 )
      | ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ~ ( v3_orders_2 @ ( k3_lattice3 @ sk_B ) )
      | ~ ( l1_orders_2 @ ( k3_lattice3 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['248','249'])).

thf('251',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ~ ( l1_orders_2 @ ( k3_lattice3 @ sk_B ) )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ X0 )
      | ~ ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['247','250'])).

thf('252',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( l1_orders_2 @ ( k3_lattice3 @ sk_B ) )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ X0 )
      | ~ ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['251','252','253'])).

thf('255',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ~ ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ X0 )
      | ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['246','254'])).

thf('256',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('257',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('258',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ X0 )
      | ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['255','256','257'])).

thf('259',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ X0 )
      | ~ ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['258'])).

thf('260',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( r3_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['245','259'])).

thf('261',plain,
    ( ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
    | ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ ( sk_D_1 @ sk_C @ sk_A @ ( k3_lattice3 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['244','260'])).

thf('262',plain,(
    ! [X20: $i] :
      ( ( l1_orders_2 @ ( k3_lattice3 @ X20 ) )
      | ~ ( l3_lattices @ X20 )
      | ~ ( v10_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_lattice3])).

thf('263',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('264',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ~ ( r1_orders_2 @ X17 @ X16 @ ( sk_D_1 @ X16 @ X18 @ X17 ) )
      | ( r1_lattice3 @ X17 @ X18 @ X16 )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('265',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ ( k3_lattice3 @ sk_B ) )
      | ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ~ ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['263','264'])).

thf('266',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ~ ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['262','265'])).

thf('267',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('268',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('269',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) )
      | ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['266','267','268'])).

thf('270',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('271',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ~ ( r1_orders_2 @ ( k3_lattice3 @ sk_B ) @ sk_C @ ( sk_D_1 @ sk_C @ X0 @ ( k3_lattice3 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['269','270'])).

thf('272',plain,
    ( ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
    | ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['261','271'])).

thf('273',plain,
    ( ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['272'])).

thf('274',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('275',plain,
    ( ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C )
    | ( v2_struct_0 @ ( k3_lattice3 @ sk_B ) ) ),
    inference(clc,[status(thm)],['273','274'])).

thf('276',plain,(
    ~ ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['208','209'])).

thf('277',plain,(
    v2_struct_0 @ ( k3_lattice3 @ sk_B ) ),
    inference(clc,[status(thm)],['275','276'])).

thf('278',plain,(
    ! [X25: $i] :
      ( ~ ( v2_struct_0 @ ( k3_lattice3 @ X25 ) )
      | ~ ( l3_lattices @ X25 )
      | ~ ( v10_lattices @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc4_lattice3])).

thf('279',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v10_lattices @ sk_B )
    | ~ ( l3_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['277','278'])).

thf('280',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('282',plain,(
    v2_struct_0 @ sk_B ),
    inference(demod,[status(thm)],['279','280','281'])).

thf('283',plain,(
    $false ),
    inference(demod,[status(thm)],['0','282'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LQFhMF1qnR
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:10:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.58/0.83  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.58/0.83  % Solved by: fo/fo7.sh
% 0.58/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.83  % done 464 iterations in 0.389s
% 0.58/0.83  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.58/0.83  % SZS output start Refutation
% 0.58/0.83  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.58/0.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.83  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.58/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.83  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.83  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.58/0.83  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.58/0.83  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.58/0.83  thf(sk_C_type, type, sk_C: $i).
% 0.58/0.83  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.58/0.83  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.58/0.83  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.58/0.83  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.58/0.83  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.58/0.83  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 0.58/0.83  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.58/0.83  thf(k4_lattice3_type, type, k4_lattice3: $i > $i > $i).
% 0.58/0.83  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.83  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.58/0.83  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.58/0.83  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.58/0.83  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 0.58/0.83  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.58/0.83  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.58/0.83  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.58/0.83  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.58/0.83  thf(r3_lattice3_type, type, r3_lattice3: $i > $i > $i > $o).
% 0.58/0.83  thf(k5_lattice3_type, type, k5_lattice3: $i > $i > $i).
% 0.58/0.83  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.58/0.83  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.58/0.83  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.58/0.83  thf(t28_lattice3, conjecture,
% 0.58/0.83    (![A:$i,B:$i]:
% 0.58/0.83     ( ( ( ~( v2_struct_0 @ B ) ) & ( v10_lattices @ B ) & ( l3_lattices @ B ) ) =>
% 0.58/0.83       ( ![C:$i]:
% 0.58/0.83         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.58/0.83           ( ( r3_lattice3 @ B @ C @ A ) <=>
% 0.58/0.83             ( r1_lattice3 @ ( k3_lattice3 @ B ) @ A @ ( k4_lattice3 @ B @ C ) ) ) ) ) ))).
% 0.58/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.83    (~( ![A:$i,B:$i]:
% 0.58/0.83        ( ( ( ~( v2_struct_0 @ B ) ) & ( v10_lattices @ B ) & 
% 0.58/0.83            ( l3_lattices @ B ) ) =>
% 0.58/0.83          ( ![C:$i]:
% 0.58/0.83            ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.58/0.83              ( ( r3_lattice3 @ B @ C @ A ) <=>
% 0.58/0.83                ( r1_lattice3 @
% 0.58/0.83                  ( k3_lattice3 @ B ) @ A @ ( k4_lattice3 @ B @ C ) ) ) ) ) ) )),
% 0.58/0.83    inference('cnf.neg', [status(esa)], [t28_lattice3])).
% 0.58/0.83  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf(dt_k3_lattice3, axiom,
% 0.58/0.83    (![A:$i]:
% 0.58/0.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.58/0.83       ( ( v1_orders_2 @ ( k3_lattice3 @ A ) ) & 
% 0.58/0.83         ( v3_orders_2 @ ( k3_lattice3 @ A ) ) & 
% 0.58/0.83         ( v4_orders_2 @ ( k3_lattice3 @ A ) ) & 
% 0.58/0.83         ( v5_orders_2 @ ( k3_lattice3 @ A ) ) & 
% 0.58/0.83         ( l1_orders_2 @ ( k3_lattice3 @ A ) ) ) ))).
% 0.58/0.83  thf('1', plain,
% 0.58/0.83      (![X20 : $i]:
% 0.58/0.83         ((l1_orders_2 @ (k3_lattice3 @ X20))
% 0.58/0.83          | ~ (l3_lattices @ X20)
% 0.58/0.83          | ~ (v10_lattices @ X20)
% 0.58/0.83          | (v2_struct_0 @ X20))),
% 0.58/0.83      inference('cnf', [status(esa)], [dt_k3_lattice3])).
% 0.58/0.83  thf('2', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_B))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf(dt_k4_lattice3, axiom,
% 0.58/0.83    (![A:$i,B:$i]:
% 0.58/0.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.58/0.83         ( l3_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.83       ( m1_subset_1 @
% 0.58/0.83         ( k4_lattice3 @ A @ B ) @ ( u1_struct_0 @ ( k3_lattice3 @ A ) ) ) ))).
% 0.58/0.83  thf('3', plain,
% 0.58/0.83      (![X21 : $i, X22 : $i]:
% 0.58/0.83         (~ (l3_lattices @ X21)
% 0.58/0.83          | ~ (v10_lattices @ X21)
% 0.58/0.83          | (v2_struct_0 @ X21)
% 0.58/0.83          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.58/0.83          | (m1_subset_1 @ (k4_lattice3 @ X21 @ X22) @ 
% 0.58/0.83             (u1_struct_0 @ (k3_lattice3 @ X21))))),
% 0.58/0.83      inference('cnf', [status(esa)], [dt_k4_lattice3])).
% 0.58/0.83  thf('4', plain,
% 0.58/0.83      (((m1_subset_1 @ (k4_lattice3 @ sk_B @ sk_C) @ 
% 0.58/0.83         (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 0.58/0.83        | (v2_struct_0 @ sk_B)
% 0.58/0.83        | ~ (v10_lattices @ sk_B)
% 0.58/0.83        | ~ (l3_lattices @ sk_B))),
% 0.58/0.83      inference('sup-', [status(thm)], ['2', '3'])).
% 0.58/0.83  thf('5', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_B))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf(d3_lattice3, axiom,
% 0.58/0.83    (![A:$i]:
% 0.58/0.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.58/0.83       ( ![B:$i]:
% 0.58/0.83         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.83           ( ( k4_lattice3 @ A @ B ) = ( B ) ) ) ) ))).
% 0.58/0.83  thf('6', plain,
% 0.58/0.83      (![X12 : $i, X13 : $i]:
% 0.58/0.83         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.58/0.83          | ((k4_lattice3 @ X13 @ X12) = (X12))
% 0.58/0.83          | ~ (l3_lattices @ X13)
% 0.58/0.83          | ~ (v10_lattices @ X13)
% 0.58/0.83          | (v2_struct_0 @ X13))),
% 0.58/0.83      inference('cnf', [status(esa)], [d3_lattice3])).
% 0.58/0.83  thf('7', plain,
% 0.58/0.83      (((v2_struct_0 @ sk_B)
% 0.58/0.83        | ~ (v10_lattices @ sk_B)
% 0.58/0.83        | ~ (l3_lattices @ sk_B)
% 0.58/0.83        | ((k4_lattice3 @ sk_B @ sk_C) = (sk_C)))),
% 0.58/0.83      inference('sup-', [status(thm)], ['5', '6'])).
% 0.58/0.83  thf('8', plain, ((v10_lattices @ sk_B)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('9', plain, ((l3_lattices @ sk_B)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('10', plain,
% 0.58/0.83      (((v2_struct_0 @ sk_B) | ((k4_lattice3 @ sk_B @ sk_C) = (sk_C)))),
% 0.58/0.83      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.58/0.83  thf('11', plain, (~ (v2_struct_0 @ sk_B)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('12', plain, (((k4_lattice3 @ sk_B @ sk_C) = (sk_C))),
% 0.58/0.83      inference('clc', [status(thm)], ['10', '11'])).
% 0.58/0.83  thf('13', plain, ((v10_lattices @ sk_B)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('14', plain, ((l3_lattices @ sk_B)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('15', plain,
% 0.58/0.83      (((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 0.58/0.83        | (v2_struct_0 @ sk_B))),
% 0.58/0.83      inference('demod', [status(thm)], ['4', '12', '13', '14'])).
% 0.58/0.83  thf('16', plain, (~ (v2_struct_0 @ sk_B)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('17', plain,
% 0.58/0.83      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))),
% 0.58/0.83      inference('clc', [status(thm)], ['15', '16'])).
% 0.58/0.83  thf(d8_lattice3, axiom,
% 0.58/0.83    (![A:$i]:
% 0.58/0.83     ( ( l1_orders_2 @ A ) =>
% 0.58/0.83       ( ![B:$i,C:$i]:
% 0.58/0.83         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.83           ( ( r1_lattice3 @ A @ B @ C ) <=>
% 0.58/0.83             ( ![D:$i]:
% 0.58/0.83               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.83                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ))).
% 0.58/0.83  thf('18', plain,
% 0.58/0.83      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.58/0.83         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.58/0.83          | (m1_subset_1 @ (sk_D_1 @ X16 @ X18 @ X17) @ (u1_struct_0 @ X17))
% 0.58/0.83          | (r1_lattice3 @ X17 @ X18 @ X16)
% 0.58/0.83          | ~ (l1_orders_2 @ X17))),
% 0.58/0.83      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.58/0.83  thf('19', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         (~ (l1_orders_2 @ (k3_lattice3 @ sk_B))
% 0.58/0.83          | (r1_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 0.58/0.83          | (m1_subset_1 @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ 
% 0.58/0.83             (u1_struct_0 @ (k3_lattice3 @ sk_B))))),
% 0.58/0.83      inference('sup-', [status(thm)], ['17', '18'])).
% 0.58/0.83  thf('20', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         ((v2_struct_0 @ sk_B)
% 0.58/0.83          | ~ (v10_lattices @ sk_B)
% 0.58/0.83          | ~ (l3_lattices @ sk_B)
% 0.58/0.83          | (m1_subset_1 @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ 
% 0.58/0.83             (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 0.58/0.83          | (r1_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C))),
% 0.58/0.83      inference('sup-', [status(thm)], ['1', '19'])).
% 0.58/0.83  thf('21', plain, ((v10_lattices @ sk_B)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('22', plain, ((l3_lattices @ sk_B)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('23', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         ((v2_struct_0 @ sk_B)
% 0.58/0.83          | (m1_subset_1 @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ 
% 0.58/0.83             (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 0.58/0.83          | (r1_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C))),
% 0.58/0.83      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.58/0.83  thf('24', plain, (~ (v2_struct_0 @ sk_B)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('25', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         ((r1_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 0.58/0.83          | (m1_subset_1 @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ 
% 0.58/0.83             (u1_struct_0 @ (k3_lattice3 @ sk_B))))),
% 0.58/0.83      inference('clc', [status(thm)], ['23', '24'])).
% 0.58/0.83  thf(d4_lattice3, axiom,
% 0.58/0.83    (![A:$i]:
% 0.58/0.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.58/0.83       ( ![B:$i]:
% 0.58/0.83         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k3_lattice3 @ A ) ) ) =>
% 0.58/0.83           ( ( k5_lattice3 @ A @ B ) = ( B ) ) ) ) ))).
% 0.58/0.83  thf('26', plain,
% 0.58/0.83      (![X14 : $i, X15 : $i]:
% 0.58/0.83         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ (k3_lattice3 @ X15)))
% 0.58/0.83          | ((k5_lattice3 @ X15 @ X14) = (X14))
% 0.58/0.83          | ~ (l3_lattices @ X15)
% 0.58/0.83          | ~ (v10_lattices @ X15)
% 0.58/0.83          | (v2_struct_0 @ X15))),
% 0.58/0.83      inference('cnf', [status(esa)], [d4_lattice3])).
% 0.58/0.83  thf('27', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         ((r1_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 0.58/0.83          | (v2_struct_0 @ sk_B)
% 0.58/0.83          | ~ (v10_lattices @ sk_B)
% 0.58/0.83          | ~ (l3_lattices @ sk_B)
% 0.58/0.83          | ((k5_lattice3 @ sk_B @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)))
% 0.58/0.83              = (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B))))),
% 0.58/0.83      inference('sup-', [status(thm)], ['25', '26'])).
% 0.58/0.83  thf('28', plain, ((v10_lattices @ sk_B)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('29', plain, ((l3_lattices @ sk_B)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('30', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         ((r1_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 0.58/0.83          | (v2_struct_0 @ sk_B)
% 0.58/0.83          | ((k5_lattice3 @ sk_B @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)))
% 0.58/0.83              = (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B))))),
% 0.58/0.83      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.58/0.83  thf('31', plain, (~ (v2_struct_0 @ sk_B)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('32', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         (((k5_lattice3 @ sk_B @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)))
% 0.58/0.83            = (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)))
% 0.58/0.83          | (r1_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C))),
% 0.58/0.83      inference('clc', [status(thm)], ['30', '31'])).
% 0.58/0.83  thf('33', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         ((r1_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 0.58/0.83          | (m1_subset_1 @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ 
% 0.58/0.83             (u1_struct_0 @ (k3_lattice3 @ sk_B))))),
% 0.58/0.83      inference('clc', [status(thm)], ['23', '24'])).
% 0.58/0.83  thf(dt_k5_lattice3, axiom,
% 0.58/0.83    (![A:$i,B:$i]:
% 0.58/0.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.58/0.83         ( l3_lattices @ A ) & 
% 0.58/0.83         ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k3_lattice3 @ A ) ) ) ) =>
% 0.58/0.83       ( m1_subset_1 @ ( k5_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.58/0.83  thf('34', plain,
% 0.58/0.83      (![X23 : $i, X24 : $i]:
% 0.58/0.83         (~ (l3_lattices @ X23)
% 0.58/0.83          | ~ (v10_lattices @ X23)
% 0.58/0.83          | (v2_struct_0 @ X23)
% 0.58/0.83          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ (k3_lattice3 @ X23)))
% 0.58/0.83          | (m1_subset_1 @ (k5_lattice3 @ X23 @ X24) @ (u1_struct_0 @ X23)))),
% 0.58/0.83      inference('cnf', [status(esa)], [dt_k5_lattice3])).
% 0.58/0.83  thf('35', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         ((r1_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 0.58/0.83          | (m1_subset_1 @ 
% 0.58/0.83             (k5_lattice3 @ sk_B @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B))) @ 
% 0.58/0.83             (u1_struct_0 @ sk_B))
% 0.58/0.83          | (v2_struct_0 @ sk_B)
% 0.58/0.83          | ~ (v10_lattices @ sk_B)
% 0.58/0.83          | ~ (l3_lattices @ sk_B))),
% 0.58/0.83      inference('sup-', [status(thm)], ['33', '34'])).
% 0.58/0.83  thf('36', plain, ((v10_lattices @ sk_B)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('37', plain, ((l3_lattices @ sk_B)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('38', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         ((r1_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 0.58/0.83          | (m1_subset_1 @ 
% 0.58/0.83             (k5_lattice3 @ sk_B @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B))) @ 
% 0.58/0.83             (u1_struct_0 @ sk_B))
% 0.58/0.83          | (v2_struct_0 @ sk_B))),
% 0.58/0.83      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.58/0.83  thf('39', plain, (~ (v2_struct_0 @ sk_B)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('40', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         ((m1_subset_1 @ 
% 0.58/0.83           (k5_lattice3 @ sk_B @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B))) @ 
% 0.58/0.83           (u1_struct_0 @ sk_B))
% 0.58/0.83          | (r1_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C))),
% 0.58/0.83      inference('clc', [status(thm)], ['38', '39'])).
% 0.58/0.83  thf('41', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         ((m1_subset_1 @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ 
% 0.58/0.83           (u1_struct_0 @ sk_B))
% 0.58/0.83          | (r1_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 0.58/0.83          | (r1_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C))),
% 0.58/0.83      inference('sup+', [status(thm)], ['32', '40'])).
% 0.58/0.83  thf('42', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         ((r1_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 0.58/0.83          | (m1_subset_1 @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ 
% 0.58/0.83             (u1_struct_0 @ sk_B)))),
% 0.58/0.83      inference('simplify', [status(thm)], ['41'])).
% 0.58/0.83  thf('43', plain,
% 0.58/0.83      (![X12 : $i, X13 : $i]:
% 0.58/0.83         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.58/0.83          | ((k4_lattice3 @ X13 @ X12) = (X12))
% 0.58/0.83          | ~ (l3_lattices @ X13)
% 0.58/0.83          | ~ (v10_lattices @ X13)
% 0.58/0.83          | (v2_struct_0 @ X13))),
% 0.58/0.83      inference('cnf', [status(esa)], [d3_lattice3])).
% 0.58/0.83  thf('44', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         ((r1_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 0.58/0.83          | (v2_struct_0 @ sk_B)
% 0.58/0.83          | ~ (v10_lattices @ sk_B)
% 0.58/0.83          | ~ (l3_lattices @ sk_B)
% 0.58/0.83          | ((k4_lattice3 @ sk_B @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)))
% 0.58/0.83              = (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B))))),
% 0.58/0.83      inference('sup-', [status(thm)], ['42', '43'])).
% 0.58/0.83  thf('45', plain, ((v10_lattices @ sk_B)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('46', plain, ((l3_lattices @ sk_B)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('47', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         ((r1_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 0.58/0.83          | (v2_struct_0 @ sk_B)
% 0.58/0.83          | ((k4_lattice3 @ sk_B @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)))
% 0.58/0.83              = (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B))))),
% 0.58/0.83      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.58/0.83  thf('48', plain, (~ (v2_struct_0 @ sk_B)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('49', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         (((k4_lattice3 @ sk_B @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)))
% 0.58/0.83            = (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)))
% 0.58/0.83          | (r1_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C))),
% 0.58/0.83      inference('clc', [status(thm)], ['47', '48'])).
% 0.58/0.83  thf('50', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         ((r1_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 0.58/0.83          | (m1_subset_1 @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ 
% 0.58/0.83             (u1_struct_0 @ sk_B)))),
% 0.58/0.83      inference('simplify', [status(thm)], ['41'])).
% 0.58/0.83  thf('51', plain,
% 0.58/0.83      (((r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 0.58/0.83         (k4_lattice3 @ sk_B @ sk_C))
% 0.58/0.83        | (r3_lattice3 @ sk_B @ sk_C @ sk_A))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('52', plain,
% 0.58/0.83      (((r3_lattice3 @ sk_B @ sk_C @ sk_A))
% 0.58/0.83         <= (((r3_lattice3 @ sk_B @ sk_C @ sk_A)))),
% 0.58/0.83      inference('split', [status(esa)], ['51'])).
% 0.58/0.83  thf('53', plain,
% 0.58/0.83      ((~ (r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 0.58/0.83           (k4_lattice3 @ sk_B @ sk_C))
% 0.58/0.83        | ~ (r3_lattice3 @ sk_B @ sk_C @ sk_A))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('54', plain,
% 0.58/0.83      (~
% 0.58/0.83       ((r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 0.58/0.83         (k4_lattice3 @ sk_B @ sk_C))) | 
% 0.58/0.83       ~ ((r3_lattice3 @ sk_B @ sk_C @ sk_A))),
% 0.58/0.83      inference('split', [status(esa)], ['53'])).
% 0.58/0.83  thf('55', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_B))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf(d16_lattice3, axiom,
% 0.58/0.83    (![A:$i]:
% 0.58/0.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.58/0.83       ( ![B:$i]:
% 0.58/0.83         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.83           ( ![C:$i]:
% 0.58/0.83             ( ( r3_lattice3 @ A @ B @ C ) <=>
% 0.58/0.83               ( ![D:$i]:
% 0.58/0.83                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.83                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 0.58/0.83  thf('56', plain,
% 0.58/0.83      (![X7 : $i, X8 : $i, X11 : $i]:
% 0.58/0.83         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.58/0.83          | (m1_subset_1 @ (sk_D @ X11 @ X7 @ X8) @ (u1_struct_0 @ X8))
% 0.58/0.83          | (r3_lattice3 @ X8 @ X7 @ X11)
% 0.58/0.83          | ~ (l3_lattices @ X8)
% 0.58/0.83          | (v2_struct_0 @ X8))),
% 0.58/0.83      inference('cnf', [status(esa)], [d16_lattice3])).
% 0.58/0.83  thf('57', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         ((v2_struct_0 @ sk_B)
% 0.58/0.83          | ~ (l3_lattices @ sk_B)
% 0.58/0.83          | (r3_lattice3 @ sk_B @ sk_C @ X0)
% 0.58/0.83          | (m1_subset_1 @ (sk_D @ X0 @ sk_C @ sk_B) @ (u1_struct_0 @ sk_B)))),
% 0.58/0.83      inference('sup-', [status(thm)], ['55', '56'])).
% 0.58/0.83  thf('58', plain, ((l3_lattices @ sk_B)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('59', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         ((v2_struct_0 @ sk_B)
% 0.58/0.83          | (r3_lattice3 @ sk_B @ sk_C @ X0)
% 0.58/0.83          | (m1_subset_1 @ (sk_D @ X0 @ sk_C @ sk_B) @ (u1_struct_0 @ sk_B)))),
% 0.58/0.83      inference('demod', [status(thm)], ['57', '58'])).
% 0.58/0.83  thf('60', plain, (~ (v2_struct_0 @ sk_B)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('61', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         ((m1_subset_1 @ (sk_D @ X0 @ sk_C @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.58/0.83          | (r3_lattice3 @ sk_B @ sk_C @ X0))),
% 0.58/0.83      inference('clc', [status(thm)], ['59', '60'])).
% 0.58/0.83  thf('62', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         ((m1_subset_1 @ (sk_D @ X0 @ sk_C @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.58/0.83          | (r3_lattice3 @ sk_B @ sk_C @ X0))),
% 0.58/0.83      inference('clc', [status(thm)], ['59', '60'])).
% 0.58/0.83  thf('63', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_B))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('64', plain,
% 0.58/0.83      (![X7 : $i, X8 : $i, X11 : $i]:
% 0.58/0.83         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.58/0.83          | (r2_hidden @ (sk_D @ X11 @ X7 @ X8) @ X11)
% 0.58/0.83          | (r3_lattice3 @ X8 @ X7 @ X11)
% 0.58/0.83          | ~ (l3_lattices @ X8)
% 0.58/0.83          | (v2_struct_0 @ X8))),
% 0.58/0.83      inference('cnf', [status(esa)], [d16_lattice3])).
% 0.58/0.83  thf('65', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         ((v2_struct_0 @ sk_B)
% 0.58/0.83          | ~ (l3_lattices @ sk_B)
% 0.58/0.83          | (r3_lattice3 @ sk_B @ sk_C @ X0)
% 0.58/0.83          | (r2_hidden @ (sk_D @ X0 @ sk_C @ sk_B) @ X0))),
% 0.58/0.83      inference('sup-', [status(thm)], ['63', '64'])).
% 0.58/0.83  thf('66', plain, ((l3_lattices @ sk_B)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('67', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         ((v2_struct_0 @ sk_B)
% 0.58/0.83          | (r3_lattice3 @ sk_B @ sk_C @ X0)
% 0.58/0.83          | (r2_hidden @ (sk_D @ X0 @ sk_C @ sk_B) @ X0))),
% 0.58/0.83      inference('demod', [status(thm)], ['65', '66'])).
% 0.58/0.83  thf('68', plain, (~ (v2_struct_0 @ sk_B)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('69', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         ((r2_hidden @ (sk_D @ X0 @ sk_C @ sk_B) @ X0)
% 0.58/0.83          | (r3_lattice3 @ sk_B @ sk_C @ X0))),
% 0.58/0.83      inference('clc', [status(thm)], ['67', '68'])).
% 0.58/0.83  thf('70', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         ((m1_subset_1 @ (sk_D @ X0 @ sk_C @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.58/0.83          | (r3_lattice3 @ sk_B @ sk_C @ X0))),
% 0.58/0.83      inference('clc', [status(thm)], ['59', '60'])).
% 0.58/0.83  thf('71', plain,
% 0.58/0.83      (![X12 : $i, X13 : $i]:
% 0.58/0.83         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.58/0.83          | ((k4_lattice3 @ X13 @ X12) = (X12))
% 0.58/0.83          | ~ (l3_lattices @ X13)
% 0.58/0.83          | ~ (v10_lattices @ X13)
% 0.58/0.83          | (v2_struct_0 @ X13))),
% 0.58/0.83      inference('cnf', [status(esa)], [d3_lattice3])).
% 0.58/0.83  thf('72', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         ((r3_lattice3 @ sk_B @ sk_C @ X0)
% 0.58/0.83          | (v2_struct_0 @ sk_B)
% 0.58/0.83          | ~ (v10_lattices @ sk_B)
% 0.58/0.83          | ~ (l3_lattices @ sk_B)
% 0.58/0.83          | ((k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B))
% 0.58/0.83              = (sk_D @ X0 @ sk_C @ sk_B)))),
% 0.58/0.83      inference('sup-', [status(thm)], ['70', '71'])).
% 0.58/0.83  thf('73', plain, ((v10_lattices @ sk_B)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('74', plain, ((l3_lattices @ sk_B)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('75', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         ((r3_lattice3 @ sk_B @ sk_C @ X0)
% 0.58/0.83          | (v2_struct_0 @ sk_B)
% 0.58/0.83          | ((k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B))
% 0.58/0.83              = (sk_D @ X0 @ sk_C @ sk_B)))),
% 0.58/0.83      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.58/0.83  thf('76', plain, (~ (v2_struct_0 @ sk_B)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('77', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         (((k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B))
% 0.58/0.83            = (sk_D @ X0 @ sk_C @ sk_B))
% 0.58/0.83          | (r3_lattice3 @ sk_B @ sk_C @ X0))),
% 0.58/0.83      inference('clc', [status(thm)], ['75', '76'])).
% 0.58/0.83  thf('78', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         ((m1_subset_1 @ (sk_D @ X0 @ sk_C @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.58/0.83          | (r3_lattice3 @ sk_B @ sk_C @ X0))),
% 0.58/0.83      inference('clc', [status(thm)], ['59', '60'])).
% 0.58/0.83  thf('79', plain,
% 0.58/0.83      (![X21 : $i, X22 : $i]:
% 0.58/0.83         (~ (l3_lattices @ X21)
% 0.58/0.83          | ~ (v10_lattices @ X21)
% 0.58/0.83          | (v2_struct_0 @ X21)
% 0.58/0.83          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.58/0.83          | (m1_subset_1 @ (k4_lattice3 @ X21 @ X22) @ 
% 0.58/0.83             (u1_struct_0 @ (k3_lattice3 @ X21))))),
% 0.58/0.83      inference('cnf', [status(esa)], [dt_k4_lattice3])).
% 0.58/0.83  thf('80', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         ((r3_lattice3 @ sk_B @ sk_C @ X0)
% 0.58/0.83          | (m1_subset_1 @ (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B)) @ 
% 0.58/0.83             (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 0.58/0.83          | (v2_struct_0 @ sk_B)
% 0.58/0.83          | ~ (v10_lattices @ sk_B)
% 0.58/0.83          | ~ (l3_lattices @ sk_B))),
% 0.58/0.83      inference('sup-', [status(thm)], ['78', '79'])).
% 0.58/0.83  thf('81', plain, ((v10_lattices @ sk_B)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('82', plain, ((l3_lattices @ sk_B)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('83', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         ((r3_lattice3 @ sk_B @ sk_C @ X0)
% 0.58/0.83          | (m1_subset_1 @ (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B)) @ 
% 0.58/0.83             (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 0.58/0.83          | (v2_struct_0 @ sk_B))),
% 0.58/0.83      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.58/0.83  thf('84', plain, (~ (v2_struct_0 @ sk_B)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('85', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         ((m1_subset_1 @ (k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B)) @ 
% 0.58/0.83           (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 0.58/0.83          | (r3_lattice3 @ sk_B @ sk_C @ X0))),
% 0.58/0.83      inference('clc', [status(thm)], ['83', '84'])).
% 0.58/0.83  thf('86', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         ((m1_subset_1 @ (sk_D @ X0 @ sk_C @ sk_B) @ 
% 0.58/0.83           (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 0.58/0.83          | (r3_lattice3 @ sk_B @ sk_C @ X0)
% 0.58/0.83          | (r3_lattice3 @ sk_B @ sk_C @ X0))),
% 0.58/0.83      inference('sup+', [status(thm)], ['77', '85'])).
% 0.67/0.83  thf('87', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         ((r3_lattice3 @ sk_B @ sk_C @ X0)
% 0.67/0.83          | (m1_subset_1 @ (sk_D @ X0 @ sk_C @ sk_B) @ 
% 0.67/0.83             (u1_struct_0 @ (k3_lattice3 @ sk_B))))),
% 0.67/0.83      inference('simplify', [status(thm)], ['86'])).
% 0.67/0.83  thf('88', plain, (((k4_lattice3 @ sk_B @ sk_C) = (sk_C))),
% 0.67/0.83      inference('clc', [status(thm)], ['10', '11'])).
% 0.67/0.83  thf('89', plain,
% 0.67/0.83      (((r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 0.67/0.83         (k4_lattice3 @ sk_B @ sk_C)))
% 0.67/0.83         <= (((r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 0.67/0.83               (k4_lattice3 @ sk_B @ sk_C))))),
% 0.67/0.83      inference('split', [status(esa)], ['51'])).
% 0.67/0.83  thf('90', plain,
% 0.67/0.83      (((r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ sk_C))
% 0.67/0.83         <= (((r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 0.67/0.83               (k4_lattice3 @ sk_B @ sk_C))))),
% 0.67/0.83      inference('sup+', [status(thm)], ['88', '89'])).
% 0.67/0.83  thf('91', plain,
% 0.67/0.83      (![X20 : $i]:
% 0.67/0.83         ((l1_orders_2 @ (k3_lattice3 @ X20))
% 0.67/0.83          | ~ (l3_lattices @ X20)
% 0.67/0.83          | ~ (v10_lattices @ X20)
% 0.67/0.83          | (v2_struct_0 @ X20))),
% 0.67/0.83      inference('cnf', [status(esa)], [dt_k3_lattice3])).
% 0.67/0.83  thf('92', plain,
% 0.67/0.83      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))),
% 0.67/0.83      inference('clc', [status(thm)], ['15', '16'])).
% 0.67/0.83  thf('93', plain,
% 0.67/0.83      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.67/0.83         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.67/0.83          | ~ (r1_lattice3 @ X17 @ X18 @ X16)
% 0.67/0.83          | ~ (r2_hidden @ X19 @ X18)
% 0.67/0.83          | (r1_orders_2 @ X17 @ X16 @ X19)
% 0.67/0.83          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.67/0.83          | ~ (l1_orders_2 @ X17))),
% 0.67/0.83      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.67/0.83  thf('94', plain,
% 0.67/0.83      (![X0 : $i, X1 : $i]:
% 0.67/0.83         (~ (l1_orders_2 @ (k3_lattice3 @ sk_B))
% 0.67/0.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 0.67/0.83          | (r1_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ X0)
% 0.67/0.83          | ~ (r2_hidden @ X0 @ X1)
% 0.67/0.83          | ~ (r1_lattice3 @ (k3_lattice3 @ sk_B) @ X1 @ sk_C))),
% 0.67/0.83      inference('sup-', [status(thm)], ['92', '93'])).
% 0.67/0.83  thf('95', plain,
% 0.67/0.83      (![X0 : $i, X1 : $i]:
% 0.67/0.83         ((v2_struct_0 @ sk_B)
% 0.67/0.83          | ~ (v10_lattices @ sk_B)
% 0.67/0.83          | ~ (l3_lattices @ sk_B)
% 0.67/0.83          | ~ (r1_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 0.67/0.83          | ~ (r2_hidden @ X1 @ X0)
% 0.67/0.83          | (r1_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ X1)
% 0.67/0.83          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k3_lattice3 @ sk_B))))),
% 0.67/0.83      inference('sup-', [status(thm)], ['91', '94'])).
% 0.67/0.83  thf('96', plain, ((v10_lattices @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('97', plain, ((l3_lattices @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('98', plain,
% 0.67/0.83      (![X0 : $i, X1 : $i]:
% 0.67/0.83         ((v2_struct_0 @ sk_B)
% 0.67/0.83          | ~ (r1_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 0.67/0.83          | ~ (r2_hidden @ X1 @ X0)
% 0.67/0.83          | (r1_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ X1)
% 0.67/0.83          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k3_lattice3 @ sk_B))))),
% 0.67/0.83      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.67/0.83  thf('99', plain,
% 0.67/0.83      ((![X0 : $i]:
% 0.67/0.83          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 0.67/0.83           | (r1_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ X0)
% 0.67/0.83           | ~ (r2_hidden @ X0 @ sk_A)
% 0.67/0.83           | (v2_struct_0 @ sk_B)))
% 0.67/0.83         <= (((r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 0.67/0.83               (k4_lattice3 @ sk_B @ sk_C))))),
% 0.67/0.83      inference('sup-', [status(thm)], ['90', '98'])).
% 0.67/0.83  thf('100', plain,
% 0.67/0.83      ((![X0 : $i]:
% 0.67/0.83          ((r3_lattice3 @ sk_B @ sk_C @ X0)
% 0.67/0.83           | (v2_struct_0 @ sk_B)
% 0.67/0.83           | ~ (r2_hidden @ (sk_D @ X0 @ sk_C @ sk_B) @ sk_A)
% 0.67/0.83           | (r1_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ 
% 0.67/0.83              (sk_D @ X0 @ sk_C @ sk_B))))
% 0.67/0.83         <= (((r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 0.67/0.83               (k4_lattice3 @ sk_B @ sk_C))))),
% 0.67/0.83      inference('sup-', [status(thm)], ['87', '99'])).
% 0.67/0.83  thf('101', plain,
% 0.67/0.83      ((((r3_lattice3 @ sk_B @ sk_C @ sk_A)
% 0.67/0.83         | (r1_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ 
% 0.67/0.83            (sk_D @ sk_A @ sk_C @ sk_B))
% 0.67/0.83         | (v2_struct_0 @ sk_B)
% 0.67/0.83         | (r3_lattice3 @ sk_B @ sk_C @ sk_A)))
% 0.67/0.83         <= (((r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 0.67/0.83               (k4_lattice3 @ sk_B @ sk_C))))),
% 0.67/0.83      inference('sup-', [status(thm)], ['69', '100'])).
% 0.67/0.83  thf('102', plain,
% 0.67/0.83      ((((v2_struct_0 @ sk_B)
% 0.67/0.83         | (r1_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ 
% 0.67/0.83            (sk_D @ sk_A @ sk_C @ sk_B))
% 0.67/0.83         | (r3_lattice3 @ sk_B @ sk_C @ sk_A)))
% 0.67/0.83         <= (((r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 0.67/0.83               (k4_lattice3 @ sk_B @ sk_C))))),
% 0.67/0.83      inference('simplify', [status(thm)], ['101'])).
% 0.67/0.83  thf('103', plain, (~ (v2_struct_0 @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('104', plain,
% 0.67/0.83      ((((r3_lattice3 @ sk_B @ sk_C @ sk_A)
% 0.67/0.83         | (r1_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ 
% 0.67/0.83            (sk_D @ sk_A @ sk_C @ sk_B))))
% 0.67/0.83         <= (((r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 0.67/0.83               (k4_lattice3 @ sk_B @ sk_C))))),
% 0.67/0.83      inference('clc', [status(thm)], ['102', '103'])).
% 0.67/0.83  thf('105', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         ((r3_lattice3 @ sk_B @ sk_C @ X0)
% 0.67/0.83          | (m1_subset_1 @ (sk_D @ X0 @ sk_C @ sk_B) @ 
% 0.67/0.83             (u1_struct_0 @ (k3_lattice3 @ sk_B))))),
% 0.67/0.83      inference('simplify', [status(thm)], ['86'])).
% 0.67/0.83  thf('106', plain,
% 0.67/0.83      (![X20 : $i]:
% 0.67/0.83         ((l1_orders_2 @ (k3_lattice3 @ X20))
% 0.67/0.83          | ~ (l3_lattices @ X20)
% 0.67/0.83          | ~ (v10_lattices @ X20)
% 0.67/0.83          | (v2_struct_0 @ X20))),
% 0.67/0.83      inference('cnf', [status(esa)], [dt_k3_lattice3])).
% 0.67/0.83  thf('107', plain,
% 0.67/0.83      (![X20 : $i]:
% 0.67/0.83         ((v3_orders_2 @ (k3_lattice3 @ X20))
% 0.67/0.83          | ~ (l3_lattices @ X20)
% 0.67/0.83          | ~ (v10_lattices @ X20)
% 0.67/0.83          | (v2_struct_0 @ X20))),
% 0.67/0.83      inference('cnf', [status(esa)], [dt_k3_lattice3])).
% 0.67/0.83  thf('108', plain,
% 0.67/0.83      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))),
% 0.67/0.83      inference('clc', [status(thm)], ['15', '16'])).
% 0.67/0.83  thf(redefinition_r3_orders_2, axiom,
% 0.67/0.83    (![A:$i,B:$i,C:$i]:
% 0.67/0.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.67/0.83         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.67/0.83         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.83       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.67/0.83  thf('109', plain,
% 0.67/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.83         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.67/0.83          | ~ (l1_orders_2 @ X1)
% 0.67/0.83          | ~ (v3_orders_2 @ X1)
% 0.67/0.83          | (v2_struct_0 @ X1)
% 0.67/0.83          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.67/0.83          | (r3_orders_2 @ X1 @ X0 @ X2)
% 0.67/0.83          | ~ (r1_orders_2 @ X1 @ X0 @ X2))),
% 0.67/0.83      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.67/0.83  thf('110', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         (~ (r1_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ X0)
% 0.67/0.83          | (r3_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ X0)
% 0.67/0.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 0.67/0.83          | (v2_struct_0 @ (k3_lattice3 @ sk_B))
% 0.67/0.83          | ~ (v3_orders_2 @ (k3_lattice3 @ sk_B))
% 0.67/0.83          | ~ (l1_orders_2 @ (k3_lattice3 @ sk_B)))),
% 0.67/0.83      inference('sup-', [status(thm)], ['108', '109'])).
% 0.67/0.83  thf('111', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         ((v2_struct_0 @ sk_B)
% 0.67/0.83          | ~ (v10_lattices @ sk_B)
% 0.67/0.83          | ~ (l3_lattices @ sk_B)
% 0.67/0.83          | ~ (l1_orders_2 @ (k3_lattice3 @ sk_B))
% 0.67/0.83          | (v2_struct_0 @ (k3_lattice3 @ sk_B))
% 0.67/0.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 0.67/0.83          | (r3_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ X0)
% 0.67/0.83          | ~ (r1_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ X0))),
% 0.67/0.83      inference('sup-', [status(thm)], ['107', '110'])).
% 0.67/0.83  thf('112', plain, ((v10_lattices @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('113', plain, ((l3_lattices @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('114', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         ((v2_struct_0 @ sk_B)
% 0.67/0.83          | ~ (l1_orders_2 @ (k3_lattice3 @ sk_B))
% 0.67/0.83          | (v2_struct_0 @ (k3_lattice3 @ sk_B))
% 0.67/0.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 0.67/0.83          | (r3_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ X0)
% 0.67/0.83          | ~ (r1_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ X0))),
% 0.67/0.83      inference('demod', [status(thm)], ['111', '112', '113'])).
% 0.67/0.83  thf('115', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         ((v2_struct_0 @ sk_B)
% 0.67/0.83          | ~ (v10_lattices @ sk_B)
% 0.67/0.83          | ~ (l3_lattices @ sk_B)
% 0.67/0.83          | ~ (r1_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ X0)
% 0.67/0.83          | (r3_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ X0)
% 0.67/0.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 0.67/0.83          | (v2_struct_0 @ (k3_lattice3 @ sk_B))
% 0.67/0.83          | (v2_struct_0 @ sk_B))),
% 0.67/0.83      inference('sup-', [status(thm)], ['106', '114'])).
% 0.67/0.83  thf('116', plain, ((v10_lattices @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('117', plain, ((l3_lattices @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('118', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         ((v2_struct_0 @ sk_B)
% 0.67/0.83          | ~ (r1_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ X0)
% 0.67/0.83          | (r3_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ X0)
% 0.67/0.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 0.67/0.83          | (v2_struct_0 @ (k3_lattice3 @ sk_B))
% 0.67/0.83          | (v2_struct_0 @ sk_B))),
% 0.67/0.83      inference('demod', [status(thm)], ['115', '116', '117'])).
% 0.67/0.83  thf('119', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         ((v2_struct_0 @ (k3_lattice3 @ sk_B))
% 0.67/0.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 0.67/0.83          | (r3_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ X0)
% 0.67/0.83          | ~ (r1_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ X0)
% 0.67/0.83          | (v2_struct_0 @ sk_B))),
% 0.67/0.83      inference('simplify', [status(thm)], ['118'])).
% 0.67/0.83  thf('120', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         ((r3_lattice3 @ sk_B @ sk_C @ X0)
% 0.67/0.83          | (v2_struct_0 @ sk_B)
% 0.67/0.83          | ~ (r1_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ 
% 0.67/0.83               (sk_D @ X0 @ sk_C @ sk_B))
% 0.67/0.83          | (r3_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ 
% 0.67/0.83             (sk_D @ X0 @ sk_C @ sk_B))
% 0.67/0.83          | (v2_struct_0 @ (k3_lattice3 @ sk_B)))),
% 0.67/0.83      inference('sup-', [status(thm)], ['105', '119'])).
% 0.67/0.83  thf('121', plain,
% 0.67/0.83      ((((r3_lattice3 @ sk_B @ sk_C @ sk_A)
% 0.67/0.83         | (v2_struct_0 @ (k3_lattice3 @ sk_B))
% 0.67/0.83         | (r3_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ 
% 0.67/0.83            (sk_D @ sk_A @ sk_C @ sk_B))
% 0.67/0.83         | (v2_struct_0 @ sk_B)
% 0.67/0.83         | (r3_lattice3 @ sk_B @ sk_C @ sk_A)))
% 0.67/0.83         <= (((r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 0.67/0.83               (k4_lattice3 @ sk_B @ sk_C))))),
% 0.67/0.83      inference('sup-', [status(thm)], ['104', '120'])).
% 0.67/0.83  thf('122', plain,
% 0.67/0.83      ((((v2_struct_0 @ sk_B)
% 0.67/0.83         | (r3_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ 
% 0.67/0.83            (sk_D @ sk_A @ sk_C @ sk_B))
% 0.67/0.83         | (v2_struct_0 @ (k3_lattice3 @ sk_B))
% 0.67/0.83         | (r3_lattice3 @ sk_B @ sk_C @ sk_A)))
% 0.67/0.83         <= (((r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 0.67/0.83               (k4_lattice3 @ sk_B @ sk_C))))),
% 0.67/0.83      inference('simplify', [status(thm)], ['121'])).
% 0.67/0.83  thf('123', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         (((k4_lattice3 @ sk_B @ (sk_D @ X0 @ sk_C @ sk_B))
% 0.67/0.83            = (sk_D @ X0 @ sk_C @ sk_B))
% 0.67/0.83          | (r3_lattice3 @ sk_B @ sk_C @ X0))),
% 0.67/0.83      inference('clc', [status(thm)], ['75', '76'])).
% 0.67/0.83  thf('124', plain, (((k4_lattice3 @ sk_B @ sk_C) = (sk_C))),
% 0.67/0.83      inference('clc', [status(thm)], ['10', '11'])).
% 0.67/0.83  thf(t7_lattice3, axiom,
% 0.67/0.83    (![A:$i]:
% 0.67/0.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.67/0.83       ( ![B:$i]:
% 0.67/0.83         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.67/0.83           ( ![C:$i]:
% 0.67/0.83             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.67/0.83               ( ( r3_lattices @ A @ B @ C ) <=>
% 0.67/0.83                 ( r3_orders_2 @
% 0.67/0.83                   ( k3_lattice3 @ A ) @ ( k4_lattice3 @ A @ B ) @ 
% 0.67/0.83                   ( k4_lattice3 @ A @ C ) ) ) ) ) ) ) ))).
% 0.67/0.83  thf('125', plain,
% 0.67/0.83      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.67/0.83         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 0.67/0.83          | ~ (r3_orders_2 @ (k3_lattice3 @ X27) @ (k4_lattice3 @ X27 @ X26) @ 
% 0.67/0.83               (k4_lattice3 @ X27 @ X28))
% 0.67/0.83          | (r3_lattices @ X27 @ X26 @ X28)
% 0.67/0.83          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X27))
% 0.67/0.83          | ~ (l3_lattices @ X27)
% 0.67/0.83          | ~ (v10_lattices @ X27)
% 0.67/0.83          | (v2_struct_0 @ X27))),
% 0.67/0.83      inference('cnf', [status(esa)], [t7_lattice3])).
% 0.67/0.83  thf('126', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         (~ (r3_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ 
% 0.67/0.83             (k4_lattice3 @ sk_B @ X0))
% 0.67/0.83          | (v2_struct_0 @ sk_B)
% 0.67/0.83          | ~ (v10_lattices @ sk_B)
% 0.67/0.83          | ~ (l3_lattices @ sk_B)
% 0.67/0.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.67/0.83          | (r3_lattices @ sk_B @ sk_C @ X0)
% 0.67/0.83          | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_B)))),
% 0.67/0.83      inference('sup-', [status(thm)], ['124', '125'])).
% 0.67/0.83  thf('127', plain, ((v10_lattices @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('128', plain, ((l3_lattices @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('129', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_B))),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('130', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         (~ (r3_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ 
% 0.67/0.83             (k4_lattice3 @ sk_B @ X0))
% 0.67/0.83          | (v2_struct_0 @ sk_B)
% 0.67/0.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.67/0.83          | (r3_lattices @ sk_B @ sk_C @ X0))),
% 0.67/0.83      inference('demod', [status(thm)], ['126', '127', '128', '129'])).
% 0.67/0.83  thf('131', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         (~ (r3_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ 
% 0.67/0.83             (sk_D @ X0 @ sk_C @ sk_B))
% 0.67/0.83          | (r3_lattice3 @ sk_B @ sk_C @ X0)
% 0.67/0.83          | (r3_lattices @ sk_B @ sk_C @ (sk_D @ X0 @ sk_C @ sk_B))
% 0.67/0.83          | ~ (m1_subset_1 @ (sk_D @ X0 @ sk_C @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.67/0.83          | (v2_struct_0 @ sk_B))),
% 0.67/0.83      inference('sup-', [status(thm)], ['123', '130'])).
% 0.67/0.83  thf('132', plain,
% 0.67/0.83      ((((r3_lattice3 @ sk_B @ sk_C @ sk_A)
% 0.67/0.83         | (v2_struct_0 @ (k3_lattice3 @ sk_B))
% 0.67/0.83         | (v2_struct_0 @ sk_B)
% 0.67/0.83         | (v2_struct_0 @ sk_B)
% 0.67/0.83         | ~ (m1_subset_1 @ (sk_D @ sk_A @ sk_C @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.67/0.83         | (r3_lattices @ sk_B @ sk_C @ (sk_D @ sk_A @ sk_C @ sk_B))
% 0.67/0.83         | (r3_lattice3 @ sk_B @ sk_C @ sk_A)))
% 0.67/0.83         <= (((r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 0.67/0.83               (k4_lattice3 @ sk_B @ sk_C))))),
% 0.67/0.83      inference('sup-', [status(thm)], ['122', '131'])).
% 0.67/0.83  thf('133', plain,
% 0.67/0.83      ((((r3_lattices @ sk_B @ sk_C @ (sk_D @ sk_A @ sk_C @ sk_B))
% 0.67/0.83         | ~ (m1_subset_1 @ (sk_D @ sk_A @ sk_C @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.67/0.83         | (v2_struct_0 @ sk_B)
% 0.67/0.83         | (v2_struct_0 @ (k3_lattice3 @ sk_B))
% 0.67/0.83         | (r3_lattice3 @ sk_B @ sk_C @ sk_A)))
% 0.67/0.83         <= (((r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 0.67/0.83               (k4_lattice3 @ sk_B @ sk_C))))),
% 0.67/0.83      inference('simplify', [status(thm)], ['132'])).
% 0.67/0.83  thf('134', plain,
% 0.67/0.83      ((((r3_lattice3 @ sk_B @ sk_C @ sk_A)
% 0.67/0.83         | (r3_lattice3 @ sk_B @ sk_C @ sk_A)
% 0.67/0.83         | (v2_struct_0 @ (k3_lattice3 @ sk_B))
% 0.67/0.83         | (v2_struct_0 @ sk_B)
% 0.67/0.83         | (r3_lattices @ sk_B @ sk_C @ (sk_D @ sk_A @ sk_C @ sk_B))))
% 0.67/0.83         <= (((r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 0.67/0.83               (k4_lattice3 @ sk_B @ sk_C))))),
% 0.67/0.83      inference('sup-', [status(thm)], ['62', '133'])).
% 0.67/0.83  thf('135', plain,
% 0.67/0.83      ((((r3_lattices @ sk_B @ sk_C @ (sk_D @ sk_A @ sk_C @ sk_B))
% 0.67/0.83         | (v2_struct_0 @ sk_B)
% 0.67/0.83         | (v2_struct_0 @ (k3_lattice3 @ sk_B))
% 0.67/0.83         | (r3_lattice3 @ sk_B @ sk_C @ sk_A)))
% 0.67/0.83         <= (((r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 0.67/0.83               (k4_lattice3 @ sk_B @ sk_C))))),
% 0.67/0.83      inference('simplify', [status(thm)], ['134'])).
% 0.67/0.83  thf('136', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_B))),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf(redefinition_r3_lattices, axiom,
% 0.67/0.83    (![A:$i,B:$i,C:$i]:
% 0.67/0.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.67/0.83         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 0.67/0.83         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.67/0.83         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.83       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 0.67/0.83  thf('137', plain,
% 0.67/0.83      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.67/0.83         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.67/0.83          | ~ (l3_lattices @ X5)
% 0.67/0.83          | ~ (v9_lattices @ X5)
% 0.67/0.83          | ~ (v8_lattices @ X5)
% 0.67/0.83          | ~ (v6_lattices @ X5)
% 0.67/0.83          | (v2_struct_0 @ X5)
% 0.67/0.83          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.67/0.83          | (r1_lattices @ X5 @ X4 @ X6)
% 0.67/0.83          | ~ (r3_lattices @ X5 @ X4 @ X6))),
% 0.67/0.83      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.67/0.83  thf('138', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         (~ (r3_lattices @ sk_B @ sk_C @ X0)
% 0.67/0.83          | (r1_lattices @ sk_B @ sk_C @ X0)
% 0.67/0.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.67/0.83          | (v2_struct_0 @ sk_B)
% 0.67/0.83          | ~ (v6_lattices @ sk_B)
% 0.67/0.83          | ~ (v8_lattices @ sk_B)
% 0.67/0.83          | ~ (v9_lattices @ sk_B)
% 0.67/0.83          | ~ (l3_lattices @ sk_B))),
% 0.67/0.83      inference('sup-', [status(thm)], ['136', '137'])).
% 0.67/0.83  thf(cc1_lattices, axiom,
% 0.67/0.83    (![A:$i]:
% 0.67/0.83     ( ( l3_lattices @ A ) =>
% 0.67/0.83       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.67/0.83         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.67/0.83           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.67/0.83           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.67/0.83  thf('139', plain,
% 0.67/0.83      (![X3 : $i]:
% 0.67/0.83         ((v2_struct_0 @ X3)
% 0.67/0.83          | ~ (v10_lattices @ X3)
% 0.67/0.83          | (v6_lattices @ X3)
% 0.67/0.83          | ~ (l3_lattices @ X3))),
% 0.67/0.83      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.67/0.83  thf('140', plain, (~ (v2_struct_0 @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('141', plain,
% 0.67/0.83      ((~ (l3_lattices @ sk_B) | (v6_lattices @ sk_B) | ~ (v10_lattices @ sk_B))),
% 0.67/0.83      inference('sup-', [status(thm)], ['139', '140'])).
% 0.67/0.83  thf('142', plain, ((l3_lattices @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('143', plain, ((v10_lattices @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('144', plain, ((v6_lattices @ sk_B)),
% 0.67/0.83      inference('demod', [status(thm)], ['141', '142', '143'])).
% 0.67/0.83  thf('145', plain,
% 0.67/0.83      (![X3 : $i]:
% 0.67/0.83         ((v2_struct_0 @ X3)
% 0.67/0.83          | ~ (v10_lattices @ X3)
% 0.67/0.83          | (v8_lattices @ X3)
% 0.67/0.83          | ~ (l3_lattices @ X3))),
% 0.67/0.83      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.67/0.83  thf('146', plain, (~ (v2_struct_0 @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('147', plain,
% 0.67/0.83      ((~ (l3_lattices @ sk_B) | (v8_lattices @ sk_B) | ~ (v10_lattices @ sk_B))),
% 0.67/0.83      inference('sup-', [status(thm)], ['145', '146'])).
% 0.67/0.83  thf('148', plain, ((l3_lattices @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('149', plain, ((v10_lattices @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('150', plain, ((v8_lattices @ sk_B)),
% 0.67/0.83      inference('demod', [status(thm)], ['147', '148', '149'])).
% 0.67/0.83  thf('151', plain,
% 0.67/0.83      (![X3 : $i]:
% 0.67/0.83         ((v2_struct_0 @ X3)
% 0.67/0.83          | ~ (v10_lattices @ X3)
% 0.67/0.83          | (v9_lattices @ X3)
% 0.67/0.83          | ~ (l3_lattices @ X3))),
% 0.67/0.83      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.67/0.83  thf('152', plain, (~ (v2_struct_0 @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('153', plain,
% 0.67/0.83      ((~ (l3_lattices @ sk_B) | (v9_lattices @ sk_B) | ~ (v10_lattices @ sk_B))),
% 0.67/0.83      inference('sup-', [status(thm)], ['151', '152'])).
% 0.67/0.83  thf('154', plain, ((l3_lattices @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('155', plain, ((v10_lattices @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('156', plain, ((v9_lattices @ sk_B)),
% 0.67/0.83      inference('demod', [status(thm)], ['153', '154', '155'])).
% 0.67/0.83  thf('157', plain, ((l3_lattices @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('158', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         (~ (r3_lattices @ sk_B @ sk_C @ X0)
% 0.67/0.83          | (r1_lattices @ sk_B @ sk_C @ X0)
% 0.67/0.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.67/0.83          | (v2_struct_0 @ sk_B))),
% 0.67/0.83      inference('demod', [status(thm)], ['138', '144', '150', '156', '157'])).
% 0.67/0.83  thf('159', plain,
% 0.67/0.83      ((((r3_lattice3 @ sk_B @ sk_C @ sk_A)
% 0.67/0.83         | (v2_struct_0 @ (k3_lattice3 @ sk_B))
% 0.67/0.83         | (v2_struct_0 @ sk_B)
% 0.67/0.83         | (v2_struct_0 @ sk_B)
% 0.67/0.83         | ~ (m1_subset_1 @ (sk_D @ sk_A @ sk_C @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.67/0.83         | (r1_lattices @ sk_B @ sk_C @ (sk_D @ sk_A @ sk_C @ sk_B))))
% 0.67/0.83         <= (((r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 0.67/0.83               (k4_lattice3 @ sk_B @ sk_C))))),
% 0.67/0.83      inference('sup-', [status(thm)], ['135', '158'])).
% 0.67/0.83  thf('160', plain,
% 0.67/0.83      ((((r1_lattices @ sk_B @ sk_C @ (sk_D @ sk_A @ sk_C @ sk_B))
% 0.67/0.83         | ~ (m1_subset_1 @ (sk_D @ sk_A @ sk_C @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.67/0.83         | (v2_struct_0 @ sk_B)
% 0.67/0.83         | (v2_struct_0 @ (k3_lattice3 @ sk_B))
% 0.67/0.83         | (r3_lattice3 @ sk_B @ sk_C @ sk_A)))
% 0.67/0.83         <= (((r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 0.67/0.83               (k4_lattice3 @ sk_B @ sk_C))))),
% 0.67/0.83      inference('simplify', [status(thm)], ['159'])).
% 0.67/0.83  thf('161', plain,
% 0.67/0.83      ((((r3_lattice3 @ sk_B @ sk_C @ sk_A)
% 0.67/0.83         | (r3_lattice3 @ sk_B @ sk_C @ sk_A)
% 0.67/0.83         | (v2_struct_0 @ (k3_lattice3 @ sk_B))
% 0.67/0.83         | (v2_struct_0 @ sk_B)
% 0.67/0.83         | (r1_lattices @ sk_B @ sk_C @ (sk_D @ sk_A @ sk_C @ sk_B))))
% 0.67/0.83         <= (((r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 0.67/0.83               (k4_lattice3 @ sk_B @ sk_C))))),
% 0.67/0.83      inference('sup-', [status(thm)], ['61', '160'])).
% 0.67/0.83  thf('162', plain,
% 0.67/0.83      ((((r1_lattices @ sk_B @ sk_C @ (sk_D @ sk_A @ sk_C @ sk_B))
% 0.67/0.83         | (v2_struct_0 @ sk_B)
% 0.67/0.83         | (v2_struct_0 @ (k3_lattice3 @ sk_B))
% 0.67/0.83         | (r3_lattice3 @ sk_B @ sk_C @ sk_A)))
% 0.67/0.83         <= (((r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 0.67/0.83               (k4_lattice3 @ sk_B @ sk_C))))),
% 0.67/0.83      inference('simplify', [status(thm)], ['161'])).
% 0.67/0.83  thf('163', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_B))),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('164', plain,
% 0.67/0.83      (![X7 : $i, X8 : $i, X11 : $i]:
% 0.67/0.83         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.67/0.83          | ~ (r1_lattices @ X8 @ X7 @ (sk_D @ X11 @ X7 @ X8))
% 0.67/0.83          | (r3_lattice3 @ X8 @ X7 @ X11)
% 0.67/0.83          | ~ (l3_lattices @ X8)
% 0.67/0.83          | (v2_struct_0 @ X8))),
% 0.67/0.83      inference('cnf', [status(esa)], [d16_lattice3])).
% 0.67/0.83  thf('165', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         ((v2_struct_0 @ sk_B)
% 0.67/0.83          | ~ (l3_lattices @ sk_B)
% 0.67/0.83          | (r3_lattice3 @ sk_B @ sk_C @ X0)
% 0.67/0.83          | ~ (r1_lattices @ sk_B @ sk_C @ (sk_D @ X0 @ sk_C @ sk_B)))),
% 0.67/0.83      inference('sup-', [status(thm)], ['163', '164'])).
% 0.67/0.83  thf('166', plain, ((l3_lattices @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('167', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         ((v2_struct_0 @ sk_B)
% 0.67/0.83          | (r3_lattice3 @ sk_B @ sk_C @ X0)
% 0.67/0.83          | ~ (r1_lattices @ sk_B @ sk_C @ (sk_D @ X0 @ sk_C @ sk_B)))),
% 0.67/0.83      inference('demod', [status(thm)], ['165', '166'])).
% 0.67/0.83  thf('168', plain, (~ (v2_struct_0 @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('169', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         (~ (r1_lattices @ sk_B @ sk_C @ (sk_D @ X0 @ sk_C @ sk_B))
% 0.67/0.83          | (r3_lattice3 @ sk_B @ sk_C @ X0))),
% 0.67/0.83      inference('clc', [status(thm)], ['167', '168'])).
% 0.67/0.83  thf('170', plain,
% 0.67/0.83      ((((r3_lattice3 @ sk_B @ sk_C @ sk_A)
% 0.67/0.83         | (v2_struct_0 @ (k3_lattice3 @ sk_B))
% 0.67/0.83         | (v2_struct_0 @ sk_B)
% 0.67/0.83         | (r3_lattice3 @ sk_B @ sk_C @ sk_A)))
% 0.67/0.83         <= (((r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 0.67/0.83               (k4_lattice3 @ sk_B @ sk_C))))),
% 0.67/0.83      inference('sup-', [status(thm)], ['162', '169'])).
% 0.67/0.83  thf('171', plain,
% 0.67/0.83      ((((v2_struct_0 @ sk_B)
% 0.67/0.83         | (v2_struct_0 @ (k3_lattice3 @ sk_B))
% 0.67/0.83         | (r3_lattice3 @ sk_B @ sk_C @ sk_A)))
% 0.67/0.83         <= (((r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 0.67/0.83               (k4_lattice3 @ sk_B @ sk_C))))),
% 0.67/0.83      inference('simplify', [status(thm)], ['170'])).
% 0.67/0.83  thf('172', plain, (~ (v2_struct_0 @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('173', plain,
% 0.67/0.83      ((((r3_lattice3 @ sk_B @ sk_C @ sk_A)
% 0.67/0.83         | (v2_struct_0 @ (k3_lattice3 @ sk_B))))
% 0.67/0.83         <= (((r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 0.67/0.83               (k4_lattice3 @ sk_B @ sk_C))))),
% 0.67/0.83      inference('clc', [status(thm)], ['171', '172'])).
% 0.67/0.83  thf('174', plain,
% 0.67/0.83      ((~ (r3_lattice3 @ sk_B @ sk_C @ sk_A))
% 0.67/0.83         <= (~ ((r3_lattice3 @ sk_B @ sk_C @ sk_A)))),
% 0.67/0.83      inference('split', [status(esa)], ['53'])).
% 0.67/0.83  thf('175', plain,
% 0.67/0.83      (((v2_struct_0 @ (k3_lattice3 @ sk_B)))
% 0.67/0.83         <= (~ ((r3_lattice3 @ sk_B @ sk_C @ sk_A)) & 
% 0.67/0.83             ((r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 0.67/0.83               (k4_lattice3 @ sk_B @ sk_C))))),
% 0.67/0.83      inference('sup-', [status(thm)], ['173', '174'])).
% 0.67/0.83  thf(fc4_lattice3, axiom,
% 0.67/0.83    (![A:$i]:
% 0.67/0.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.67/0.83       ( ( ~( v2_struct_0 @ ( k3_lattice3 @ A ) ) ) & 
% 0.67/0.83         ( v1_orders_2 @ ( k3_lattice3 @ A ) ) & 
% 0.67/0.83         ( v3_orders_2 @ ( k3_lattice3 @ A ) ) & 
% 0.67/0.83         ( v4_orders_2 @ ( k3_lattice3 @ A ) ) & 
% 0.67/0.83         ( v5_orders_2 @ ( k3_lattice3 @ A ) ) ) ))).
% 0.67/0.83  thf('176', plain,
% 0.67/0.83      (![X25 : $i]:
% 0.67/0.83         (~ (v2_struct_0 @ (k3_lattice3 @ X25))
% 0.67/0.83          | ~ (l3_lattices @ X25)
% 0.67/0.83          | ~ (v10_lattices @ X25)
% 0.67/0.83          | (v2_struct_0 @ X25))),
% 0.67/0.83      inference('cnf', [status(esa)], [fc4_lattice3])).
% 0.67/0.83  thf('177', plain,
% 0.67/0.83      ((((v2_struct_0 @ sk_B)
% 0.67/0.83         | ~ (v10_lattices @ sk_B)
% 0.67/0.83         | ~ (l3_lattices @ sk_B)))
% 0.67/0.83         <= (~ ((r3_lattice3 @ sk_B @ sk_C @ sk_A)) & 
% 0.67/0.83             ((r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 0.67/0.83               (k4_lattice3 @ sk_B @ sk_C))))),
% 0.67/0.83      inference('sup-', [status(thm)], ['175', '176'])).
% 0.67/0.83  thf('178', plain, ((v10_lattices @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('179', plain, ((l3_lattices @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('180', plain,
% 0.67/0.83      (((v2_struct_0 @ sk_B))
% 0.67/0.83         <= (~ ((r3_lattice3 @ sk_B @ sk_C @ sk_A)) & 
% 0.67/0.83             ((r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 0.67/0.83               (k4_lattice3 @ sk_B @ sk_C))))),
% 0.67/0.83      inference('demod', [status(thm)], ['177', '178', '179'])).
% 0.67/0.83  thf('181', plain, (~ (v2_struct_0 @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('182', plain,
% 0.67/0.83      (((r3_lattice3 @ sk_B @ sk_C @ sk_A)) | 
% 0.67/0.83       ~
% 0.67/0.83       ((r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 0.67/0.83         (k4_lattice3 @ sk_B @ sk_C)))),
% 0.67/0.83      inference('sup-', [status(thm)], ['180', '181'])).
% 0.67/0.83  thf('183', plain,
% 0.67/0.83      (((r3_lattice3 @ sk_B @ sk_C @ sk_A)) | 
% 0.67/0.83       ((r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 0.67/0.83         (k4_lattice3 @ sk_B @ sk_C)))),
% 0.67/0.83      inference('split', [status(esa)], ['51'])).
% 0.67/0.83  thf('184', plain, (((r3_lattice3 @ sk_B @ sk_C @ sk_A))),
% 0.67/0.83      inference('sat_resolution*', [status(thm)], ['54', '182', '183'])).
% 0.67/0.83  thf('185', plain, ((r3_lattice3 @ sk_B @ sk_C @ sk_A)),
% 0.67/0.83      inference('simpl_trail', [status(thm)], ['52', '184'])).
% 0.67/0.83  thf('186', plain,
% 0.67/0.83      (![X20 : $i]:
% 0.67/0.83         ((l1_orders_2 @ (k3_lattice3 @ X20))
% 0.67/0.83          | ~ (l3_lattices @ X20)
% 0.67/0.83          | ~ (v10_lattices @ X20)
% 0.67/0.83          | (v2_struct_0 @ X20))),
% 0.67/0.83      inference('cnf', [status(esa)], [dt_k3_lattice3])).
% 0.67/0.83  thf('187', plain,
% 0.67/0.83      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))),
% 0.67/0.83      inference('clc', [status(thm)], ['15', '16'])).
% 0.67/0.83  thf('188', plain,
% 0.67/0.83      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.67/0.83         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.67/0.83          | (r2_hidden @ (sk_D_1 @ X16 @ X18 @ X17) @ X18)
% 0.67/0.83          | (r1_lattice3 @ X17 @ X18 @ X16)
% 0.67/0.83          | ~ (l1_orders_2 @ X17))),
% 0.67/0.83      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.67/0.83  thf('189', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         (~ (l1_orders_2 @ (k3_lattice3 @ sk_B))
% 0.67/0.83          | (r1_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 0.67/0.83          | (r2_hidden @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ X0))),
% 0.67/0.83      inference('sup-', [status(thm)], ['187', '188'])).
% 0.67/0.83  thf('190', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         ((v2_struct_0 @ sk_B)
% 0.67/0.83          | ~ (v10_lattices @ sk_B)
% 0.67/0.83          | ~ (l3_lattices @ sk_B)
% 0.67/0.83          | (r2_hidden @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ X0)
% 0.67/0.83          | (r1_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C))),
% 0.67/0.83      inference('sup-', [status(thm)], ['186', '189'])).
% 0.67/0.83  thf('191', plain, ((v10_lattices @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('192', plain, ((l3_lattices @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('193', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         ((v2_struct_0 @ sk_B)
% 0.67/0.83          | (r2_hidden @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ X0)
% 0.67/0.83          | (r1_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C))),
% 0.67/0.83      inference('demod', [status(thm)], ['190', '191', '192'])).
% 0.67/0.83  thf('194', plain, (~ (v2_struct_0 @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('195', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         ((r1_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 0.67/0.83          | (r2_hidden @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ X0))),
% 0.67/0.83      inference('clc', [status(thm)], ['193', '194'])).
% 0.67/0.83  thf('196', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         ((r1_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 0.67/0.83          | (m1_subset_1 @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ 
% 0.67/0.83             (u1_struct_0 @ sk_B)))),
% 0.67/0.83      inference('simplify', [status(thm)], ['41'])).
% 0.67/0.83  thf('197', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_B))),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('198', plain,
% 0.67/0.83      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.67/0.83         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.67/0.83          | ~ (r3_lattice3 @ X8 @ X7 @ X9)
% 0.67/0.83          | ~ (r2_hidden @ X10 @ X9)
% 0.67/0.83          | (r1_lattices @ X8 @ X7 @ X10)
% 0.67/0.83          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X8))
% 0.67/0.83          | ~ (l3_lattices @ X8)
% 0.67/0.83          | (v2_struct_0 @ X8))),
% 0.67/0.83      inference('cnf', [status(esa)], [d16_lattice3])).
% 0.67/0.83  thf('199', plain,
% 0.67/0.83      (![X0 : $i, X1 : $i]:
% 0.67/0.83         ((v2_struct_0 @ sk_B)
% 0.67/0.83          | ~ (l3_lattices @ sk_B)
% 0.67/0.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.67/0.83          | (r1_lattices @ sk_B @ sk_C @ X0)
% 0.67/0.83          | ~ (r2_hidden @ X0 @ X1)
% 0.67/0.83          | ~ (r3_lattice3 @ sk_B @ sk_C @ X1))),
% 0.67/0.83      inference('sup-', [status(thm)], ['197', '198'])).
% 0.67/0.83  thf('200', plain, ((l3_lattices @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('201', plain,
% 0.67/0.83      (![X0 : $i, X1 : $i]:
% 0.67/0.83         ((v2_struct_0 @ sk_B)
% 0.67/0.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.67/0.83          | (r1_lattices @ sk_B @ sk_C @ X0)
% 0.67/0.83          | ~ (r2_hidden @ X0 @ X1)
% 0.67/0.83          | ~ (r3_lattice3 @ sk_B @ sk_C @ X1))),
% 0.67/0.83      inference('demod', [status(thm)], ['199', '200'])).
% 0.67/0.83  thf('202', plain,
% 0.67/0.83      (![X0 : $i, X1 : $i]:
% 0.67/0.83         ((r1_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 0.67/0.83          | ~ (r3_lattice3 @ sk_B @ sk_C @ X1)
% 0.67/0.83          | ~ (r2_hidden @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ X1)
% 0.67/0.83          | (r1_lattices @ sk_B @ sk_C @ 
% 0.67/0.83             (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)))
% 0.67/0.83          | (v2_struct_0 @ sk_B))),
% 0.67/0.83      inference('sup-', [status(thm)], ['196', '201'])).
% 0.67/0.83  thf('203', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         ((r1_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 0.67/0.83          | (v2_struct_0 @ sk_B)
% 0.67/0.83          | (r1_lattices @ sk_B @ sk_C @ 
% 0.67/0.83             (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)))
% 0.67/0.83          | ~ (r3_lattice3 @ sk_B @ sk_C @ X0)
% 0.67/0.83          | (r1_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C))),
% 0.67/0.83      inference('sup-', [status(thm)], ['195', '202'])).
% 0.67/0.83  thf('204', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         (~ (r3_lattice3 @ sk_B @ sk_C @ X0)
% 0.67/0.83          | (r1_lattices @ sk_B @ sk_C @ 
% 0.67/0.83             (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)))
% 0.67/0.83          | (v2_struct_0 @ sk_B)
% 0.67/0.83          | (r1_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C))),
% 0.67/0.83      inference('simplify', [status(thm)], ['203'])).
% 0.67/0.83  thf('205', plain,
% 0.67/0.83      (((r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ sk_C)
% 0.67/0.83        | (v2_struct_0 @ sk_B)
% 0.67/0.83        | (r1_lattices @ sk_B @ sk_C @ 
% 0.67/0.83           (sk_D_1 @ sk_C @ sk_A @ (k3_lattice3 @ sk_B))))),
% 0.67/0.83      inference('sup-', [status(thm)], ['185', '204'])).
% 0.67/0.83  thf('206', plain,
% 0.67/0.83      ((~ (r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 0.67/0.83           (k4_lattice3 @ sk_B @ sk_C)))
% 0.67/0.83         <= (~
% 0.67/0.83             ((r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 0.67/0.83               (k4_lattice3 @ sk_B @ sk_C))))),
% 0.67/0.83      inference('split', [status(esa)], ['53'])).
% 0.67/0.83  thf('207', plain, (((k4_lattice3 @ sk_B @ sk_C) = (sk_C))),
% 0.67/0.83      inference('clc', [status(thm)], ['10', '11'])).
% 0.67/0.83  thf('208', plain,
% 0.67/0.83      ((~ (r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ sk_C))
% 0.67/0.83         <= (~
% 0.67/0.83             ((r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 0.67/0.83               (k4_lattice3 @ sk_B @ sk_C))))),
% 0.67/0.83      inference('demod', [status(thm)], ['206', '207'])).
% 0.67/0.83  thf('209', plain,
% 0.67/0.83      (~
% 0.67/0.83       ((r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ 
% 0.67/0.83         (k4_lattice3 @ sk_B @ sk_C)))),
% 0.67/0.83      inference('sat_resolution*', [status(thm)], ['54', '182'])).
% 0.67/0.83  thf('210', plain, (~ (r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ sk_C)),
% 0.67/0.83      inference('simpl_trail', [status(thm)], ['208', '209'])).
% 0.67/0.83  thf('211', plain,
% 0.67/0.83      (((r1_lattices @ sk_B @ sk_C @ 
% 0.67/0.83         (sk_D_1 @ sk_C @ sk_A @ (k3_lattice3 @ sk_B)))
% 0.67/0.83        | (v2_struct_0 @ sk_B))),
% 0.67/0.83      inference('clc', [status(thm)], ['205', '210'])).
% 0.67/0.83  thf('212', plain, (~ (v2_struct_0 @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('213', plain,
% 0.67/0.83      ((r1_lattices @ sk_B @ sk_C @ 
% 0.67/0.83        (sk_D_1 @ sk_C @ sk_A @ (k3_lattice3 @ sk_B)))),
% 0.67/0.83      inference('clc', [status(thm)], ['211', '212'])).
% 0.67/0.83  thf('214', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_B))),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('215', plain,
% 0.67/0.83      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.67/0.83         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.67/0.83          | ~ (l3_lattices @ X5)
% 0.67/0.83          | ~ (v9_lattices @ X5)
% 0.67/0.83          | ~ (v8_lattices @ X5)
% 0.67/0.83          | ~ (v6_lattices @ X5)
% 0.67/0.83          | (v2_struct_0 @ X5)
% 0.67/0.83          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.67/0.83          | (r3_lattices @ X5 @ X4 @ X6)
% 0.67/0.83          | ~ (r1_lattices @ X5 @ X4 @ X6))),
% 0.67/0.83      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.67/0.83  thf('216', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         (~ (r1_lattices @ sk_B @ sk_C @ X0)
% 0.67/0.83          | (r3_lattices @ sk_B @ sk_C @ X0)
% 0.67/0.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.67/0.83          | (v2_struct_0 @ sk_B)
% 0.67/0.83          | ~ (v6_lattices @ sk_B)
% 0.67/0.83          | ~ (v8_lattices @ sk_B)
% 0.67/0.83          | ~ (v9_lattices @ sk_B)
% 0.67/0.83          | ~ (l3_lattices @ sk_B))),
% 0.67/0.83      inference('sup-', [status(thm)], ['214', '215'])).
% 0.67/0.83  thf('217', plain, ((v6_lattices @ sk_B)),
% 0.67/0.83      inference('demod', [status(thm)], ['141', '142', '143'])).
% 0.67/0.83  thf('218', plain, ((v8_lattices @ sk_B)),
% 0.67/0.83      inference('demod', [status(thm)], ['147', '148', '149'])).
% 0.67/0.83  thf('219', plain, ((v9_lattices @ sk_B)),
% 0.67/0.83      inference('demod', [status(thm)], ['153', '154', '155'])).
% 0.67/0.83  thf('220', plain, ((l3_lattices @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('221', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         (~ (r1_lattices @ sk_B @ sk_C @ X0)
% 0.67/0.83          | (r3_lattices @ sk_B @ sk_C @ X0)
% 0.67/0.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.67/0.83          | (v2_struct_0 @ sk_B))),
% 0.67/0.83      inference('demod', [status(thm)], ['216', '217', '218', '219', '220'])).
% 0.67/0.83  thf('222', plain,
% 0.67/0.83      (((v2_struct_0 @ sk_B)
% 0.67/0.83        | ~ (m1_subset_1 @ (sk_D_1 @ sk_C @ sk_A @ (k3_lattice3 @ sk_B)) @ 
% 0.67/0.83             (u1_struct_0 @ sk_B))
% 0.67/0.83        | (r3_lattices @ sk_B @ sk_C @ 
% 0.67/0.83           (sk_D_1 @ sk_C @ sk_A @ (k3_lattice3 @ sk_B))))),
% 0.67/0.83      inference('sup-', [status(thm)], ['213', '221'])).
% 0.67/0.83  thf('223', plain, (~ (v2_struct_0 @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('224', plain,
% 0.67/0.83      (((r3_lattices @ sk_B @ sk_C @ 
% 0.67/0.83         (sk_D_1 @ sk_C @ sk_A @ (k3_lattice3 @ sk_B)))
% 0.67/0.83        | ~ (m1_subset_1 @ (sk_D_1 @ sk_C @ sk_A @ (k3_lattice3 @ sk_B)) @ 
% 0.67/0.83             (u1_struct_0 @ sk_B)))),
% 0.67/0.83      inference('clc', [status(thm)], ['222', '223'])).
% 0.67/0.83  thf('225', plain,
% 0.67/0.83      (((r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ sk_C)
% 0.67/0.83        | (r3_lattices @ sk_B @ sk_C @ 
% 0.67/0.83           (sk_D_1 @ sk_C @ sk_A @ (k3_lattice3 @ sk_B))))),
% 0.67/0.83      inference('sup-', [status(thm)], ['50', '224'])).
% 0.67/0.83  thf('226', plain, (~ (r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ sk_C)),
% 0.67/0.83      inference('simpl_trail', [status(thm)], ['208', '209'])).
% 0.67/0.83  thf('227', plain,
% 0.67/0.83      ((r3_lattices @ sk_B @ sk_C @ 
% 0.67/0.83        (sk_D_1 @ sk_C @ sk_A @ (k3_lattice3 @ sk_B)))),
% 0.67/0.83      inference('clc', [status(thm)], ['225', '226'])).
% 0.67/0.83  thf('228', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         ((r1_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 0.67/0.83          | (m1_subset_1 @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ 
% 0.67/0.83             (u1_struct_0 @ sk_B)))),
% 0.67/0.83      inference('simplify', [status(thm)], ['41'])).
% 0.67/0.83  thf('229', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_B))),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('230', plain,
% 0.67/0.83      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.67/0.83         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 0.67/0.83          | ~ (r3_lattices @ X27 @ X26 @ X28)
% 0.67/0.83          | (r3_orders_2 @ (k3_lattice3 @ X27) @ (k4_lattice3 @ X27 @ X26) @ 
% 0.67/0.83             (k4_lattice3 @ X27 @ X28))
% 0.67/0.83          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X27))
% 0.67/0.83          | ~ (l3_lattices @ X27)
% 0.67/0.83          | ~ (v10_lattices @ X27)
% 0.67/0.83          | (v2_struct_0 @ X27))),
% 0.67/0.83      inference('cnf', [status(esa)], [t7_lattice3])).
% 0.67/0.83  thf('231', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         ((v2_struct_0 @ sk_B)
% 0.67/0.83          | ~ (v10_lattices @ sk_B)
% 0.67/0.83          | ~ (l3_lattices @ sk_B)
% 0.67/0.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.67/0.83          | (r3_orders_2 @ (k3_lattice3 @ sk_B) @ 
% 0.67/0.83             (k4_lattice3 @ sk_B @ sk_C) @ (k4_lattice3 @ sk_B @ X0))
% 0.67/0.83          | ~ (r3_lattices @ sk_B @ sk_C @ X0))),
% 0.67/0.83      inference('sup-', [status(thm)], ['229', '230'])).
% 0.67/0.83  thf('232', plain, ((v10_lattices @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('233', plain, ((l3_lattices @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('234', plain, (((k4_lattice3 @ sk_B @ sk_C) = (sk_C))),
% 0.67/0.83      inference('clc', [status(thm)], ['10', '11'])).
% 0.67/0.83  thf('235', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         ((v2_struct_0 @ sk_B)
% 0.67/0.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.67/0.83          | (r3_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ 
% 0.67/0.83             (k4_lattice3 @ sk_B @ X0))
% 0.67/0.83          | ~ (r3_lattices @ sk_B @ sk_C @ X0))),
% 0.67/0.83      inference('demod', [status(thm)], ['231', '232', '233', '234'])).
% 0.67/0.83  thf('236', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         ((r1_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 0.67/0.83          | ~ (r3_lattices @ sk_B @ sk_C @ 
% 0.67/0.83               (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)))
% 0.67/0.83          | (r3_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ 
% 0.67/0.83             (k4_lattice3 @ sk_B @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B))))
% 0.67/0.83          | (v2_struct_0 @ sk_B))),
% 0.67/0.83      inference('sup-', [status(thm)], ['228', '235'])).
% 0.67/0.83  thf('237', plain,
% 0.67/0.83      (((v2_struct_0 @ sk_B)
% 0.67/0.83        | (r3_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ 
% 0.67/0.83           (k4_lattice3 @ sk_B @ (sk_D_1 @ sk_C @ sk_A @ (k3_lattice3 @ sk_B))))
% 0.67/0.83        | (r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ sk_C))),
% 0.67/0.83      inference('sup-', [status(thm)], ['227', '236'])).
% 0.67/0.83  thf('238', plain, (~ (v2_struct_0 @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('239', plain,
% 0.67/0.83      (((r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ sk_C)
% 0.67/0.83        | (r3_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ 
% 0.67/0.83           (k4_lattice3 @ sk_B @ (sk_D_1 @ sk_C @ sk_A @ (k3_lattice3 @ sk_B)))))),
% 0.67/0.83      inference('clc', [status(thm)], ['237', '238'])).
% 0.67/0.83  thf('240', plain, (~ (r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ sk_C)),
% 0.67/0.83      inference('simpl_trail', [status(thm)], ['208', '209'])).
% 0.67/0.83  thf('241', plain,
% 0.67/0.83      ((r3_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ 
% 0.67/0.83        (k4_lattice3 @ sk_B @ (sk_D_1 @ sk_C @ sk_A @ (k3_lattice3 @ sk_B))))),
% 0.67/0.83      inference('clc', [status(thm)], ['239', '240'])).
% 0.67/0.83  thf('242', plain,
% 0.67/0.83      (((r3_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ 
% 0.67/0.83         (sk_D_1 @ sk_C @ sk_A @ (k3_lattice3 @ sk_B)))
% 0.67/0.83        | (r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ sk_C))),
% 0.67/0.83      inference('sup+', [status(thm)], ['49', '241'])).
% 0.67/0.83  thf('243', plain, (~ (r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ sk_C)),
% 0.67/0.83      inference('simpl_trail', [status(thm)], ['208', '209'])).
% 0.67/0.83  thf('244', plain,
% 0.67/0.83      ((r3_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ 
% 0.67/0.83        (sk_D_1 @ sk_C @ sk_A @ (k3_lattice3 @ sk_B)))),
% 0.67/0.83      inference('clc', [status(thm)], ['242', '243'])).
% 0.67/0.83  thf('245', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         ((r1_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 0.67/0.83          | (m1_subset_1 @ (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)) @ 
% 0.67/0.83             (u1_struct_0 @ (k3_lattice3 @ sk_B))))),
% 0.67/0.83      inference('clc', [status(thm)], ['23', '24'])).
% 0.67/0.83  thf('246', plain,
% 0.67/0.83      (![X20 : $i]:
% 0.67/0.83         ((l1_orders_2 @ (k3_lattice3 @ X20))
% 0.67/0.83          | ~ (l3_lattices @ X20)
% 0.67/0.83          | ~ (v10_lattices @ X20)
% 0.67/0.83          | (v2_struct_0 @ X20))),
% 0.67/0.83      inference('cnf', [status(esa)], [dt_k3_lattice3])).
% 0.67/0.83  thf('247', plain,
% 0.67/0.83      (![X20 : $i]:
% 0.67/0.83         ((v3_orders_2 @ (k3_lattice3 @ X20))
% 0.67/0.83          | ~ (l3_lattices @ X20)
% 0.67/0.83          | ~ (v10_lattices @ X20)
% 0.67/0.83          | (v2_struct_0 @ X20))),
% 0.67/0.83      inference('cnf', [status(esa)], [dt_k3_lattice3])).
% 0.67/0.83  thf('248', plain,
% 0.67/0.83      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))),
% 0.67/0.83      inference('clc', [status(thm)], ['15', '16'])).
% 0.67/0.83  thf('249', plain,
% 0.67/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.83         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.67/0.83          | ~ (l1_orders_2 @ X1)
% 0.67/0.83          | ~ (v3_orders_2 @ X1)
% 0.67/0.83          | (v2_struct_0 @ X1)
% 0.67/0.83          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.67/0.83          | (r1_orders_2 @ X1 @ X0 @ X2)
% 0.67/0.83          | ~ (r3_orders_2 @ X1 @ X0 @ X2))),
% 0.67/0.83      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.67/0.83  thf('250', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         (~ (r3_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ X0)
% 0.67/0.83          | (r1_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ X0)
% 0.67/0.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 0.67/0.83          | (v2_struct_0 @ (k3_lattice3 @ sk_B))
% 0.67/0.83          | ~ (v3_orders_2 @ (k3_lattice3 @ sk_B))
% 0.67/0.83          | ~ (l1_orders_2 @ (k3_lattice3 @ sk_B)))),
% 0.67/0.83      inference('sup-', [status(thm)], ['248', '249'])).
% 0.67/0.83  thf('251', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         ((v2_struct_0 @ sk_B)
% 0.67/0.83          | ~ (v10_lattices @ sk_B)
% 0.67/0.83          | ~ (l3_lattices @ sk_B)
% 0.67/0.83          | ~ (l1_orders_2 @ (k3_lattice3 @ sk_B))
% 0.67/0.83          | (v2_struct_0 @ (k3_lattice3 @ sk_B))
% 0.67/0.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 0.67/0.83          | (r1_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ X0)
% 0.67/0.83          | ~ (r3_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ X0))),
% 0.67/0.83      inference('sup-', [status(thm)], ['247', '250'])).
% 0.67/0.83  thf('252', plain, ((v10_lattices @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('253', plain, ((l3_lattices @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('254', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         ((v2_struct_0 @ sk_B)
% 0.67/0.83          | ~ (l1_orders_2 @ (k3_lattice3 @ sk_B))
% 0.67/0.83          | (v2_struct_0 @ (k3_lattice3 @ sk_B))
% 0.67/0.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 0.67/0.83          | (r1_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ X0)
% 0.67/0.83          | ~ (r3_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ X0))),
% 0.67/0.83      inference('demod', [status(thm)], ['251', '252', '253'])).
% 0.67/0.83  thf('255', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         ((v2_struct_0 @ sk_B)
% 0.67/0.83          | ~ (v10_lattices @ sk_B)
% 0.67/0.83          | ~ (l3_lattices @ sk_B)
% 0.67/0.83          | ~ (r3_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ X0)
% 0.67/0.83          | (r1_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ X0)
% 0.67/0.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 0.67/0.83          | (v2_struct_0 @ (k3_lattice3 @ sk_B))
% 0.67/0.83          | (v2_struct_0 @ sk_B))),
% 0.67/0.83      inference('sup-', [status(thm)], ['246', '254'])).
% 0.67/0.83  thf('256', plain, ((v10_lattices @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('257', plain, ((l3_lattices @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('258', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         ((v2_struct_0 @ sk_B)
% 0.67/0.83          | ~ (r3_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ X0)
% 0.67/0.83          | (r1_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ X0)
% 0.67/0.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 0.67/0.83          | (v2_struct_0 @ (k3_lattice3 @ sk_B))
% 0.67/0.83          | (v2_struct_0 @ sk_B))),
% 0.67/0.83      inference('demod', [status(thm)], ['255', '256', '257'])).
% 0.67/0.83  thf('259', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         ((v2_struct_0 @ (k3_lattice3 @ sk_B))
% 0.67/0.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))
% 0.67/0.83          | (r1_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ X0)
% 0.67/0.83          | ~ (r3_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ X0)
% 0.67/0.83          | (v2_struct_0 @ sk_B))),
% 0.67/0.83      inference('simplify', [status(thm)], ['258'])).
% 0.67/0.83  thf('260', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         ((r1_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 0.67/0.83          | (v2_struct_0 @ sk_B)
% 0.67/0.83          | ~ (r3_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ 
% 0.67/0.83               (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)))
% 0.67/0.83          | (r1_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ 
% 0.67/0.83             (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)))
% 0.67/0.83          | (v2_struct_0 @ (k3_lattice3 @ sk_B)))),
% 0.67/0.83      inference('sup-', [status(thm)], ['245', '259'])).
% 0.67/0.83  thf('261', plain,
% 0.67/0.83      (((v2_struct_0 @ (k3_lattice3 @ sk_B))
% 0.67/0.83        | (r1_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ 
% 0.67/0.83           (sk_D_1 @ sk_C @ sk_A @ (k3_lattice3 @ sk_B)))
% 0.67/0.83        | (v2_struct_0 @ sk_B)
% 0.67/0.83        | (r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ sk_C))),
% 0.67/0.83      inference('sup-', [status(thm)], ['244', '260'])).
% 0.67/0.83  thf('262', plain,
% 0.67/0.83      (![X20 : $i]:
% 0.67/0.83         ((l1_orders_2 @ (k3_lattice3 @ X20))
% 0.67/0.83          | ~ (l3_lattices @ X20)
% 0.67/0.83          | ~ (v10_lattices @ X20)
% 0.67/0.83          | (v2_struct_0 @ X20))),
% 0.67/0.83      inference('cnf', [status(esa)], [dt_k3_lattice3])).
% 0.67/0.83  thf('263', plain,
% 0.67/0.83      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k3_lattice3 @ sk_B)))),
% 0.67/0.83      inference('clc', [status(thm)], ['15', '16'])).
% 0.67/0.83  thf('264', plain,
% 0.67/0.83      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.67/0.83         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.67/0.83          | ~ (r1_orders_2 @ X17 @ X16 @ (sk_D_1 @ X16 @ X18 @ X17))
% 0.67/0.83          | (r1_lattice3 @ X17 @ X18 @ X16)
% 0.67/0.83          | ~ (l1_orders_2 @ X17))),
% 0.67/0.83      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.67/0.83  thf('265', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         (~ (l1_orders_2 @ (k3_lattice3 @ sk_B))
% 0.67/0.83          | (r1_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 0.67/0.83          | ~ (r1_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ 
% 0.67/0.83               (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B))))),
% 0.67/0.83      inference('sup-', [status(thm)], ['263', '264'])).
% 0.67/0.83  thf('266', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         ((v2_struct_0 @ sk_B)
% 0.67/0.83          | ~ (v10_lattices @ sk_B)
% 0.67/0.83          | ~ (l3_lattices @ sk_B)
% 0.67/0.83          | ~ (r1_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ 
% 0.67/0.83               (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)))
% 0.67/0.83          | (r1_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C))),
% 0.67/0.83      inference('sup-', [status(thm)], ['262', '265'])).
% 0.67/0.83  thf('267', plain, ((v10_lattices @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('268', plain, ((l3_lattices @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('269', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         ((v2_struct_0 @ sk_B)
% 0.67/0.83          | ~ (r1_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ 
% 0.67/0.83               (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B)))
% 0.67/0.83          | (r1_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C))),
% 0.67/0.83      inference('demod', [status(thm)], ['266', '267', '268'])).
% 0.67/0.83  thf('270', plain, (~ (v2_struct_0 @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('271', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         ((r1_lattice3 @ (k3_lattice3 @ sk_B) @ X0 @ sk_C)
% 0.67/0.83          | ~ (r1_orders_2 @ (k3_lattice3 @ sk_B) @ sk_C @ 
% 0.67/0.83               (sk_D_1 @ sk_C @ X0 @ (k3_lattice3 @ sk_B))))),
% 0.67/0.83      inference('clc', [status(thm)], ['269', '270'])).
% 0.67/0.83  thf('272', plain,
% 0.67/0.83      (((r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ sk_C)
% 0.67/0.83        | (v2_struct_0 @ sk_B)
% 0.67/0.83        | (v2_struct_0 @ (k3_lattice3 @ sk_B))
% 0.67/0.83        | (r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ sk_C))),
% 0.67/0.83      inference('sup-', [status(thm)], ['261', '271'])).
% 0.67/0.83  thf('273', plain,
% 0.67/0.83      (((v2_struct_0 @ (k3_lattice3 @ sk_B))
% 0.67/0.83        | (v2_struct_0 @ sk_B)
% 0.67/0.83        | (r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ sk_C))),
% 0.67/0.83      inference('simplify', [status(thm)], ['272'])).
% 0.67/0.83  thf('274', plain, (~ (v2_struct_0 @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('275', plain,
% 0.67/0.83      (((r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ sk_C)
% 0.67/0.83        | (v2_struct_0 @ (k3_lattice3 @ sk_B)))),
% 0.67/0.83      inference('clc', [status(thm)], ['273', '274'])).
% 0.67/0.83  thf('276', plain, (~ (r1_lattice3 @ (k3_lattice3 @ sk_B) @ sk_A @ sk_C)),
% 0.67/0.83      inference('simpl_trail', [status(thm)], ['208', '209'])).
% 0.67/0.83  thf('277', plain, ((v2_struct_0 @ (k3_lattice3 @ sk_B))),
% 0.67/0.83      inference('clc', [status(thm)], ['275', '276'])).
% 0.67/0.83  thf('278', plain,
% 0.67/0.83      (![X25 : $i]:
% 0.67/0.83         (~ (v2_struct_0 @ (k3_lattice3 @ X25))
% 0.67/0.83          | ~ (l3_lattices @ X25)
% 0.67/0.83          | ~ (v10_lattices @ X25)
% 0.67/0.83          | (v2_struct_0 @ X25))),
% 0.67/0.83      inference('cnf', [status(esa)], [fc4_lattice3])).
% 0.67/0.83  thf('279', plain,
% 0.67/0.83      (((v2_struct_0 @ sk_B) | ~ (v10_lattices @ sk_B) | ~ (l3_lattices @ sk_B))),
% 0.67/0.83      inference('sup-', [status(thm)], ['277', '278'])).
% 0.67/0.83  thf('280', plain, ((v10_lattices @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('281', plain, ((l3_lattices @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('282', plain, ((v2_struct_0 @ sk_B)),
% 0.67/0.83      inference('demod', [status(thm)], ['279', '280', '281'])).
% 0.67/0.83  thf('283', plain, ($false), inference('demod', [status(thm)], ['0', '282'])).
% 0.67/0.83  
% 0.67/0.83  % SZS output end Refutation
% 0.67/0.83  
% 0.67/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
