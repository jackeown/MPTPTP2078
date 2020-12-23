%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cOr3xVZKJq

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:33 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 233 expanded)
%              Number of leaves         :   36 (  80 expanded)
%              Depth                    :   22
%              Number of atoms          : 2275 (3807 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :   20 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(r4_lattice3_type,type,(
    r4_lattice3: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(r3_lattice3_type,type,(
    r3_lattice3: $i > $i > $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t46_lattice3,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v4_lattice3 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( r3_lattices @ A @ ( k15_lattice3 @ A @ B ) @ ( k15_lattice3 @ A @ C ) )
            & ( r3_lattices @ A @ ( k16_lattice3 @ A @ C ) @ ( k16_lattice3 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v4_lattice3 @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i,C: $i] :
            ( ( r1_tarski @ B @ C )
           => ( ( r3_lattices @ A @ ( k15_lattice3 @ A @ B ) @ ( k15_lattice3 @ A @ C ) )
              & ( r3_lattices @ A @ ( k16_lattice3 @ A @ C ) @ ( k16_lattice3 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t46_lattice3])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k15_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l3_lattices @ X22 )
      | ( v2_struct_0 @ X22 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X22 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) ),
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

thf('2',plain,(
    ! [X13: $i,X14: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ( r2_hidden @ ( sk_D_1 @ X17 @ X13 @ X14 ) @ X17 )
      | ( r4_lattice3 @ X14 @ X13 @ X17 )
      | ~ ( l3_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_B @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l3_lattices @ X22 )
      | ( v2_struct_0 @ X22 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X22 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('10',plain,(
    ! [X13: $i,X14: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X17 @ X13 @ X14 ) @ ( u1_struct_0 @ X14 ) )
      | ( r4_lattice3 @ X14 @ X13 @ X17 )
      | ~ ( l3_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( m1_subset_1 @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l3_lattices @ X22 )
      | ( v2_struct_0 @ X22 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X22 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) ),
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

thf('14',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v10_lattices @ X18 )
      | ~ ( v4_lattice3 @ X18 )
      | ~ ( l3_lattices @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ( X19
       != ( k15_lattice3 @ X18 @ X20 ) )
      | ( r4_lattice3 @ X18 @ X19 @ X20 )
      | ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('15',plain,(
    ! [X18: $i,X20: $i] :
      ( ( r4_lattice3 @ X18 @ ( k15_lattice3 @ X18 @ X20 ) @ X20 )
      | ~ ( m1_subset_1 @ ( k15_lattice3 @ X18 @ X20 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( l3_lattices @ X18 )
      | ~ ( v4_lattice3 @ X18 )
      | ~ ( v10_lattices @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X1 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l3_lattices @ X22 )
      | ( v2_struct_0 @ X22 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X22 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('19',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( r4_lattice3 @ X14 @ X13 @ X15 )
      | ~ ( r2_hidden @ X16 @ X15 )
      | ( r1_lattices @ X14 @ X16 @ X13 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l3_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X3 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ( r1_lattices @ X0 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
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
    inference('sup-',[status(thm)],['17','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r1_lattices @ X1 @ X2 @ ( k15_lattice3 @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r1_lattices @ X0 @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X3 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['12','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X3 )
      | ( r1_lattices @ X0 @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X3 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ sk_B )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ sk_B )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r1_lattices @ X0 @ ( sk_D_1 @ sk_B @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['8','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattices @ X0 @ ( sk_D_1 @ sk_B @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ sk_C_1 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l3_lattices @ X22 )
      | ( v2_struct_0 @ X22 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X22 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('29',plain,(
    ! [X13: $i,X14: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( r1_lattices @ X14 @ ( sk_D_1 @ X17 @ X13 @ X14 ) @ X13 )
      | ( r4_lattice3 @ X14 @ X13 @ X17 )
      | ~ ( l3_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_lattices @ X0 @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattices @ X0 @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ sk_C_1 ) @ sk_B )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ sk_C_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ sk_C_1 ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l3_lattices @ X22 )
      | ( v2_struct_0 @ X22 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X22 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('35',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l3_lattices @ X22 )
      | ( v2_struct_0 @ X22 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X22 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('36',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v10_lattices @ X18 )
      | ~ ( v4_lattice3 @ X18 )
      | ~ ( l3_lattices @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ( X19
       != ( k15_lattice3 @ X18 @ X20 ) )
      | ~ ( r4_lattice3 @ X18 @ X21 @ X20 )
      | ( r1_lattices @ X18 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('37',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X18 ) )
      | ( r1_lattices @ X18 @ ( k15_lattice3 @ X18 @ X20 ) @ X21 )
      | ~ ( r4_lattice3 @ X18 @ X21 @ X20 )
      | ~ ( m1_subset_1 @ ( k15_lattice3 @ X18 @ X20 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( l3_lattices @ X18 )
      | ~ ( v4_lattice3 @ X18 )
      | ~ ( v10_lattices @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r4_lattice3 @ X0 @ X2 @ X1 )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r4_lattice3 @ X0 @ X2 @ X1 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ sk_B ) @ ( k15_lattice3 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['33','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ sk_B ) @ ( k15_lattice3 @ X0 @ sk_C_1 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l3_lattices @ X22 )
      | ( v2_struct_0 @ X22 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X22 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('45',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l3_lattices @ X22 )
      | ( v2_struct_0 @ X22 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X22 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) ),
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

thf('46',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l3_lattices @ X6 )
      | ~ ( v9_lattices @ X6 )
      | ~ ( v8_lattices @ X6 )
      | ~ ( v6_lattices @ X6 )
      | ( v2_struct_0 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ( r3_lattices @ X6 @ X5 @ X7 )
      | ~ ( r1_lattices @ X6 @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ sk_B ) @ ( k15_lattice3 @ X0 @ sk_C_1 ) )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ sk_B ) @ ( k15_lattice3 @ X0 @ sk_C_1 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ~ ( r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_C_1 ) )
    | ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C_1 ) @ ( k16_lattice3 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ~ ( r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_C_1 ) )
   <= ~ ( r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['53'])).

thf(dt_k16_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( m1_subset_1 @ ( k16_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('55',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l3_lattices @ X24 )
      | ( v2_struct_0 @ X24 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ),
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

thf('56',plain,(
    ! [X8: $i,X9: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ( r2_hidden @ ( sk_D @ X12 @ X8 @ X9 ) @ X12 )
      | ( r3_lattice3 @ X9 @ X8 @ X12 )
      | ~ ( l3_lattices @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ sk_B )
      | ( r2_hidden @ ( sk_D @ sk_B @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l3_lattices @ X24 )
      | ( v2_struct_0 @ X24 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf('62',plain,(
    ! [X8: $i,X9: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ( m1_subset_1 @ ( sk_D @ X12 @ X8 @ X9 ) @ ( u1_struct_0 @ X9 ) )
      | ( r3_lattice3 @ X9 @ X8 @ X12 )
      | ~ ( l3_lattices @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ( m1_subset_1 @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l3_lattices @ X24 )
      | ( v2_struct_0 @ X24 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ),
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

thf('66',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ( X26
       != ( k16_lattice3 @ X27 @ X28 ) )
      | ( r3_lattice3 @ X27 @ X26 @ X28 )
      | ~ ( l3_lattices @ X27 )
      | ~ ( v4_lattice3 @ X27 )
      | ~ ( v10_lattices @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('67',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v10_lattices @ X27 )
      | ~ ( v4_lattice3 @ X27 )
      | ~ ( l3_lattices @ X27 )
      | ( r3_lattice3 @ X27 @ ( k16_lattice3 @ X27 @ X28 ) @ X28 )
      | ~ ( m1_subset_1 @ ( k16_lattice3 @ X27 @ X28 ) @ ( u1_struct_0 @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l3_lattices @ X24 )
      | ( v2_struct_0 @ X24 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf('71',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( r3_lattice3 @ X9 @ X8 @ X10 )
      | ~ ( r2_hidden @ X11 @ X10 )
      | ( r1_lattices @ X9 @ X8 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l3_lattices @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X3 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
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
    inference('sup-',[status(thm)],['69','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r1_lattices @ X1 @ ( k16_lattice3 @ X1 @ X0 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X3 ) @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['64','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) @ X3 )
      | ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X3 ) @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ sk_B )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ sk_B )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ sk_C_1 ) @ ( sk_D @ sk_B @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ sk_C_1 ) @ ( sk_D @ sk_B @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l3_lattices @ X24 )
      | ( v2_struct_0 @ X24 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf('81',plain,(
    ! [X8: $i,X9: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( r1_lattices @ X9 @ X8 @ ( sk_D @ X12 @ X8 @ X9 ) )
      | ( r3_lattice3 @ X9 @ X8 @ X12 )
      | ~ ( l3_lattices @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ sk_C_1 ) @ sk_B )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ sk_C_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['79','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ sk_C_1 ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l3_lattices @ X24 )
      | ( v2_struct_0 @ X24 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf(t40_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v4_lattice3 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( r3_lattice3 @ A @ B @ C )
             => ( r3_lattices @ A @ B @ ( k16_lattice3 @ A @ C ) ) ) ) ) )).

thf('87',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ( r3_lattices @ X32 @ X31 @ ( k16_lattice3 @ X32 @ X33 ) )
      | ~ ( r3_lattice3 @ X32 @ X31 @ X33 )
      | ~ ( l3_lattices @ X32 )
      | ~ ( v4_lattice3 @ X32 )
      | ~ ( v10_lattices @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t40_lattice3])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( k16_lattice3 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( k16_lattice3 @ X0 @ X2 ) )
      | ~ ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ sk_C_1 ) @ ( k16_lattice3 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['85','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ sk_C_1 ) @ ( k16_lattice3 @ X0 @ sk_B ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C_1 ) @ ( k16_lattice3 @ sk_A @ sk_B ) )
   <= ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C_1 ) @ ( k16_lattice3 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['53'])).

thf('93',plain,
    ( ( ~ ( l3_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( v10_lattices @ sk_A ) )
   <= ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C_1 ) @ ( k16_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C_1 ) @ ( k16_lattice3 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['93','94','95','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C_1 ) @ ( k16_lattice3 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ~ ( r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_C_1 ) )
    | ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C_1 ) @ ( k16_lattice3 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['53'])).

thf('101',plain,(
    ~ ( r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_C_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['99','100'])).

thf('102',plain,(
    ~ ( r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_C_1 ) ) ),
    inference(simpl_trail,[status(thm)],['54','101'])).

thf('103',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( v6_lattices @ sk_A )
    | ~ ( v8_lattices @ sk_A )
    | ~ ( v9_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['52','102'])).

thf('104',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v4_lattice3 @ sk_A ),
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

thf('107',plain,(
    ! [X4: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( v10_lattices @ X4 )
      | ( v6_lattices @ X4 )
      | ~ ( l3_lattices @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('108',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,(
    ! [X4: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( v10_lattices @ X4 )
      | ( v8_lattices @ X4 )
      | ~ ( l3_lattices @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('114',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['115','116','117'])).

thf('119',plain,(
    ! [X4: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( v10_lattices @ X4 )
      | ( v9_lattices @ X4 )
      | ~ ( l3_lattices @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['121','122','123'])).

thf('125',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['103','104','105','106','112','118','124'])).

thf('126',plain,(
    $false ),
    inference(demod,[status(thm)],['0','125'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cOr3xVZKJq
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:56:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.49/0.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.49/0.70  % Solved by: fo/fo7.sh
% 0.49/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.70  % done 233 iterations in 0.241s
% 0.49/0.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.49/0.70  % SZS output start Refutation
% 0.49/0.70  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 0.49/0.70  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 0.49/0.70  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.49/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.49/0.70  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 0.49/0.70  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.49/0.70  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.49/0.70  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.49/0.70  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.49/0.70  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 0.49/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.49/0.70  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.49/0.70  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.49/0.70  thf(r4_lattice3_type, type, r4_lattice3: $i > $i > $i > $o).
% 0.49/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.49/0.70  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.49/0.70  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.49/0.70  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.49/0.70  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.49/0.70  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.49/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.70  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.49/0.70  thf(r3_lattice3_type, type, r3_lattice3: $i > $i > $i > $o).
% 0.49/0.70  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.49/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.70  thf(t46_lattice3, conjecture,
% 0.49/0.70    (![A:$i]:
% 0.49/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.49/0.70         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.49/0.70       ( ![B:$i,C:$i]:
% 0.49/0.70         ( ( r1_tarski @ B @ C ) =>
% 0.49/0.70           ( ( r3_lattices @
% 0.49/0.70               A @ ( k15_lattice3 @ A @ B ) @ ( k15_lattice3 @ A @ C ) ) & 
% 0.49/0.70             ( r3_lattices @
% 0.49/0.70               A @ ( k16_lattice3 @ A @ C ) @ ( k16_lattice3 @ A @ B ) ) ) ) ) ))).
% 0.49/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.70    (~( ![A:$i]:
% 0.49/0.70        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.49/0.70            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.49/0.70          ( ![B:$i,C:$i]:
% 0.49/0.70            ( ( r1_tarski @ B @ C ) =>
% 0.49/0.70              ( ( r3_lattices @
% 0.49/0.70                  A @ ( k15_lattice3 @ A @ B ) @ ( k15_lattice3 @ A @ C ) ) & 
% 0.49/0.70                ( r3_lattices @
% 0.49/0.70                  A @ ( k16_lattice3 @ A @ C ) @ ( k16_lattice3 @ A @ B ) ) ) ) ) ) )),
% 0.49/0.70    inference('cnf.neg', [status(esa)], [t46_lattice3])).
% 0.49/0.70  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf(dt_k15_lattice3, axiom,
% 0.49/0.70    (![A:$i,B:$i]:
% 0.49/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.49/0.70       ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.49/0.70  thf('1', plain,
% 0.49/0.70      (![X22 : $i, X23 : $i]:
% 0.49/0.70         (~ (l3_lattices @ X22)
% 0.49/0.70          | (v2_struct_0 @ X22)
% 0.49/0.70          | (m1_subset_1 @ (k15_lattice3 @ X22 @ X23) @ (u1_struct_0 @ X22)))),
% 0.49/0.70      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.49/0.70  thf(d17_lattice3, axiom,
% 0.49/0.70    (![A:$i]:
% 0.49/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.49/0.70       ( ![B:$i]:
% 0.49/0.70         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.49/0.70           ( ![C:$i]:
% 0.49/0.70             ( ( r4_lattice3 @ A @ B @ C ) <=>
% 0.49/0.70               ( ![D:$i]:
% 0.49/0.70                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.49/0.70                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ))).
% 0.49/0.70  thf('2', plain,
% 0.49/0.70      (![X13 : $i, X14 : $i, X17 : $i]:
% 0.49/0.70         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.49/0.70          | (r2_hidden @ (sk_D_1 @ X17 @ X13 @ X14) @ X17)
% 0.49/0.70          | (r4_lattice3 @ X14 @ X13 @ X17)
% 0.49/0.70          | ~ (l3_lattices @ X14)
% 0.49/0.70          | (v2_struct_0 @ X14))),
% 0.49/0.70      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.49/0.70  thf('3', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.70         ((v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.49/0.70          | (r2_hidden @ (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X2))),
% 0.49/0.70      inference('sup-', [status(thm)], ['1', '2'])).
% 0.49/0.70  thf('4', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.70         ((r2_hidden @ (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X2)
% 0.49/0.70          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0))),
% 0.49/0.70      inference('simplify', [status(thm)], ['3'])).
% 0.49/0.70  thf('5', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf(d3_tarski, axiom,
% 0.49/0.70    (![A:$i,B:$i]:
% 0.49/0.70     ( ( r1_tarski @ A @ B ) <=>
% 0.49/0.70       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.49/0.70  thf('6', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.70         (~ (r2_hidden @ X0 @ X1)
% 0.49/0.70          | (r2_hidden @ X0 @ X2)
% 0.49/0.70          | ~ (r1_tarski @ X1 @ X2))),
% 0.49/0.70      inference('cnf', [status(esa)], [d3_tarski])).
% 0.49/0.70  thf('7', plain,
% 0.49/0.70      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.49/0.70      inference('sup-', [status(thm)], ['5', '6'])).
% 0.49/0.70  thf('8', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         ((v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ sk_B)
% 0.49/0.70          | (r2_hidden @ (sk_D_1 @ sk_B @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.49/0.70             sk_C_1))),
% 0.49/0.70      inference('sup-', [status(thm)], ['4', '7'])).
% 0.49/0.70  thf('9', plain,
% 0.49/0.70      (![X22 : $i, X23 : $i]:
% 0.49/0.70         (~ (l3_lattices @ X22)
% 0.49/0.70          | (v2_struct_0 @ X22)
% 0.49/0.70          | (m1_subset_1 @ (k15_lattice3 @ X22 @ X23) @ (u1_struct_0 @ X22)))),
% 0.49/0.70      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.49/0.70  thf('10', plain,
% 0.49/0.70      (![X13 : $i, X14 : $i, X17 : $i]:
% 0.49/0.70         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.49/0.70          | (m1_subset_1 @ (sk_D_1 @ X17 @ X13 @ X14) @ (u1_struct_0 @ X14))
% 0.49/0.70          | (r4_lattice3 @ X14 @ X13 @ X17)
% 0.49/0.70          | ~ (l3_lattices @ X14)
% 0.49/0.70          | (v2_struct_0 @ X14))),
% 0.49/0.70      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.49/0.70  thf('11', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.70         ((v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.49/0.70          | (m1_subset_1 @ (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.49/0.70             (u1_struct_0 @ X0)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['9', '10'])).
% 0.49/0.70  thf('12', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.70         ((m1_subset_1 @ (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.49/0.70           (u1_struct_0 @ X0))
% 0.49/0.70          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0))),
% 0.49/0.70      inference('simplify', [status(thm)], ['11'])).
% 0.49/0.70  thf('13', plain,
% 0.49/0.70      (![X22 : $i, X23 : $i]:
% 0.49/0.70         (~ (l3_lattices @ X22)
% 0.49/0.70          | (v2_struct_0 @ X22)
% 0.49/0.70          | (m1_subset_1 @ (k15_lattice3 @ X22 @ X23) @ (u1_struct_0 @ X22)))),
% 0.49/0.70      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.49/0.70  thf(d21_lattice3, axiom,
% 0.49/0.70    (![A:$i]:
% 0.49/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.49/0.70       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.49/0.70           ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.49/0.70         ( ![B:$i,C:$i]:
% 0.49/0.70           ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.49/0.70             ( ( ( C ) = ( k15_lattice3 @ A @ B ) ) <=>
% 0.49/0.70               ( ( r4_lattice3 @ A @ C @ B ) & 
% 0.49/0.70                 ( ![D:$i]:
% 0.49/0.70                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.49/0.70                     ( ( r4_lattice3 @ A @ D @ B ) =>
% 0.49/0.70                       ( r1_lattices @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.49/0.70  thf('14', plain,
% 0.49/0.70      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.49/0.70         ((v2_struct_0 @ X18)
% 0.49/0.70          | ~ (v10_lattices @ X18)
% 0.49/0.70          | ~ (v4_lattice3 @ X18)
% 0.49/0.70          | ~ (l3_lattices @ X18)
% 0.49/0.70          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 0.49/0.70          | ((X19) != (k15_lattice3 @ X18 @ X20))
% 0.49/0.70          | (r4_lattice3 @ X18 @ X19 @ X20)
% 0.49/0.70          | ~ (l3_lattices @ X18)
% 0.49/0.70          | (v2_struct_0 @ X18))),
% 0.49/0.70      inference('cnf', [status(esa)], [d21_lattice3])).
% 0.49/0.70  thf('15', plain,
% 0.49/0.70      (![X18 : $i, X20 : $i]:
% 0.49/0.70         ((r4_lattice3 @ X18 @ (k15_lattice3 @ X18 @ X20) @ X20)
% 0.49/0.70          | ~ (m1_subset_1 @ (k15_lattice3 @ X18 @ X20) @ (u1_struct_0 @ X18))
% 0.49/0.70          | ~ (l3_lattices @ X18)
% 0.49/0.70          | ~ (v4_lattice3 @ X18)
% 0.49/0.70          | ~ (v10_lattices @ X18)
% 0.49/0.70          | (v2_struct_0 @ X18))),
% 0.49/0.70      inference('simplify', [status(thm)], ['14'])).
% 0.49/0.70  thf('16', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         ((v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0)
% 0.49/0.70          | ~ (v10_lattices @ X0)
% 0.49/0.70          | ~ (v4_lattice3 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X1))),
% 0.49/0.70      inference('sup-', [status(thm)], ['13', '15'])).
% 0.49/0.70  thf('17', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         ((r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X1)
% 0.49/0.70          | ~ (v4_lattice3 @ X0)
% 0.49/0.70          | ~ (v10_lattices @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0))),
% 0.49/0.70      inference('simplify', [status(thm)], ['16'])).
% 0.49/0.70  thf('18', plain,
% 0.49/0.70      (![X22 : $i, X23 : $i]:
% 0.49/0.70         (~ (l3_lattices @ X22)
% 0.49/0.70          | (v2_struct_0 @ X22)
% 0.49/0.70          | (m1_subset_1 @ (k15_lattice3 @ X22 @ X23) @ (u1_struct_0 @ X22)))),
% 0.49/0.70      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.49/0.70  thf('19', plain,
% 0.49/0.70      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.49/0.70         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.49/0.70          | ~ (r4_lattice3 @ X14 @ X13 @ X15)
% 0.49/0.70          | ~ (r2_hidden @ X16 @ X15)
% 0.49/0.70          | (r1_lattices @ X14 @ X16 @ X13)
% 0.49/0.70          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X14))
% 0.49/0.70          | ~ (l3_lattices @ X14)
% 0.49/0.70          | (v2_struct_0 @ X14))),
% 0.49/0.70      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.49/0.70  thf('20', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.70         ((v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.49/0.70          | (r1_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))
% 0.49/0.70          | ~ (r2_hidden @ X2 @ X3)
% 0.49/0.70          | ~ (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X3))),
% 0.49/0.70      inference('sup-', [status(thm)], ['18', '19'])).
% 0.49/0.70  thf('21', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.70         (~ (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X3)
% 0.49/0.70          | ~ (r2_hidden @ X2 @ X3)
% 0.49/0.70          | (r1_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))
% 0.49/0.70          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0))),
% 0.49/0.70      inference('simplify', [status(thm)], ['20'])).
% 0.49/0.70  thf('22', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.70         ((v2_struct_0 @ X1)
% 0.49/0.70          | ~ (l3_lattices @ X1)
% 0.49/0.70          | ~ (v10_lattices @ X1)
% 0.49/0.70          | ~ (v4_lattice3 @ X1)
% 0.49/0.70          | (v2_struct_0 @ X1)
% 0.49/0.70          | ~ (l3_lattices @ X1)
% 0.49/0.70          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.49/0.70          | (r1_lattices @ X1 @ X2 @ (k15_lattice3 @ X1 @ X0))
% 0.49/0.70          | ~ (r2_hidden @ X2 @ X0))),
% 0.49/0.70      inference('sup-', [status(thm)], ['17', '21'])).
% 0.49/0.70  thf('23', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.70         (~ (r2_hidden @ X2 @ X0)
% 0.49/0.70          | (r1_lattices @ X1 @ X2 @ (k15_lattice3 @ X1 @ X0))
% 0.49/0.70          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.49/0.70          | ~ (v4_lattice3 @ X1)
% 0.49/0.70          | ~ (v10_lattices @ X1)
% 0.49/0.70          | ~ (l3_lattices @ X1)
% 0.49/0.70          | (v2_struct_0 @ X1))),
% 0.49/0.70      inference('simplify', [status(thm)], ['22'])).
% 0.49/0.70  thf('24', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.70         ((v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.49/0.70          | (v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | ~ (v10_lattices @ X0)
% 0.49/0.70          | ~ (v4_lattice3 @ X0)
% 0.49/0.70          | (r1_lattices @ X0 @ 
% 0.49/0.70             (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.49/0.70             (k15_lattice3 @ X0 @ X3))
% 0.49/0.70          | ~ (r2_hidden @ (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X3))),
% 0.49/0.70      inference('sup-', [status(thm)], ['12', '23'])).
% 0.49/0.70  thf('25', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.70         (~ (r2_hidden @ (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X3)
% 0.49/0.70          | (r1_lattices @ X0 @ 
% 0.49/0.70             (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.49/0.70             (k15_lattice3 @ X0 @ X3))
% 0.49/0.70          | ~ (v4_lattice3 @ X0)
% 0.49/0.70          | ~ (v10_lattices @ X0)
% 0.49/0.70          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0))),
% 0.49/0.70      inference('simplify', [status(thm)], ['24'])).
% 0.49/0.70  thf('26', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         ((r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ sk_B)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ sk_B)
% 0.49/0.70          | ~ (v10_lattices @ X0)
% 0.49/0.70          | ~ (v4_lattice3 @ X0)
% 0.49/0.70          | (r1_lattices @ X0 @ 
% 0.49/0.70             (sk_D_1 @ sk_B @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.49/0.70             (k15_lattice3 @ X0 @ sk_C_1)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['8', '25'])).
% 0.49/0.70  thf('27', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         ((r1_lattices @ X0 @ 
% 0.49/0.70           (sk_D_1 @ sk_B @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.49/0.70           (k15_lattice3 @ X0 @ sk_C_1))
% 0.49/0.70          | ~ (v4_lattice3 @ X0)
% 0.49/0.70          | ~ (v10_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ sk_B))),
% 0.49/0.70      inference('simplify', [status(thm)], ['26'])).
% 0.49/0.70  thf('28', plain,
% 0.49/0.70      (![X22 : $i, X23 : $i]:
% 0.49/0.70         (~ (l3_lattices @ X22)
% 0.49/0.70          | (v2_struct_0 @ X22)
% 0.49/0.70          | (m1_subset_1 @ (k15_lattice3 @ X22 @ X23) @ (u1_struct_0 @ X22)))),
% 0.49/0.70      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.49/0.70  thf('29', plain,
% 0.49/0.70      (![X13 : $i, X14 : $i, X17 : $i]:
% 0.49/0.70         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.49/0.70          | ~ (r1_lattices @ X14 @ (sk_D_1 @ X17 @ X13 @ X14) @ X13)
% 0.49/0.70          | (r4_lattice3 @ X14 @ X13 @ X17)
% 0.49/0.70          | ~ (l3_lattices @ X14)
% 0.49/0.70          | (v2_struct_0 @ X14))),
% 0.49/0.70      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.49/0.70  thf('30', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.70         ((v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.49/0.70          | ~ (r1_lattices @ X0 @ 
% 0.49/0.70               (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.49/0.70               (k15_lattice3 @ X0 @ X1)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['28', '29'])).
% 0.49/0.70  thf('31', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.70         (~ (r1_lattices @ X0 @ 
% 0.49/0.70             (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.49/0.70             (k15_lattice3 @ X0 @ X1))
% 0.49/0.70          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0))),
% 0.49/0.70      inference('simplify', [status(thm)], ['30'])).
% 0.49/0.70  thf('32', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         ((r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ sk_C_1) @ sk_B)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0)
% 0.49/0.70          | ~ (v10_lattices @ X0)
% 0.49/0.70          | ~ (v4_lattice3 @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ sk_C_1) @ sk_B))),
% 0.49/0.70      inference('sup-', [status(thm)], ['27', '31'])).
% 0.49/0.70  thf('33', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         (~ (v4_lattice3 @ X0)
% 0.49/0.70          | ~ (v10_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ sk_C_1) @ sk_B))),
% 0.49/0.70      inference('simplify', [status(thm)], ['32'])).
% 0.49/0.70  thf('34', plain,
% 0.49/0.70      (![X22 : $i, X23 : $i]:
% 0.49/0.70         (~ (l3_lattices @ X22)
% 0.49/0.70          | (v2_struct_0 @ X22)
% 0.49/0.70          | (m1_subset_1 @ (k15_lattice3 @ X22 @ X23) @ (u1_struct_0 @ X22)))),
% 0.49/0.70      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.49/0.70  thf('35', plain,
% 0.49/0.70      (![X22 : $i, X23 : $i]:
% 0.49/0.70         (~ (l3_lattices @ X22)
% 0.49/0.70          | (v2_struct_0 @ X22)
% 0.49/0.70          | (m1_subset_1 @ (k15_lattice3 @ X22 @ X23) @ (u1_struct_0 @ X22)))),
% 0.49/0.70      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.49/0.70  thf('36', plain,
% 0.49/0.70      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.49/0.70         ((v2_struct_0 @ X18)
% 0.49/0.70          | ~ (v10_lattices @ X18)
% 0.49/0.70          | ~ (v4_lattice3 @ X18)
% 0.49/0.70          | ~ (l3_lattices @ X18)
% 0.49/0.70          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 0.49/0.70          | ((X19) != (k15_lattice3 @ X18 @ X20))
% 0.49/0.70          | ~ (r4_lattice3 @ X18 @ X21 @ X20)
% 0.49/0.70          | (r1_lattices @ X18 @ X19 @ X21)
% 0.49/0.70          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X18))
% 0.49/0.70          | ~ (l3_lattices @ X18)
% 0.49/0.70          | (v2_struct_0 @ X18))),
% 0.49/0.70      inference('cnf', [status(esa)], [d21_lattice3])).
% 0.49/0.70  thf('37', plain,
% 0.49/0.70      (![X18 : $i, X20 : $i, X21 : $i]:
% 0.49/0.70         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X18))
% 0.49/0.70          | (r1_lattices @ X18 @ (k15_lattice3 @ X18 @ X20) @ X21)
% 0.49/0.70          | ~ (r4_lattice3 @ X18 @ X21 @ X20)
% 0.49/0.70          | ~ (m1_subset_1 @ (k15_lattice3 @ X18 @ X20) @ (u1_struct_0 @ X18))
% 0.49/0.70          | ~ (l3_lattices @ X18)
% 0.49/0.70          | ~ (v4_lattice3 @ X18)
% 0.49/0.70          | ~ (v10_lattices @ X18)
% 0.49/0.70          | (v2_struct_0 @ X18))),
% 0.49/0.70      inference('simplify', [status(thm)], ['36'])).
% 0.49/0.70  thf('38', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.70         ((v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0)
% 0.49/0.70          | ~ (v10_lattices @ X0)
% 0.49/0.70          | ~ (v4_lattice3 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | ~ (r4_lattice3 @ X0 @ X2 @ X1)
% 0.49/0.70          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.49/0.70          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['35', '37'])).
% 0.49/0.70  thf('39', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.70         (~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.49/0.70          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.49/0.70          | ~ (r4_lattice3 @ X0 @ X2 @ X1)
% 0.49/0.70          | ~ (v4_lattice3 @ X0)
% 0.49/0.70          | ~ (v10_lattices @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0))),
% 0.49/0.70      inference('simplify', [status(thm)], ['38'])).
% 0.49/0.70  thf('40', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.70         ((v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | ~ (v10_lattices @ X0)
% 0.49/0.70          | ~ (v4_lattice3 @ X0)
% 0.49/0.70          | ~ (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.49/0.70          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 0.49/0.70             (k15_lattice3 @ X0 @ X1)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['34', '39'])).
% 0.49/0.70  thf('41', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.70         ((r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 0.49/0.70           (k15_lattice3 @ X0 @ X1))
% 0.49/0.70          | ~ (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.49/0.70          | ~ (v4_lattice3 @ X0)
% 0.49/0.70          | ~ (v10_lattices @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0))),
% 0.49/0.70      inference('simplify', [status(thm)], ['40'])).
% 0.49/0.70  thf('42', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         (~ (l3_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0)
% 0.49/0.70          | ~ (v10_lattices @ X0)
% 0.49/0.70          | ~ (v4_lattice3 @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | ~ (v10_lattices @ X0)
% 0.49/0.70          | ~ (v4_lattice3 @ X0)
% 0.49/0.70          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ sk_B) @ 
% 0.49/0.70             (k15_lattice3 @ X0 @ sk_C_1)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['33', '41'])).
% 0.49/0.70  thf('43', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         ((r1_lattices @ X0 @ (k15_lattice3 @ X0 @ sk_B) @ 
% 0.49/0.70           (k15_lattice3 @ X0 @ sk_C_1))
% 0.49/0.70          | ~ (v4_lattice3 @ X0)
% 0.49/0.70          | ~ (v10_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0))),
% 0.49/0.70      inference('simplify', [status(thm)], ['42'])).
% 0.49/0.70  thf('44', plain,
% 0.49/0.70      (![X22 : $i, X23 : $i]:
% 0.49/0.70         (~ (l3_lattices @ X22)
% 0.49/0.70          | (v2_struct_0 @ X22)
% 0.49/0.70          | (m1_subset_1 @ (k15_lattice3 @ X22 @ X23) @ (u1_struct_0 @ X22)))),
% 0.49/0.70      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.49/0.70  thf('45', plain,
% 0.49/0.70      (![X22 : $i, X23 : $i]:
% 0.49/0.70         (~ (l3_lattices @ X22)
% 0.49/0.70          | (v2_struct_0 @ X22)
% 0.49/0.70          | (m1_subset_1 @ (k15_lattice3 @ X22 @ X23) @ (u1_struct_0 @ X22)))),
% 0.49/0.70      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.49/0.70  thf(redefinition_r3_lattices, axiom,
% 0.49/0.70    (![A:$i,B:$i,C:$i]:
% 0.49/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.49/0.70         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 0.49/0.70         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.49/0.70         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.70       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 0.49/0.70  thf('46', plain,
% 0.49/0.70      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.49/0.70         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 0.49/0.70          | ~ (l3_lattices @ X6)
% 0.49/0.70          | ~ (v9_lattices @ X6)
% 0.49/0.70          | ~ (v8_lattices @ X6)
% 0.49/0.70          | ~ (v6_lattices @ X6)
% 0.49/0.70          | (v2_struct_0 @ X6)
% 0.49/0.70          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 0.49/0.70          | (r3_lattices @ X6 @ X5 @ X7)
% 0.49/0.70          | ~ (r1_lattices @ X6 @ X5 @ X7))),
% 0.49/0.70      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.49/0.70  thf('47', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.70         ((v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | ~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.49/0.70          | (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.49/0.70          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.49/0.70          | (v2_struct_0 @ X0)
% 0.49/0.70          | ~ (v6_lattices @ X0)
% 0.49/0.70          | ~ (v8_lattices @ X0)
% 0.49/0.70          | ~ (v9_lattices @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0))),
% 0.49/0.70      inference('sup-', [status(thm)], ['45', '46'])).
% 0.49/0.70  thf('48', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.70         (~ (v9_lattices @ X0)
% 0.49/0.70          | ~ (v8_lattices @ X0)
% 0.49/0.70          | ~ (v6_lattices @ X0)
% 0.49/0.70          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.49/0.70          | (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.49/0.70          | ~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0))),
% 0.49/0.70      inference('simplify', [status(thm)], ['47'])).
% 0.49/0.70  thf('49', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.70         ((v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | ~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 0.49/0.70               (k15_lattice3 @ X0 @ X1))
% 0.49/0.70          | (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 0.49/0.70             (k15_lattice3 @ X0 @ X1))
% 0.49/0.70          | ~ (v6_lattices @ X0)
% 0.49/0.70          | ~ (v8_lattices @ X0)
% 0.49/0.70          | ~ (v9_lattices @ X0))),
% 0.49/0.70      inference('sup-', [status(thm)], ['44', '48'])).
% 0.49/0.70  thf('50', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.70         (~ (v9_lattices @ X0)
% 0.49/0.70          | ~ (v8_lattices @ X0)
% 0.49/0.70          | ~ (v6_lattices @ X0)
% 0.49/0.70          | (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 0.49/0.70             (k15_lattice3 @ X0 @ X1))
% 0.49/0.70          | ~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 0.49/0.70               (k15_lattice3 @ X0 @ X1))
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0))),
% 0.49/0.70      inference('simplify', [status(thm)], ['49'])).
% 0.49/0.70  thf('51', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         (~ (l3_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0)
% 0.49/0.70          | ~ (v10_lattices @ X0)
% 0.49/0.70          | ~ (v4_lattice3 @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ sk_B) @ 
% 0.49/0.70             (k15_lattice3 @ X0 @ sk_C_1))
% 0.49/0.70          | ~ (v6_lattices @ X0)
% 0.49/0.70          | ~ (v8_lattices @ X0)
% 0.49/0.70          | ~ (v9_lattices @ X0))),
% 0.49/0.70      inference('sup-', [status(thm)], ['43', '50'])).
% 0.49/0.70  thf('52', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         (~ (v9_lattices @ X0)
% 0.49/0.70          | ~ (v8_lattices @ X0)
% 0.49/0.70          | ~ (v6_lattices @ X0)
% 0.49/0.70          | (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ sk_B) @ 
% 0.49/0.70             (k15_lattice3 @ X0 @ sk_C_1))
% 0.49/0.70          | ~ (v4_lattice3 @ X0)
% 0.49/0.70          | ~ (v10_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0))),
% 0.49/0.70      inference('simplify', [status(thm)], ['51'])).
% 0.49/0.70  thf('53', plain,
% 0.49/0.70      ((~ (r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 0.49/0.70           (k15_lattice3 @ sk_A @ sk_C_1))
% 0.49/0.70        | ~ (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C_1) @ 
% 0.49/0.70             (k16_lattice3 @ sk_A @ sk_B)))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('54', plain,
% 0.49/0.70      ((~ (r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 0.49/0.70           (k15_lattice3 @ sk_A @ sk_C_1)))
% 0.49/0.70         <= (~
% 0.49/0.70             ((r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 0.49/0.70               (k15_lattice3 @ sk_A @ sk_C_1))))),
% 0.49/0.70      inference('split', [status(esa)], ['53'])).
% 0.49/0.70  thf(dt_k16_lattice3, axiom,
% 0.49/0.70    (![A:$i,B:$i]:
% 0.49/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.49/0.70       ( m1_subset_1 @ ( k16_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.49/0.70  thf('55', plain,
% 0.49/0.70      (![X24 : $i, X25 : $i]:
% 0.49/0.70         (~ (l3_lattices @ X24)
% 0.49/0.70          | (v2_struct_0 @ X24)
% 0.49/0.70          | (m1_subset_1 @ (k16_lattice3 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 0.49/0.70      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.49/0.70  thf(d16_lattice3, axiom,
% 0.49/0.70    (![A:$i]:
% 0.49/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.49/0.70       ( ![B:$i]:
% 0.49/0.70         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.49/0.70           ( ![C:$i]:
% 0.49/0.70             ( ( r3_lattice3 @ A @ B @ C ) <=>
% 0.49/0.70               ( ![D:$i]:
% 0.49/0.70                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.49/0.70                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 0.49/0.70  thf('56', plain,
% 0.49/0.70      (![X8 : $i, X9 : $i, X12 : $i]:
% 0.49/0.70         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.49/0.70          | (r2_hidden @ (sk_D @ X12 @ X8 @ X9) @ X12)
% 0.49/0.70          | (r3_lattice3 @ X9 @ X8 @ X12)
% 0.49/0.70          | ~ (l3_lattices @ X9)
% 0.49/0.70          | (v2_struct_0 @ X9))),
% 0.49/0.70      inference('cnf', [status(esa)], [d16_lattice3])).
% 0.49/0.70  thf('57', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.70         ((v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.49/0.70          | (r2_hidden @ (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0) @ X2))),
% 0.49/0.70      inference('sup-', [status(thm)], ['55', '56'])).
% 0.49/0.70  thf('58', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.70         ((r2_hidden @ (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0) @ X2)
% 0.49/0.70          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0))),
% 0.49/0.70      inference('simplify', [status(thm)], ['57'])).
% 0.49/0.70  thf('59', plain,
% 0.49/0.70      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.49/0.70      inference('sup-', [status(thm)], ['5', '6'])).
% 0.49/0.70  thf('60', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         ((v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ sk_B)
% 0.49/0.70          | (r2_hidden @ (sk_D @ sk_B @ (k16_lattice3 @ X0 @ X1) @ X0) @ sk_C_1))),
% 0.49/0.70      inference('sup-', [status(thm)], ['58', '59'])).
% 0.49/0.70  thf('61', plain,
% 0.49/0.70      (![X24 : $i, X25 : $i]:
% 0.49/0.70         (~ (l3_lattices @ X24)
% 0.49/0.70          | (v2_struct_0 @ X24)
% 0.49/0.70          | (m1_subset_1 @ (k16_lattice3 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 0.49/0.70      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.49/0.70  thf('62', plain,
% 0.49/0.70      (![X8 : $i, X9 : $i, X12 : $i]:
% 0.49/0.70         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.49/0.70          | (m1_subset_1 @ (sk_D @ X12 @ X8 @ X9) @ (u1_struct_0 @ X9))
% 0.49/0.70          | (r3_lattice3 @ X9 @ X8 @ X12)
% 0.49/0.70          | ~ (l3_lattices @ X9)
% 0.49/0.70          | (v2_struct_0 @ X9))),
% 0.49/0.70      inference('cnf', [status(esa)], [d16_lattice3])).
% 0.49/0.70  thf('63', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.70         ((v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.49/0.70          | (m1_subset_1 @ (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0) @ 
% 0.49/0.70             (u1_struct_0 @ X0)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['61', '62'])).
% 0.49/0.70  thf('64', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.70         ((m1_subset_1 @ (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0) @ 
% 0.49/0.70           (u1_struct_0 @ X0))
% 0.49/0.70          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0))),
% 0.49/0.70      inference('simplify', [status(thm)], ['63'])).
% 0.49/0.70  thf('65', plain,
% 0.49/0.70      (![X24 : $i, X25 : $i]:
% 0.49/0.70         (~ (l3_lattices @ X24)
% 0.49/0.70          | (v2_struct_0 @ X24)
% 0.49/0.70          | (m1_subset_1 @ (k16_lattice3 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 0.49/0.70      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.49/0.70  thf(t34_lattice3, axiom,
% 0.49/0.70    (![A:$i]:
% 0.49/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.49/0.70         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.49/0.70       ( ![B:$i]:
% 0.49/0.70         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.49/0.70           ( ![C:$i]:
% 0.49/0.70             ( ( ( B ) = ( k16_lattice3 @ A @ C ) ) <=>
% 0.49/0.70               ( ( r3_lattice3 @ A @ B @ C ) & 
% 0.49/0.70                 ( ![D:$i]:
% 0.49/0.70                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.49/0.70                     ( ( r3_lattice3 @ A @ D @ C ) =>
% 0.49/0.70                       ( r3_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.49/0.70  thf('66', plain,
% 0.49/0.70      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.49/0.70         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 0.49/0.70          | ((X26) != (k16_lattice3 @ X27 @ X28))
% 0.49/0.70          | (r3_lattice3 @ X27 @ X26 @ X28)
% 0.49/0.70          | ~ (l3_lattices @ X27)
% 0.49/0.70          | ~ (v4_lattice3 @ X27)
% 0.49/0.70          | ~ (v10_lattices @ X27)
% 0.49/0.70          | (v2_struct_0 @ X27))),
% 0.49/0.70      inference('cnf', [status(esa)], [t34_lattice3])).
% 0.49/0.70  thf('67', plain,
% 0.49/0.70      (![X27 : $i, X28 : $i]:
% 0.49/0.70         ((v2_struct_0 @ X27)
% 0.49/0.70          | ~ (v10_lattices @ X27)
% 0.49/0.70          | ~ (v4_lattice3 @ X27)
% 0.49/0.70          | ~ (l3_lattices @ X27)
% 0.49/0.70          | (r3_lattice3 @ X27 @ (k16_lattice3 @ X27 @ X28) @ X28)
% 0.49/0.70          | ~ (m1_subset_1 @ (k16_lattice3 @ X27 @ X28) @ (u1_struct_0 @ X27)))),
% 0.49/0.70      inference('simplify', [status(thm)], ['66'])).
% 0.49/0.70  thf('68', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         ((v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X1)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | ~ (v4_lattice3 @ X0)
% 0.49/0.70          | ~ (v10_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0))),
% 0.49/0.70      inference('sup-', [status(thm)], ['65', '67'])).
% 0.49/0.70  thf('69', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         (~ (v10_lattices @ X0)
% 0.49/0.70          | ~ (v4_lattice3 @ X0)
% 0.49/0.70          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X1)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0))),
% 0.49/0.70      inference('simplify', [status(thm)], ['68'])).
% 0.49/0.70  thf('70', plain,
% 0.49/0.70      (![X24 : $i, X25 : $i]:
% 0.49/0.70         (~ (l3_lattices @ X24)
% 0.49/0.70          | (v2_struct_0 @ X24)
% 0.49/0.70          | (m1_subset_1 @ (k16_lattice3 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 0.49/0.70      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.49/0.70  thf('71', plain,
% 0.49/0.70      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.49/0.70         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.49/0.70          | ~ (r3_lattice3 @ X9 @ X8 @ X10)
% 0.49/0.70          | ~ (r2_hidden @ X11 @ X10)
% 0.49/0.70          | (r1_lattices @ X9 @ X8 @ X11)
% 0.49/0.70          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X9))
% 0.49/0.70          | ~ (l3_lattices @ X9)
% 0.49/0.70          | (v2_struct_0 @ X9))),
% 0.49/0.70      inference('cnf', [status(esa)], [d16_lattice3])).
% 0.49/0.70  thf('72', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.70         ((v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.49/0.70          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.49/0.70          | ~ (r2_hidden @ X2 @ X3)
% 0.49/0.70          | ~ (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X3))),
% 0.49/0.70      inference('sup-', [status(thm)], ['70', '71'])).
% 0.49/0.70  thf('73', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.70         (~ (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X3)
% 0.49/0.70          | ~ (r2_hidden @ X2 @ X3)
% 0.49/0.70          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.49/0.70          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0))),
% 0.49/0.70      inference('simplify', [status(thm)], ['72'])).
% 0.49/0.70  thf('74', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.70         ((v2_struct_0 @ X1)
% 0.49/0.70          | ~ (l3_lattices @ X1)
% 0.49/0.70          | ~ (v4_lattice3 @ X1)
% 0.49/0.70          | ~ (v10_lattices @ X1)
% 0.49/0.70          | (v2_struct_0 @ X1)
% 0.49/0.70          | ~ (l3_lattices @ X1)
% 0.49/0.70          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.49/0.70          | (r1_lattices @ X1 @ (k16_lattice3 @ X1 @ X0) @ X2)
% 0.49/0.70          | ~ (r2_hidden @ X2 @ X0))),
% 0.49/0.70      inference('sup-', [status(thm)], ['69', '73'])).
% 0.49/0.70  thf('75', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.70         (~ (r2_hidden @ X2 @ X0)
% 0.49/0.70          | (r1_lattices @ X1 @ (k16_lattice3 @ X1 @ X0) @ X2)
% 0.49/0.70          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.49/0.70          | ~ (v10_lattices @ X1)
% 0.49/0.70          | ~ (v4_lattice3 @ X1)
% 0.49/0.70          | ~ (l3_lattices @ X1)
% 0.49/0.70          | (v2_struct_0 @ X1))),
% 0.49/0.70      inference('simplify', [status(thm)], ['74'])).
% 0.49/0.70  thf('76', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.70         ((v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.49/0.70          | (v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | ~ (v4_lattice3 @ X0)
% 0.49/0.70          | ~ (v10_lattices @ X0)
% 0.49/0.70          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X3) @ 
% 0.49/0.70             (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0))
% 0.49/0.70          | ~ (r2_hidden @ (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0) @ X3))),
% 0.49/0.70      inference('sup-', [status(thm)], ['64', '75'])).
% 0.49/0.70  thf('77', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.70         (~ (r2_hidden @ (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0) @ X3)
% 0.49/0.70          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X3) @ 
% 0.49/0.70             (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0))
% 0.49/0.70          | ~ (v10_lattices @ X0)
% 0.49/0.70          | ~ (v4_lattice3 @ X0)
% 0.49/0.70          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0))),
% 0.49/0.70      inference('simplify', [status(thm)], ['76'])).
% 0.49/0.70  thf('78', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         ((r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ sk_B)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ sk_B)
% 0.49/0.70          | ~ (v4_lattice3 @ X0)
% 0.49/0.70          | ~ (v10_lattices @ X0)
% 0.49/0.70          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ sk_C_1) @ 
% 0.49/0.70             (sk_D @ sk_B @ (k16_lattice3 @ X0 @ X1) @ X0)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['60', '77'])).
% 0.49/0.70  thf('79', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         ((r1_lattices @ X0 @ (k16_lattice3 @ X0 @ sk_C_1) @ 
% 0.49/0.70           (sk_D @ sk_B @ (k16_lattice3 @ X0 @ X1) @ X0))
% 0.49/0.70          | ~ (v10_lattices @ X0)
% 0.49/0.70          | ~ (v4_lattice3 @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ sk_B))),
% 0.49/0.70      inference('simplify', [status(thm)], ['78'])).
% 0.49/0.70  thf('80', plain,
% 0.49/0.70      (![X24 : $i, X25 : $i]:
% 0.49/0.70         (~ (l3_lattices @ X24)
% 0.49/0.70          | (v2_struct_0 @ X24)
% 0.49/0.70          | (m1_subset_1 @ (k16_lattice3 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 0.49/0.70      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.49/0.70  thf('81', plain,
% 0.49/0.70      (![X8 : $i, X9 : $i, X12 : $i]:
% 0.49/0.70         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.49/0.70          | ~ (r1_lattices @ X9 @ X8 @ (sk_D @ X12 @ X8 @ X9))
% 0.49/0.70          | (r3_lattice3 @ X9 @ X8 @ X12)
% 0.49/0.70          | ~ (l3_lattices @ X9)
% 0.49/0.70          | (v2_struct_0 @ X9))),
% 0.49/0.70      inference('cnf', [status(esa)], [d16_lattice3])).
% 0.49/0.70  thf('82', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.70         ((v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.49/0.70          | ~ (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 0.49/0.70               (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['80', '81'])).
% 0.49/0.70  thf('83', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.70         (~ (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 0.49/0.70             (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0))
% 0.49/0.70          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0))),
% 0.49/0.70      inference('simplify', [status(thm)], ['82'])).
% 0.49/0.70  thf('84', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         ((r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ sk_C_1) @ sk_B)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0)
% 0.49/0.70          | ~ (v4_lattice3 @ X0)
% 0.49/0.70          | ~ (v10_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ sk_C_1) @ sk_B))),
% 0.49/0.70      inference('sup-', [status(thm)], ['79', '83'])).
% 0.49/0.70  thf('85', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         (~ (v10_lattices @ X0)
% 0.49/0.70          | ~ (v4_lattice3 @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ sk_C_1) @ sk_B))),
% 0.49/0.70      inference('simplify', [status(thm)], ['84'])).
% 0.49/0.70  thf('86', plain,
% 0.49/0.70      (![X24 : $i, X25 : $i]:
% 0.49/0.70         (~ (l3_lattices @ X24)
% 0.49/0.70          | (v2_struct_0 @ X24)
% 0.49/0.70          | (m1_subset_1 @ (k16_lattice3 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 0.49/0.70      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.49/0.70  thf(t40_lattice3, axiom,
% 0.49/0.70    (![A:$i]:
% 0.49/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.49/0.70         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.49/0.70       ( ![B:$i]:
% 0.49/0.70         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.49/0.70           ( ![C:$i]:
% 0.49/0.70             ( ( r3_lattice3 @ A @ B @ C ) =>
% 0.49/0.70               ( r3_lattices @ A @ B @ ( k16_lattice3 @ A @ C ) ) ) ) ) ) ))).
% 0.49/0.70  thf('87', plain,
% 0.49/0.70      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.49/0.70         (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X32))
% 0.49/0.70          | (r3_lattices @ X32 @ X31 @ (k16_lattice3 @ X32 @ X33))
% 0.49/0.70          | ~ (r3_lattice3 @ X32 @ X31 @ X33)
% 0.49/0.70          | ~ (l3_lattices @ X32)
% 0.49/0.70          | ~ (v4_lattice3 @ X32)
% 0.49/0.70          | ~ (v10_lattices @ X32)
% 0.49/0.70          | (v2_struct_0 @ X32))),
% 0.49/0.70      inference('cnf', [status(esa)], [t40_lattice3])).
% 0.49/0.70  thf('88', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.70         ((v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0)
% 0.49/0.70          | ~ (v10_lattices @ X0)
% 0.49/0.70          | ~ (v4_lattice3 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | ~ (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.49/0.70          | (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 0.49/0.70             (k16_lattice3 @ X0 @ X2)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['86', '87'])).
% 0.49/0.70  thf('89', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.70         ((r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 0.49/0.70           (k16_lattice3 @ X0 @ X2))
% 0.49/0.70          | ~ (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.49/0.70          | ~ (v4_lattice3 @ X0)
% 0.49/0.70          | ~ (v10_lattices @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0))),
% 0.49/0.70      inference('simplify', [status(thm)], ['88'])).
% 0.49/0.70  thf('90', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         (~ (l3_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0)
% 0.49/0.70          | ~ (v4_lattice3 @ X0)
% 0.49/0.70          | ~ (v10_lattices @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0)
% 0.49/0.70          | ~ (v10_lattices @ X0)
% 0.49/0.70          | ~ (v4_lattice3 @ X0)
% 0.49/0.70          | (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ sk_C_1) @ 
% 0.49/0.70             (k16_lattice3 @ X0 @ sk_B)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['85', '89'])).
% 0.49/0.70  thf('91', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         ((r3_lattices @ X0 @ (k16_lattice3 @ X0 @ sk_C_1) @ 
% 0.49/0.70           (k16_lattice3 @ X0 @ sk_B))
% 0.49/0.70          | ~ (v10_lattices @ X0)
% 0.49/0.70          | ~ (v4_lattice3 @ X0)
% 0.49/0.70          | (v2_struct_0 @ X0)
% 0.49/0.70          | ~ (l3_lattices @ X0))),
% 0.49/0.70      inference('simplify', [status(thm)], ['90'])).
% 0.49/0.70  thf('92', plain,
% 0.49/0.70      ((~ (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C_1) @ 
% 0.49/0.70           (k16_lattice3 @ sk_A @ sk_B)))
% 0.49/0.70         <= (~
% 0.49/0.70             ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C_1) @ 
% 0.49/0.70               (k16_lattice3 @ sk_A @ sk_B))))),
% 0.49/0.70      inference('split', [status(esa)], ['53'])).
% 0.49/0.70  thf('93', plain,
% 0.49/0.70      (((~ (l3_lattices @ sk_A)
% 0.49/0.70         | (v2_struct_0 @ sk_A)
% 0.49/0.70         | ~ (v4_lattice3 @ sk_A)
% 0.49/0.70         | ~ (v10_lattices @ sk_A)))
% 0.49/0.70         <= (~
% 0.49/0.70             ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C_1) @ 
% 0.49/0.70               (k16_lattice3 @ sk_A @ sk_B))))),
% 0.49/0.70      inference('sup-', [status(thm)], ['91', '92'])).
% 0.49/0.70  thf('94', plain, ((l3_lattices @ sk_A)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('95', plain, ((v4_lattice3 @ sk_A)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('96', plain, ((v10_lattices @ sk_A)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('97', plain,
% 0.49/0.70      (((v2_struct_0 @ sk_A))
% 0.49/0.70         <= (~
% 0.49/0.70             ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C_1) @ 
% 0.49/0.70               (k16_lattice3 @ sk_A @ sk_B))))),
% 0.49/0.70      inference('demod', [status(thm)], ['93', '94', '95', '96'])).
% 0.49/0.70  thf('98', plain, (~ (v2_struct_0 @ sk_A)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('99', plain,
% 0.49/0.70      (((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C_1) @ 
% 0.49/0.70         (k16_lattice3 @ sk_A @ sk_B)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['97', '98'])).
% 0.49/0.70  thf('100', plain,
% 0.49/0.70      (~
% 0.49/0.70       ((r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 0.49/0.70         (k15_lattice3 @ sk_A @ sk_C_1))) | 
% 0.49/0.70       ~
% 0.49/0.70       ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C_1) @ 
% 0.49/0.70         (k16_lattice3 @ sk_A @ sk_B)))),
% 0.49/0.70      inference('split', [status(esa)], ['53'])).
% 0.49/0.70  thf('101', plain,
% 0.49/0.70      (~
% 0.49/0.70       ((r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 0.49/0.70         (k15_lattice3 @ sk_A @ sk_C_1)))),
% 0.49/0.70      inference('sat_resolution*', [status(thm)], ['99', '100'])).
% 0.49/0.70  thf('102', plain,
% 0.49/0.70      (~ (r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 0.49/0.70          (k15_lattice3 @ sk_A @ sk_C_1))),
% 0.49/0.70      inference('simpl_trail', [status(thm)], ['54', '101'])).
% 0.49/0.70  thf('103', plain,
% 0.49/0.70      ((~ (l3_lattices @ sk_A)
% 0.49/0.70        | (v2_struct_0 @ sk_A)
% 0.49/0.70        | ~ (v10_lattices @ sk_A)
% 0.49/0.70        | ~ (v4_lattice3 @ sk_A)
% 0.49/0.70        | ~ (v6_lattices @ sk_A)
% 0.49/0.70        | ~ (v8_lattices @ sk_A)
% 0.49/0.70        | ~ (v9_lattices @ sk_A))),
% 0.49/0.70      inference('sup-', [status(thm)], ['52', '102'])).
% 0.49/0.70  thf('104', plain, ((l3_lattices @ sk_A)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('105', plain, ((v10_lattices @ sk_A)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('106', plain, ((v4_lattice3 @ sk_A)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf(cc1_lattices, axiom,
% 0.49/0.70    (![A:$i]:
% 0.49/0.70     ( ( l3_lattices @ A ) =>
% 0.49/0.70       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.49/0.70         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.49/0.70           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.49/0.70           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.49/0.70  thf('107', plain,
% 0.49/0.70      (![X4 : $i]:
% 0.49/0.70         ((v2_struct_0 @ X4)
% 0.49/0.70          | ~ (v10_lattices @ X4)
% 0.49/0.70          | (v6_lattices @ X4)
% 0.49/0.70          | ~ (l3_lattices @ X4))),
% 0.49/0.70      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.49/0.70  thf('108', plain, (~ (v2_struct_0 @ sk_A)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('109', plain,
% 0.49/0.70      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.49/0.70      inference('sup-', [status(thm)], ['107', '108'])).
% 0.49/0.70  thf('110', plain, ((l3_lattices @ sk_A)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('111', plain, ((v10_lattices @ sk_A)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('112', plain, ((v6_lattices @ sk_A)),
% 0.49/0.70      inference('demod', [status(thm)], ['109', '110', '111'])).
% 0.49/0.70  thf('113', plain,
% 0.49/0.70      (![X4 : $i]:
% 0.49/0.70         ((v2_struct_0 @ X4)
% 0.49/0.70          | ~ (v10_lattices @ X4)
% 0.49/0.70          | (v8_lattices @ X4)
% 0.49/0.70          | ~ (l3_lattices @ X4))),
% 0.49/0.70      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.49/0.70  thf('114', plain, (~ (v2_struct_0 @ sk_A)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('115', plain,
% 0.49/0.70      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.49/0.70      inference('sup-', [status(thm)], ['113', '114'])).
% 0.49/0.70  thf('116', plain, ((l3_lattices @ sk_A)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('117', plain, ((v10_lattices @ sk_A)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('118', plain, ((v8_lattices @ sk_A)),
% 0.49/0.70      inference('demod', [status(thm)], ['115', '116', '117'])).
% 0.49/0.70  thf('119', plain,
% 0.49/0.70      (![X4 : $i]:
% 0.49/0.70         ((v2_struct_0 @ X4)
% 0.49/0.70          | ~ (v10_lattices @ X4)
% 0.49/0.70          | (v9_lattices @ X4)
% 0.49/0.70          | ~ (l3_lattices @ X4))),
% 0.49/0.70      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.49/0.70  thf('120', plain, (~ (v2_struct_0 @ sk_A)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('121', plain,
% 0.49/0.70      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.49/0.70      inference('sup-', [status(thm)], ['119', '120'])).
% 0.49/0.70  thf('122', plain, ((l3_lattices @ sk_A)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('123', plain, ((v10_lattices @ sk_A)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('124', plain, ((v9_lattices @ sk_A)),
% 0.49/0.70      inference('demod', [status(thm)], ['121', '122', '123'])).
% 0.49/0.70  thf('125', plain, ((v2_struct_0 @ sk_A)),
% 0.49/0.70      inference('demod', [status(thm)],
% 0.49/0.70                ['103', '104', '105', '106', '112', '118', '124'])).
% 0.49/0.70  thf('126', plain, ($false), inference('demod', [status(thm)], ['0', '125'])).
% 0.49/0.70  
% 0.49/0.70  % SZS output end Refutation
% 0.49/0.70  
% 0.49/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
