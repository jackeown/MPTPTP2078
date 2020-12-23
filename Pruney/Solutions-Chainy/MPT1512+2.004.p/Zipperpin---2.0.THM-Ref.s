%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uJn6Rb9AmY

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:33 EST 2020

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 275 expanded)
%              Number of leaves         :   38 (  94 expanded)
%              Depth                    :   22
%              Number of atoms          : 2413 (4678 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   20 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(r4_lattice3_type,type,(
    r4_lattice3: $i > $i > $i > $o )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(a_2_2_lattice3_type,type,(
    a_2_2_lattice3: $i > $i > $i )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(r3_lattice3_type,type,(
    r3_lattice3: $i > $i > $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

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
    ! [X26: $i,X27: $i] :
      ( ( ( k15_lattice3 @ X26 @ X27 )
        = ( k16_lattice3 @ X26 @ ( a_2_2_lattice3 @ X26 @ X27 ) ) )
      | ~ ( l3_lattices @ X26 )
      | ~ ( v4_lattice3 @ X26 )
      | ~ ( v10_lattices @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t37_lattice3])).

thf(dt_k15_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('3',plain,(
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

thf('4',plain,(
    ! [X13: $i,X14: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ( r2_hidden @ ( sk_D_1 @ X17 @ X13 @ X14 ) @ X17 )
      | ( r4_lattice3 @ X14 @ X13 @ X17 )
      | ~ ( l3_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_B @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('12',plain,(
    ! [X13: $i,X14: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X17 @ X13 @ X14 ) @ ( u1_struct_0 @ X14 ) )
      | ( r4_lattice3 @ X14 @ X13 @ X17 )
      | ~ ( l3_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( m1_subset_1 @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ( r3_lattices @ X29 @ X28 @ ( k15_lattice3 @ X29 @ X30 ) )
      | ~ ( r2_hidden @ X28 @ X30 )
      | ~ ( l3_lattices @ X29 )
      | ~ ( v4_lattice3 @ X29 )
      | ~ ( v10_lattices @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t38_lattice3])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X3 )
      | ( r3_lattices @ X0 @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X3 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r3_lattices @ X0 @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X3 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X3 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ sk_B )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ sk_B )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r3_lattices @ X0 @ ( sk_D_1 @ sk_B @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['10','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattices @ X0 @ ( sk_D_1 @ sk_B @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ sk_C_1 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

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

thf('21',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l3_lattices @ X6 )
      | ~ ( v9_lattices @ X6 )
      | ~ ( v8_lattices @ X6 )
      | ~ ( v6_lattices @ X6 )
      | ( v2_struct_0 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ( r1_lattices @ X6 @ X5 @ X7 )
      | ~ ( r3_lattices @ X6 @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r3_lattices @ X0 @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X3 )
      | ( r1_lattices @ X0 @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X3 )
      | ~ ( r3_lattices @ X0 @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X3 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ sk_B )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ sk_B )
      | ( r1_lattices @ X0 @ ( sk_D_1 @ sk_B @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ ( k15_lattice3 @ X0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ ( k15_lattice3 @ X0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( sk_D_1 @ sk_B @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ sk_C_1 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ sk_B )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r1_lattices @ X0 @ ( sk_D_1 @ sk_B @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ sk_C_1 ) )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ( r1_lattices @ X0 @ ( sk_D_1 @ sk_B @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ sk_C_1 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ sk_B )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) ),
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
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ sk_C_1 ) @ sk_B )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ sk_C_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ sk_C_1 ) @ sk_B )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

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

thf('35',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( l3_lattices @ X22 )
      | ~ ( v4_lattice3 @ X22 )
      | ~ ( v10_lattices @ X22 )
      | ( v2_struct_0 @ X22 )
      | ( r2_hidden @ X24 @ ( a_2_2_lattice3 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X22 ) )
      | ( X24 != X25 )
      | ~ ( r4_lattice3 @ X22 @ X25 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_2_lattice3])).

thf('36',plain,(
    ! [X22: $i,X23: $i,X25: $i] :
      ( ~ ( r4_lattice3 @ X22 @ X25 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X22 ) )
      | ( r2_hidden @ X25 @ ( a_2_2_lattice3 @ X22 @ X23 ) )
      | ( v2_struct_0 @ X22 )
      | ~ ( v10_lattices @ X22 )
      | ~ ( v4_lattice3 @ X22 )
      | ~ ( l3_lattices @ X22 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r2_hidden @ ( k15_lattice3 @ X0 @ X1 ) @ ( a_2_2_lattice3 @ X0 @ X2 ) )
      | ~ ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( k15_lattice3 @ X0 @ X1 ) @ ( a_2_2_lattice3 @ X0 @ X2 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( r2_hidden @ ( k15_lattice3 @ X0 @ sk_C_1 ) @ ( a_2_2_lattice3 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k15_lattice3 @ X0 @ sk_C_1 ) @ ( a_2_2_lattice3 @ X0 @ sk_B ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('42',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ( r3_lattices @ X29 @ ( k16_lattice3 @ X29 @ X30 ) @ X28 )
      | ~ ( r2_hidden @ X28 @ X30 )
      | ~ ( l3_lattices @ X29 )
      | ~ ( v4_lattice3 @ X29 )
      | ~ ( v10_lattices @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t38_lattice3])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r2_hidden @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ ( a_2_2_lattice3 @ X0 @ sk_B ) ) @ ( k15_lattice3 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['40','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ ( a_2_2_lattice3 @ X0 @ sk_B ) ) @ ( k15_lattice3 @ X0 @ sk_C_1 ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ sk_B ) @ ( k15_lattice3 @ X0 @ sk_C_1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ sk_B ) @ ( k15_lattice3 @ X0 @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ~ ( r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_C_1 ) )
    | ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C_1 ) @ ( k16_lattice3 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ~ ( r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_C_1 ) )
   <= ~ ( r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['49'])).

thf(dt_k16_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( m1_subset_1 @ ( k16_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('51',plain,(
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

thf('52',plain,(
    ! [X8: $i,X9: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ( r2_hidden @ ( sk_D @ X12 @ X8 @ X9 ) @ X12 )
      | ( r3_lattice3 @ X9 @ X8 @ X12 )
      | ~ ( l3_lattices @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ sk_B )
      | ( r2_hidden @ ( sk_D @ sk_B @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf('58',plain,(
    ! [X8: $i,X9: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ( m1_subset_1 @ ( sk_D @ X12 @ X8 @ X9 ) @ ( u1_struct_0 @ X9 ) )
      | ( r3_lattice3 @ X9 @ X8 @ X12 )
      | ~ ( l3_lattices @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ( m1_subset_1 @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ( r3_lattices @ X29 @ ( k16_lattice3 @ X29 @ X30 ) @ X28 )
      | ~ ( r2_hidden @ X28 @ X30 )
      | ~ ( l3_lattices @ X29 )
      | ~ ( v4_lattice3 @ X29 )
      | ~ ( v10_lattices @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t38_lattice3])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) @ X3 )
      | ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X3 ) @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X3 ) @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) @ X3 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ sk_B )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ sk_B )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ sk_C_1 ) @ ( sk_D @ sk_B @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ sk_C_1 ) @ ( sk_D @ sk_B @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('67',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf('68',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l3_lattices @ X6 )
      | ~ ( v9_lattices @ X6 )
      | ~ ( v8_lattices @ X6 )
      | ~ ( v6_lattices @ X6 )
      | ( v2_struct_0 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ( r1_lattices @ X6 @ X5 @ X7 )
      | ~ ( r3_lattices @ X6 @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X3 ) @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X3 ) @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X3 ) @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ~ ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X3 ) @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ sk_B )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ sk_B )
      | ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ sk_C_1 ) @ ( sk_D @ sk_B @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ sk_C_1 ) @ ( sk_D @ sk_B @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf('76',plain,(
    ! [X8: $i,X9: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( r1_lattices @ X9 @ X8 @ ( sk_D @ X12 @ X8 @ X9 ) )
      | ( r3_lattice3 @ X9 @ X8 @ X12 )
      | ~ ( l3_lattices @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ sk_C_1 ) @ sk_B )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ sk_C_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['74','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ sk_C_1 ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) ),
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

thf('82',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ( r3_lattices @ X32 @ X31 @ ( k16_lattice3 @ X32 @ X33 ) )
      | ~ ( r3_lattice3 @ X32 @ X31 @ X33 )
      | ~ ( l3_lattices @ X32 )
      | ~ ( v4_lattice3 @ X32 )
      | ~ ( v10_lattices @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t40_lattice3])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( k16_lattice3 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( k16_lattice3 @ X0 @ X2 ) )
      | ~ ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ sk_C_1 ) @ ( k16_lattice3 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['80','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ sk_C_1 ) @ ( k16_lattice3 @ X0 @ sk_B ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,
    ( ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C_1 ) @ ( k16_lattice3 @ sk_A @ sk_B ) )
   <= ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C_1 ) @ ( k16_lattice3 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['49'])).

thf('88',plain,
    ( ( ~ ( l3_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A ) )
   <= ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C_1 ) @ ( k16_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
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

thf('92',plain,(
    ! [X4: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( v10_lattices @ X4 )
      | ( v6_lattices @ X4 )
      | ~ ( l3_lattices @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('93',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,(
    ! [X4: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( v10_lattices @ X4 )
      | ( v8_lattices @ X4 )
      | ~ ( l3_lattices @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('99',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,(
    ! [X4: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( v10_lattices @ X4 )
      | ( v9_lattices @ X4 )
      | ~ ( l3_lattices @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('105',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C_1 ) @ ( k16_lattice3 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['88','89','90','91','97','103','109'])).

thf('111',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C_1 ) @ ( k16_lattice3 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ~ ( r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_C_1 ) )
    | ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C_1 ) @ ( k16_lattice3 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['49'])).

thf('114',plain,(
    ~ ( r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_C_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['112','113'])).

thf('115',plain,(
    ~ ( r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_C_1 ) ) ),
    inference(simpl_trail,[status(thm)],['50','114'])).

thf('116',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v6_lattices @ sk_A )
    | ~ ( v8_lattices @ sk_A )
    | ~ ( v9_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['48','115'])).

thf('117',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('121',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('122',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('123',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['116','117','118','119','120','121','122'])).

thf('124',plain,(
    $false ),
    inference(demod,[status(thm)],['0','123'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uJn6Rb9AmY
% 0.13/0.37  % Computer   : n017.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 16:15:02 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.22/0.38  % Running in FO mode
% 0.74/0.95  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.74/0.95  % Solved by: fo/fo7.sh
% 0.74/0.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.74/0.95  % done 401 iterations in 0.467s
% 0.74/0.95  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.74/0.95  % SZS output start Refutation
% 0.74/0.95  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.74/0.95  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 0.74/0.95  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.74/0.95  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.74/0.95  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.74/0.95  thf(sk_A_type, type, sk_A: $i).
% 0.74/0.95  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 0.74/0.95  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.74/0.95  thf(sk_B_type, type, sk_B: $i).
% 0.74/0.95  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.74/0.95  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.74/0.95  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.74/0.95  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.74/0.95  thf(r4_lattice3_type, type, r4_lattice3: $i > $i > $i > $o).
% 0.74/0.95  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 0.74/0.95  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.74/0.95  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.74/0.95  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.74/0.95  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 0.74/0.95  thf(a_2_2_lattice3_type, type, a_2_2_lattice3: $i > $i > $i).
% 0.74/0.95  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.74/0.95  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.74/0.95  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.74/0.95  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.74/0.95  thf(r3_lattice3_type, type, r3_lattice3: $i > $i > $i > $o).
% 0.74/0.95  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.74/0.95  thf(t46_lattice3, conjecture,
% 0.74/0.95    (![A:$i]:
% 0.74/0.95     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.74/0.95         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.74/0.95       ( ![B:$i,C:$i]:
% 0.74/0.95         ( ( r1_tarski @ B @ C ) =>
% 0.74/0.95           ( ( r3_lattices @
% 0.74/0.95               A @ ( k15_lattice3 @ A @ B ) @ ( k15_lattice3 @ A @ C ) ) & 
% 0.74/0.95             ( r3_lattices @
% 0.74/0.95               A @ ( k16_lattice3 @ A @ C ) @ ( k16_lattice3 @ A @ B ) ) ) ) ) ))).
% 0.74/0.95  thf(zf_stmt_0, negated_conjecture,
% 0.74/0.95    (~( ![A:$i]:
% 0.74/0.95        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.74/0.95            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.74/0.95          ( ![B:$i,C:$i]:
% 0.74/0.95            ( ( r1_tarski @ B @ C ) =>
% 0.74/0.95              ( ( r3_lattices @
% 0.74/0.95                  A @ ( k15_lattice3 @ A @ B ) @ ( k15_lattice3 @ A @ C ) ) & 
% 0.74/0.95                ( r3_lattices @
% 0.74/0.95                  A @ ( k16_lattice3 @ A @ C ) @ ( k16_lattice3 @ A @ B ) ) ) ) ) ) )),
% 0.74/0.95    inference('cnf.neg', [status(esa)], [t46_lattice3])).
% 0.74/0.95  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf(t37_lattice3, axiom,
% 0.74/0.95    (![A:$i]:
% 0.74/0.95     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.74/0.95         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.74/0.95       ( ![B:$i]:
% 0.74/0.95         ( ( k15_lattice3 @ A @ B ) =
% 0.74/0.95           ( k16_lattice3 @ A @ ( a_2_2_lattice3 @ A @ B ) ) ) ) ))).
% 0.74/0.95  thf('1', plain,
% 0.74/0.95      (![X26 : $i, X27 : $i]:
% 0.74/0.95         (((k15_lattice3 @ X26 @ X27)
% 0.74/0.95            = (k16_lattice3 @ X26 @ (a_2_2_lattice3 @ X26 @ X27)))
% 0.74/0.95          | ~ (l3_lattices @ X26)
% 0.74/0.95          | ~ (v4_lattice3 @ X26)
% 0.74/0.95          | ~ (v10_lattices @ X26)
% 0.74/0.95          | (v2_struct_0 @ X26))),
% 0.74/0.95      inference('cnf', [status(esa)], [t37_lattice3])).
% 0.74/0.95  thf(dt_k15_lattice3, axiom,
% 0.74/0.95    (![A:$i,B:$i]:
% 0.74/0.95     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.74/0.95       ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.74/0.95  thf('2', plain,
% 0.74/0.95      (![X18 : $i, X19 : $i]:
% 0.74/0.95         (~ (l3_lattices @ X18)
% 0.74/0.95          | (v2_struct_0 @ X18)
% 0.74/0.95          | (m1_subset_1 @ (k15_lattice3 @ X18 @ X19) @ (u1_struct_0 @ X18)))),
% 0.74/0.95      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.74/0.95  thf('3', plain,
% 0.74/0.95      (![X18 : $i, X19 : $i]:
% 0.74/0.95         (~ (l3_lattices @ X18)
% 0.74/0.95          | (v2_struct_0 @ X18)
% 0.74/0.95          | (m1_subset_1 @ (k15_lattice3 @ X18 @ X19) @ (u1_struct_0 @ X18)))),
% 0.74/0.95      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.74/0.95  thf(d17_lattice3, axiom,
% 0.74/0.95    (![A:$i]:
% 0.74/0.95     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.74/0.95       ( ![B:$i]:
% 0.74/0.95         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.74/0.95           ( ![C:$i]:
% 0.74/0.95             ( ( r4_lattice3 @ A @ B @ C ) <=>
% 0.74/0.95               ( ![D:$i]:
% 0.74/0.95                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.74/0.95                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ))).
% 0.74/0.95  thf('4', plain,
% 0.74/0.95      (![X13 : $i, X14 : $i, X17 : $i]:
% 0.74/0.95         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.74/0.95          | (r2_hidden @ (sk_D_1 @ X17 @ X13 @ X14) @ X17)
% 0.74/0.95          | (r4_lattice3 @ X14 @ X13 @ X17)
% 0.74/0.95          | ~ (l3_lattices @ X14)
% 0.74/0.95          | (v2_struct_0 @ X14))),
% 0.74/0.95      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.74/0.95  thf('5', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.95         ((v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.74/0.95          | (r2_hidden @ (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X2))),
% 0.74/0.95      inference('sup-', [status(thm)], ['3', '4'])).
% 0.74/0.95  thf('6', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.95         ((r2_hidden @ (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X2)
% 0.74/0.95          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0))),
% 0.74/0.95      inference('simplify', [status(thm)], ['5'])).
% 0.74/0.95  thf('7', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf(d3_tarski, axiom,
% 0.74/0.95    (![A:$i,B:$i]:
% 0.74/0.95     ( ( r1_tarski @ A @ B ) <=>
% 0.74/0.95       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.74/0.95  thf('8', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.95         (~ (r2_hidden @ X0 @ X1)
% 0.74/0.95          | (r2_hidden @ X0 @ X2)
% 0.74/0.95          | ~ (r1_tarski @ X1 @ X2))),
% 0.74/0.95      inference('cnf', [status(esa)], [d3_tarski])).
% 0.74/0.95  thf('9', plain,
% 0.74/0.95      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.74/0.95      inference('sup-', [status(thm)], ['7', '8'])).
% 0.74/0.95  thf('10', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i]:
% 0.74/0.95         ((v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ sk_B)
% 0.74/0.95          | (r2_hidden @ (sk_D_1 @ sk_B @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.74/0.95             sk_C_1))),
% 0.74/0.95      inference('sup-', [status(thm)], ['6', '9'])).
% 0.74/0.95  thf('11', plain,
% 0.74/0.95      (![X18 : $i, X19 : $i]:
% 0.74/0.95         (~ (l3_lattices @ X18)
% 0.74/0.95          | (v2_struct_0 @ X18)
% 0.74/0.95          | (m1_subset_1 @ (k15_lattice3 @ X18 @ X19) @ (u1_struct_0 @ X18)))),
% 0.74/0.95      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.74/0.95  thf('12', plain,
% 0.74/0.95      (![X13 : $i, X14 : $i, X17 : $i]:
% 0.74/0.95         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.74/0.95          | (m1_subset_1 @ (sk_D_1 @ X17 @ X13 @ X14) @ (u1_struct_0 @ X14))
% 0.74/0.95          | (r4_lattice3 @ X14 @ X13 @ X17)
% 0.74/0.95          | ~ (l3_lattices @ X14)
% 0.74/0.95          | (v2_struct_0 @ X14))),
% 0.74/0.95      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.74/0.95  thf('13', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.95         ((v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.74/0.95          | (m1_subset_1 @ (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.74/0.95             (u1_struct_0 @ X0)))),
% 0.74/0.95      inference('sup-', [status(thm)], ['11', '12'])).
% 0.74/0.95  thf('14', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.95         ((m1_subset_1 @ (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.74/0.95           (u1_struct_0 @ X0))
% 0.74/0.95          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0))),
% 0.74/0.95      inference('simplify', [status(thm)], ['13'])).
% 0.74/0.95  thf(t38_lattice3, axiom,
% 0.74/0.95    (![A:$i]:
% 0.74/0.95     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.74/0.95         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.74/0.95       ( ![B:$i]:
% 0.74/0.95         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.74/0.95           ( ![C:$i]:
% 0.74/0.95             ( ( r2_hidden @ B @ C ) =>
% 0.74/0.95               ( ( r3_lattices @ A @ B @ ( k15_lattice3 @ A @ C ) ) & 
% 0.74/0.95                 ( r3_lattices @ A @ ( k16_lattice3 @ A @ C ) @ B ) ) ) ) ) ) ))).
% 0.74/0.95  thf('15', plain,
% 0.74/0.95      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.74/0.95         (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X29))
% 0.74/0.95          | (r3_lattices @ X29 @ X28 @ (k15_lattice3 @ X29 @ X30))
% 0.74/0.95          | ~ (r2_hidden @ X28 @ X30)
% 0.74/0.95          | ~ (l3_lattices @ X29)
% 0.74/0.95          | ~ (v4_lattice3 @ X29)
% 0.74/0.95          | ~ (v10_lattices @ X29)
% 0.74/0.95          | (v2_struct_0 @ X29))),
% 0.74/0.95      inference('cnf', [status(esa)], [t38_lattice3])).
% 0.74/0.95  thf('16', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.74/0.95         ((v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.74/0.95          | (v2_struct_0 @ X0)
% 0.74/0.95          | ~ (v10_lattices @ X0)
% 0.74/0.95          | ~ (v4_lattice3 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | ~ (r2_hidden @ (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X3)
% 0.74/0.95          | (r3_lattices @ X0 @ 
% 0.74/0.95             (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.74/0.95             (k15_lattice3 @ X0 @ X3)))),
% 0.74/0.95      inference('sup-', [status(thm)], ['14', '15'])).
% 0.74/0.95  thf('17', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.74/0.95         ((r3_lattices @ X0 @ (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.74/0.95           (k15_lattice3 @ X0 @ X3))
% 0.74/0.95          | ~ (r2_hidden @ (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X3)
% 0.74/0.95          | ~ (v4_lattice3 @ X0)
% 0.74/0.95          | ~ (v10_lattices @ X0)
% 0.74/0.95          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0))),
% 0.74/0.95      inference('simplify', [status(thm)], ['16'])).
% 0.74/0.95  thf('18', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i]:
% 0.74/0.95         ((r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ sk_B)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ sk_B)
% 0.74/0.95          | ~ (v10_lattices @ X0)
% 0.74/0.95          | ~ (v4_lattice3 @ X0)
% 0.74/0.95          | (r3_lattices @ X0 @ 
% 0.74/0.95             (sk_D_1 @ sk_B @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.74/0.95             (k15_lattice3 @ X0 @ sk_C_1)))),
% 0.74/0.95      inference('sup-', [status(thm)], ['10', '17'])).
% 0.74/0.95  thf('19', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i]:
% 0.74/0.95         ((r3_lattices @ X0 @ 
% 0.74/0.95           (sk_D_1 @ sk_B @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.74/0.95           (k15_lattice3 @ X0 @ sk_C_1))
% 0.74/0.95          | ~ (v4_lattice3 @ X0)
% 0.74/0.95          | ~ (v10_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ sk_B))),
% 0.74/0.95      inference('simplify', [status(thm)], ['18'])).
% 0.74/0.95  thf('20', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.95         ((m1_subset_1 @ (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.74/0.95           (u1_struct_0 @ X0))
% 0.74/0.95          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0))),
% 0.74/0.95      inference('simplify', [status(thm)], ['13'])).
% 0.74/0.95  thf(redefinition_r3_lattices, axiom,
% 0.74/0.95    (![A:$i,B:$i,C:$i]:
% 0.74/0.95     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.74/0.95         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 0.74/0.95         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.74/0.95         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.74/0.95       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 0.74/0.95  thf('21', plain,
% 0.74/0.95      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.74/0.95         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 0.74/0.95          | ~ (l3_lattices @ X6)
% 0.74/0.95          | ~ (v9_lattices @ X6)
% 0.74/0.95          | ~ (v8_lattices @ X6)
% 0.74/0.95          | ~ (v6_lattices @ X6)
% 0.74/0.95          | (v2_struct_0 @ X6)
% 0.74/0.95          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 0.74/0.95          | (r1_lattices @ X6 @ X5 @ X7)
% 0.74/0.95          | ~ (r3_lattices @ X6 @ X5 @ X7))),
% 0.74/0.95      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.74/0.95  thf('22', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.74/0.95         ((v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.74/0.95          | ~ (r3_lattices @ X0 @ 
% 0.74/0.95               (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X3)
% 0.74/0.95          | (r1_lattices @ X0 @ 
% 0.74/0.95             (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X3)
% 0.74/0.95          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X0))
% 0.74/0.95          | (v2_struct_0 @ X0)
% 0.74/0.95          | ~ (v6_lattices @ X0)
% 0.74/0.95          | ~ (v8_lattices @ X0)
% 0.74/0.95          | ~ (v9_lattices @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0))),
% 0.74/0.95      inference('sup-', [status(thm)], ['20', '21'])).
% 0.74/0.95  thf('23', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.74/0.95         (~ (v9_lattices @ X0)
% 0.74/0.95          | ~ (v8_lattices @ X0)
% 0.74/0.95          | ~ (v6_lattices @ X0)
% 0.74/0.95          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X0))
% 0.74/0.95          | (r1_lattices @ X0 @ 
% 0.74/0.95             (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X3)
% 0.74/0.95          | ~ (r3_lattices @ X0 @ 
% 0.74/0.95               (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X3)
% 0.74/0.95          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0))),
% 0.74/0.95      inference('simplify', [status(thm)], ['22'])).
% 0.74/0.95  thf('24', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i]:
% 0.74/0.95         ((r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ sk_B)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0)
% 0.74/0.95          | ~ (v10_lattices @ X0)
% 0.74/0.95          | ~ (v4_lattice3 @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ sk_B)
% 0.74/0.95          | (r1_lattices @ X0 @ 
% 0.74/0.95             (sk_D_1 @ sk_B @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.74/0.95             (k15_lattice3 @ X0 @ sk_C_1))
% 0.74/0.95          | ~ (m1_subset_1 @ (k15_lattice3 @ X0 @ sk_C_1) @ (u1_struct_0 @ X0))
% 0.74/0.95          | ~ (v6_lattices @ X0)
% 0.74/0.95          | ~ (v8_lattices @ X0)
% 0.74/0.95          | ~ (v9_lattices @ X0))),
% 0.74/0.95      inference('sup-', [status(thm)], ['19', '23'])).
% 0.74/0.95  thf('25', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i]:
% 0.74/0.95         (~ (v9_lattices @ X0)
% 0.74/0.95          | ~ (v8_lattices @ X0)
% 0.74/0.95          | ~ (v6_lattices @ X0)
% 0.74/0.95          | ~ (m1_subset_1 @ (k15_lattice3 @ X0 @ sk_C_1) @ (u1_struct_0 @ X0))
% 0.74/0.95          | (r1_lattices @ X0 @ 
% 0.74/0.95             (sk_D_1 @ sk_B @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.74/0.95             (k15_lattice3 @ X0 @ sk_C_1))
% 0.74/0.95          | ~ (v4_lattice3 @ X0)
% 0.74/0.95          | ~ (v10_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ sk_B))),
% 0.74/0.95      inference('simplify', [status(thm)], ['24'])).
% 0.74/0.95  thf('26', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i]:
% 0.74/0.95         ((v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ sk_B)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0)
% 0.74/0.95          | ~ (v10_lattices @ X0)
% 0.74/0.95          | ~ (v4_lattice3 @ X0)
% 0.74/0.95          | (r1_lattices @ X0 @ 
% 0.74/0.95             (sk_D_1 @ sk_B @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.74/0.95             (k15_lattice3 @ X0 @ sk_C_1))
% 0.74/0.95          | ~ (v6_lattices @ X0)
% 0.74/0.95          | ~ (v8_lattices @ X0)
% 0.74/0.95          | ~ (v9_lattices @ X0))),
% 0.74/0.95      inference('sup-', [status(thm)], ['2', '25'])).
% 0.74/0.95  thf('27', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i]:
% 0.74/0.95         (~ (v9_lattices @ X0)
% 0.74/0.95          | ~ (v8_lattices @ X0)
% 0.74/0.95          | ~ (v6_lattices @ X0)
% 0.74/0.95          | (r1_lattices @ X0 @ 
% 0.74/0.95             (sk_D_1 @ sk_B @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.74/0.95             (k15_lattice3 @ X0 @ sk_C_1))
% 0.74/0.95          | ~ (v4_lattice3 @ X0)
% 0.74/0.95          | ~ (v10_lattices @ X0)
% 0.74/0.95          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ sk_B)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0))),
% 0.74/0.95      inference('simplify', [status(thm)], ['26'])).
% 0.74/0.95  thf('28', plain,
% 0.74/0.95      (![X18 : $i, X19 : $i]:
% 0.74/0.95         (~ (l3_lattices @ X18)
% 0.74/0.95          | (v2_struct_0 @ X18)
% 0.74/0.95          | (m1_subset_1 @ (k15_lattice3 @ X18 @ X19) @ (u1_struct_0 @ X18)))),
% 0.74/0.95      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.74/0.95  thf('29', plain,
% 0.74/0.95      (![X13 : $i, X14 : $i, X17 : $i]:
% 0.74/0.95         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.74/0.95          | ~ (r1_lattices @ X14 @ (sk_D_1 @ X17 @ X13 @ X14) @ X13)
% 0.74/0.95          | (r4_lattice3 @ X14 @ X13 @ X17)
% 0.74/0.95          | ~ (l3_lattices @ X14)
% 0.74/0.95          | (v2_struct_0 @ X14))),
% 0.74/0.95      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.74/0.95  thf('30', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.95         ((v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.74/0.95          | ~ (r1_lattices @ X0 @ 
% 0.74/0.95               (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.74/0.95               (k15_lattice3 @ X0 @ X1)))),
% 0.74/0.95      inference('sup-', [status(thm)], ['28', '29'])).
% 0.74/0.95  thf('31', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.95         (~ (r1_lattices @ X0 @ 
% 0.74/0.95             (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.74/0.95             (k15_lattice3 @ X0 @ X1))
% 0.74/0.95          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0))),
% 0.74/0.95      inference('simplify', [status(thm)], ['30'])).
% 0.74/0.95  thf('32', plain,
% 0.74/0.95      (![X0 : $i]:
% 0.74/0.95         ((v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ sk_C_1) @ sk_B)
% 0.74/0.95          | ~ (v10_lattices @ X0)
% 0.74/0.95          | ~ (v4_lattice3 @ X0)
% 0.74/0.95          | ~ (v6_lattices @ X0)
% 0.74/0.95          | ~ (v8_lattices @ X0)
% 0.74/0.95          | ~ (v9_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ sk_C_1) @ sk_B))),
% 0.74/0.95      inference('sup-', [status(thm)], ['27', '31'])).
% 0.74/0.95  thf('33', plain,
% 0.74/0.95      (![X0 : $i]:
% 0.74/0.95         (~ (v9_lattices @ X0)
% 0.74/0.95          | ~ (v8_lattices @ X0)
% 0.74/0.95          | ~ (v6_lattices @ X0)
% 0.74/0.95          | ~ (v4_lattice3 @ X0)
% 0.74/0.95          | ~ (v10_lattices @ X0)
% 0.74/0.95          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ sk_C_1) @ sk_B)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0))),
% 0.74/0.95      inference('simplify', [status(thm)], ['32'])).
% 0.74/0.95  thf('34', plain,
% 0.74/0.95      (![X18 : $i, X19 : $i]:
% 0.74/0.95         (~ (l3_lattices @ X18)
% 0.74/0.95          | (v2_struct_0 @ X18)
% 0.74/0.95          | (m1_subset_1 @ (k15_lattice3 @ X18 @ X19) @ (u1_struct_0 @ X18)))),
% 0.74/0.95      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.74/0.95  thf(fraenkel_a_2_2_lattice3, axiom,
% 0.74/0.95    (![A:$i,B:$i,C:$i]:
% 0.74/0.95     ( ( ( ~( v2_struct_0 @ B ) ) & ( v10_lattices @ B ) & 
% 0.74/0.95         ( v4_lattice3 @ B ) & ( l3_lattices @ B ) ) =>
% 0.74/0.95       ( ( r2_hidden @ A @ ( a_2_2_lattice3 @ B @ C ) ) <=>
% 0.74/0.95         ( ?[D:$i]:
% 0.74/0.95           ( ( r4_lattice3 @ B @ D @ C ) & ( ( A ) = ( D ) ) & 
% 0.74/0.95             ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.74/0.95  thf('35', plain,
% 0.74/0.95      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.74/0.95         (~ (l3_lattices @ X22)
% 0.74/0.95          | ~ (v4_lattice3 @ X22)
% 0.74/0.95          | ~ (v10_lattices @ X22)
% 0.74/0.95          | (v2_struct_0 @ X22)
% 0.74/0.95          | (r2_hidden @ X24 @ (a_2_2_lattice3 @ X22 @ X23))
% 0.74/0.95          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X22))
% 0.74/0.95          | ((X24) != (X25))
% 0.74/0.95          | ~ (r4_lattice3 @ X22 @ X25 @ X23))),
% 0.74/0.95      inference('cnf', [status(esa)], [fraenkel_a_2_2_lattice3])).
% 0.74/0.95  thf('36', plain,
% 0.74/0.95      (![X22 : $i, X23 : $i, X25 : $i]:
% 0.74/0.95         (~ (r4_lattice3 @ X22 @ X25 @ X23)
% 0.74/0.95          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X22))
% 0.74/0.95          | (r2_hidden @ X25 @ (a_2_2_lattice3 @ X22 @ X23))
% 0.74/0.95          | (v2_struct_0 @ X22)
% 0.74/0.95          | ~ (v10_lattices @ X22)
% 0.74/0.95          | ~ (v4_lattice3 @ X22)
% 0.74/0.95          | ~ (l3_lattices @ X22))),
% 0.74/0.95      inference('simplify', [status(thm)], ['35'])).
% 0.74/0.95  thf('37', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.95         ((v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | ~ (v4_lattice3 @ X0)
% 0.74/0.95          | ~ (v10_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0)
% 0.74/0.95          | (r2_hidden @ (k15_lattice3 @ X0 @ X1) @ (a_2_2_lattice3 @ X0 @ X2))
% 0.74/0.95          | ~ (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))),
% 0.74/0.95      inference('sup-', [status(thm)], ['34', '36'])).
% 0.74/0.95  thf('38', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.95         (~ (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.74/0.95          | (r2_hidden @ (k15_lattice3 @ X0 @ X1) @ (a_2_2_lattice3 @ X0 @ X2))
% 0.74/0.95          | ~ (v10_lattices @ X0)
% 0.74/0.95          | ~ (v4_lattice3 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0))),
% 0.74/0.95      inference('simplify', [status(thm)], ['37'])).
% 0.74/0.95  thf('39', plain,
% 0.74/0.95      (![X0 : $i]:
% 0.74/0.95         ((v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | ~ (v10_lattices @ X0)
% 0.74/0.95          | ~ (v4_lattice3 @ X0)
% 0.74/0.95          | ~ (v6_lattices @ X0)
% 0.74/0.95          | ~ (v8_lattices @ X0)
% 0.74/0.95          | ~ (v9_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | ~ (v4_lattice3 @ X0)
% 0.74/0.95          | ~ (v10_lattices @ X0)
% 0.74/0.95          | (r2_hidden @ (k15_lattice3 @ X0 @ sk_C_1) @ 
% 0.74/0.95             (a_2_2_lattice3 @ X0 @ sk_B)))),
% 0.74/0.95      inference('sup-', [status(thm)], ['33', '38'])).
% 0.74/0.95  thf('40', plain,
% 0.74/0.95      (![X0 : $i]:
% 0.74/0.95         ((r2_hidden @ (k15_lattice3 @ X0 @ sk_C_1) @ 
% 0.74/0.95           (a_2_2_lattice3 @ X0 @ sk_B))
% 0.74/0.95          | ~ (v9_lattices @ X0)
% 0.74/0.95          | ~ (v8_lattices @ X0)
% 0.74/0.95          | ~ (v6_lattices @ X0)
% 0.74/0.95          | ~ (v4_lattice3 @ X0)
% 0.74/0.95          | ~ (v10_lattices @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0))),
% 0.74/0.95      inference('simplify', [status(thm)], ['39'])).
% 0.74/0.95  thf('41', plain,
% 0.74/0.95      (![X18 : $i, X19 : $i]:
% 0.74/0.95         (~ (l3_lattices @ X18)
% 0.74/0.95          | (v2_struct_0 @ X18)
% 0.74/0.95          | (m1_subset_1 @ (k15_lattice3 @ X18 @ X19) @ (u1_struct_0 @ X18)))),
% 0.74/0.95      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.74/0.95  thf('42', plain,
% 0.74/0.95      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.74/0.95         (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X29))
% 0.74/0.95          | (r3_lattices @ X29 @ (k16_lattice3 @ X29 @ X30) @ X28)
% 0.74/0.95          | ~ (r2_hidden @ X28 @ X30)
% 0.74/0.95          | ~ (l3_lattices @ X29)
% 0.74/0.95          | ~ (v4_lattice3 @ X29)
% 0.74/0.95          | ~ (v10_lattices @ X29)
% 0.74/0.95          | (v2_struct_0 @ X29))),
% 0.74/0.95      inference('cnf', [status(esa)], [t38_lattice3])).
% 0.74/0.95  thf('43', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.95         ((v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0)
% 0.74/0.95          | ~ (v10_lattices @ X0)
% 0.74/0.95          | ~ (v4_lattice3 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | ~ (r2_hidden @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.74/0.95          | (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X2) @ 
% 0.74/0.95             (k15_lattice3 @ X0 @ X1)))),
% 0.74/0.95      inference('sup-', [status(thm)], ['41', '42'])).
% 0.74/0.95  thf('44', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.95         ((r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X2) @ 
% 0.74/0.95           (k15_lattice3 @ X0 @ X1))
% 0.74/0.95          | ~ (r2_hidden @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.74/0.95          | ~ (v4_lattice3 @ X0)
% 0.74/0.95          | ~ (v10_lattices @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0))),
% 0.74/0.95      inference('simplify', [status(thm)], ['43'])).
% 0.74/0.95  thf('45', plain,
% 0.74/0.95      (![X0 : $i]:
% 0.74/0.95         ((v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | ~ (v10_lattices @ X0)
% 0.74/0.95          | ~ (v4_lattice3 @ X0)
% 0.74/0.95          | ~ (v6_lattices @ X0)
% 0.74/0.95          | ~ (v8_lattices @ X0)
% 0.74/0.95          | ~ (v9_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | ~ (v10_lattices @ X0)
% 0.74/0.95          | ~ (v4_lattice3 @ X0)
% 0.74/0.95          | (r3_lattices @ X0 @ 
% 0.74/0.95             (k16_lattice3 @ X0 @ (a_2_2_lattice3 @ X0 @ sk_B)) @ 
% 0.74/0.95             (k15_lattice3 @ X0 @ sk_C_1)))),
% 0.74/0.95      inference('sup-', [status(thm)], ['40', '44'])).
% 0.74/0.95  thf('46', plain,
% 0.74/0.95      (![X0 : $i]:
% 0.74/0.95         ((r3_lattices @ X0 @ 
% 0.74/0.95           (k16_lattice3 @ X0 @ (a_2_2_lattice3 @ X0 @ sk_B)) @ 
% 0.74/0.95           (k15_lattice3 @ X0 @ sk_C_1))
% 0.74/0.95          | ~ (v9_lattices @ X0)
% 0.74/0.95          | ~ (v8_lattices @ X0)
% 0.74/0.95          | ~ (v6_lattices @ X0)
% 0.74/0.95          | ~ (v4_lattice3 @ X0)
% 0.74/0.95          | ~ (v10_lattices @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0))),
% 0.74/0.95      inference('simplify', [status(thm)], ['45'])).
% 0.74/0.95  thf('47', plain,
% 0.74/0.95      (![X0 : $i]:
% 0.74/0.95         ((r3_lattices @ X0 @ (k15_lattice3 @ X0 @ sk_B) @ 
% 0.74/0.95           (k15_lattice3 @ X0 @ sk_C_1))
% 0.74/0.95          | (v2_struct_0 @ X0)
% 0.74/0.95          | ~ (v10_lattices @ X0)
% 0.74/0.95          | ~ (v4_lattice3 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | ~ (v10_lattices @ X0)
% 0.74/0.95          | ~ (v4_lattice3 @ X0)
% 0.74/0.95          | ~ (v6_lattices @ X0)
% 0.74/0.95          | ~ (v8_lattices @ X0)
% 0.74/0.95          | ~ (v9_lattices @ X0))),
% 0.74/0.95      inference('sup+', [status(thm)], ['1', '46'])).
% 0.74/0.95  thf('48', plain,
% 0.74/0.95      (![X0 : $i]:
% 0.74/0.95         (~ (v9_lattices @ X0)
% 0.74/0.95          | ~ (v8_lattices @ X0)
% 0.74/0.95          | ~ (v6_lattices @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | ~ (v4_lattice3 @ X0)
% 0.74/0.95          | ~ (v10_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0)
% 0.74/0.95          | (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ sk_B) @ 
% 0.74/0.95             (k15_lattice3 @ X0 @ sk_C_1)))),
% 0.74/0.95      inference('simplify', [status(thm)], ['47'])).
% 0.74/0.95  thf('49', plain,
% 0.74/0.95      ((~ (r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 0.74/0.95           (k15_lattice3 @ sk_A @ sk_C_1))
% 0.74/0.95        | ~ (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C_1) @ 
% 0.74/0.95             (k16_lattice3 @ sk_A @ sk_B)))),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('50', plain,
% 0.74/0.95      ((~ (r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 0.74/0.95           (k15_lattice3 @ sk_A @ sk_C_1)))
% 0.74/0.95         <= (~
% 0.74/0.95             ((r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 0.74/0.95               (k15_lattice3 @ sk_A @ sk_C_1))))),
% 0.74/0.95      inference('split', [status(esa)], ['49'])).
% 0.74/0.95  thf(dt_k16_lattice3, axiom,
% 0.74/0.95    (![A:$i,B:$i]:
% 0.74/0.95     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.74/0.95       ( m1_subset_1 @ ( k16_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.74/0.95  thf('51', plain,
% 0.74/0.95      (![X20 : $i, X21 : $i]:
% 0.74/0.95         (~ (l3_lattices @ X20)
% 0.74/0.95          | (v2_struct_0 @ X20)
% 0.74/0.95          | (m1_subset_1 @ (k16_lattice3 @ X20 @ X21) @ (u1_struct_0 @ X20)))),
% 0.74/0.95      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.74/0.95  thf(d16_lattice3, axiom,
% 0.74/0.95    (![A:$i]:
% 0.74/0.95     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.74/0.95       ( ![B:$i]:
% 0.74/0.95         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.74/0.95           ( ![C:$i]:
% 0.74/0.95             ( ( r3_lattice3 @ A @ B @ C ) <=>
% 0.74/0.95               ( ![D:$i]:
% 0.74/0.95                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.74/0.95                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 0.74/0.95  thf('52', plain,
% 0.74/0.95      (![X8 : $i, X9 : $i, X12 : $i]:
% 0.74/0.95         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.74/0.95          | (r2_hidden @ (sk_D @ X12 @ X8 @ X9) @ X12)
% 0.74/0.95          | (r3_lattice3 @ X9 @ X8 @ X12)
% 0.74/0.95          | ~ (l3_lattices @ X9)
% 0.74/0.95          | (v2_struct_0 @ X9))),
% 0.74/0.95      inference('cnf', [status(esa)], [d16_lattice3])).
% 0.74/0.95  thf('53', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.95         ((v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.74/0.95          | (r2_hidden @ (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0) @ X2))),
% 0.74/0.95      inference('sup-', [status(thm)], ['51', '52'])).
% 0.74/0.95  thf('54', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.95         ((r2_hidden @ (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0) @ X2)
% 0.74/0.95          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0))),
% 0.74/0.95      inference('simplify', [status(thm)], ['53'])).
% 0.74/0.95  thf('55', plain,
% 0.74/0.95      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.74/0.95      inference('sup-', [status(thm)], ['7', '8'])).
% 0.74/0.95  thf('56', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i]:
% 0.74/0.95         ((v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ sk_B)
% 0.74/0.95          | (r2_hidden @ (sk_D @ sk_B @ (k16_lattice3 @ X0 @ X1) @ X0) @ sk_C_1))),
% 0.74/0.95      inference('sup-', [status(thm)], ['54', '55'])).
% 0.74/0.95  thf('57', plain,
% 0.74/0.95      (![X20 : $i, X21 : $i]:
% 0.74/0.95         (~ (l3_lattices @ X20)
% 0.74/0.95          | (v2_struct_0 @ X20)
% 0.74/0.95          | (m1_subset_1 @ (k16_lattice3 @ X20 @ X21) @ (u1_struct_0 @ X20)))),
% 0.74/0.95      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.74/0.95  thf('58', plain,
% 0.74/0.95      (![X8 : $i, X9 : $i, X12 : $i]:
% 0.74/0.95         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.74/0.95          | (m1_subset_1 @ (sk_D @ X12 @ X8 @ X9) @ (u1_struct_0 @ X9))
% 0.74/0.95          | (r3_lattice3 @ X9 @ X8 @ X12)
% 0.74/0.95          | ~ (l3_lattices @ X9)
% 0.74/0.95          | (v2_struct_0 @ X9))),
% 0.74/0.95      inference('cnf', [status(esa)], [d16_lattice3])).
% 0.74/0.95  thf('59', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.95         ((v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.74/0.95          | (m1_subset_1 @ (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0) @ 
% 0.74/0.95             (u1_struct_0 @ X0)))),
% 0.74/0.95      inference('sup-', [status(thm)], ['57', '58'])).
% 0.74/0.95  thf('60', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.95         ((m1_subset_1 @ (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0) @ 
% 0.74/0.95           (u1_struct_0 @ X0))
% 0.74/0.95          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0))),
% 0.74/0.95      inference('simplify', [status(thm)], ['59'])).
% 0.74/0.95  thf('61', plain,
% 0.74/0.95      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.74/0.95         (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X29))
% 0.74/0.95          | (r3_lattices @ X29 @ (k16_lattice3 @ X29 @ X30) @ X28)
% 0.74/0.95          | ~ (r2_hidden @ X28 @ X30)
% 0.74/0.95          | ~ (l3_lattices @ X29)
% 0.74/0.95          | ~ (v4_lattice3 @ X29)
% 0.74/0.95          | ~ (v10_lattices @ X29)
% 0.74/0.95          | (v2_struct_0 @ X29))),
% 0.74/0.95      inference('cnf', [status(esa)], [t38_lattice3])).
% 0.74/0.95  thf('62', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.74/0.95         ((v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.74/0.95          | (v2_struct_0 @ X0)
% 0.74/0.95          | ~ (v10_lattices @ X0)
% 0.74/0.95          | ~ (v4_lattice3 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | ~ (r2_hidden @ (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0) @ X3)
% 0.74/0.95          | (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X3) @ 
% 0.74/0.95             (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0)))),
% 0.74/0.95      inference('sup-', [status(thm)], ['60', '61'])).
% 0.74/0.95  thf('63', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.74/0.95         ((r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X3) @ 
% 0.74/0.95           (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0))
% 0.74/0.95          | ~ (r2_hidden @ (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0) @ X3)
% 0.74/0.95          | ~ (v4_lattice3 @ X0)
% 0.74/0.95          | ~ (v10_lattices @ X0)
% 0.74/0.95          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0))),
% 0.74/0.95      inference('simplify', [status(thm)], ['62'])).
% 0.74/0.95  thf('64', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i]:
% 0.74/0.95         ((r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ sk_B)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ sk_B)
% 0.74/0.95          | ~ (v10_lattices @ X0)
% 0.74/0.95          | ~ (v4_lattice3 @ X0)
% 0.74/0.95          | (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ sk_C_1) @ 
% 0.74/0.95             (sk_D @ sk_B @ (k16_lattice3 @ X0 @ X1) @ X0)))),
% 0.74/0.95      inference('sup-', [status(thm)], ['56', '63'])).
% 0.74/0.95  thf('65', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i]:
% 0.74/0.95         ((r3_lattices @ X0 @ (k16_lattice3 @ X0 @ sk_C_1) @ 
% 0.74/0.95           (sk_D @ sk_B @ (k16_lattice3 @ X0 @ X1) @ X0))
% 0.74/0.95          | ~ (v4_lattice3 @ X0)
% 0.74/0.95          | ~ (v10_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ sk_B))),
% 0.74/0.95      inference('simplify', [status(thm)], ['64'])).
% 0.74/0.95  thf('66', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.95         ((m1_subset_1 @ (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0) @ 
% 0.74/0.95           (u1_struct_0 @ X0))
% 0.74/0.95          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0))),
% 0.74/0.95      inference('simplify', [status(thm)], ['59'])).
% 0.74/0.95  thf('67', plain,
% 0.74/0.95      (![X20 : $i, X21 : $i]:
% 0.74/0.95         (~ (l3_lattices @ X20)
% 0.74/0.95          | (v2_struct_0 @ X20)
% 0.74/0.95          | (m1_subset_1 @ (k16_lattice3 @ X20 @ X21) @ (u1_struct_0 @ X20)))),
% 0.74/0.95      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.74/0.95  thf('68', plain,
% 0.74/0.95      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.74/0.95         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 0.74/0.95          | ~ (l3_lattices @ X6)
% 0.74/0.95          | ~ (v9_lattices @ X6)
% 0.74/0.95          | ~ (v8_lattices @ X6)
% 0.74/0.95          | ~ (v6_lattices @ X6)
% 0.74/0.95          | (v2_struct_0 @ X6)
% 0.74/0.95          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 0.74/0.95          | (r1_lattices @ X6 @ X5 @ X7)
% 0.74/0.95          | ~ (r3_lattices @ X6 @ X5 @ X7))),
% 0.74/0.95      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.74/0.95  thf('69', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.95         ((v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | ~ (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.74/0.95          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.74/0.95          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.74/0.95          | (v2_struct_0 @ X0)
% 0.74/0.95          | ~ (v6_lattices @ X0)
% 0.74/0.95          | ~ (v8_lattices @ X0)
% 0.74/0.95          | ~ (v9_lattices @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0))),
% 0.74/0.95      inference('sup-', [status(thm)], ['67', '68'])).
% 0.74/0.95  thf('70', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.95         (~ (v9_lattices @ X0)
% 0.74/0.95          | ~ (v8_lattices @ X0)
% 0.74/0.95          | ~ (v6_lattices @ X0)
% 0.74/0.95          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.74/0.95          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.74/0.95          | ~ (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0))),
% 0.74/0.95      inference('simplify', [status(thm)], ['69'])).
% 0.74/0.95  thf('71', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.74/0.95         ((v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.74/0.95          | (v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | ~ (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X3) @ 
% 0.74/0.95               (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0))
% 0.74/0.95          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X3) @ 
% 0.74/0.95             (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0))
% 0.74/0.95          | ~ (v6_lattices @ X0)
% 0.74/0.95          | ~ (v8_lattices @ X0)
% 0.74/0.95          | ~ (v9_lattices @ X0))),
% 0.74/0.95      inference('sup-', [status(thm)], ['66', '70'])).
% 0.74/0.95  thf('72', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.74/0.95         (~ (v9_lattices @ X0)
% 0.74/0.95          | ~ (v8_lattices @ X0)
% 0.74/0.95          | ~ (v6_lattices @ X0)
% 0.74/0.95          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X3) @ 
% 0.74/0.95             (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0))
% 0.74/0.95          | ~ (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X3) @ 
% 0.74/0.95               (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0))
% 0.74/0.95          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0))),
% 0.74/0.95      inference('simplify', [status(thm)], ['71'])).
% 0.74/0.95  thf('73', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i]:
% 0.74/0.95         ((r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ sk_B)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0)
% 0.74/0.95          | ~ (v10_lattices @ X0)
% 0.74/0.95          | ~ (v4_lattice3 @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ sk_B)
% 0.74/0.95          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ sk_C_1) @ 
% 0.74/0.95             (sk_D @ sk_B @ (k16_lattice3 @ X0 @ X1) @ X0))
% 0.74/0.95          | ~ (v6_lattices @ X0)
% 0.74/0.95          | ~ (v8_lattices @ X0)
% 0.74/0.95          | ~ (v9_lattices @ X0))),
% 0.74/0.95      inference('sup-', [status(thm)], ['65', '72'])).
% 0.74/0.95  thf('74', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i]:
% 0.74/0.95         (~ (v9_lattices @ X0)
% 0.74/0.95          | ~ (v8_lattices @ X0)
% 0.74/0.95          | ~ (v6_lattices @ X0)
% 0.74/0.95          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ sk_C_1) @ 
% 0.74/0.95             (sk_D @ sk_B @ (k16_lattice3 @ X0 @ X1) @ X0))
% 0.74/0.95          | ~ (v4_lattice3 @ X0)
% 0.74/0.95          | ~ (v10_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ sk_B))),
% 0.74/0.95      inference('simplify', [status(thm)], ['73'])).
% 0.74/0.95  thf('75', plain,
% 0.74/0.95      (![X20 : $i, X21 : $i]:
% 0.74/0.95         (~ (l3_lattices @ X20)
% 0.74/0.95          | (v2_struct_0 @ X20)
% 0.74/0.95          | (m1_subset_1 @ (k16_lattice3 @ X20 @ X21) @ (u1_struct_0 @ X20)))),
% 0.74/0.95      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.74/0.95  thf('76', plain,
% 0.74/0.95      (![X8 : $i, X9 : $i, X12 : $i]:
% 0.74/0.95         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.74/0.95          | ~ (r1_lattices @ X9 @ X8 @ (sk_D @ X12 @ X8 @ X9))
% 0.74/0.95          | (r3_lattice3 @ X9 @ X8 @ X12)
% 0.74/0.95          | ~ (l3_lattices @ X9)
% 0.74/0.95          | (v2_struct_0 @ X9))),
% 0.74/0.95      inference('cnf', [status(esa)], [d16_lattice3])).
% 0.74/0.95  thf('77', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.95         ((v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.74/0.95          | ~ (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 0.74/0.95               (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0)))),
% 0.74/0.95      inference('sup-', [status(thm)], ['75', '76'])).
% 0.74/0.95  thf('78', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.95         (~ (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 0.74/0.95             (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0))
% 0.74/0.95          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0))),
% 0.74/0.95      inference('simplify', [status(thm)], ['77'])).
% 0.74/0.95  thf('79', plain,
% 0.74/0.95      (![X0 : $i]:
% 0.74/0.95         ((r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ sk_C_1) @ sk_B)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0)
% 0.74/0.95          | ~ (v10_lattices @ X0)
% 0.74/0.95          | ~ (v4_lattice3 @ X0)
% 0.74/0.95          | ~ (v6_lattices @ X0)
% 0.74/0.95          | ~ (v8_lattices @ X0)
% 0.74/0.95          | ~ (v9_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ sk_C_1) @ sk_B))),
% 0.74/0.95      inference('sup-', [status(thm)], ['74', '78'])).
% 0.74/0.95  thf('80', plain,
% 0.74/0.95      (![X0 : $i]:
% 0.74/0.95         (~ (v9_lattices @ X0)
% 0.74/0.95          | ~ (v8_lattices @ X0)
% 0.74/0.95          | ~ (v6_lattices @ X0)
% 0.74/0.95          | ~ (v4_lattice3 @ X0)
% 0.74/0.95          | ~ (v10_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ sk_C_1) @ sk_B))),
% 0.74/0.95      inference('simplify', [status(thm)], ['79'])).
% 0.74/0.95  thf('81', plain,
% 0.74/0.95      (![X20 : $i, X21 : $i]:
% 0.74/0.95         (~ (l3_lattices @ X20)
% 0.74/0.95          | (v2_struct_0 @ X20)
% 0.74/0.95          | (m1_subset_1 @ (k16_lattice3 @ X20 @ X21) @ (u1_struct_0 @ X20)))),
% 0.74/0.95      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.74/0.95  thf(t40_lattice3, axiom,
% 0.74/0.95    (![A:$i]:
% 0.74/0.95     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.74/0.95         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.74/0.95       ( ![B:$i]:
% 0.74/0.95         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.74/0.95           ( ![C:$i]:
% 0.74/0.95             ( ( r3_lattice3 @ A @ B @ C ) =>
% 0.74/0.95               ( r3_lattices @ A @ B @ ( k16_lattice3 @ A @ C ) ) ) ) ) ) ))).
% 0.74/0.95  thf('82', plain,
% 0.74/0.95      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.74/0.95         (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X32))
% 0.74/0.95          | (r3_lattices @ X32 @ X31 @ (k16_lattice3 @ X32 @ X33))
% 0.74/0.95          | ~ (r3_lattice3 @ X32 @ X31 @ X33)
% 0.74/0.95          | ~ (l3_lattices @ X32)
% 0.74/0.95          | ~ (v4_lattice3 @ X32)
% 0.74/0.95          | ~ (v10_lattices @ X32)
% 0.74/0.95          | (v2_struct_0 @ X32))),
% 0.74/0.95      inference('cnf', [status(esa)], [t40_lattice3])).
% 0.74/0.95  thf('83', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.95         ((v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0)
% 0.74/0.95          | ~ (v10_lattices @ X0)
% 0.74/0.95          | ~ (v4_lattice3 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | ~ (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.74/0.95          | (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 0.74/0.95             (k16_lattice3 @ X0 @ X2)))),
% 0.74/0.95      inference('sup-', [status(thm)], ['81', '82'])).
% 0.74/0.95  thf('84', plain,
% 0.74/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.95         ((r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 0.74/0.95           (k16_lattice3 @ X0 @ X2))
% 0.74/0.95          | ~ (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.74/0.95          | ~ (v4_lattice3 @ X0)
% 0.74/0.95          | ~ (v10_lattices @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0))),
% 0.74/0.95      inference('simplify', [status(thm)], ['83'])).
% 0.74/0.95  thf('85', plain,
% 0.74/0.95      (![X0 : $i]:
% 0.74/0.95         (~ (l3_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0)
% 0.74/0.95          | ~ (v10_lattices @ X0)
% 0.74/0.95          | ~ (v4_lattice3 @ X0)
% 0.74/0.95          | ~ (v6_lattices @ X0)
% 0.74/0.95          | ~ (v8_lattices @ X0)
% 0.74/0.95          | ~ (v9_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0)
% 0.74/0.95          | ~ (v10_lattices @ X0)
% 0.74/0.95          | ~ (v4_lattice3 @ X0)
% 0.74/0.95          | (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ sk_C_1) @ 
% 0.74/0.95             (k16_lattice3 @ X0 @ sk_B)))),
% 0.74/0.95      inference('sup-', [status(thm)], ['80', '84'])).
% 0.74/0.95  thf('86', plain,
% 0.74/0.95      (![X0 : $i]:
% 0.74/0.95         ((r3_lattices @ X0 @ (k16_lattice3 @ X0 @ sk_C_1) @ 
% 0.74/0.95           (k16_lattice3 @ X0 @ sk_B))
% 0.74/0.95          | ~ (v9_lattices @ X0)
% 0.74/0.95          | ~ (v8_lattices @ X0)
% 0.74/0.95          | ~ (v6_lattices @ X0)
% 0.74/0.95          | ~ (v4_lattice3 @ X0)
% 0.74/0.95          | ~ (v10_lattices @ X0)
% 0.74/0.95          | (v2_struct_0 @ X0)
% 0.74/0.95          | ~ (l3_lattices @ X0))),
% 0.74/0.95      inference('simplify', [status(thm)], ['85'])).
% 0.74/0.95  thf('87', plain,
% 0.74/0.95      ((~ (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C_1) @ 
% 0.74/0.95           (k16_lattice3 @ sk_A @ sk_B)))
% 0.74/0.95         <= (~
% 0.74/0.95             ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C_1) @ 
% 0.74/0.95               (k16_lattice3 @ sk_A @ sk_B))))),
% 0.74/0.95      inference('split', [status(esa)], ['49'])).
% 0.74/0.95  thf('88', plain,
% 0.74/0.95      (((~ (l3_lattices @ sk_A)
% 0.74/0.95         | (v2_struct_0 @ sk_A)
% 0.74/0.95         | ~ (v10_lattices @ sk_A)
% 0.74/0.95         | ~ (v4_lattice3 @ sk_A)
% 0.74/0.95         | ~ (v6_lattices @ sk_A)
% 0.74/0.95         | ~ (v8_lattices @ sk_A)
% 0.74/0.95         | ~ (v9_lattices @ sk_A)))
% 0.74/0.95         <= (~
% 0.74/0.95             ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C_1) @ 
% 0.74/0.95               (k16_lattice3 @ sk_A @ sk_B))))),
% 0.74/0.95      inference('sup-', [status(thm)], ['86', '87'])).
% 0.74/0.95  thf('89', plain, ((l3_lattices @ sk_A)),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('90', plain, ((v10_lattices @ sk_A)),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('91', plain, ((v4_lattice3 @ sk_A)),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf(cc1_lattices, axiom,
% 0.74/0.95    (![A:$i]:
% 0.74/0.95     ( ( l3_lattices @ A ) =>
% 0.74/0.95       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.74/0.95         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.74/0.95           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.74/0.95           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.74/0.95  thf('92', plain,
% 0.74/0.95      (![X4 : $i]:
% 0.74/0.95         ((v2_struct_0 @ X4)
% 0.74/0.95          | ~ (v10_lattices @ X4)
% 0.74/0.95          | (v6_lattices @ X4)
% 0.74/0.95          | ~ (l3_lattices @ X4))),
% 0.74/0.95      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.74/0.95  thf('93', plain, (~ (v2_struct_0 @ sk_A)),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('94', plain,
% 0.74/0.95      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.74/0.95      inference('sup-', [status(thm)], ['92', '93'])).
% 0.74/0.95  thf('95', plain, ((l3_lattices @ sk_A)),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('96', plain, ((v10_lattices @ sk_A)),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('97', plain, ((v6_lattices @ sk_A)),
% 0.74/0.95      inference('demod', [status(thm)], ['94', '95', '96'])).
% 0.74/0.95  thf('98', plain,
% 0.74/0.95      (![X4 : $i]:
% 0.74/0.95         ((v2_struct_0 @ X4)
% 0.74/0.95          | ~ (v10_lattices @ X4)
% 0.74/0.95          | (v8_lattices @ X4)
% 0.74/0.95          | ~ (l3_lattices @ X4))),
% 0.74/0.95      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.74/0.95  thf('99', plain, (~ (v2_struct_0 @ sk_A)),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('100', plain,
% 0.74/0.95      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.74/0.95      inference('sup-', [status(thm)], ['98', '99'])).
% 0.74/0.95  thf('101', plain, ((l3_lattices @ sk_A)),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('102', plain, ((v10_lattices @ sk_A)),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('103', plain, ((v8_lattices @ sk_A)),
% 0.74/0.95      inference('demod', [status(thm)], ['100', '101', '102'])).
% 0.74/0.95  thf('104', plain,
% 0.74/0.95      (![X4 : $i]:
% 0.74/0.95         ((v2_struct_0 @ X4)
% 0.74/0.95          | ~ (v10_lattices @ X4)
% 0.74/0.95          | (v9_lattices @ X4)
% 0.74/0.95          | ~ (l3_lattices @ X4))),
% 0.74/0.95      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.74/0.95  thf('105', plain, (~ (v2_struct_0 @ sk_A)),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('106', plain,
% 0.74/0.95      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.74/0.95      inference('sup-', [status(thm)], ['104', '105'])).
% 0.74/0.95  thf('107', plain, ((l3_lattices @ sk_A)),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('108', plain, ((v10_lattices @ sk_A)),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('109', plain, ((v9_lattices @ sk_A)),
% 0.74/0.95      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.74/0.95  thf('110', plain,
% 0.74/0.95      (((v2_struct_0 @ sk_A))
% 0.74/0.95         <= (~
% 0.74/0.95             ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C_1) @ 
% 0.74/0.95               (k16_lattice3 @ sk_A @ sk_B))))),
% 0.74/0.95      inference('demod', [status(thm)],
% 0.74/0.95                ['88', '89', '90', '91', '97', '103', '109'])).
% 0.74/0.95  thf('111', plain, (~ (v2_struct_0 @ sk_A)),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('112', plain,
% 0.74/0.95      (((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C_1) @ 
% 0.74/0.95         (k16_lattice3 @ sk_A @ sk_B)))),
% 0.74/0.95      inference('sup-', [status(thm)], ['110', '111'])).
% 0.74/0.95  thf('113', plain,
% 0.74/0.95      (~
% 0.74/0.95       ((r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 0.74/0.95         (k15_lattice3 @ sk_A @ sk_C_1))) | 
% 0.74/0.95       ~
% 0.74/0.95       ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C_1) @ 
% 0.74/0.95         (k16_lattice3 @ sk_A @ sk_B)))),
% 0.74/0.95      inference('split', [status(esa)], ['49'])).
% 0.74/0.95  thf('114', plain,
% 0.74/0.95      (~
% 0.74/0.95       ((r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 0.74/0.95         (k15_lattice3 @ sk_A @ sk_C_1)))),
% 0.74/0.95      inference('sat_resolution*', [status(thm)], ['112', '113'])).
% 0.74/0.95  thf('115', plain,
% 0.74/0.95      (~ (r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 0.74/0.95          (k15_lattice3 @ sk_A @ sk_C_1))),
% 0.74/0.95      inference('simpl_trail', [status(thm)], ['50', '114'])).
% 0.74/0.95  thf('116', plain,
% 0.74/0.95      (((v2_struct_0 @ sk_A)
% 0.74/0.95        | ~ (v10_lattices @ sk_A)
% 0.74/0.95        | ~ (v4_lattice3 @ sk_A)
% 0.74/0.95        | ~ (l3_lattices @ sk_A)
% 0.74/0.95        | ~ (v6_lattices @ sk_A)
% 0.74/0.95        | ~ (v8_lattices @ sk_A)
% 0.74/0.95        | ~ (v9_lattices @ sk_A))),
% 0.74/0.95      inference('sup-', [status(thm)], ['48', '115'])).
% 0.74/0.95  thf('117', plain, ((v10_lattices @ sk_A)),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('118', plain, ((v4_lattice3 @ sk_A)),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('119', plain, ((l3_lattices @ sk_A)),
% 0.74/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.95  thf('120', plain, ((v6_lattices @ sk_A)),
% 0.74/0.95      inference('demod', [status(thm)], ['94', '95', '96'])).
% 0.74/0.95  thf('121', plain, ((v8_lattices @ sk_A)),
% 0.74/0.95      inference('demod', [status(thm)], ['100', '101', '102'])).
% 0.74/0.95  thf('122', plain, ((v9_lattices @ sk_A)),
% 0.74/0.95      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.74/0.95  thf('123', plain, ((v2_struct_0 @ sk_A)),
% 0.74/0.95      inference('demod', [status(thm)],
% 0.74/0.95                ['116', '117', '118', '119', '120', '121', '122'])).
% 0.74/0.95  thf('124', plain, ($false), inference('demod', [status(thm)], ['0', '123'])).
% 0.74/0.95  
% 0.74/0.95  % SZS output end Refutation
% 0.74/0.95  
% 0.74/0.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
