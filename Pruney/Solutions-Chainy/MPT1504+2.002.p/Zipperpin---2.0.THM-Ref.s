%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rWrztL6uAn

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:27 EST 2020

% Result     : Theorem 1.03s
% Output     : Refutation 1.03s
% Verified   : 
% Statistics : Number of formulae       :  317 (4554 expanded)
%              Number of leaves         :   33 (1212 expanded)
%              Depth                    :   87
%              Number of atoms          : 5111 (88590 expanded)
%              Number of equality atoms :   65 (1736 expanded)
%              Maximal formula depth    :   22 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(a_2_2_lattice3_type,type,(
    a_2_2_lattice3: $i > $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i > $i )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r3_lattice3_type,type,(
    r3_lattice3: $i > $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(r4_lattice3_type,type,(
    r4_lattice3: $i > $i > $i > $o )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t37_lattice3,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v4_lattice3 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( k15_lattice3 @ A @ B )
          = ( k16_lattice3 @ A @ ( a_2_2_lattice3 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v4_lattice3 @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( k15_lattice3 @ A @ B )
            = ( k16_lattice3 @ A @ ( a_2_2_lattice3 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t37_lattice3])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k15_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l3_lattices @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X13 @ X14 ) @ ( u1_struct_0 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l3_lattices @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X13 @ X14 ) @ ( u1_struct_0 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l3_lattices @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X13 @ X14 ) @ ( u1_struct_0 @ X13 ) ) ) ),
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

thf('4',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v10_lattices @ X9 )
      | ~ ( v4_lattice3 @ X9 )
      | ~ ( l3_lattices @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( X10
       != ( k15_lattice3 @ X9 @ X11 ) )
      | ( r4_lattice3 @ X9 @ X10 @ X11 )
      | ~ ( l3_lattices @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('5',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r4_lattice3 @ X9 @ ( k15_lattice3 @ X9 @ X11 ) @ X11 )
      | ~ ( m1_subset_1 @ ( k15_lattice3 @ X9 @ X11 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( l3_lattices @ X9 )
      | ~ ( v4_lattice3 @ X9 )
      | ~ ( v10_lattices @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X1 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l3_lattices @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X13 @ X14 ) @ ( u1_struct_0 @ X13 ) ) ) ),
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

thf('9',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( l3_lattices @ X15 )
      | ~ ( v4_lattice3 @ X15 )
      | ~ ( v10_lattices @ X15 )
      | ( v2_struct_0 @ X15 )
      | ( r2_hidden @ X17 @ ( a_2_2_lattice3 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X15 ) )
      | ( X17 != X18 )
      | ~ ( r4_lattice3 @ X15 @ X18 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_2_lattice3])).

thf('10',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ~ ( r4_lattice3 @ X15 @ X18 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X15 ) )
      | ( r2_hidden @ X18 @ ( a_2_2_lattice3 @ X15 @ X16 ) )
      | ( v2_struct_0 @ X15 )
      | ~ ( v10_lattices @ X15 )
      | ~ ( v4_lattice3 @ X15 )
      | ~ ( l3_lattices @ X15 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r2_hidden @ ( k15_lattice3 @ X0 @ X1 ) @ ( a_2_2_lattice3 @ X0 @ X2 ) )
      | ~ ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( k15_lattice3 @ X0 @ X1 ) @ ( a_2_2_lattice3 @ X0 @ X2 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( r2_hidden @ ( k15_lattice3 @ X1 @ X0 ) @ ( a_2_2_lattice3 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k15_lattice3 @ X1 @ X0 ) @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l3_lattices @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X13 @ X14 ) @ ( u1_struct_0 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

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

thf('16',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X4 @ X5 ) @ X8 )
      | ( r3_lattice3 @ X5 @ X4 @ X8 )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 )
      | ( r3_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( l3_lattices @ X15 )
      | ~ ( v4_lattice3 @ X15 )
      | ~ ( v10_lattices @ X15 )
      | ( v2_struct_0 @ X15 )
      | ( X17
        = ( sk_D_2 @ X16 @ X15 @ X17 ) )
      | ~ ( r2_hidden @ X17 @ ( a_2_2_lattice3 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_2_lattice3])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( l3_lattices @ X2 )
      | ( r3_lattice3 @ X2 @ ( k15_lattice3 @ X2 @ X3 ) @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ( ( sk_D @ ( a_2_2_lattice3 @ X1 @ X0 ) @ ( k15_lattice3 @ X2 @ X3 ) @ X2 )
        = ( sk_D_2 @ X0 @ X1 @ ( sk_D @ ( a_2_2_lattice3 @ X1 @ X0 ) @ ( k15_lattice3 @ X2 @ X3 ) @ X2 ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 )
      | ( r3_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('22',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( l3_lattices @ X15 )
      | ~ ( v4_lattice3 @ X15 )
      | ~ ( v10_lattices @ X15 )
      | ( v2_struct_0 @ X15 )
      | ( r4_lattice3 @ X15 @ ( sk_D_2 @ X16 @ X15 @ X17 ) @ X16 )
      | ~ ( r2_hidden @ X17 @ ( a_2_2_lattice3 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_2_lattice3])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( l3_lattices @ X2 )
      | ( r3_lattice3 @ X2 @ ( k15_lattice3 @ X2 @ X3 ) @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ( r4_lattice3 @ X1 @ ( sk_D_2 @ X0 @ X1 @ ( sk_D @ ( a_2_2_lattice3 @ X1 @ X0 ) @ ( k15_lattice3 @ X2 @ X3 ) @ X2 ) ) @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r4_lattice3 @ X3 @ ( sk_D @ ( a_2_2_lattice3 @ X3 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 )
      | ~ ( l3_lattices @ X3 )
      | ~ ( v4_lattice3 @ X3 )
      | ~ ( v10_lattices @ X3 )
      | ( v2_struct_0 @ X3 )
      | ( r3_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( a_2_2_lattice3 @ X3 @ X2 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X3 )
      | ~ ( v4_lattice3 @ X3 )
      | ~ ( v10_lattices @ X3 )
      | ( v2_struct_0 @ X3 )
      | ( r3_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( a_2_2_lattice3 @ X3 @ X2 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( a_2_2_lattice3 @ X3 @ X2 ) )
      | ( v2_struct_0 @ X3 )
      | ~ ( v10_lattices @ X3 )
      | ~ ( v4_lattice3 @ X3 )
      | ~ ( l3_lattices @ X3 )
      | ( r4_lattice3 @ X3 @ ( sk_D @ ( a_2_2_lattice3 @ X3 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( a_2_2_lattice3 @ X3 @ X2 ) )
      | ( v2_struct_0 @ X3 )
      | ~ ( v10_lattices @ X3 )
      | ~ ( v4_lattice3 @ X3 )
      | ~ ( l3_lattices @ X3 )
      | ( r4_lattice3 @ X3 @ ( sk_D @ ( a_2_2_lattice3 @ X3 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('27',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l3_lattices @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X13 @ X14 ) @ ( u1_struct_0 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('28',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( m1_subset_1 @ ( sk_D @ X8 @ X4 @ X5 ) @ ( u1_struct_0 @ X5 ) )
      | ( r3_lattice3 @ X5 @ X4 @ X8 )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( m1_subset_1 @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r3_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l3_lattices @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X13 @ X14 ) @ ( u1_struct_0 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('32',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v10_lattices @ X9 )
      | ~ ( v4_lattice3 @ X9 )
      | ~ ( l3_lattices @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( X10
       != ( k15_lattice3 @ X9 @ X11 ) )
      | ~ ( r4_lattice3 @ X9 @ X12 @ X11 )
      | ( r1_lattices @ X9 @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l3_lattices @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('33',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X9 ) )
      | ( r1_lattices @ X9 @ ( k15_lattice3 @ X9 @ X11 ) @ X12 )
      | ~ ( r4_lattice3 @ X9 @ X12 @ X11 )
      | ~ ( m1_subset_1 @ ( k15_lattice3 @ X9 @ X11 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( l3_lattices @ X9 )
      | ~ ( v4_lattice3 @ X9 )
      | ~ ( v10_lattices @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
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
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r4_lattice3 @ X0 @ X2 @ X1 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( r4_lattice3 @ X0 @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X3 )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X3 ) @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X3 ) @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ~ ( r4_lattice3 @ X0 @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X3 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( r3_lattice3 @ X1 @ ( k15_lattice3 @ X1 @ X2 ) @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( r3_lattice3 @ X1 @ ( k15_lattice3 @ X1 @ X2 ) @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ( r1_lattices @ X1 @ ( k15_lattice3 @ X1 @ X0 ) @ ( sk_D @ ( a_2_2_lattice3 @ X1 @ X0 ) @ ( k15_lattice3 @ X1 @ X2 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['26','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_lattices @ X1 @ ( k15_lattice3 @ X1 @ X0 ) @ ( sk_D @ ( a_2_2_lattice3 @ X1 @ X0 ) @ ( k15_lattice3 @ X1 @ X2 ) @ X1 ) )
      | ( r3_lattice3 @ X1 @ ( k15_lattice3 @ X1 @ X2 ) @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l3_lattices @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X13 @ X14 ) @ ( u1_struct_0 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('41',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r1_lattices @ X5 @ X4 @ ( sk_D @ X8 @ X4 @ X5 ) )
      | ( r3_lattice3 @ X5 @ X4 @ X8 )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ( r3_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r3_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( a_2_2_lattice3 @ X0 @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( a_2_2_lattice3 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['39','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( a_2_2_lattice3 @ X0 @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l3_lattices @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X13 @ X14 ) @ ( u1_struct_0 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('47',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l3_lattices @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X13 @ X14 ) @ ( u1_struct_0 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k15_lattice3 @ X1 @ X0 ) @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( a_2_2_lattice3 @ X0 @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('50',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l3_lattices @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X13 @ X14 ) @ ( u1_struct_0 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

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

thf('51',plain,(
    ! [X19: $i,X20: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( r3_lattice3 @ X20 @ X19 @ X23 )
      | ( r3_lattice3 @ X20 @ ( sk_D_3 @ X23 @ X19 @ X20 ) @ X23 )
      | ( X19
        = ( k16_lattice3 @ X20 @ X23 ) )
      | ~ ( l3_lattices @ X20 )
      | ~ ( v4_lattice3 @ X20 )
      | ~ ( v10_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( ( k15_lattice3 @ X0 @ X1 )
        = ( k16_lattice3 @ X0 @ X2 ) )
      | ( r3_lattice3 @ X0 @ ( sk_D_3 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 )
      | ~ ( r3_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r3_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( r3_lattice3 @ X0 @ ( sk_D_3 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 )
      | ( ( k15_lattice3 @ X0 @ X1 )
        = ( k16_lattice3 @ X0 @ X2 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ( ( k15_lattice3 @ X1 @ X0 )
        = ( k16_lattice3 @ X1 @ ( a_2_2_lattice3 @ X1 @ X0 ) ) )
      | ( r3_lattice3 @ X1 @ ( sk_D_3 @ ( a_2_2_lattice3 @ X1 @ X0 ) @ ( k15_lattice3 @ X1 @ X0 ) @ X1 ) @ ( a_2_2_lattice3 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ X1 @ ( sk_D_3 @ ( a_2_2_lattice3 @ X1 @ X0 ) @ ( k15_lattice3 @ X1 @ X0 ) @ X1 ) @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ( ( k15_lattice3 @ X1 @ X0 )
        = ( k16_lattice3 @ X1 @ ( a_2_2_lattice3 @ X1 @ X0 ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k15_lattice3 @ X1 @ X0 ) @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('57',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( l3_lattices @ X15 )
      | ~ ( v4_lattice3 @ X15 )
      | ~ ( v10_lattices @ X15 )
      | ( v2_struct_0 @ X15 )
      | ( X17
        = ( sk_D_2 @ X16 @ X15 @ X17 ) )
      | ~ ( r2_hidden @ X17 @ ( a_2_2_lattice3 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_2_lattice3])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ( ( k15_lattice3 @ X1 @ X0 )
        = ( sk_D_2 @ X0 @ X1 @ ( k15_lattice3 @ X1 @ X0 ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k15_lattice3 @ X1 @ X0 )
        = ( sk_D_2 @ X0 @ X1 @ ( k15_lattice3 @ X1 @ X0 ) ) )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k15_lattice3 @ X1 @ X0 )
        = ( sk_D_2 @ X0 @ X1 @ ( k15_lattice3 @ X1 @ X0 ) ) )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k15_lattice3 @ X1 @ X0 )
        = ( sk_D_2 @ X0 @ X1 @ ( k15_lattice3 @ X1 @ X0 ) ) )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k15_lattice3 @ X1 @ X0 ) @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('63',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( l3_lattices @ X15 )
      | ~ ( v4_lattice3 @ X15 )
      | ~ ( v10_lattices @ X15 )
      | ( v2_struct_0 @ X15 )
      | ( m1_subset_1 @ ( sk_D_2 @ X16 @ X15 @ X17 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( r2_hidden @ X17 @ ( a_2_2_lattice3 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_2_lattice3])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ( m1_subset_1 @ ( sk_D_2 @ X0 @ X1 @ ( k15_lattice3 @ X1 @ X0 ) ) @ ( u1_struct_0 @ X1 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_D_2 @ X0 @ X1 @ ( k15_lattice3 @ X1 @ X0 ) ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( m1_subset_1 @ ( sk_D @ X8 @ X4 @ X5 ) @ ( u1_struct_0 @ X5 ) )
      | ( r3_lattice3 @ X5 @ X4 @ X8 )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( sk_D_2 @ X1 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) ) @ X2 )
      | ( m1_subset_1 @ ( sk_D @ X2 @ ( sk_D_2 @ X1 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X2 @ ( sk_D_2 @ X1 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r3_lattice3 @ X0 @ ( sk_D_2 @ X1 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X2 @ ( k15_lattice3 @ X1 @ X0 ) @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ( r3_lattice3 @ X1 @ ( sk_D_2 @ X0 @ X1 @ ( k15_lattice3 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['61','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r3_lattice3 @ X1 @ ( sk_D_2 @ X0 @ X1 @ ( k15_lattice3 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( m1_subset_1 @ ( sk_D @ X2 @ ( k15_lattice3 @ X1 @ X0 ) @ X1 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_D_2 @ X0 @ X1 @ ( k15_lattice3 @ X1 @ X0 ) ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('72',plain,(
    ! [X19: $i,X20: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( r3_lattice3 @ X20 @ X19 @ X23 )
      | ( m1_subset_1 @ ( sk_D_3 @ X23 @ X19 @ X20 ) @ ( u1_struct_0 @ X20 ) )
      | ( X19
        = ( k16_lattice3 @ X20 @ X23 ) )
      | ~ ( l3_lattices @ X20 )
      | ~ ( v4_lattice3 @ X20 )
      | ~ ( v10_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( ( sk_D_2 @ X1 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) )
        = ( k16_lattice3 @ X0 @ X2 ) )
      | ( m1_subset_1 @ ( sk_D_3 @ X2 @ ( sk_D_2 @ X1 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r3_lattice3 @ X0 @ ( sk_D_2 @ X1 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r3_lattice3 @ X0 @ ( sk_D_2 @ X1 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) ) @ X2 )
      | ( m1_subset_1 @ ( sk_D_3 @ X2 @ ( sk_D_2 @ X1 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( sk_D_2 @ X1 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) )
        = ( k16_lattice3 @ X0 @ X2 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X0 @ ( k15_lattice3 @ X2 @ X1 ) @ X2 ) @ ( u1_struct_0 @ X2 ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( l3_lattices @ X2 )
      | ~ ( v10_lattices @ X2 )
      | ~ ( v4_lattice3 @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( l3_lattices @ X2 )
      | ~ ( v10_lattices @ X2 )
      | ~ ( v4_lattice3 @ X2 )
      | ( ( sk_D_2 @ X1 @ X2 @ ( k15_lattice3 @ X2 @ X1 ) )
        = ( k16_lattice3 @ X2 @ X0 ) )
      | ( m1_subset_1 @ ( sk_D_3 @ X0 @ ( sk_D_2 @ X1 @ X2 @ ( k15_lattice3 @ X2 @ X1 ) ) @ X2 ) @ ( u1_struct_0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['70','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D_3 @ X0 @ ( sk_D_2 @ X1 @ X2 @ ( k15_lattice3 @ X2 @ X1 ) ) @ X2 ) @ ( u1_struct_0 @ X2 ) )
      | ( ( sk_D_2 @ X1 @ X2 @ ( k15_lattice3 @ X2 @ X1 ) )
        = ( k16_lattice3 @ X2 @ X0 ) )
      | ~ ( v4_lattice3 @ X2 )
      | ~ ( v10_lattices @ X2 )
      | ~ ( l3_lattices @ X2 )
      | ( v2_struct_0 @ X2 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ ( k15_lattice3 @ X2 @ X1 ) @ X2 ) @ ( u1_struct_0 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D_3 @ X2 @ ( k15_lattice3 @ X1 @ X0 ) @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ( m1_subset_1 @ ( sk_D @ X2 @ ( k15_lattice3 @ X1 @ X0 ) @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ( ( sk_D_2 @ X0 @ X1 @ ( k15_lattice3 @ X1 @ X0 ) )
        = ( k16_lattice3 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['60','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_D_2 @ X0 @ X1 @ ( k15_lattice3 @ X1 @ X0 ) )
        = ( k16_lattice3 @ X1 @ X2 ) )
      | ( m1_subset_1 @ ( sk_D @ X2 @ ( k15_lattice3 @ X1 @ X0 ) @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( m1_subset_1 @ ( sk_D_3 @ X2 @ ( k15_lattice3 @ X1 @ X0 ) @ X1 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ( k15_lattice3 @ sk_A @ sk_B )
 != ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k15_lattice3 @ sk_A @ sk_B )
       != ( sk_D_2 @ X0 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) ) )
      | ( m1_subset_1 @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( ( k15_lattice3 @ sk_A @ sk_B )
       != ( sk_D_2 @ X0 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) ) )
      | ( m1_subset_1 @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['80','81','82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( ( k15_lattice3 @ sk_A @ sk_B )
       != ( k15_lattice3 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['59','84'])).

thf('86',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( ( k15_lattice3 @ sk_A @ sk_B )
       != ( k15_lattice3 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['85','86','87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( k15_lattice3 @ sk_A @ sk_B )
       != ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(eq_res,[status(thm)],['90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( m1_subset_1 @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r3_lattice3 @ X5 @ X4 @ X6 )
      | ~ ( r2_hidden @ X7 @ X6 )
      | ( r1_lattices @ X5 @ X4 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ X1 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( k15_lattice3 @ sk_A @ sk_B )
        = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) )
      | ( r1_lattices @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['55','97'])).

thf('99',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k15_lattice3 @ sk_A @ sk_B )
        = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) )
      | ( r1_lattices @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['98','99','100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ X0 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) )
      | ( ( k15_lattice3 @ sk_A @ sk_B )
        = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ( k15_lattice3 @ sk_A @ sk_B )
 != ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ X0 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','105'])).

thf('107',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['106','107','108','109'])).

thf('111',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_lattices @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','111'])).

thf('113',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_lattices @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( r1_lattices @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( a_2_2_lattice3 @ X0 @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('119',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l3_lattices @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X13 @ X14 ) @ ( u1_struct_0 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('120',plain,(
    ! [X19: $i,X20: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( r3_lattice3 @ X20 @ X19 @ X23 )
      | ( m1_subset_1 @ ( sk_D_3 @ X23 @ X19 @ X20 ) @ ( u1_struct_0 @ X20 ) )
      | ( X19
        = ( k16_lattice3 @ X20 @ X23 ) )
      | ~ ( l3_lattices @ X20 )
      | ~ ( v4_lattice3 @ X20 )
      | ~ ( v10_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( ( k15_lattice3 @ X0 @ X1 )
        = ( k16_lattice3 @ X0 @ X2 ) )
      | ( m1_subset_1 @ ( sk_D_3 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r3_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r3_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( m1_subset_1 @ ( sk_D_3 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k15_lattice3 @ X0 @ X1 )
        = ( k16_lattice3 @ X0 @ X2 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ( ( k15_lattice3 @ X1 @ X0 )
        = ( k16_lattice3 @ X1 @ ( a_2_2_lattice3 @ X1 @ X0 ) ) )
      | ( m1_subset_1 @ ( sk_D_3 @ ( a_2_2_lattice3 @ X1 @ X0 ) @ ( k15_lattice3 @ X1 @ X0 ) @ X1 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['118','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_D_3 @ ( a_2_2_lattice3 @ X1 @ X0 ) @ ( k15_lattice3 @ X1 @ X0 ) @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ( ( k15_lattice3 @ X1 @ X0 )
        = ( k16_lattice3 @ X1 @ ( a_2_2_lattice3 @ X1 @ X0 ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(simplify,[status(thm)],['123'])).

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

thf('125',plain,(
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

thf('126',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k15_lattice3 @ X0 @ X1 )
        = ( k16_lattice3 @ X0 @ ( a_2_2_lattice3 @ X0 @ X1 ) ) )
      | ~ ( r1_lattices @ X0 @ ( sk_D_3 @ ( a_2_2_lattice3 @ X0 @ X1 ) @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 )
      | ( r3_lattices @ X0 @ ( sk_D_3 @ ( a_2_2_lattice3 @ X0 @ X1 ) @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r3_lattices @ X0 @ ( sk_D_3 @ ( a_2_2_lattice3 @ X0 @ X1 ) @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 )
      | ~ ( r1_lattices @ X0 @ ( sk_D_3 @ ( a_2_2_lattice3 @ X0 @ X1 ) @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 )
      | ( ( k15_lattice3 @ X0 @ X1 )
        = ( k16_lattice3 @ X0 @ ( a_2_2_lattice3 @ X0 @ X1 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( ( k15_lattice3 @ sk_A @ sk_B )
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ sk_B ) ) )
    | ( r3_lattices @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v6_lattices @ sk_A )
    | ~ ( v8_lattices @ sk_A )
    | ~ ( v9_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['117','127'])).

thf('129',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v10_lattices @ sk_A ),
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

thf('132',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('133',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('139',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['140','141','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('145',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['146','147','148'])).

thf('150',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( k15_lattice3 @ sk_A @ sk_B )
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ sk_B ) ) )
    | ( r3_lattices @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['128','129','130','131','137','143','149'])).

thf('151',plain,(
    ( k15_lattice3 @ sk_A @ sk_B )
 != ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r3_lattices @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['150','151'])).

thf('153',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( r3_lattices @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','152'])).

thf('154',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_lattices @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r3_lattices @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( r3_lattices @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l3_lattices @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X13 @ X14 ) @ ( u1_struct_0 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('160',plain,(
    ! [X19: $i,X20: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( r3_lattice3 @ X20 @ X19 @ X23 )
      | ~ ( r3_lattices @ X20 @ ( sk_D_3 @ X23 @ X19 @ X20 ) @ X19 )
      | ( X19
        = ( k16_lattice3 @ X20 @ X23 ) )
      | ~ ( l3_lattices @ X20 )
      | ~ ( v4_lattice3 @ X20 )
      | ~ ( v10_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('161',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( ( k15_lattice3 @ X0 @ X1 )
        = ( k16_lattice3 @ X0 @ X2 ) )
      | ~ ( r3_lattices @ X0 @ ( sk_D_3 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( r3_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r3_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r3_lattices @ X0 @ ( sk_D_3 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ( ( k15_lattice3 @ X0 @ X1 )
        = ( k16_lattice3 @ X0 @ X2 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ( ( k15_lattice3 @ sk_A @ sk_B )
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ sk_B ) ) )
    | ~ ( r3_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( a_2_2_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['158','162'])).

thf('164',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( k15_lattice3 @ sk_A @ sk_B )
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ sk_B ) ) )
    | ~ ( r3_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( a_2_2_lattice3 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['163','164','165','166'])).

thf('168',plain,(
    ( k15_lattice3 @ sk_A @ sk_B )
 != ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r3_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( a_2_2_lattice3 @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['167','168'])).

thf('170',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( ~ ( r3_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( a_2_2_lattice3 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['169','170'])).

thf('172',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','171'])).

thf('173',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['172','173','174','175'])).

thf('177',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ~ ( r4_lattice3 @ X15 @ X18 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X15 ) )
      | ( r2_hidden @ X18 @ ( a_2_2_lattice3 @ X15 @ X16 ) )
      | ( v2_struct_0 @ X15 )
      | ~ ( v10_lattices @ X15 )
      | ~ ( v4_lattice3 @ X15 )
      | ~ ( l3_lattices @ X15 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ X0 ) )
      | ~ ( r4_lattice3 @ sk_A @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ X0 ) )
      | ~ ( r4_lattice3 @ sk_A @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['180','181','182','183'])).

thf('185',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    ! [X0: $i] :
      ( ~ ( r4_lattice3 @ sk_A @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(clc,[status(thm)],['184','185'])).

thf('187',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r3_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( a_2_2_lattice3 @ sk_A @ sk_B ) )
    | ~ ( l3_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','186'])).

thf('188',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( a_2_2_lattice3 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['187','188','189','190','191'])).

thf('193',plain,
    ( ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B ) )
    | ( r3_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( a_2_2_lattice3 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['192'])).

thf('194',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ( r3_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( a_2_2_lattice3 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( a_2_2_lattice3 @ X0 @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('197',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l3_lattices @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X13 @ X14 ) @ ( u1_struct_0 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('198',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r3_lattice3 @ X5 @ X4 @ X6 )
      | ~ ( r2_hidden @ X7 @ X6 )
      | ( r1_lattices @ X5 @ X4 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('199',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r3_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r3_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X3 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r1_lattices @ X1 @ ( k15_lattice3 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X2 @ ( a_2_2_lattice3 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['196','200'])).

thf('202',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ( r1_lattices @ X1 @ ( k15_lattice3 @ X1 @ X0 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(simplify,[status(thm)],['201'])).

thf('203',plain,
    ( ( r3_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( a_2_2_lattice3 @ sk_A @ sk_B ) )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['195','202'])).

thf('204',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['176','177'])).

thf('208',plain,
    ( ( r3_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( a_2_2_lattice3 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['203','204','205','206','207'])).

thf('209',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,
    ( ( r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) )
    | ( r3_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( a_2_2_lattice3 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['208','209'])).

thf('211',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ( r3_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('212',plain,
    ( ( r3_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( a_2_2_lattice3 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( r3_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( a_2_2_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('213',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,
    ( ( r3_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( a_2_2_lattice3 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( r3_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( a_2_2_lattice3 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['212','213'])).

thf('215',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( a_2_2_lattice3 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['214'])).

thf('216',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    r3_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( a_2_2_lattice3 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['215','216'])).

thf('218',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r3_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( r3_lattice3 @ X0 @ ( sk_D_3 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 )
      | ( ( k15_lattice3 @ X0 @ X1 )
        = ( k16_lattice3 @ X0 @ X2 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('219',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ( ( k15_lattice3 @ sk_A @ sk_B )
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ sk_B ) ) )
    | ( r3_lattice3 @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k15_lattice3 @ sk_A @ sk_B )
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ sk_B ) ) )
    | ( r3_lattice3 @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['219','220','221','222'])).

thf('224',plain,(
    ( k15_lattice3 @ sk_A @ sk_B )
 != ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_lattice3 @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['223','224'])).

thf('226',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,(
    r3_lattice3 @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['225','226'])).

thf('228',plain,(
    r3_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( a_2_2_lattice3 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['215','216'])).

thf('229',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r3_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( m1_subset_1 @ ( sk_D_3 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k15_lattice3 @ X0 @ X1 )
        = ( k16_lattice3 @ X0 @ X2 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('230',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ( ( k15_lattice3 @ sk_A @ sk_B )
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['228','229'])).

thf('231',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k15_lattice3 @ sk_A @ sk_B )
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['230','231','232','233'])).

thf('235',plain,(
    ( k15_lattice3 @ sk_A @ sk_B )
 != ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['234','235'])).

thf('237',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    m1_subset_1 @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['236','237'])).

thf('239',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r3_lattice3 @ X5 @ X4 @ X6 )
      | ~ ( r2_hidden @ X7 @ X6 )
      | ( r1_lattices @ X5 @ X4 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('240',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['238','239'])).

thf('241',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ X1 ) ) ),
    inference(demod,[status(thm)],['240','241'])).

thf('243',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) )
      | ( r1_lattices @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['227','242'])).

thf('244',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_lattices @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','243'])).

thf('245',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('246',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_lattices @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['244','245','246','247'])).

thf('249',plain,
    ( ( r1_lattices @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['248'])).

thf('250',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,
    ( ~ ( m1_subset_1 @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_lattices @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['249','250'])).

thf('252',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( r1_lattices @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','251'])).

thf('253',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['252','253'])).

thf('255',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,(
    r1_lattices @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['254','255'])).

thf('257',plain,(
    m1_subset_1 @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['236','237'])).

thf('258',plain,(
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

thf('259',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ X0 )
      | ( r3_lattices @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['257','258'])).

thf('260',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('261',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['140','141','142'])).

thf('262',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['146','147','148'])).

thf('263',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ X0 )
      | ( r3_lattices @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['259','260','261','262','263'])).

thf('265',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( r3_lattices @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['256','264'])).

thf('266',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,
    ( ( r3_lattices @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['265','266'])).

thf('268',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( r3_lattices @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','267'])).

thf('269',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('270',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_lattices @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['268','269'])).

thf('271',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('272',plain,(
    r3_lattices @ sk_A @ ( sk_D_3 @ ( a_2_2_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_B ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['270','271'])).

thf('273',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r3_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r3_lattices @ X0 @ ( sk_D_3 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ( ( k15_lattice3 @ X0 @ X1 )
        = ( k16_lattice3 @ X0 @ X2 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('274',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ( ( k15_lattice3 @ sk_A @ sk_B )
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ sk_B ) ) )
    | ~ ( r3_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( a_2_2_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['272','273'])).

thf('275',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('277',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('278',plain,(
    r3_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( a_2_2_lattice3 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['215','216'])).

thf('279',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k15_lattice3 @ sk_A @ sk_B )
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['274','275','276','277','278'])).

thf('280',plain,(
    ( k15_lattice3 @ sk_A @ sk_B )
 != ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['279','280'])).

thf('282',plain,(
    $false ),
    inference(demod,[status(thm)],['0','281'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rWrztL6uAn
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:59:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.03/1.25  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.03/1.25  % Solved by: fo/fo7.sh
% 1.03/1.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.03/1.25  % done 500 iterations in 0.802s
% 1.03/1.25  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.03/1.25  % SZS output start Refutation
% 1.03/1.25  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 1.03/1.25  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.03/1.25  thf(a_2_2_lattice3_type, type, a_2_2_lattice3: $i > $i > $i).
% 1.03/1.25  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i > $i).
% 1.03/1.25  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 1.03/1.25  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 1.03/1.25  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 1.03/1.25  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 1.03/1.25  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.03/1.25  thf(r3_lattice3_type, type, r3_lattice3: $i > $i > $i > $o).
% 1.03/1.25  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 1.03/1.25  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.03/1.25  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.03/1.25  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 1.03/1.25  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 1.03/1.25  thf(r4_lattice3_type, type, r4_lattice3: $i > $i > $i > $o).
% 1.03/1.25  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 1.03/1.25  thf(sk_A_type, type, sk_A: $i).
% 1.03/1.25  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 1.03/1.25  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 1.03/1.25  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 1.03/1.25  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 1.03/1.25  thf(sk_B_type, type, sk_B: $i).
% 1.03/1.25  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 1.03/1.25  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.03/1.25  thf(t37_lattice3, conjecture,
% 1.03/1.25    (![A:$i]:
% 1.03/1.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 1.03/1.25         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 1.03/1.25       ( ![B:$i]:
% 1.03/1.25         ( ( k15_lattice3 @ A @ B ) =
% 1.03/1.25           ( k16_lattice3 @ A @ ( a_2_2_lattice3 @ A @ B ) ) ) ) ))).
% 1.03/1.25  thf(zf_stmt_0, negated_conjecture,
% 1.03/1.25    (~( ![A:$i]:
% 1.03/1.25        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 1.03/1.25            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 1.03/1.25          ( ![B:$i]:
% 1.03/1.25            ( ( k15_lattice3 @ A @ B ) =
% 1.03/1.25              ( k16_lattice3 @ A @ ( a_2_2_lattice3 @ A @ B ) ) ) ) ) )),
% 1.03/1.25    inference('cnf.neg', [status(esa)], [t37_lattice3])).
% 1.03/1.25  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 1.03/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.25  thf(dt_k15_lattice3, axiom,
% 1.03/1.25    (![A:$i,B:$i]:
% 1.03/1.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 1.03/1.25       ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 1.03/1.25  thf('1', plain,
% 1.03/1.25      (![X13 : $i, X14 : $i]:
% 1.03/1.25         (~ (l3_lattices @ X13)
% 1.03/1.25          | (v2_struct_0 @ X13)
% 1.03/1.25          | (m1_subset_1 @ (k15_lattice3 @ X13 @ X14) @ (u1_struct_0 @ X13)))),
% 1.03/1.25      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 1.03/1.25  thf('2', plain,
% 1.03/1.25      (![X13 : $i, X14 : $i]:
% 1.03/1.25         (~ (l3_lattices @ X13)
% 1.03/1.25          | (v2_struct_0 @ X13)
% 1.03/1.25          | (m1_subset_1 @ (k15_lattice3 @ X13 @ X14) @ (u1_struct_0 @ X13)))),
% 1.03/1.25      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 1.03/1.25  thf('3', plain,
% 1.03/1.25      (![X13 : $i, X14 : $i]:
% 1.03/1.25         (~ (l3_lattices @ X13)
% 1.03/1.25          | (v2_struct_0 @ X13)
% 1.03/1.25          | (m1_subset_1 @ (k15_lattice3 @ X13 @ X14) @ (u1_struct_0 @ X13)))),
% 1.03/1.25      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 1.03/1.25  thf(d21_lattice3, axiom,
% 1.03/1.25    (![A:$i]:
% 1.03/1.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 1.03/1.25       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 1.03/1.25           ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 1.03/1.25         ( ![B:$i,C:$i]:
% 1.03/1.25           ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.03/1.25             ( ( ( C ) = ( k15_lattice3 @ A @ B ) ) <=>
% 1.03/1.25               ( ( r4_lattice3 @ A @ C @ B ) & 
% 1.03/1.25                 ( ![D:$i]:
% 1.03/1.25                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 1.03/1.25                     ( ( r4_lattice3 @ A @ D @ B ) =>
% 1.03/1.25                       ( r1_lattices @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 1.03/1.25  thf('4', plain,
% 1.03/1.25      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.03/1.25         ((v2_struct_0 @ X9)
% 1.03/1.25          | ~ (v10_lattices @ X9)
% 1.03/1.25          | ~ (v4_lattice3 @ X9)
% 1.03/1.25          | ~ (l3_lattices @ X9)
% 1.03/1.25          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 1.03/1.25          | ((X10) != (k15_lattice3 @ X9 @ X11))
% 1.03/1.25          | (r4_lattice3 @ X9 @ X10 @ X11)
% 1.03/1.25          | ~ (l3_lattices @ X9)
% 1.03/1.25          | (v2_struct_0 @ X9))),
% 1.03/1.25      inference('cnf', [status(esa)], [d21_lattice3])).
% 1.03/1.25  thf('5', plain,
% 1.03/1.25      (![X9 : $i, X11 : $i]:
% 1.03/1.25         ((r4_lattice3 @ X9 @ (k15_lattice3 @ X9 @ X11) @ X11)
% 1.03/1.25          | ~ (m1_subset_1 @ (k15_lattice3 @ X9 @ X11) @ (u1_struct_0 @ X9))
% 1.03/1.25          | ~ (l3_lattices @ X9)
% 1.03/1.25          | ~ (v4_lattice3 @ X9)
% 1.03/1.25          | ~ (v10_lattices @ X9)
% 1.03/1.25          | (v2_struct_0 @ X9))),
% 1.03/1.25      inference('simplify', [status(thm)], ['4'])).
% 1.03/1.25  thf('6', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i]:
% 1.03/1.25         ((v2_struct_0 @ X0)
% 1.03/1.25          | ~ (l3_lattices @ X0)
% 1.03/1.25          | (v2_struct_0 @ X0)
% 1.03/1.25          | ~ (v10_lattices @ X0)
% 1.03/1.25          | ~ (v4_lattice3 @ X0)
% 1.03/1.25          | ~ (l3_lattices @ X0)
% 1.03/1.25          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X1))),
% 1.03/1.25      inference('sup-', [status(thm)], ['3', '5'])).
% 1.03/1.25  thf('7', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i]:
% 1.03/1.25         ((r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X1)
% 1.03/1.25          | ~ (v4_lattice3 @ X0)
% 1.03/1.25          | ~ (v10_lattices @ X0)
% 1.03/1.25          | ~ (l3_lattices @ X0)
% 1.03/1.25          | (v2_struct_0 @ X0))),
% 1.03/1.25      inference('simplify', [status(thm)], ['6'])).
% 1.03/1.25  thf('8', plain,
% 1.03/1.25      (![X13 : $i, X14 : $i]:
% 1.03/1.25         (~ (l3_lattices @ X13)
% 1.03/1.25          | (v2_struct_0 @ X13)
% 1.03/1.25          | (m1_subset_1 @ (k15_lattice3 @ X13 @ X14) @ (u1_struct_0 @ X13)))),
% 1.03/1.25      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 1.03/1.25  thf(fraenkel_a_2_2_lattice3, axiom,
% 1.03/1.25    (![A:$i,B:$i,C:$i]:
% 1.03/1.25     ( ( ( ~( v2_struct_0 @ B ) ) & ( v10_lattices @ B ) & 
% 1.03/1.25         ( v4_lattice3 @ B ) & ( l3_lattices @ B ) ) =>
% 1.03/1.25       ( ( r2_hidden @ A @ ( a_2_2_lattice3 @ B @ C ) ) <=>
% 1.03/1.25         ( ?[D:$i]:
% 1.03/1.25           ( ( r4_lattice3 @ B @ D @ C ) & ( ( A ) = ( D ) ) & 
% 1.03/1.25             ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 1.03/1.25  thf('9', plain,
% 1.03/1.25      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 1.03/1.25         (~ (l3_lattices @ X15)
% 1.03/1.25          | ~ (v4_lattice3 @ X15)
% 1.03/1.25          | ~ (v10_lattices @ X15)
% 1.03/1.25          | (v2_struct_0 @ X15)
% 1.03/1.25          | (r2_hidden @ X17 @ (a_2_2_lattice3 @ X15 @ X16))
% 1.03/1.25          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X15))
% 1.03/1.25          | ((X17) != (X18))
% 1.03/1.25          | ~ (r4_lattice3 @ X15 @ X18 @ X16))),
% 1.03/1.25      inference('cnf', [status(esa)], [fraenkel_a_2_2_lattice3])).
% 1.03/1.25  thf('10', plain,
% 1.03/1.25      (![X15 : $i, X16 : $i, X18 : $i]:
% 1.03/1.25         (~ (r4_lattice3 @ X15 @ X18 @ X16)
% 1.03/1.25          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X15))
% 1.03/1.25          | (r2_hidden @ X18 @ (a_2_2_lattice3 @ X15 @ X16))
% 1.03/1.25          | (v2_struct_0 @ X15)
% 1.03/1.25          | ~ (v10_lattices @ X15)
% 1.03/1.25          | ~ (v4_lattice3 @ X15)
% 1.03/1.25          | ~ (l3_lattices @ X15))),
% 1.03/1.25      inference('simplify', [status(thm)], ['9'])).
% 1.03/1.25  thf('11', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.25         ((v2_struct_0 @ X0)
% 1.03/1.25          | ~ (l3_lattices @ X0)
% 1.03/1.25          | ~ (l3_lattices @ X0)
% 1.03/1.25          | ~ (v4_lattice3 @ X0)
% 1.03/1.25          | ~ (v10_lattices @ X0)
% 1.03/1.25          | (v2_struct_0 @ X0)
% 1.03/1.25          | (r2_hidden @ (k15_lattice3 @ X0 @ X1) @ (a_2_2_lattice3 @ X0 @ X2))
% 1.03/1.25          | ~ (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))),
% 1.03/1.25      inference('sup-', [status(thm)], ['8', '10'])).
% 1.03/1.25  thf('12', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.25         (~ (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 1.03/1.25          | (r2_hidden @ (k15_lattice3 @ X0 @ X1) @ (a_2_2_lattice3 @ X0 @ X2))
% 1.03/1.25          | ~ (v10_lattices @ X0)
% 1.03/1.25          | ~ (v4_lattice3 @ X0)
% 1.03/1.25          | ~ (l3_lattices @ X0)
% 1.03/1.25          | (v2_struct_0 @ X0))),
% 1.03/1.25      inference('simplify', [status(thm)], ['11'])).
% 1.03/1.25  thf('13', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i]:
% 1.03/1.25         ((v2_struct_0 @ X1)
% 1.03/1.25          | ~ (l3_lattices @ X1)
% 1.03/1.25          | ~ (v10_lattices @ X1)
% 1.03/1.25          | ~ (v4_lattice3 @ X1)
% 1.03/1.25          | (v2_struct_0 @ X1)
% 1.03/1.25          | ~ (l3_lattices @ X1)
% 1.03/1.25          | ~ (v4_lattice3 @ X1)
% 1.03/1.25          | ~ (v10_lattices @ X1)
% 1.03/1.25          | (r2_hidden @ (k15_lattice3 @ X1 @ X0) @ (a_2_2_lattice3 @ X1 @ X0)))),
% 1.03/1.25      inference('sup-', [status(thm)], ['7', '12'])).
% 1.03/1.25  thf('14', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i]:
% 1.03/1.25         ((r2_hidden @ (k15_lattice3 @ X1 @ X0) @ (a_2_2_lattice3 @ X1 @ X0))
% 1.03/1.25          | ~ (v4_lattice3 @ X1)
% 1.03/1.25          | ~ (v10_lattices @ X1)
% 1.03/1.25          | ~ (l3_lattices @ X1)
% 1.03/1.25          | (v2_struct_0 @ X1))),
% 1.03/1.25      inference('simplify', [status(thm)], ['13'])).
% 1.03/1.25  thf('15', plain,
% 1.03/1.25      (![X13 : $i, X14 : $i]:
% 1.03/1.25         (~ (l3_lattices @ X13)
% 1.03/1.25          | (v2_struct_0 @ X13)
% 1.03/1.25          | (m1_subset_1 @ (k15_lattice3 @ X13 @ X14) @ (u1_struct_0 @ X13)))),
% 1.03/1.25      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 1.03/1.25  thf(d16_lattice3, axiom,
% 1.03/1.25    (![A:$i]:
% 1.03/1.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 1.03/1.25       ( ![B:$i]:
% 1.03/1.25         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.03/1.25           ( ![C:$i]:
% 1.03/1.25             ( ( r3_lattice3 @ A @ B @ C ) <=>
% 1.03/1.25               ( ![D:$i]:
% 1.03/1.25                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 1.03/1.25                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 1.03/1.25  thf('16', plain,
% 1.03/1.25      (![X4 : $i, X5 : $i, X8 : $i]:
% 1.03/1.25         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 1.03/1.25          | (r2_hidden @ (sk_D @ X8 @ X4 @ X5) @ X8)
% 1.03/1.25          | (r3_lattice3 @ X5 @ X4 @ X8)
% 1.03/1.25          | ~ (l3_lattices @ X5)
% 1.03/1.25          | (v2_struct_0 @ X5))),
% 1.03/1.25      inference('cnf', [status(esa)], [d16_lattice3])).
% 1.03/1.25  thf('17', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.25         ((v2_struct_0 @ X0)
% 1.03/1.25          | ~ (l3_lattices @ X0)
% 1.03/1.25          | (v2_struct_0 @ X0)
% 1.03/1.25          | ~ (l3_lattices @ X0)
% 1.03/1.25          | (r3_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 1.03/1.25          | (r2_hidden @ (sk_D @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X2))),
% 1.03/1.25      inference('sup-', [status(thm)], ['15', '16'])).
% 1.03/1.25  thf('18', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.25         ((r2_hidden @ (sk_D @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X2)
% 1.03/1.25          | (r3_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 1.03/1.25          | ~ (l3_lattices @ X0)
% 1.03/1.25          | (v2_struct_0 @ X0))),
% 1.03/1.25      inference('simplify', [status(thm)], ['17'])).
% 1.03/1.25  thf('19', plain,
% 1.03/1.25      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.03/1.25         (~ (l3_lattices @ X15)
% 1.03/1.25          | ~ (v4_lattice3 @ X15)
% 1.03/1.25          | ~ (v10_lattices @ X15)
% 1.03/1.25          | (v2_struct_0 @ X15)
% 1.03/1.25          | ((X17) = (sk_D_2 @ X16 @ X15 @ X17))
% 1.03/1.25          | ~ (r2_hidden @ X17 @ (a_2_2_lattice3 @ X15 @ X16)))),
% 1.03/1.25      inference('cnf', [status(esa)], [fraenkel_a_2_2_lattice3])).
% 1.03/1.25  thf('20', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.03/1.25         ((v2_struct_0 @ X2)
% 1.03/1.25          | ~ (l3_lattices @ X2)
% 1.03/1.25          | (r3_lattice3 @ X2 @ (k15_lattice3 @ X2 @ X3) @ 
% 1.03/1.25             (a_2_2_lattice3 @ X1 @ X0))
% 1.03/1.25          | ((sk_D @ (a_2_2_lattice3 @ X1 @ X0) @ (k15_lattice3 @ X2 @ X3) @ X2)
% 1.03/1.25              = (sk_D_2 @ X0 @ X1 @ 
% 1.03/1.25                 (sk_D @ (a_2_2_lattice3 @ X1 @ X0) @ 
% 1.03/1.25                  (k15_lattice3 @ X2 @ X3) @ X2)))
% 1.03/1.25          | (v2_struct_0 @ X1)
% 1.03/1.25          | ~ (v10_lattices @ X1)
% 1.03/1.25          | ~ (v4_lattice3 @ X1)
% 1.03/1.25          | ~ (l3_lattices @ X1))),
% 1.03/1.25      inference('sup-', [status(thm)], ['18', '19'])).
% 1.03/1.25  thf('21', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.25         ((r2_hidden @ (sk_D @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X2)
% 1.03/1.25          | (r3_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 1.03/1.25          | ~ (l3_lattices @ X0)
% 1.03/1.25          | (v2_struct_0 @ X0))),
% 1.03/1.25      inference('simplify', [status(thm)], ['17'])).
% 1.03/1.25  thf('22', plain,
% 1.03/1.25      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.03/1.25         (~ (l3_lattices @ X15)
% 1.03/1.25          | ~ (v4_lattice3 @ X15)
% 1.03/1.25          | ~ (v10_lattices @ X15)
% 1.03/1.25          | (v2_struct_0 @ X15)
% 1.03/1.25          | (r4_lattice3 @ X15 @ (sk_D_2 @ X16 @ X15 @ X17) @ X16)
% 1.03/1.25          | ~ (r2_hidden @ X17 @ (a_2_2_lattice3 @ X15 @ X16)))),
% 1.03/1.25      inference('cnf', [status(esa)], [fraenkel_a_2_2_lattice3])).
% 1.03/1.25  thf('23', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.03/1.25         ((v2_struct_0 @ X2)
% 1.03/1.25          | ~ (l3_lattices @ X2)
% 1.03/1.25          | (r3_lattice3 @ X2 @ (k15_lattice3 @ X2 @ X3) @ 
% 1.03/1.25             (a_2_2_lattice3 @ X1 @ X0))
% 1.03/1.25          | (r4_lattice3 @ X1 @ 
% 1.03/1.25             (sk_D_2 @ X0 @ X1 @ 
% 1.03/1.25              (sk_D @ (a_2_2_lattice3 @ X1 @ X0) @ (k15_lattice3 @ X2 @ X3) @ 
% 1.03/1.25               X2)) @ 
% 1.03/1.25             X0)
% 1.03/1.25          | (v2_struct_0 @ X1)
% 1.03/1.25          | ~ (v10_lattices @ X1)
% 1.03/1.25          | ~ (v4_lattice3 @ X1)
% 1.03/1.25          | ~ (l3_lattices @ X1))),
% 1.03/1.25      inference('sup-', [status(thm)], ['21', '22'])).
% 1.03/1.25  thf('24', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.03/1.25         ((r4_lattice3 @ X3 @ 
% 1.03/1.25           (sk_D @ (a_2_2_lattice3 @ X3 @ X2) @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 1.03/1.25           X2)
% 1.03/1.25          | ~ (l3_lattices @ X3)
% 1.03/1.25          | ~ (v4_lattice3 @ X3)
% 1.03/1.25          | ~ (v10_lattices @ X3)
% 1.03/1.25          | (v2_struct_0 @ X3)
% 1.03/1.25          | (r3_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 1.03/1.25             (a_2_2_lattice3 @ X3 @ X2))
% 1.03/1.25          | ~ (l3_lattices @ X0)
% 1.03/1.25          | (v2_struct_0 @ X0)
% 1.03/1.25          | ~ (l3_lattices @ X3)
% 1.03/1.25          | ~ (v4_lattice3 @ X3)
% 1.03/1.25          | ~ (v10_lattices @ X3)
% 1.03/1.25          | (v2_struct_0 @ X3)
% 1.03/1.25          | (r3_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 1.03/1.25             (a_2_2_lattice3 @ X3 @ X2))
% 1.03/1.25          | ~ (l3_lattices @ X0)
% 1.03/1.25          | (v2_struct_0 @ X0))),
% 1.03/1.25      inference('sup+', [status(thm)], ['20', '23'])).
% 1.03/1.25  thf('25', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.03/1.25         ((v2_struct_0 @ X0)
% 1.03/1.25          | ~ (l3_lattices @ X0)
% 1.03/1.25          | (r3_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 1.03/1.25             (a_2_2_lattice3 @ X3 @ X2))
% 1.03/1.25          | (v2_struct_0 @ X3)
% 1.03/1.25          | ~ (v10_lattices @ X3)
% 1.03/1.25          | ~ (v4_lattice3 @ X3)
% 1.03/1.25          | ~ (l3_lattices @ X3)
% 1.03/1.25          | (r4_lattice3 @ X3 @ 
% 1.03/1.25             (sk_D @ (a_2_2_lattice3 @ X3 @ X2) @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 1.03/1.25             X2))),
% 1.03/1.25      inference('simplify', [status(thm)], ['24'])).
% 1.03/1.25  thf('26', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.03/1.25         ((v2_struct_0 @ X0)
% 1.03/1.25          | ~ (l3_lattices @ X0)
% 1.03/1.25          | (r3_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 1.03/1.25             (a_2_2_lattice3 @ X3 @ X2))
% 1.03/1.25          | (v2_struct_0 @ X3)
% 1.03/1.25          | ~ (v10_lattices @ X3)
% 1.03/1.25          | ~ (v4_lattice3 @ X3)
% 1.03/1.25          | ~ (l3_lattices @ X3)
% 1.03/1.25          | (r4_lattice3 @ X3 @ 
% 1.03/1.25             (sk_D @ (a_2_2_lattice3 @ X3 @ X2) @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 1.03/1.25             X2))),
% 1.03/1.25      inference('simplify', [status(thm)], ['24'])).
% 1.03/1.25  thf('27', plain,
% 1.03/1.25      (![X13 : $i, X14 : $i]:
% 1.03/1.25         (~ (l3_lattices @ X13)
% 1.03/1.25          | (v2_struct_0 @ X13)
% 1.03/1.25          | (m1_subset_1 @ (k15_lattice3 @ X13 @ X14) @ (u1_struct_0 @ X13)))),
% 1.03/1.25      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 1.03/1.25  thf('28', plain,
% 1.03/1.25      (![X4 : $i, X5 : $i, X8 : $i]:
% 1.03/1.25         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 1.03/1.25          | (m1_subset_1 @ (sk_D @ X8 @ X4 @ X5) @ (u1_struct_0 @ X5))
% 1.03/1.25          | (r3_lattice3 @ X5 @ X4 @ X8)
% 1.03/1.25          | ~ (l3_lattices @ X5)
% 1.03/1.25          | (v2_struct_0 @ X5))),
% 1.03/1.25      inference('cnf', [status(esa)], [d16_lattice3])).
% 1.03/1.25  thf('29', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.25         ((v2_struct_0 @ X0)
% 1.03/1.25          | ~ (l3_lattices @ X0)
% 1.03/1.25          | (v2_struct_0 @ X0)
% 1.03/1.25          | ~ (l3_lattices @ X0)
% 1.03/1.25          | (r3_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 1.03/1.25          | (m1_subset_1 @ (sk_D @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 1.03/1.25             (u1_struct_0 @ X0)))),
% 1.03/1.25      inference('sup-', [status(thm)], ['27', '28'])).
% 1.03/1.25  thf('30', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.25         ((m1_subset_1 @ (sk_D @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 1.03/1.25           (u1_struct_0 @ X0))
% 1.03/1.25          | (r3_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 1.03/1.25          | ~ (l3_lattices @ X0)
% 1.03/1.25          | (v2_struct_0 @ X0))),
% 1.03/1.25      inference('simplify', [status(thm)], ['29'])).
% 1.03/1.25  thf('31', plain,
% 1.03/1.25      (![X13 : $i, X14 : $i]:
% 1.03/1.25         (~ (l3_lattices @ X13)
% 1.03/1.25          | (v2_struct_0 @ X13)
% 1.03/1.25          | (m1_subset_1 @ (k15_lattice3 @ X13 @ X14) @ (u1_struct_0 @ X13)))),
% 1.03/1.25      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 1.03/1.25  thf('32', plain,
% 1.03/1.25      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 1.03/1.25         ((v2_struct_0 @ X9)
% 1.03/1.25          | ~ (v10_lattices @ X9)
% 1.03/1.25          | ~ (v4_lattice3 @ X9)
% 1.03/1.25          | ~ (l3_lattices @ X9)
% 1.03/1.25          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 1.03/1.25          | ((X10) != (k15_lattice3 @ X9 @ X11))
% 1.03/1.25          | ~ (r4_lattice3 @ X9 @ X12 @ X11)
% 1.03/1.25          | (r1_lattices @ X9 @ X10 @ X12)
% 1.03/1.25          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X9))
% 1.03/1.25          | ~ (l3_lattices @ X9)
% 1.03/1.25          | (v2_struct_0 @ X9))),
% 1.03/1.25      inference('cnf', [status(esa)], [d21_lattice3])).
% 1.03/1.25  thf('33', plain,
% 1.03/1.25      (![X9 : $i, X11 : $i, X12 : $i]:
% 1.03/1.25         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X9))
% 1.03/1.25          | (r1_lattices @ X9 @ (k15_lattice3 @ X9 @ X11) @ X12)
% 1.03/1.25          | ~ (r4_lattice3 @ X9 @ X12 @ X11)
% 1.03/1.25          | ~ (m1_subset_1 @ (k15_lattice3 @ X9 @ X11) @ (u1_struct_0 @ X9))
% 1.03/1.25          | ~ (l3_lattices @ X9)
% 1.03/1.25          | ~ (v4_lattice3 @ X9)
% 1.03/1.25          | ~ (v10_lattices @ X9)
% 1.03/1.25          | (v2_struct_0 @ X9))),
% 1.03/1.25      inference('simplify', [status(thm)], ['32'])).
% 1.03/1.25  thf('34', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.25         ((v2_struct_0 @ X0)
% 1.03/1.25          | ~ (l3_lattices @ X0)
% 1.03/1.25          | (v2_struct_0 @ X0)
% 1.03/1.25          | ~ (v10_lattices @ X0)
% 1.03/1.25          | ~ (v4_lattice3 @ X0)
% 1.03/1.25          | ~ (l3_lattices @ X0)
% 1.03/1.25          | ~ (r4_lattice3 @ X0 @ X2 @ X1)
% 1.03/1.25          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 1.03/1.25          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0)))),
% 1.03/1.25      inference('sup-', [status(thm)], ['31', '33'])).
% 1.03/1.25  thf('35', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.25         (~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 1.03/1.25          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 1.03/1.25          | ~ (r4_lattice3 @ X0 @ X2 @ X1)
% 1.03/1.25          | ~ (v4_lattice3 @ X0)
% 1.03/1.25          | ~ (v10_lattices @ X0)
% 1.03/1.25          | ~ (l3_lattices @ X0)
% 1.03/1.25          | (v2_struct_0 @ X0))),
% 1.03/1.25      inference('simplify', [status(thm)], ['34'])).
% 1.03/1.25  thf('36', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.03/1.25         ((v2_struct_0 @ X0)
% 1.03/1.25          | ~ (l3_lattices @ X0)
% 1.03/1.25          | (r3_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 1.03/1.25          | (v2_struct_0 @ X0)
% 1.03/1.25          | ~ (l3_lattices @ X0)
% 1.03/1.25          | ~ (v10_lattices @ X0)
% 1.03/1.25          | ~ (v4_lattice3 @ X0)
% 1.03/1.25          | ~ (r4_lattice3 @ X0 @ 
% 1.03/1.25               (sk_D @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X3)
% 1.03/1.25          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X3) @ 
% 1.03/1.25             (sk_D @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0)))),
% 1.03/1.25      inference('sup-', [status(thm)], ['30', '35'])).
% 1.03/1.25  thf('37', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.03/1.25         ((r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X3) @ 
% 1.03/1.25           (sk_D @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 1.03/1.25          | ~ (r4_lattice3 @ X0 @ 
% 1.03/1.25               (sk_D @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X3)
% 1.03/1.25          | ~ (v4_lattice3 @ X0)
% 1.03/1.25          | ~ (v10_lattices @ X0)
% 1.03/1.25          | (r3_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 1.03/1.25          | ~ (l3_lattices @ X0)
% 1.03/1.25          | (v2_struct_0 @ X0))),
% 1.03/1.25      inference('simplify', [status(thm)], ['36'])).
% 1.03/1.25  thf('38', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.25         (~ (l3_lattices @ X1)
% 1.03/1.25          | ~ (v4_lattice3 @ X1)
% 1.03/1.25          | ~ (v10_lattices @ X1)
% 1.03/1.25          | (v2_struct_0 @ X1)
% 1.03/1.25          | (r3_lattice3 @ X1 @ (k15_lattice3 @ X1 @ X2) @ 
% 1.03/1.25             (a_2_2_lattice3 @ X1 @ X0))
% 1.03/1.25          | ~ (l3_lattices @ X1)
% 1.03/1.25          | (v2_struct_0 @ X1)
% 1.03/1.25          | (v2_struct_0 @ X1)
% 1.03/1.25          | ~ (l3_lattices @ X1)
% 1.03/1.25          | (r3_lattice3 @ X1 @ (k15_lattice3 @ X1 @ X2) @ 
% 1.03/1.25             (a_2_2_lattice3 @ X1 @ X0))
% 1.03/1.25          | ~ (v10_lattices @ X1)
% 1.03/1.25          | ~ (v4_lattice3 @ X1)
% 1.03/1.25          | (r1_lattices @ X1 @ (k15_lattice3 @ X1 @ X0) @ 
% 1.03/1.25             (sk_D @ (a_2_2_lattice3 @ X1 @ X0) @ (k15_lattice3 @ X1 @ X2) @ X1)))),
% 1.03/1.25      inference('sup-', [status(thm)], ['26', '37'])).
% 1.03/1.25  thf('39', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.25         ((r1_lattices @ X1 @ (k15_lattice3 @ X1 @ X0) @ 
% 1.03/1.25           (sk_D @ (a_2_2_lattice3 @ X1 @ X0) @ (k15_lattice3 @ X1 @ X2) @ X1))
% 1.03/1.25          | (r3_lattice3 @ X1 @ (k15_lattice3 @ X1 @ X2) @ 
% 1.03/1.25             (a_2_2_lattice3 @ X1 @ X0))
% 1.03/1.25          | (v2_struct_0 @ X1)
% 1.03/1.25          | ~ (v10_lattices @ X1)
% 1.03/1.25          | ~ (v4_lattice3 @ X1)
% 1.03/1.25          | ~ (l3_lattices @ X1))),
% 1.03/1.25      inference('simplify', [status(thm)], ['38'])).
% 1.03/1.25  thf('40', plain,
% 1.03/1.25      (![X13 : $i, X14 : $i]:
% 1.03/1.25         (~ (l3_lattices @ X13)
% 1.03/1.25          | (v2_struct_0 @ X13)
% 1.03/1.25          | (m1_subset_1 @ (k15_lattice3 @ X13 @ X14) @ (u1_struct_0 @ X13)))),
% 1.03/1.25      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 1.03/1.25  thf('41', plain,
% 1.03/1.25      (![X4 : $i, X5 : $i, X8 : $i]:
% 1.03/1.25         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 1.03/1.25          | ~ (r1_lattices @ X5 @ X4 @ (sk_D @ X8 @ X4 @ X5))
% 1.03/1.25          | (r3_lattice3 @ X5 @ X4 @ X8)
% 1.03/1.25          | ~ (l3_lattices @ X5)
% 1.03/1.25          | (v2_struct_0 @ X5))),
% 1.03/1.25      inference('cnf', [status(esa)], [d16_lattice3])).
% 1.03/1.25  thf('42', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.25         ((v2_struct_0 @ X0)
% 1.03/1.25          | ~ (l3_lattices @ X0)
% 1.03/1.25          | (v2_struct_0 @ X0)
% 1.03/1.25          | ~ (l3_lattices @ X0)
% 1.03/1.25          | (r3_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 1.03/1.25          | ~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 1.03/1.25               (sk_D @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0)))),
% 1.03/1.25      inference('sup-', [status(thm)], ['40', '41'])).
% 1.03/1.25  thf('43', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.25         (~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 1.03/1.25             (sk_D @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 1.03/1.25          | (r3_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 1.03/1.25          | ~ (l3_lattices @ X0)
% 1.03/1.25          | (v2_struct_0 @ X0))),
% 1.03/1.25      inference('simplify', [status(thm)], ['42'])).
% 1.03/1.25  thf('44', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i]:
% 1.03/1.25         (~ (l3_lattices @ X0)
% 1.03/1.25          | ~ (v4_lattice3 @ X0)
% 1.03/1.25          | ~ (v10_lattices @ X0)
% 1.03/1.25          | (v2_struct_0 @ X0)
% 1.03/1.25          | (r3_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 1.03/1.25             (a_2_2_lattice3 @ X0 @ X1))
% 1.03/1.25          | (v2_struct_0 @ X0)
% 1.03/1.25          | ~ (l3_lattices @ X0)
% 1.03/1.25          | (r3_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 1.03/1.25             (a_2_2_lattice3 @ X0 @ X1)))),
% 1.03/1.25      inference('sup-', [status(thm)], ['39', '43'])).
% 1.03/1.25  thf('45', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i]:
% 1.03/1.25         ((r3_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 1.03/1.25           (a_2_2_lattice3 @ X0 @ X1))
% 1.03/1.25          | (v2_struct_0 @ X0)
% 1.03/1.25          | ~ (v10_lattices @ X0)
% 1.03/1.25          | ~ (v4_lattice3 @ X0)
% 1.03/1.25          | ~ (l3_lattices @ X0))),
% 1.03/1.25      inference('simplify', [status(thm)], ['44'])).
% 1.03/1.25  thf('46', plain,
% 1.03/1.25      (![X13 : $i, X14 : $i]:
% 1.03/1.25         (~ (l3_lattices @ X13)
% 1.03/1.25          | (v2_struct_0 @ X13)
% 1.03/1.25          | (m1_subset_1 @ (k15_lattice3 @ X13 @ X14) @ (u1_struct_0 @ X13)))),
% 1.03/1.25      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 1.03/1.25  thf('47', plain,
% 1.03/1.25      (![X13 : $i, X14 : $i]:
% 1.03/1.25         (~ (l3_lattices @ X13)
% 1.03/1.25          | (v2_struct_0 @ X13)
% 1.03/1.25          | (m1_subset_1 @ (k15_lattice3 @ X13 @ X14) @ (u1_struct_0 @ X13)))),
% 1.03/1.25      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 1.03/1.25  thf('48', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i]:
% 1.03/1.25         ((r2_hidden @ (k15_lattice3 @ X1 @ X0) @ (a_2_2_lattice3 @ X1 @ X0))
% 1.03/1.25          | ~ (v4_lattice3 @ X1)
% 1.03/1.25          | ~ (v10_lattices @ X1)
% 1.03/1.25          | ~ (l3_lattices @ X1)
% 1.03/1.25          | (v2_struct_0 @ X1))),
% 1.03/1.25      inference('simplify', [status(thm)], ['13'])).
% 1.03/1.25  thf('49', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i]:
% 1.03/1.25         ((r3_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 1.03/1.25           (a_2_2_lattice3 @ X0 @ X1))
% 1.03/1.25          | (v2_struct_0 @ X0)
% 1.03/1.25          | ~ (v10_lattices @ X0)
% 1.03/1.25          | ~ (v4_lattice3 @ X0)
% 1.03/1.25          | ~ (l3_lattices @ X0))),
% 1.03/1.25      inference('simplify', [status(thm)], ['44'])).
% 1.03/1.25  thf('50', plain,
% 1.03/1.25      (![X13 : $i, X14 : $i]:
% 1.03/1.25         (~ (l3_lattices @ X13)
% 1.03/1.25          | (v2_struct_0 @ X13)
% 1.03/1.25          | (m1_subset_1 @ (k15_lattice3 @ X13 @ X14) @ (u1_struct_0 @ X13)))),
% 1.03/1.25      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 1.03/1.25  thf(t34_lattice3, axiom,
% 1.03/1.25    (![A:$i]:
% 1.03/1.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 1.03/1.25         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 1.03/1.25       ( ![B:$i]:
% 1.03/1.25         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.03/1.25           ( ![C:$i]:
% 1.03/1.25             ( ( ( B ) = ( k16_lattice3 @ A @ C ) ) <=>
% 1.03/1.25               ( ( r3_lattice3 @ A @ B @ C ) & 
% 1.03/1.25                 ( ![D:$i]:
% 1.03/1.25                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 1.03/1.25                     ( ( r3_lattice3 @ A @ D @ C ) =>
% 1.03/1.25                       ( r3_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 1.03/1.25  thf('51', plain,
% 1.03/1.25      (![X19 : $i, X20 : $i, X23 : $i]:
% 1.03/1.25         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 1.03/1.25          | ~ (r3_lattice3 @ X20 @ X19 @ X23)
% 1.03/1.25          | (r3_lattice3 @ X20 @ (sk_D_3 @ X23 @ X19 @ X20) @ X23)
% 1.03/1.25          | ((X19) = (k16_lattice3 @ X20 @ X23))
% 1.03/1.25          | ~ (l3_lattices @ X20)
% 1.03/1.25          | ~ (v4_lattice3 @ X20)
% 1.03/1.25          | ~ (v10_lattices @ X20)
% 1.03/1.25          | (v2_struct_0 @ X20))),
% 1.03/1.25      inference('cnf', [status(esa)], [t34_lattice3])).
% 1.03/1.25  thf('52', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.25         ((v2_struct_0 @ X0)
% 1.03/1.25          | ~ (l3_lattices @ X0)
% 1.03/1.25          | (v2_struct_0 @ X0)
% 1.03/1.25          | ~ (v10_lattices @ X0)
% 1.03/1.25          | ~ (v4_lattice3 @ X0)
% 1.03/1.25          | ~ (l3_lattices @ X0)
% 1.03/1.25          | ((k15_lattice3 @ X0 @ X1) = (k16_lattice3 @ X0 @ X2))
% 1.03/1.25          | (r3_lattice3 @ X0 @ 
% 1.03/1.25             (sk_D_3 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X2)
% 1.03/1.25          | ~ (r3_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))),
% 1.03/1.25      inference('sup-', [status(thm)], ['50', '51'])).
% 1.03/1.25  thf('53', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.25         (~ (r3_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 1.03/1.25          | (r3_lattice3 @ X0 @ 
% 1.03/1.25             (sk_D_3 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X2)
% 1.03/1.25          | ((k15_lattice3 @ X0 @ X1) = (k16_lattice3 @ X0 @ X2))
% 1.03/1.25          | ~ (v4_lattice3 @ X0)
% 1.03/1.25          | ~ (v10_lattices @ X0)
% 1.03/1.25          | ~ (l3_lattices @ X0)
% 1.03/1.25          | (v2_struct_0 @ X0))),
% 1.03/1.25      inference('simplify', [status(thm)], ['52'])).
% 1.03/1.25  thf('54', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i]:
% 1.03/1.25         (~ (l3_lattices @ X1)
% 1.03/1.25          | ~ (v4_lattice3 @ X1)
% 1.03/1.25          | ~ (v10_lattices @ X1)
% 1.03/1.25          | (v2_struct_0 @ X1)
% 1.03/1.25          | (v2_struct_0 @ X1)
% 1.03/1.25          | ~ (l3_lattices @ X1)
% 1.03/1.25          | ~ (v10_lattices @ X1)
% 1.03/1.25          | ~ (v4_lattice3 @ X1)
% 1.03/1.25          | ((k15_lattice3 @ X1 @ X0)
% 1.03/1.25              = (k16_lattice3 @ X1 @ (a_2_2_lattice3 @ X1 @ X0)))
% 1.03/1.25          | (r3_lattice3 @ X1 @ 
% 1.03/1.25             (sk_D_3 @ (a_2_2_lattice3 @ X1 @ X0) @ (k15_lattice3 @ X1 @ X0) @ 
% 1.03/1.25              X1) @ 
% 1.03/1.25             (a_2_2_lattice3 @ X1 @ X0)))),
% 1.03/1.25      inference('sup-', [status(thm)], ['49', '53'])).
% 1.03/1.25  thf('55', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i]:
% 1.03/1.25         ((r3_lattice3 @ X1 @ 
% 1.03/1.25           (sk_D_3 @ (a_2_2_lattice3 @ X1 @ X0) @ (k15_lattice3 @ X1 @ X0) @ X1) @ 
% 1.03/1.25           (a_2_2_lattice3 @ X1 @ X0))
% 1.03/1.25          | ((k15_lattice3 @ X1 @ X0)
% 1.03/1.25              = (k16_lattice3 @ X1 @ (a_2_2_lattice3 @ X1 @ X0)))
% 1.03/1.25          | (v2_struct_0 @ X1)
% 1.03/1.25          | ~ (v10_lattices @ X1)
% 1.03/1.25          | ~ (v4_lattice3 @ X1)
% 1.03/1.25          | ~ (l3_lattices @ X1))),
% 1.03/1.25      inference('simplify', [status(thm)], ['54'])).
% 1.03/1.25  thf('56', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i]:
% 1.03/1.25         ((r2_hidden @ (k15_lattice3 @ X1 @ X0) @ (a_2_2_lattice3 @ X1 @ X0))
% 1.03/1.25          | ~ (v4_lattice3 @ X1)
% 1.03/1.25          | ~ (v10_lattices @ X1)
% 1.03/1.25          | ~ (l3_lattices @ X1)
% 1.03/1.25          | (v2_struct_0 @ X1))),
% 1.03/1.25      inference('simplify', [status(thm)], ['13'])).
% 1.03/1.25  thf('57', plain,
% 1.03/1.25      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.03/1.25         (~ (l3_lattices @ X15)
% 1.03/1.25          | ~ (v4_lattice3 @ X15)
% 1.03/1.25          | ~ (v10_lattices @ X15)
% 1.03/1.25          | (v2_struct_0 @ X15)
% 1.03/1.25          | ((X17) = (sk_D_2 @ X16 @ X15 @ X17))
% 1.03/1.25          | ~ (r2_hidden @ X17 @ (a_2_2_lattice3 @ X15 @ X16)))),
% 1.03/1.25      inference('cnf', [status(esa)], [fraenkel_a_2_2_lattice3])).
% 1.03/1.25  thf('58', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i]:
% 1.03/1.25         ((v2_struct_0 @ X1)
% 1.03/1.25          | ~ (l3_lattices @ X1)
% 1.03/1.25          | ~ (v10_lattices @ X1)
% 1.03/1.25          | ~ (v4_lattice3 @ X1)
% 1.03/1.25          | ((k15_lattice3 @ X1 @ X0)
% 1.03/1.25              = (sk_D_2 @ X0 @ X1 @ (k15_lattice3 @ X1 @ X0)))
% 1.03/1.25          | (v2_struct_0 @ X1)
% 1.03/1.25          | ~ (v10_lattices @ X1)
% 1.03/1.25          | ~ (v4_lattice3 @ X1)
% 1.03/1.25          | ~ (l3_lattices @ X1))),
% 1.03/1.25      inference('sup-', [status(thm)], ['56', '57'])).
% 1.03/1.25  thf('59', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i]:
% 1.03/1.25         (((k15_lattice3 @ X1 @ X0)
% 1.03/1.25            = (sk_D_2 @ X0 @ X1 @ (k15_lattice3 @ X1 @ X0)))
% 1.03/1.25          | ~ (v4_lattice3 @ X1)
% 1.03/1.25          | ~ (v10_lattices @ X1)
% 1.03/1.25          | ~ (l3_lattices @ X1)
% 1.03/1.25          | (v2_struct_0 @ X1))),
% 1.03/1.25      inference('simplify', [status(thm)], ['58'])).
% 1.03/1.25  thf('60', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i]:
% 1.03/1.25         (((k15_lattice3 @ X1 @ X0)
% 1.03/1.25            = (sk_D_2 @ X0 @ X1 @ (k15_lattice3 @ X1 @ X0)))
% 1.03/1.25          | ~ (v4_lattice3 @ X1)
% 1.03/1.25          | ~ (v10_lattices @ X1)
% 1.03/1.25          | ~ (l3_lattices @ X1)
% 1.03/1.25          | (v2_struct_0 @ X1))),
% 1.03/1.25      inference('simplify', [status(thm)], ['58'])).
% 1.03/1.25  thf('61', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i]:
% 1.03/1.25         (((k15_lattice3 @ X1 @ X0)
% 1.03/1.25            = (sk_D_2 @ X0 @ X1 @ (k15_lattice3 @ X1 @ X0)))
% 1.03/1.25          | ~ (v4_lattice3 @ X1)
% 1.03/1.25          | ~ (v10_lattices @ X1)
% 1.03/1.25          | ~ (l3_lattices @ X1)
% 1.03/1.25          | (v2_struct_0 @ X1))),
% 1.03/1.25      inference('simplify', [status(thm)], ['58'])).
% 1.03/1.25  thf('62', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i]:
% 1.03/1.25         ((r2_hidden @ (k15_lattice3 @ X1 @ X0) @ (a_2_2_lattice3 @ X1 @ X0))
% 1.03/1.25          | ~ (v4_lattice3 @ X1)
% 1.03/1.25          | ~ (v10_lattices @ X1)
% 1.03/1.25          | ~ (l3_lattices @ X1)
% 1.03/1.25          | (v2_struct_0 @ X1))),
% 1.03/1.25      inference('simplify', [status(thm)], ['13'])).
% 1.03/1.25  thf('63', plain,
% 1.03/1.25      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.03/1.25         (~ (l3_lattices @ X15)
% 1.03/1.25          | ~ (v4_lattice3 @ X15)
% 1.03/1.25          | ~ (v10_lattices @ X15)
% 1.03/1.25          | (v2_struct_0 @ X15)
% 1.03/1.25          | (m1_subset_1 @ (sk_D_2 @ X16 @ X15 @ X17) @ (u1_struct_0 @ X15))
% 1.03/1.25          | ~ (r2_hidden @ X17 @ (a_2_2_lattice3 @ X15 @ X16)))),
% 1.03/1.25      inference('cnf', [status(esa)], [fraenkel_a_2_2_lattice3])).
% 1.03/1.25  thf('64', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i]:
% 1.03/1.25         ((v2_struct_0 @ X1)
% 1.03/1.25          | ~ (l3_lattices @ X1)
% 1.03/1.25          | ~ (v10_lattices @ X1)
% 1.03/1.25          | ~ (v4_lattice3 @ X1)
% 1.03/1.25          | (m1_subset_1 @ (sk_D_2 @ X0 @ X1 @ (k15_lattice3 @ X1 @ X0)) @ 
% 1.03/1.25             (u1_struct_0 @ X1))
% 1.03/1.25          | (v2_struct_0 @ X1)
% 1.03/1.25          | ~ (v10_lattices @ X1)
% 1.03/1.25          | ~ (v4_lattice3 @ X1)
% 1.03/1.25          | ~ (l3_lattices @ X1))),
% 1.03/1.25      inference('sup-', [status(thm)], ['62', '63'])).
% 1.03/1.25  thf('65', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i]:
% 1.03/1.25         ((m1_subset_1 @ (sk_D_2 @ X0 @ X1 @ (k15_lattice3 @ X1 @ X0)) @ 
% 1.03/1.25           (u1_struct_0 @ X1))
% 1.03/1.25          | ~ (v4_lattice3 @ X1)
% 1.03/1.25          | ~ (v10_lattices @ X1)
% 1.03/1.25          | ~ (l3_lattices @ X1)
% 1.03/1.25          | (v2_struct_0 @ X1))),
% 1.03/1.25      inference('simplify', [status(thm)], ['64'])).
% 1.03/1.25  thf('66', plain,
% 1.03/1.25      (![X4 : $i, X5 : $i, X8 : $i]:
% 1.03/1.25         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 1.03/1.25          | (m1_subset_1 @ (sk_D @ X8 @ X4 @ X5) @ (u1_struct_0 @ X5))
% 1.03/1.25          | (r3_lattice3 @ X5 @ X4 @ X8)
% 1.03/1.25          | ~ (l3_lattices @ X5)
% 1.03/1.25          | (v2_struct_0 @ X5))),
% 1.03/1.25      inference('cnf', [status(esa)], [d16_lattice3])).
% 1.03/1.25  thf('67', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.25         ((v2_struct_0 @ X0)
% 1.03/1.25          | ~ (l3_lattices @ X0)
% 1.03/1.25          | ~ (v10_lattices @ X0)
% 1.03/1.25          | ~ (v4_lattice3 @ X0)
% 1.03/1.25          | (v2_struct_0 @ X0)
% 1.03/1.25          | ~ (l3_lattices @ X0)
% 1.03/1.25          | (r3_lattice3 @ X0 @ 
% 1.03/1.25             (sk_D_2 @ X1 @ X0 @ (k15_lattice3 @ X0 @ X1)) @ X2)
% 1.03/1.25          | (m1_subset_1 @ 
% 1.03/1.25             (sk_D @ X2 @ (sk_D_2 @ X1 @ X0 @ (k15_lattice3 @ X0 @ X1)) @ X0) @ 
% 1.03/1.25             (u1_struct_0 @ X0)))),
% 1.03/1.25      inference('sup-', [status(thm)], ['65', '66'])).
% 1.03/1.25  thf('68', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.25         ((m1_subset_1 @ 
% 1.03/1.25           (sk_D @ X2 @ (sk_D_2 @ X1 @ X0 @ (k15_lattice3 @ X0 @ X1)) @ X0) @ 
% 1.03/1.25           (u1_struct_0 @ X0))
% 1.03/1.25          | (r3_lattice3 @ X0 @ 
% 1.03/1.25             (sk_D_2 @ X1 @ X0 @ (k15_lattice3 @ X0 @ X1)) @ X2)
% 1.03/1.25          | ~ (v4_lattice3 @ X0)
% 1.03/1.25          | ~ (v10_lattices @ X0)
% 1.03/1.25          | ~ (l3_lattices @ X0)
% 1.03/1.25          | (v2_struct_0 @ X0))),
% 1.03/1.25      inference('simplify', [status(thm)], ['67'])).
% 1.03/1.25  thf('69', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.25         ((m1_subset_1 @ (sk_D @ X2 @ (k15_lattice3 @ X1 @ X0) @ X1) @ 
% 1.03/1.25           (u1_struct_0 @ X1))
% 1.03/1.25          | (v2_struct_0 @ X1)
% 1.03/1.25          | ~ (l3_lattices @ X1)
% 1.03/1.25          | ~ (v10_lattices @ X1)
% 1.03/1.25          | ~ (v4_lattice3 @ X1)
% 1.03/1.25          | (v2_struct_0 @ X1)
% 1.03/1.25          | ~ (l3_lattices @ X1)
% 1.03/1.25          | ~ (v10_lattices @ X1)
% 1.03/1.25          | ~ (v4_lattice3 @ X1)
% 1.03/1.25          | (r3_lattice3 @ X1 @ 
% 1.03/1.25             (sk_D_2 @ X0 @ X1 @ (k15_lattice3 @ X1 @ X0)) @ X2))),
% 1.03/1.25      inference('sup+', [status(thm)], ['61', '68'])).
% 1.03/1.25  thf('70', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.25         ((r3_lattice3 @ X1 @ (sk_D_2 @ X0 @ X1 @ (k15_lattice3 @ X1 @ X0)) @ 
% 1.03/1.25           X2)
% 1.03/1.25          | ~ (v4_lattice3 @ X1)
% 1.03/1.25          | ~ (v10_lattices @ X1)
% 1.03/1.25          | ~ (l3_lattices @ X1)
% 1.03/1.25          | (v2_struct_0 @ X1)
% 1.03/1.25          | (m1_subset_1 @ (sk_D @ X2 @ (k15_lattice3 @ X1 @ X0) @ X1) @ 
% 1.03/1.25             (u1_struct_0 @ X1)))),
% 1.03/1.25      inference('simplify', [status(thm)], ['69'])).
% 1.03/1.25  thf('71', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i]:
% 1.03/1.25         ((m1_subset_1 @ (sk_D_2 @ X0 @ X1 @ (k15_lattice3 @ X1 @ X0)) @ 
% 1.03/1.25           (u1_struct_0 @ X1))
% 1.03/1.25          | ~ (v4_lattice3 @ X1)
% 1.03/1.25          | ~ (v10_lattices @ X1)
% 1.03/1.25          | ~ (l3_lattices @ X1)
% 1.03/1.25          | (v2_struct_0 @ X1))),
% 1.03/1.25      inference('simplify', [status(thm)], ['64'])).
% 1.03/1.25  thf('72', plain,
% 1.03/1.25      (![X19 : $i, X20 : $i, X23 : $i]:
% 1.03/1.25         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 1.03/1.25          | ~ (r3_lattice3 @ X20 @ X19 @ X23)
% 1.03/1.25          | (m1_subset_1 @ (sk_D_3 @ X23 @ X19 @ X20) @ (u1_struct_0 @ X20))
% 1.03/1.25          | ((X19) = (k16_lattice3 @ X20 @ X23))
% 1.03/1.25          | ~ (l3_lattices @ X20)
% 1.03/1.25          | ~ (v4_lattice3 @ X20)
% 1.03/1.25          | ~ (v10_lattices @ X20)
% 1.03/1.25          | (v2_struct_0 @ X20))),
% 1.03/1.25      inference('cnf', [status(esa)], [t34_lattice3])).
% 1.03/1.25  thf('73', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.25         ((v2_struct_0 @ X0)
% 1.03/1.25          | ~ (l3_lattices @ X0)
% 1.03/1.25          | ~ (v10_lattices @ X0)
% 1.03/1.25          | ~ (v4_lattice3 @ X0)
% 1.03/1.25          | (v2_struct_0 @ X0)
% 1.03/1.25          | ~ (v10_lattices @ X0)
% 1.03/1.25          | ~ (v4_lattice3 @ X0)
% 1.03/1.25          | ~ (l3_lattices @ X0)
% 1.03/1.25          | ((sk_D_2 @ X1 @ X0 @ (k15_lattice3 @ X0 @ X1))
% 1.03/1.25              = (k16_lattice3 @ X0 @ X2))
% 1.03/1.25          | (m1_subset_1 @ 
% 1.03/1.25             (sk_D_3 @ X2 @ (sk_D_2 @ X1 @ X0 @ (k15_lattice3 @ X0 @ X1)) @ X0) @ 
% 1.03/1.25             (u1_struct_0 @ X0))
% 1.03/1.25          | ~ (r3_lattice3 @ X0 @ 
% 1.03/1.25               (sk_D_2 @ X1 @ X0 @ (k15_lattice3 @ X0 @ X1)) @ X2))),
% 1.03/1.25      inference('sup-', [status(thm)], ['71', '72'])).
% 1.03/1.25  thf('74', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.25         (~ (r3_lattice3 @ X0 @ 
% 1.03/1.25             (sk_D_2 @ X1 @ X0 @ (k15_lattice3 @ X0 @ X1)) @ X2)
% 1.03/1.25          | (m1_subset_1 @ 
% 1.03/1.25             (sk_D_3 @ X2 @ (sk_D_2 @ X1 @ X0 @ (k15_lattice3 @ X0 @ X1)) @ X0) @ 
% 1.03/1.25             (u1_struct_0 @ X0))
% 1.03/1.25          | ((sk_D_2 @ X1 @ X0 @ (k15_lattice3 @ X0 @ X1))
% 1.03/1.25              = (k16_lattice3 @ X0 @ X2))
% 1.03/1.25          | ~ (v4_lattice3 @ X0)
% 1.03/1.25          | ~ (v10_lattices @ X0)
% 1.03/1.25          | ~ (l3_lattices @ X0)
% 1.03/1.25          | (v2_struct_0 @ X0))),
% 1.03/1.25      inference('simplify', [status(thm)], ['73'])).
% 1.03/1.25  thf('75', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.25         ((m1_subset_1 @ (sk_D @ X0 @ (k15_lattice3 @ X2 @ X1) @ X2) @ 
% 1.03/1.25           (u1_struct_0 @ X2))
% 1.03/1.25          | (v2_struct_0 @ X2)
% 1.03/1.25          | ~ (l3_lattices @ X2)
% 1.03/1.25          | ~ (v10_lattices @ X2)
% 1.03/1.25          | ~ (v4_lattice3 @ X2)
% 1.03/1.25          | (v2_struct_0 @ X2)
% 1.03/1.25          | ~ (l3_lattices @ X2)
% 1.03/1.25          | ~ (v10_lattices @ X2)
% 1.03/1.25          | ~ (v4_lattice3 @ X2)
% 1.03/1.25          | ((sk_D_2 @ X1 @ X2 @ (k15_lattice3 @ X2 @ X1))
% 1.03/1.25              = (k16_lattice3 @ X2 @ X0))
% 1.03/1.25          | (m1_subset_1 @ 
% 1.03/1.25             (sk_D_3 @ X0 @ (sk_D_2 @ X1 @ X2 @ (k15_lattice3 @ X2 @ X1)) @ X2) @ 
% 1.03/1.25             (u1_struct_0 @ X2)))),
% 1.03/1.25      inference('sup-', [status(thm)], ['70', '74'])).
% 1.03/1.25  thf('76', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.25         ((m1_subset_1 @ 
% 1.03/1.25           (sk_D_3 @ X0 @ (sk_D_2 @ X1 @ X2 @ (k15_lattice3 @ X2 @ X1)) @ X2) @ 
% 1.03/1.25           (u1_struct_0 @ X2))
% 1.03/1.25          | ((sk_D_2 @ X1 @ X2 @ (k15_lattice3 @ X2 @ X1))
% 1.03/1.25              = (k16_lattice3 @ X2 @ X0))
% 1.03/1.25          | ~ (v4_lattice3 @ X2)
% 1.03/1.25          | ~ (v10_lattices @ X2)
% 1.03/1.25          | ~ (l3_lattices @ X2)
% 1.03/1.25          | (v2_struct_0 @ X2)
% 1.03/1.25          | (m1_subset_1 @ (sk_D @ X0 @ (k15_lattice3 @ X2 @ X1) @ X2) @ 
% 1.03/1.25             (u1_struct_0 @ X2)))),
% 1.03/1.25      inference('simplify', [status(thm)], ['75'])).
% 1.03/1.25  thf('77', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.25         ((m1_subset_1 @ (sk_D_3 @ X2 @ (k15_lattice3 @ X1 @ X0) @ X1) @ 
% 1.03/1.25           (u1_struct_0 @ X1))
% 1.03/1.25          | (v2_struct_0 @ X1)
% 1.03/1.25          | ~ (l3_lattices @ X1)
% 1.03/1.25          | ~ (v10_lattices @ X1)
% 1.03/1.25          | ~ (v4_lattice3 @ X1)
% 1.03/1.25          | (m1_subset_1 @ (sk_D @ X2 @ (k15_lattice3 @ X1 @ X0) @ X1) @ 
% 1.03/1.25             (u1_struct_0 @ X1))
% 1.03/1.25          | (v2_struct_0 @ X1)
% 1.03/1.25          | ~ (l3_lattices @ X1)
% 1.03/1.25          | ~ (v10_lattices @ X1)
% 1.03/1.25          | ~ (v4_lattice3 @ X1)
% 1.03/1.25          | ((sk_D_2 @ X0 @ X1 @ (k15_lattice3 @ X1 @ X0))
% 1.03/1.25              = (k16_lattice3 @ X1 @ X2)))),
% 1.03/1.25      inference('sup+', [status(thm)], ['60', '76'])).
% 1.03/1.25  thf('78', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.25         (((sk_D_2 @ X0 @ X1 @ (k15_lattice3 @ X1 @ X0))
% 1.03/1.25            = (k16_lattice3 @ X1 @ X2))
% 1.03/1.25          | (m1_subset_1 @ (sk_D @ X2 @ (k15_lattice3 @ X1 @ X0) @ X1) @ 
% 1.03/1.25             (u1_struct_0 @ X1))
% 1.03/1.25          | ~ (v4_lattice3 @ X1)
% 1.03/1.25          | ~ (v10_lattices @ X1)
% 1.03/1.25          | ~ (l3_lattices @ X1)
% 1.03/1.25          | (v2_struct_0 @ X1)
% 1.03/1.25          | (m1_subset_1 @ (sk_D_3 @ X2 @ (k15_lattice3 @ X1 @ X0) @ X1) @ 
% 1.03/1.25             (u1_struct_0 @ X1)))),
% 1.03/1.25      inference('simplify', [status(thm)], ['77'])).
% 1.03/1.25  thf('79', plain,
% 1.03/1.25      (((k15_lattice3 @ sk_A @ sk_B)
% 1.03/1.25         != (k16_lattice3 @ sk_A @ (a_2_2_lattice3 @ sk_A @ sk_B)))),
% 1.03/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.25  thf('80', plain,
% 1.03/1.25      (![X0 : $i]:
% 1.03/1.25         (((k15_lattice3 @ sk_A @ sk_B)
% 1.03/1.25            != (sk_D_2 @ X0 @ sk_A @ (k15_lattice3 @ sk_A @ X0)))
% 1.03/1.25          | (m1_subset_1 @ 
% 1.03/1.25             (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.25              (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 1.03/1.25             (u1_struct_0 @ sk_A))
% 1.03/1.25          | (v2_struct_0 @ sk_A)
% 1.03/1.25          | ~ (l3_lattices @ sk_A)
% 1.03/1.25          | ~ (v10_lattices @ sk_A)
% 1.03/1.25          | ~ (v4_lattice3 @ sk_A)
% 1.03/1.25          | (m1_subset_1 @ 
% 1.03/1.25             (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.25              (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 1.03/1.25             (u1_struct_0 @ sk_A)))),
% 1.03/1.25      inference('sup-', [status(thm)], ['78', '79'])).
% 1.03/1.25  thf('81', plain, ((l3_lattices @ sk_A)),
% 1.03/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.25  thf('82', plain, ((v10_lattices @ sk_A)),
% 1.03/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.25  thf('83', plain, ((v4_lattice3 @ sk_A)),
% 1.03/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.25  thf('84', plain,
% 1.03/1.25      (![X0 : $i]:
% 1.03/1.25         (((k15_lattice3 @ sk_A @ sk_B)
% 1.03/1.25            != (sk_D_2 @ X0 @ sk_A @ (k15_lattice3 @ sk_A @ X0)))
% 1.03/1.25          | (m1_subset_1 @ 
% 1.03/1.25             (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.25              (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 1.03/1.25             (u1_struct_0 @ sk_A))
% 1.03/1.25          | (v2_struct_0 @ sk_A)
% 1.03/1.25          | (m1_subset_1 @ 
% 1.03/1.25             (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.25              (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 1.03/1.25             (u1_struct_0 @ sk_A)))),
% 1.03/1.25      inference('demod', [status(thm)], ['80', '81', '82', '83'])).
% 1.03/1.25  thf('85', plain,
% 1.03/1.25      (![X0 : $i]:
% 1.03/1.25         (((k15_lattice3 @ sk_A @ sk_B) != (k15_lattice3 @ sk_A @ X0))
% 1.03/1.25          | (v2_struct_0 @ sk_A)
% 1.03/1.25          | ~ (l3_lattices @ sk_A)
% 1.03/1.25          | ~ (v10_lattices @ sk_A)
% 1.03/1.25          | ~ (v4_lattice3 @ sk_A)
% 1.03/1.25          | (m1_subset_1 @ 
% 1.03/1.25             (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.25              (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 1.03/1.25             (u1_struct_0 @ sk_A))
% 1.03/1.25          | (v2_struct_0 @ sk_A)
% 1.03/1.25          | (m1_subset_1 @ 
% 1.03/1.25             (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.25              (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 1.03/1.25             (u1_struct_0 @ sk_A)))),
% 1.03/1.25      inference('sup-', [status(thm)], ['59', '84'])).
% 1.03/1.25  thf('86', plain, ((l3_lattices @ sk_A)),
% 1.03/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.25  thf('87', plain, ((v10_lattices @ sk_A)),
% 1.03/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.25  thf('88', plain, ((v4_lattice3 @ sk_A)),
% 1.03/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.25  thf('89', plain,
% 1.03/1.25      (![X0 : $i]:
% 1.03/1.25         (((k15_lattice3 @ sk_A @ sk_B) != (k15_lattice3 @ sk_A @ X0))
% 1.03/1.25          | (v2_struct_0 @ sk_A)
% 1.03/1.25          | (m1_subset_1 @ 
% 1.03/1.25             (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.25              (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 1.03/1.25             (u1_struct_0 @ sk_A))
% 1.03/1.25          | (v2_struct_0 @ sk_A)
% 1.03/1.25          | (m1_subset_1 @ 
% 1.03/1.25             (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.25              (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 1.03/1.25             (u1_struct_0 @ sk_A)))),
% 1.03/1.25      inference('demod', [status(thm)], ['85', '86', '87', '88'])).
% 1.03/1.25  thf('90', plain,
% 1.03/1.25      (![X0 : $i]:
% 1.03/1.25         ((m1_subset_1 @ 
% 1.03/1.25           (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.25            (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 1.03/1.25           (u1_struct_0 @ sk_A))
% 1.03/1.25          | (m1_subset_1 @ 
% 1.03/1.25             (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.25              (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 1.03/1.25             (u1_struct_0 @ sk_A))
% 1.03/1.25          | (v2_struct_0 @ sk_A)
% 1.03/1.25          | ((k15_lattice3 @ sk_A @ sk_B) != (k15_lattice3 @ sk_A @ X0)))),
% 1.03/1.25      inference('simplify', [status(thm)], ['89'])).
% 1.03/1.25  thf('91', plain,
% 1.03/1.25      (((v2_struct_0 @ sk_A)
% 1.03/1.25        | (m1_subset_1 @ 
% 1.03/1.25           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.25            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.25           (u1_struct_0 @ sk_A))
% 1.03/1.25        | (m1_subset_1 @ 
% 1.03/1.25           (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.25            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.25           (u1_struct_0 @ sk_A)))),
% 1.03/1.25      inference('eq_res', [status(thm)], ['90'])).
% 1.03/1.25  thf('92', plain, (~ (v2_struct_0 @ sk_A)),
% 1.03/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.25  thf('93', plain,
% 1.03/1.25      (((m1_subset_1 @ 
% 1.03/1.25         (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.25          (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.25         (u1_struct_0 @ sk_A))
% 1.03/1.25        | (m1_subset_1 @ 
% 1.03/1.25           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.25            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.25           (u1_struct_0 @ sk_A)))),
% 1.03/1.25      inference('clc', [status(thm)], ['91', '92'])).
% 1.03/1.25  thf('94', plain,
% 1.03/1.25      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 1.03/1.25         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 1.03/1.25          | ~ (r3_lattice3 @ X5 @ X4 @ X6)
% 1.03/1.25          | ~ (r2_hidden @ X7 @ X6)
% 1.03/1.25          | (r1_lattices @ X5 @ X4 @ X7)
% 1.03/1.25          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X5))
% 1.03/1.25          | ~ (l3_lattices @ X5)
% 1.03/1.25          | (v2_struct_0 @ X5))),
% 1.03/1.25      inference('cnf', [status(esa)], [d16_lattice3])).
% 1.03/1.25  thf('95', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i]:
% 1.03/1.25         ((m1_subset_1 @ 
% 1.03/1.25           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.25            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.25           (u1_struct_0 @ sk_A))
% 1.03/1.25          | (v2_struct_0 @ sk_A)
% 1.03/1.25          | ~ (l3_lattices @ sk_A)
% 1.03/1.25          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.03/1.25          | (r1_lattices @ sk_A @ 
% 1.03/1.25             (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.25              (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.25             X0)
% 1.03/1.25          | ~ (r2_hidden @ X0 @ X1)
% 1.03/1.25          | ~ (r3_lattice3 @ sk_A @ 
% 1.03/1.25               (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.25                (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.25               X1))),
% 1.03/1.25      inference('sup-', [status(thm)], ['93', '94'])).
% 1.03/1.25  thf('96', plain, ((l3_lattices @ sk_A)),
% 1.03/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.25  thf('97', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i]:
% 1.03/1.25         ((m1_subset_1 @ 
% 1.03/1.25           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.25            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.25           (u1_struct_0 @ sk_A))
% 1.03/1.25          | (v2_struct_0 @ sk_A)
% 1.03/1.25          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.03/1.25          | (r1_lattices @ sk_A @ 
% 1.03/1.25             (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.25              (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.25             X0)
% 1.03/1.25          | ~ (r2_hidden @ X0 @ X1)
% 1.03/1.25          | ~ (r3_lattice3 @ sk_A @ 
% 1.03/1.25               (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.25                (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.25               X1))),
% 1.03/1.25      inference('demod', [status(thm)], ['95', '96'])).
% 1.03/1.25  thf('98', plain,
% 1.03/1.25      (![X0 : $i]:
% 1.03/1.25         (~ (l3_lattices @ sk_A)
% 1.03/1.25          | ~ (v4_lattice3 @ sk_A)
% 1.03/1.25          | ~ (v10_lattices @ sk_A)
% 1.03/1.25          | (v2_struct_0 @ sk_A)
% 1.03/1.25          | ((k15_lattice3 @ sk_A @ sk_B)
% 1.03/1.25              = (k16_lattice3 @ sk_A @ (a_2_2_lattice3 @ sk_A @ sk_B)))
% 1.03/1.25          | ~ (r2_hidden @ X0 @ (a_2_2_lattice3 @ sk_A @ sk_B))
% 1.03/1.25          | (r1_lattices @ sk_A @ 
% 1.03/1.25             (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.25              (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.25             X0)
% 1.03/1.25          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.03/1.25          | (v2_struct_0 @ sk_A)
% 1.03/1.25          | (m1_subset_1 @ 
% 1.03/1.25             (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.25              (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.25             (u1_struct_0 @ sk_A)))),
% 1.03/1.25      inference('sup-', [status(thm)], ['55', '97'])).
% 1.03/1.25  thf('99', plain, ((l3_lattices @ sk_A)),
% 1.03/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.25  thf('100', plain, ((v4_lattice3 @ sk_A)),
% 1.03/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.25  thf('101', plain, ((v10_lattices @ sk_A)),
% 1.03/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.25  thf('102', plain,
% 1.03/1.25      (![X0 : $i]:
% 1.03/1.25         ((v2_struct_0 @ sk_A)
% 1.03/1.25          | ((k15_lattice3 @ sk_A @ sk_B)
% 1.03/1.25              = (k16_lattice3 @ sk_A @ (a_2_2_lattice3 @ sk_A @ sk_B)))
% 1.03/1.25          | ~ (r2_hidden @ X0 @ (a_2_2_lattice3 @ sk_A @ sk_B))
% 1.03/1.25          | (r1_lattices @ sk_A @ 
% 1.03/1.25             (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.25              (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.25             X0)
% 1.03/1.25          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.03/1.25          | (v2_struct_0 @ sk_A)
% 1.03/1.25          | (m1_subset_1 @ 
% 1.03/1.25             (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.25              (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.25             (u1_struct_0 @ sk_A)))),
% 1.03/1.25      inference('demod', [status(thm)], ['98', '99', '100', '101'])).
% 1.03/1.25  thf('103', plain,
% 1.03/1.25      (![X0 : $i]:
% 1.03/1.25         ((m1_subset_1 @ 
% 1.03/1.25           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.25            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.25           (u1_struct_0 @ sk_A))
% 1.03/1.25          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.03/1.25          | (r1_lattices @ sk_A @ 
% 1.03/1.25             (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.25              (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.25             X0)
% 1.03/1.25          | ~ (r2_hidden @ X0 @ (a_2_2_lattice3 @ sk_A @ sk_B))
% 1.03/1.25          | ((k15_lattice3 @ sk_A @ sk_B)
% 1.03/1.25              = (k16_lattice3 @ sk_A @ (a_2_2_lattice3 @ sk_A @ sk_B)))
% 1.03/1.25          | (v2_struct_0 @ sk_A))),
% 1.03/1.25      inference('simplify', [status(thm)], ['102'])).
% 1.03/1.25  thf('104', plain,
% 1.03/1.25      (((k15_lattice3 @ sk_A @ sk_B)
% 1.03/1.25         != (k16_lattice3 @ sk_A @ (a_2_2_lattice3 @ sk_A @ sk_B)))),
% 1.03/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.25  thf('105', plain,
% 1.03/1.25      (![X0 : $i]:
% 1.03/1.25         ((m1_subset_1 @ 
% 1.03/1.25           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.25            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.25           (u1_struct_0 @ sk_A))
% 1.03/1.25          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.03/1.25          | (r1_lattices @ sk_A @ 
% 1.03/1.25             (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.25              (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.25             X0)
% 1.03/1.25          | ~ (r2_hidden @ X0 @ (a_2_2_lattice3 @ sk_A @ sk_B))
% 1.03/1.25          | (v2_struct_0 @ sk_A))),
% 1.03/1.25      inference('simplify_reflect-', [status(thm)], ['103', '104'])).
% 1.03/1.25  thf('106', plain,
% 1.03/1.25      (((v2_struct_0 @ sk_A)
% 1.03/1.25        | ~ (l3_lattices @ sk_A)
% 1.03/1.25        | ~ (v10_lattices @ sk_A)
% 1.03/1.25        | ~ (v4_lattice3 @ sk_A)
% 1.03/1.25        | (v2_struct_0 @ sk_A)
% 1.03/1.25        | (r1_lattices @ sk_A @ 
% 1.03/1.25           (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.25            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.25           (k15_lattice3 @ sk_A @ sk_B))
% 1.03/1.25        | ~ (m1_subset_1 @ (k15_lattice3 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.03/1.25        | (m1_subset_1 @ 
% 1.03/1.25           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.25            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.25           (u1_struct_0 @ sk_A)))),
% 1.03/1.25      inference('sup-', [status(thm)], ['48', '105'])).
% 1.03/1.25  thf('107', plain, ((l3_lattices @ sk_A)),
% 1.03/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.25  thf('108', plain, ((v10_lattices @ sk_A)),
% 1.03/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.25  thf('109', plain, ((v4_lattice3 @ sk_A)),
% 1.03/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.25  thf('110', plain,
% 1.03/1.25      (((v2_struct_0 @ sk_A)
% 1.03/1.25        | (v2_struct_0 @ sk_A)
% 1.03/1.25        | (r1_lattices @ sk_A @ 
% 1.03/1.25           (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.25            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.25           (k15_lattice3 @ sk_A @ sk_B))
% 1.03/1.25        | ~ (m1_subset_1 @ (k15_lattice3 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.03/1.25        | (m1_subset_1 @ 
% 1.03/1.25           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.25            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.25           (u1_struct_0 @ sk_A)))),
% 1.03/1.25      inference('demod', [status(thm)], ['106', '107', '108', '109'])).
% 1.03/1.25  thf('111', plain,
% 1.03/1.25      (((m1_subset_1 @ 
% 1.03/1.25         (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.25          (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.25         (u1_struct_0 @ sk_A))
% 1.03/1.25        | ~ (m1_subset_1 @ (k15_lattice3 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.03/1.25        | (r1_lattices @ sk_A @ 
% 1.03/1.25           (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.25            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.25           (k15_lattice3 @ sk_A @ sk_B))
% 1.03/1.25        | (v2_struct_0 @ sk_A))),
% 1.03/1.25      inference('simplify', [status(thm)], ['110'])).
% 1.03/1.25  thf('112', plain,
% 1.03/1.25      (((v2_struct_0 @ sk_A)
% 1.03/1.25        | ~ (l3_lattices @ sk_A)
% 1.03/1.25        | (v2_struct_0 @ sk_A)
% 1.03/1.25        | (r1_lattices @ sk_A @ 
% 1.03/1.25           (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.25            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.25           (k15_lattice3 @ sk_A @ sk_B))
% 1.03/1.25        | (m1_subset_1 @ 
% 1.03/1.25           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.25            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.25           (u1_struct_0 @ sk_A)))),
% 1.03/1.25      inference('sup-', [status(thm)], ['47', '111'])).
% 1.03/1.25  thf('113', plain, ((l3_lattices @ sk_A)),
% 1.03/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.25  thf('114', plain,
% 1.03/1.25      (((v2_struct_0 @ sk_A)
% 1.03/1.25        | (v2_struct_0 @ sk_A)
% 1.03/1.25        | (r1_lattices @ sk_A @ 
% 1.03/1.25           (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.25            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.25           (k15_lattice3 @ sk_A @ sk_B))
% 1.03/1.25        | (m1_subset_1 @ 
% 1.03/1.25           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.25            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.25           (u1_struct_0 @ sk_A)))),
% 1.03/1.25      inference('demod', [status(thm)], ['112', '113'])).
% 1.03/1.25  thf('115', plain,
% 1.03/1.25      (((m1_subset_1 @ 
% 1.03/1.25         (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.25          (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.25         (u1_struct_0 @ sk_A))
% 1.03/1.25        | (r1_lattices @ sk_A @ 
% 1.03/1.25           (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.25            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.25           (k15_lattice3 @ sk_A @ sk_B))
% 1.03/1.25        | (v2_struct_0 @ sk_A))),
% 1.03/1.25      inference('simplify', [status(thm)], ['114'])).
% 1.03/1.25  thf('116', plain, (~ (v2_struct_0 @ sk_A)),
% 1.03/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.25  thf('117', plain,
% 1.03/1.25      (((r1_lattices @ sk_A @ 
% 1.03/1.25         (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.25          (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.25         (k15_lattice3 @ sk_A @ sk_B))
% 1.03/1.25        | (m1_subset_1 @ 
% 1.03/1.25           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.25            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.25           (u1_struct_0 @ sk_A)))),
% 1.03/1.25      inference('clc', [status(thm)], ['115', '116'])).
% 1.03/1.25  thf('118', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i]:
% 1.03/1.25         ((r3_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 1.03/1.25           (a_2_2_lattice3 @ X0 @ X1))
% 1.03/1.25          | (v2_struct_0 @ X0)
% 1.03/1.25          | ~ (v10_lattices @ X0)
% 1.03/1.25          | ~ (v4_lattice3 @ X0)
% 1.03/1.25          | ~ (l3_lattices @ X0))),
% 1.03/1.25      inference('simplify', [status(thm)], ['44'])).
% 1.03/1.25  thf('119', plain,
% 1.03/1.25      (![X13 : $i, X14 : $i]:
% 1.03/1.25         (~ (l3_lattices @ X13)
% 1.03/1.25          | (v2_struct_0 @ X13)
% 1.03/1.25          | (m1_subset_1 @ (k15_lattice3 @ X13 @ X14) @ (u1_struct_0 @ X13)))),
% 1.03/1.25      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 1.03/1.25  thf('120', plain,
% 1.03/1.25      (![X19 : $i, X20 : $i, X23 : $i]:
% 1.03/1.25         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 1.03/1.25          | ~ (r3_lattice3 @ X20 @ X19 @ X23)
% 1.03/1.25          | (m1_subset_1 @ (sk_D_3 @ X23 @ X19 @ X20) @ (u1_struct_0 @ X20))
% 1.03/1.25          | ((X19) = (k16_lattice3 @ X20 @ X23))
% 1.03/1.25          | ~ (l3_lattices @ X20)
% 1.03/1.25          | ~ (v4_lattice3 @ X20)
% 1.03/1.25          | ~ (v10_lattices @ X20)
% 1.03/1.25          | (v2_struct_0 @ X20))),
% 1.03/1.25      inference('cnf', [status(esa)], [t34_lattice3])).
% 1.03/1.25  thf('121', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.25         ((v2_struct_0 @ X0)
% 1.03/1.25          | ~ (l3_lattices @ X0)
% 1.03/1.25          | (v2_struct_0 @ X0)
% 1.03/1.25          | ~ (v10_lattices @ X0)
% 1.03/1.25          | ~ (v4_lattice3 @ X0)
% 1.03/1.25          | ~ (l3_lattices @ X0)
% 1.03/1.25          | ((k15_lattice3 @ X0 @ X1) = (k16_lattice3 @ X0 @ X2))
% 1.03/1.25          | (m1_subset_1 @ (sk_D_3 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 1.03/1.25             (u1_struct_0 @ X0))
% 1.03/1.25          | ~ (r3_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))),
% 1.03/1.25      inference('sup-', [status(thm)], ['119', '120'])).
% 1.03/1.25  thf('122', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.25         (~ (r3_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 1.03/1.25          | (m1_subset_1 @ (sk_D_3 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 1.03/1.25             (u1_struct_0 @ X0))
% 1.03/1.25          | ((k15_lattice3 @ X0 @ X1) = (k16_lattice3 @ X0 @ X2))
% 1.03/1.25          | ~ (v4_lattice3 @ X0)
% 1.03/1.25          | ~ (v10_lattices @ X0)
% 1.03/1.25          | ~ (l3_lattices @ X0)
% 1.03/1.25          | (v2_struct_0 @ X0))),
% 1.03/1.25      inference('simplify', [status(thm)], ['121'])).
% 1.03/1.25  thf('123', plain,
% 1.03/1.25      (![X0 : $i, X1 : $i]:
% 1.03/1.25         (~ (l3_lattices @ X1)
% 1.03/1.25          | ~ (v4_lattice3 @ X1)
% 1.03/1.25          | ~ (v10_lattices @ X1)
% 1.03/1.25          | (v2_struct_0 @ X1)
% 1.03/1.25          | (v2_struct_0 @ X1)
% 1.03/1.25          | ~ (l3_lattices @ X1)
% 1.03/1.25          | ~ (v10_lattices @ X1)
% 1.03/1.25          | ~ (v4_lattice3 @ X1)
% 1.03/1.25          | ((k15_lattice3 @ X1 @ X0)
% 1.03/1.25              = (k16_lattice3 @ X1 @ (a_2_2_lattice3 @ X1 @ X0)))
% 1.03/1.25          | (m1_subset_1 @ 
% 1.03/1.25             (sk_D_3 @ (a_2_2_lattice3 @ X1 @ X0) @ (k15_lattice3 @ X1 @ X0) @ 
% 1.03/1.25              X1) @ 
% 1.03/1.25             (u1_struct_0 @ X1)))),
% 1.03/1.26      inference('sup-', [status(thm)], ['118', '122'])).
% 1.03/1.26  thf('124', plain,
% 1.03/1.26      (![X0 : $i, X1 : $i]:
% 1.03/1.26         ((m1_subset_1 @ 
% 1.03/1.26           (sk_D_3 @ (a_2_2_lattice3 @ X1 @ X0) @ (k15_lattice3 @ X1 @ X0) @ X1) @ 
% 1.03/1.26           (u1_struct_0 @ X1))
% 1.03/1.26          | ((k15_lattice3 @ X1 @ X0)
% 1.03/1.26              = (k16_lattice3 @ X1 @ (a_2_2_lattice3 @ X1 @ X0)))
% 1.03/1.26          | (v2_struct_0 @ X1)
% 1.03/1.26          | ~ (v10_lattices @ X1)
% 1.03/1.26          | ~ (v4_lattice3 @ X1)
% 1.03/1.26          | ~ (l3_lattices @ X1))),
% 1.03/1.26      inference('simplify', [status(thm)], ['123'])).
% 1.03/1.26  thf(redefinition_r3_lattices, axiom,
% 1.03/1.26    (![A:$i,B:$i,C:$i]:
% 1.03/1.26     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 1.03/1.26         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 1.03/1.26         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 1.03/1.26         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 1.03/1.26       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 1.03/1.26  thf('125', plain,
% 1.03/1.26      (![X1 : $i, X2 : $i, X3 : $i]:
% 1.03/1.26         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 1.03/1.26          | ~ (l3_lattices @ X2)
% 1.03/1.26          | ~ (v9_lattices @ X2)
% 1.03/1.26          | ~ (v8_lattices @ X2)
% 1.03/1.26          | ~ (v6_lattices @ X2)
% 1.03/1.26          | (v2_struct_0 @ X2)
% 1.03/1.26          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 1.03/1.26          | (r3_lattices @ X2 @ X1 @ X3)
% 1.03/1.26          | ~ (r1_lattices @ X2 @ X1 @ X3))),
% 1.03/1.26      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 1.03/1.26  thf('126', plain,
% 1.03/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.26         (~ (l3_lattices @ X0)
% 1.03/1.26          | ~ (v4_lattice3 @ X0)
% 1.03/1.26          | ~ (v10_lattices @ X0)
% 1.03/1.26          | (v2_struct_0 @ X0)
% 1.03/1.26          | ((k15_lattice3 @ X0 @ X1)
% 1.03/1.26              = (k16_lattice3 @ X0 @ (a_2_2_lattice3 @ X0 @ X1)))
% 1.03/1.26          | ~ (r1_lattices @ X0 @ 
% 1.03/1.26               (sk_D_3 @ (a_2_2_lattice3 @ X0 @ X1) @ 
% 1.03/1.26                (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 1.03/1.26               X2)
% 1.03/1.26          | (r3_lattices @ X0 @ 
% 1.03/1.26             (sk_D_3 @ (a_2_2_lattice3 @ X0 @ X1) @ (k15_lattice3 @ X0 @ X1) @ 
% 1.03/1.26              X0) @ 
% 1.03/1.26             X2)
% 1.03/1.26          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 1.03/1.26          | (v2_struct_0 @ X0)
% 1.03/1.26          | ~ (v6_lattices @ X0)
% 1.03/1.26          | ~ (v8_lattices @ X0)
% 1.03/1.26          | ~ (v9_lattices @ X0)
% 1.03/1.26          | ~ (l3_lattices @ X0))),
% 1.03/1.26      inference('sup-', [status(thm)], ['124', '125'])).
% 1.03/1.26  thf('127', plain,
% 1.03/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.26         (~ (v9_lattices @ X0)
% 1.03/1.26          | ~ (v8_lattices @ X0)
% 1.03/1.26          | ~ (v6_lattices @ X0)
% 1.03/1.26          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 1.03/1.26          | (r3_lattices @ X0 @ 
% 1.03/1.26             (sk_D_3 @ (a_2_2_lattice3 @ X0 @ X1) @ (k15_lattice3 @ X0 @ X1) @ 
% 1.03/1.26              X0) @ 
% 1.03/1.26             X2)
% 1.03/1.26          | ~ (r1_lattices @ X0 @ 
% 1.03/1.26               (sk_D_3 @ (a_2_2_lattice3 @ X0 @ X1) @ 
% 1.03/1.26                (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 1.03/1.26               X2)
% 1.03/1.26          | ((k15_lattice3 @ X0 @ X1)
% 1.03/1.26              = (k16_lattice3 @ X0 @ (a_2_2_lattice3 @ X0 @ X1)))
% 1.03/1.26          | (v2_struct_0 @ X0)
% 1.03/1.26          | ~ (v10_lattices @ X0)
% 1.03/1.26          | ~ (v4_lattice3 @ X0)
% 1.03/1.26          | ~ (l3_lattices @ X0))),
% 1.03/1.26      inference('simplify', [status(thm)], ['126'])).
% 1.03/1.26  thf('128', plain,
% 1.03/1.26      (((m1_subset_1 @ 
% 1.03/1.26         (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26          (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26         (u1_struct_0 @ sk_A))
% 1.03/1.26        | ~ (l3_lattices @ sk_A)
% 1.03/1.26        | ~ (v4_lattice3 @ sk_A)
% 1.03/1.26        | ~ (v10_lattices @ sk_A)
% 1.03/1.26        | (v2_struct_0 @ sk_A)
% 1.03/1.26        | ((k15_lattice3 @ sk_A @ sk_B)
% 1.03/1.26            = (k16_lattice3 @ sk_A @ (a_2_2_lattice3 @ sk_A @ sk_B)))
% 1.03/1.26        | (r3_lattices @ sk_A @ 
% 1.03/1.26           (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26           (k15_lattice3 @ sk_A @ sk_B))
% 1.03/1.26        | ~ (m1_subset_1 @ (k15_lattice3 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.03/1.26        | ~ (v6_lattices @ sk_A)
% 1.03/1.26        | ~ (v8_lattices @ sk_A)
% 1.03/1.26        | ~ (v9_lattices @ sk_A))),
% 1.03/1.26      inference('sup-', [status(thm)], ['117', '127'])).
% 1.03/1.26  thf('129', plain, ((l3_lattices @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('130', plain, ((v4_lattice3 @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('131', plain, ((v10_lattices @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf(cc1_lattices, axiom,
% 1.03/1.26    (![A:$i]:
% 1.03/1.26     ( ( l3_lattices @ A ) =>
% 1.03/1.26       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 1.03/1.26         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 1.03/1.26           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 1.03/1.26           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 1.03/1.26  thf('132', plain,
% 1.03/1.26      (![X0 : $i]:
% 1.03/1.26         ((v2_struct_0 @ X0)
% 1.03/1.26          | ~ (v10_lattices @ X0)
% 1.03/1.26          | (v6_lattices @ X0)
% 1.03/1.26          | ~ (l3_lattices @ X0))),
% 1.03/1.26      inference('cnf', [status(esa)], [cc1_lattices])).
% 1.03/1.26  thf('133', plain, (~ (v2_struct_0 @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('134', plain,
% 1.03/1.26      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 1.03/1.26      inference('sup-', [status(thm)], ['132', '133'])).
% 1.03/1.26  thf('135', plain, ((l3_lattices @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('136', plain, ((v10_lattices @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('137', plain, ((v6_lattices @ sk_A)),
% 1.03/1.26      inference('demod', [status(thm)], ['134', '135', '136'])).
% 1.03/1.26  thf('138', plain,
% 1.03/1.26      (![X0 : $i]:
% 1.03/1.26         ((v2_struct_0 @ X0)
% 1.03/1.26          | ~ (v10_lattices @ X0)
% 1.03/1.26          | (v8_lattices @ X0)
% 1.03/1.26          | ~ (l3_lattices @ X0))),
% 1.03/1.26      inference('cnf', [status(esa)], [cc1_lattices])).
% 1.03/1.26  thf('139', plain, (~ (v2_struct_0 @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('140', plain,
% 1.03/1.26      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 1.03/1.26      inference('sup-', [status(thm)], ['138', '139'])).
% 1.03/1.26  thf('141', plain, ((l3_lattices @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('142', plain, ((v10_lattices @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('143', plain, ((v8_lattices @ sk_A)),
% 1.03/1.26      inference('demod', [status(thm)], ['140', '141', '142'])).
% 1.03/1.26  thf('144', plain,
% 1.03/1.26      (![X0 : $i]:
% 1.03/1.26         ((v2_struct_0 @ X0)
% 1.03/1.26          | ~ (v10_lattices @ X0)
% 1.03/1.26          | (v9_lattices @ X0)
% 1.03/1.26          | ~ (l3_lattices @ X0))),
% 1.03/1.26      inference('cnf', [status(esa)], [cc1_lattices])).
% 1.03/1.26  thf('145', plain, (~ (v2_struct_0 @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('146', plain,
% 1.03/1.26      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 1.03/1.26      inference('sup-', [status(thm)], ['144', '145'])).
% 1.03/1.26  thf('147', plain, ((l3_lattices @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('148', plain, ((v10_lattices @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('149', plain, ((v9_lattices @ sk_A)),
% 1.03/1.26      inference('demod', [status(thm)], ['146', '147', '148'])).
% 1.03/1.26  thf('150', plain,
% 1.03/1.26      (((m1_subset_1 @ 
% 1.03/1.26         (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26          (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26         (u1_struct_0 @ sk_A))
% 1.03/1.26        | (v2_struct_0 @ sk_A)
% 1.03/1.26        | ((k15_lattice3 @ sk_A @ sk_B)
% 1.03/1.26            = (k16_lattice3 @ sk_A @ (a_2_2_lattice3 @ sk_A @ sk_B)))
% 1.03/1.26        | (r3_lattices @ sk_A @ 
% 1.03/1.26           (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26           (k15_lattice3 @ sk_A @ sk_B))
% 1.03/1.26        | ~ (m1_subset_1 @ (k15_lattice3 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.03/1.26      inference('demod', [status(thm)],
% 1.03/1.26                ['128', '129', '130', '131', '137', '143', '149'])).
% 1.03/1.26  thf('151', plain,
% 1.03/1.26      (((k15_lattice3 @ sk_A @ sk_B)
% 1.03/1.26         != (k16_lattice3 @ sk_A @ (a_2_2_lattice3 @ sk_A @ sk_B)))),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('152', plain,
% 1.03/1.26      (((m1_subset_1 @ 
% 1.03/1.26         (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26          (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26         (u1_struct_0 @ sk_A))
% 1.03/1.26        | (v2_struct_0 @ sk_A)
% 1.03/1.26        | (r3_lattices @ sk_A @ 
% 1.03/1.26           (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26           (k15_lattice3 @ sk_A @ sk_B))
% 1.03/1.26        | ~ (m1_subset_1 @ (k15_lattice3 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.03/1.26      inference('simplify_reflect-', [status(thm)], ['150', '151'])).
% 1.03/1.26  thf('153', plain,
% 1.03/1.26      (((v2_struct_0 @ sk_A)
% 1.03/1.26        | ~ (l3_lattices @ sk_A)
% 1.03/1.26        | (r3_lattices @ sk_A @ 
% 1.03/1.26           (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26           (k15_lattice3 @ sk_A @ sk_B))
% 1.03/1.26        | (v2_struct_0 @ sk_A)
% 1.03/1.26        | (m1_subset_1 @ 
% 1.03/1.26           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26           (u1_struct_0 @ sk_A)))),
% 1.03/1.26      inference('sup-', [status(thm)], ['46', '152'])).
% 1.03/1.26  thf('154', plain, ((l3_lattices @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('155', plain,
% 1.03/1.26      (((v2_struct_0 @ sk_A)
% 1.03/1.26        | (r3_lattices @ sk_A @ 
% 1.03/1.26           (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26           (k15_lattice3 @ sk_A @ sk_B))
% 1.03/1.26        | (v2_struct_0 @ sk_A)
% 1.03/1.26        | (m1_subset_1 @ 
% 1.03/1.26           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26           (u1_struct_0 @ sk_A)))),
% 1.03/1.26      inference('demod', [status(thm)], ['153', '154'])).
% 1.03/1.26  thf('156', plain,
% 1.03/1.26      (((m1_subset_1 @ 
% 1.03/1.26         (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26          (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26         (u1_struct_0 @ sk_A))
% 1.03/1.26        | (r3_lattices @ sk_A @ 
% 1.03/1.26           (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26           (k15_lattice3 @ sk_A @ sk_B))
% 1.03/1.26        | (v2_struct_0 @ sk_A))),
% 1.03/1.26      inference('simplify', [status(thm)], ['155'])).
% 1.03/1.26  thf('157', plain, (~ (v2_struct_0 @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('158', plain,
% 1.03/1.26      (((r3_lattices @ sk_A @ 
% 1.03/1.26         (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26          (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26         (k15_lattice3 @ sk_A @ sk_B))
% 1.03/1.26        | (m1_subset_1 @ 
% 1.03/1.26           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26           (u1_struct_0 @ sk_A)))),
% 1.03/1.26      inference('clc', [status(thm)], ['156', '157'])).
% 1.03/1.26  thf('159', plain,
% 1.03/1.26      (![X13 : $i, X14 : $i]:
% 1.03/1.26         (~ (l3_lattices @ X13)
% 1.03/1.26          | (v2_struct_0 @ X13)
% 1.03/1.26          | (m1_subset_1 @ (k15_lattice3 @ X13 @ X14) @ (u1_struct_0 @ X13)))),
% 1.03/1.26      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 1.03/1.26  thf('160', plain,
% 1.03/1.26      (![X19 : $i, X20 : $i, X23 : $i]:
% 1.03/1.26         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 1.03/1.26          | ~ (r3_lattice3 @ X20 @ X19 @ X23)
% 1.03/1.26          | ~ (r3_lattices @ X20 @ (sk_D_3 @ X23 @ X19 @ X20) @ X19)
% 1.03/1.26          | ((X19) = (k16_lattice3 @ X20 @ X23))
% 1.03/1.26          | ~ (l3_lattices @ X20)
% 1.03/1.26          | ~ (v4_lattice3 @ X20)
% 1.03/1.26          | ~ (v10_lattices @ X20)
% 1.03/1.26          | (v2_struct_0 @ X20))),
% 1.03/1.26      inference('cnf', [status(esa)], [t34_lattice3])).
% 1.03/1.26  thf('161', plain,
% 1.03/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.26         ((v2_struct_0 @ X0)
% 1.03/1.26          | ~ (l3_lattices @ X0)
% 1.03/1.26          | (v2_struct_0 @ X0)
% 1.03/1.26          | ~ (v10_lattices @ X0)
% 1.03/1.26          | ~ (v4_lattice3 @ X0)
% 1.03/1.26          | ~ (l3_lattices @ X0)
% 1.03/1.26          | ((k15_lattice3 @ X0 @ X1) = (k16_lattice3 @ X0 @ X2))
% 1.03/1.26          | ~ (r3_lattices @ X0 @ 
% 1.03/1.26               (sk_D_3 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 1.03/1.26               (k15_lattice3 @ X0 @ X1))
% 1.03/1.26          | ~ (r3_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))),
% 1.03/1.26      inference('sup-', [status(thm)], ['159', '160'])).
% 1.03/1.26  thf('162', plain,
% 1.03/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.26         (~ (r3_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 1.03/1.26          | ~ (r3_lattices @ X0 @ 
% 1.03/1.26               (sk_D_3 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 1.03/1.26               (k15_lattice3 @ X0 @ X1))
% 1.03/1.26          | ((k15_lattice3 @ X0 @ X1) = (k16_lattice3 @ X0 @ X2))
% 1.03/1.26          | ~ (v4_lattice3 @ X0)
% 1.03/1.26          | ~ (v10_lattices @ X0)
% 1.03/1.26          | ~ (l3_lattices @ X0)
% 1.03/1.26          | (v2_struct_0 @ X0))),
% 1.03/1.26      inference('simplify', [status(thm)], ['161'])).
% 1.03/1.26  thf('163', plain,
% 1.03/1.26      (((m1_subset_1 @ 
% 1.03/1.26         (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26          (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26         (u1_struct_0 @ sk_A))
% 1.03/1.26        | (v2_struct_0 @ sk_A)
% 1.03/1.26        | ~ (l3_lattices @ sk_A)
% 1.03/1.26        | ~ (v10_lattices @ sk_A)
% 1.03/1.26        | ~ (v4_lattice3 @ sk_A)
% 1.03/1.26        | ((k15_lattice3 @ sk_A @ sk_B)
% 1.03/1.26            = (k16_lattice3 @ sk_A @ (a_2_2_lattice3 @ sk_A @ sk_B)))
% 1.03/1.26        | ~ (r3_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26             (a_2_2_lattice3 @ sk_A @ sk_B)))),
% 1.03/1.26      inference('sup-', [status(thm)], ['158', '162'])).
% 1.03/1.26  thf('164', plain, ((l3_lattices @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('165', plain, ((v10_lattices @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('166', plain, ((v4_lattice3 @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('167', plain,
% 1.03/1.26      (((m1_subset_1 @ 
% 1.03/1.26         (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26          (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26         (u1_struct_0 @ sk_A))
% 1.03/1.26        | (v2_struct_0 @ sk_A)
% 1.03/1.26        | ((k15_lattice3 @ sk_A @ sk_B)
% 1.03/1.26            = (k16_lattice3 @ sk_A @ (a_2_2_lattice3 @ sk_A @ sk_B)))
% 1.03/1.26        | ~ (r3_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26             (a_2_2_lattice3 @ sk_A @ sk_B)))),
% 1.03/1.26      inference('demod', [status(thm)], ['163', '164', '165', '166'])).
% 1.03/1.26  thf('168', plain,
% 1.03/1.26      (((k15_lattice3 @ sk_A @ sk_B)
% 1.03/1.26         != (k16_lattice3 @ sk_A @ (a_2_2_lattice3 @ sk_A @ sk_B)))),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('169', plain,
% 1.03/1.26      (((m1_subset_1 @ 
% 1.03/1.26         (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26          (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26         (u1_struct_0 @ sk_A))
% 1.03/1.26        | (v2_struct_0 @ sk_A)
% 1.03/1.26        | ~ (r3_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26             (a_2_2_lattice3 @ sk_A @ sk_B)))),
% 1.03/1.26      inference('simplify_reflect-', [status(thm)], ['167', '168'])).
% 1.03/1.26  thf('170', plain, (~ (v2_struct_0 @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('171', plain,
% 1.03/1.26      ((~ (r3_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26           (a_2_2_lattice3 @ sk_A @ sk_B))
% 1.03/1.26        | (m1_subset_1 @ 
% 1.03/1.26           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26           (u1_struct_0 @ sk_A)))),
% 1.03/1.26      inference('clc', [status(thm)], ['169', '170'])).
% 1.03/1.26  thf('172', plain,
% 1.03/1.26      ((~ (l3_lattices @ sk_A)
% 1.03/1.26        | ~ (v4_lattice3 @ sk_A)
% 1.03/1.26        | ~ (v10_lattices @ sk_A)
% 1.03/1.26        | (v2_struct_0 @ sk_A)
% 1.03/1.26        | (m1_subset_1 @ 
% 1.03/1.26           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26           (u1_struct_0 @ sk_A)))),
% 1.03/1.26      inference('sup-', [status(thm)], ['45', '171'])).
% 1.03/1.26  thf('173', plain, ((l3_lattices @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('174', plain, ((v4_lattice3 @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('175', plain, ((v10_lattices @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('176', plain,
% 1.03/1.26      (((v2_struct_0 @ sk_A)
% 1.03/1.26        | (m1_subset_1 @ 
% 1.03/1.26           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26           (u1_struct_0 @ sk_A)))),
% 1.03/1.26      inference('demod', [status(thm)], ['172', '173', '174', '175'])).
% 1.03/1.26  thf('177', plain, (~ (v2_struct_0 @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('178', plain,
% 1.03/1.26      ((m1_subset_1 @ 
% 1.03/1.26        (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26         (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26        (u1_struct_0 @ sk_A))),
% 1.03/1.26      inference('clc', [status(thm)], ['176', '177'])).
% 1.03/1.26  thf('179', plain,
% 1.03/1.26      (![X15 : $i, X16 : $i, X18 : $i]:
% 1.03/1.26         (~ (r4_lattice3 @ X15 @ X18 @ X16)
% 1.03/1.26          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X15))
% 1.03/1.26          | (r2_hidden @ X18 @ (a_2_2_lattice3 @ X15 @ X16))
% 1.03/1.26          | (v2_struct_0 @ X15)
% 1.03/1.26          | ~ (v10_lattices @ X15)
% 1.03/1.26          | ~ (v4_lattice3 @ X15)
% 1.03/1.26          | ~ (l3_lattices @ X15))),
% 1.03/1.26      inference('simplify', [status(thm)], ['9'])).
% 1.03/1.26  thf('180', plain,
% 1.03/1.26      (![X0 : $i]:
% 1.03/1.26         (~ (l3_lattices @ sk_A)
% 1.03/1.26          | ~ (v4_lattice3 @ sk_A)
% 1.03/1.26          | ~ (v10_lattices @ sk_A)
% 1.03/1.26          | (v2_struct_0 @ sk_A)
% 1.03/1.26          | (r2_hidden @ 
% 1.03/1.26             (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26              (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26             (a_2_2_lattice3 @ sk_A @ X0))
% 1.03/1.26          | ~ (r4_lattice3 @ sk_A @ 
% 1.03/1.26               (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26                (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26               X0))),
% 1.03/1.26      inference('sup-', [status(thm)], ['178', '179'])).
% 1.03/1.26  thf('181', plain, ((l3_lattices @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('182', plain, ((v4_lattice3 @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('183', plain, ((v10_lattices @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('184', plain,
% 1.03/1.26      (![X0 : $i]:
% 1.03/1.26         ((v2_struct_0 @ sk_A)
% 1.03/1.26          | (r2_hidden @ 
% 1.03/1.26             (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26              (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26             (a_2_2_lattice3 @ sk_A @ X0))
% 1.03/1.26          | ~ (r4_lattice3 @ sk_A @ 
% 1.03/1.26               (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26                (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26               X0))),
% 1.03/1.26      inference('demod', [status(thm)], ['180', '181', '182', '183'])).
% 1.03/1.26  thf('185', plain, (~ (v2_struct_0 @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('186', plain,
% 1.03/1.26      (![X0 : $i]:
% 1.03/1.26         (~ (r4_lattice3 @ sk_A @ 
% 1.03/1.26             (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26              (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26             X0)
% 1.03/1.26          | (r2_hidden @ 
% 1.03/1.26             (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26              (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26             (a_2_2_lattice3 @ sk_A @ X0)))),
% 1.03/1.26      inference('clc', [status(thm)], ['184', '185'])).
% 1.03/1.26  thf('187', plain,
% 1.03/1.26      ((~ (l3_lattices @ sk_A)
% 1.03/1.26        | ~ (v4_lattice3 @ sk_A)
% 1.03/1.26        | ~ (v10_lattices @ sk_A)
% 1.03/1.26        | (v2_struct_0 @ sk_A)
% 1.03/1.26        | (r3_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26           (a_2_2_lattice3 @ sk_A @ sk_B))
% 1.03/1.26        | ~ (l3_lattices @ sk_A)
% 1.03/1.26        | (v2_struct_0 @ sk_A)
% 1.03/1.26        | (r2_hidden @ 
% 1.03/1.26           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26           (a_2_2_lattice3 @ sk_A @ sk_B)))),
% 1.03/1.26      inference('sup-', [status(thm)], ['25', '186'])).
% 1.03/1.26  thf('188', plain, ((l3_lattices @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('189', plain, ((v4_lattice3 @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('190', plain, ((v10_lattices @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('191', plain, ((l3_lattices @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('192', plain,
% 1.03/1.26      (((v2_struct_0 @ sk_A)
% 1.03/1.26        | (r3_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26           (a_2_2_lattice3 @ sk_A @ sk_B))
% 1.03/1.26        | (v2_struct_0 @ sk_A)
% 1.03/1.26        | (r2_hidden @ 
% 1.03/1.26           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26           (a_2_2_lattice3 @ sk_A @ sk_B)))),
% 1.03/1.26      inference('demod', [status(thm)], ['187', '188', '189', '190', '191'])).
% 1.03/1.26  thf('193', plain,
% 1.03/1.26      (((r2_hidden @ 
% 1.03/1.26         (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26          (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26         (a_2_2_lattice3 @ sk_A @ sk_B))
% 1.03/1.26        | (r3_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26           (a_2_2_lattice3 @ sk_A @ sk_B))
% 1.03/1.26        | (v2_struct_0 @ sk_A))),
% 1.03/1.26      inference('simplify', [status(thm)], ['192'])).
% 1.03/1.26  thf('194', plain, (~ (v2_struct_0 @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('195', plain,
% 1.03/1.26      (((r3_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26         (a_2_2_lattice3 @ sk_A @ sk_B))
% 1.03/1.26        | (r2_hidden @ 
% 1.03/1.26           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26           (a_2_2_lattice3 @ sk_A @ sk_B)))),
% 1.03/1.26      inference('clc', [status(thm)], ['193', '194'])).
% 1.03/1.26  thf('196', plain,
% 1.03/1.26      (![X0 : $i, X1 : $i]:
% 1.03/1.26         ((r3_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 1.03/1.26           (a_2_2_lattice3 @ X0 @ X1))
% 1.03/1.26          | (v2_struct_0 @ X0)
% 1.03/1.26          | ~ (v10_lattices @ X0)
% 1.03/1.26          | ~ (v4_lattice3 @ X0)
% 1.03/1.26          | ~ (l3_lattices @ X0))),
% 1.03/1.26      inference('simplify', [status(thm)], ['44'])).
% 1.03/1.26  thf('197', plain,
% 1.03/1.26      (![X13 : $i, X14 : $i]:
% 1.03/1.26         (~ (l3_lattices @ X13)
% 1.03/1.26          | (v2_struct_0 @ X13)
% 1.03/1.26          | (m1_subset_1 @ (k15_lattice3 @ X13 @ X14) @ (u1_struct_0 @ X13)))),
% 1.03/1.26      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 1.03/1.26  thf('198', plain,
% 1.03/1.26      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 1.03/1.26         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 1.03/1.26          | ~ (r3_lattice3 @ X5 @ X4 @ X6)
% 1.03/1.26          | ~ (r2_hidden @ X7 @ X6)
% 1.03/1.26          | (r1_lattices @ X5 @ X4 @ X7)
% 1.03/1.26          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X5))
% 1.03/1.26          | ~ (l3_lattices @ X5)
% 1.03/1.26          | (v2_struct_0 @ X5))),
% 1.03/1.26      inference('cnf', [status(esa)], [d16_lattice3])).
% 1.03/1.26  thf('199', plain,
% 1.03/1.26      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.03/1.26         ((v2_struct_0 @ X0)
% 1.03/1.26          | ~ (l3_lattices @ X0)
% 1.03/1.26          | (v2_struct_0 @ X0)
% 1.03/1.26          | ~ (l3_lattices @ X0)
% 1.03/1.26          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 1.03/1.26          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 1.03/1.26          | ~ (r2_hidden @ X2 @ X3)
% 1.03/1.26          | ~ (r3_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X3))),
% 1.03/1.26      inference('sup-', [status(thm)], ['197', '198'])).
% 1.03/1.26  thf('200', plain,
% 1.03/1.26      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.03/1.26         (~ (r3_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X3)
% 1.03/1.26          | ~ (r2_hidden @ X2 @ X3)
% 1.03/1.26          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 1.03/1.26          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 1.03/1.26          | ~ (l3_lattices @ X0)
% 1.03/1.26          | (v2_struct_0 @ X0))),
% 1.03/1.26      inference('simplify', [status(thm)], ['199'])).
% 1.03/1.26  thf('201', plain,
% 1.03/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.26         (~ (l3_lattices @ X1)
% 1.03/1.26          | ~ (v4_lattice3 @ X1)
% 1.03/1.26          | ~ (v10_lattices @ X1)
% 1.03/1.26          | (v2_struct_0 @ X1)
% 1.03/1.26          | (v2_struct_0 @ X1)
% 1.03/1.26          | ~ (l3_lattices @ X1)
% 1.03/1.26          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 1.03/1.26          | (r1_lattices @ X1 @ (k15_lattice3 @ X1 @ X0) @ X2)
% 1.03/1.26          | ~ (r2_hidden @ X2 @ (a_2_2_lattice3 @ X1 @ X0)))),
% 1.03/1.26      inference('sup-', [status(thm)], ['196', '200'])).
% 1.03/1.26  thf('202', plain,
% 1.03/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.26         (~ (r2_hidden @ X2 @ (a_2_2_lattice3 @ X1 @ X0))
% 1.03/1.26          | (r1_lattices @ X1 @ (k15_lattice3 @ X1 @ X0) @ X2)
% 1.03/1.26          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 1.03/1.26          | (v2_struct_0 @ X1)
% 1.03/1.26          | ~ (v10_lattices @ X1)
% 1.03/1.26          | ~ (v4_lattice3 @ X1)
% 1.03/1.26          | ~ (l3_lattices @ X1))),
% 1.03/1.26      inference('simplify', [status(thm)], ['201'])).
% 1.03/1.26  thf('203', plain,
% 1.03/1.26      (((r3_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26         (a_2_2_lattice3 @ sk_A @ sk_B))
% 1.03/1.26        | ~ (l3_lattices @ sk_A)
% 1.03/1.26        | ~ (v4_lattice3 @ sk_A)
% 1.03/1.26        | ~ (v10_lattices @ sk_A)
% 1.03/1.26        | (v2_struct_0 @ sk_A)
% 1.03/1.26        | ~ (m1_subset_1 @ 
% 1.03/1.26             (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26              (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26             (u1_struct_0 @ sk_A))
% 1.03/1.26        | (r1_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26            (k15_lattice3 @ sk_A @ sk_B) @ sk_A)))),
% 1.03/1.26      inference('sup-', [status(thm)], ['195', '202'])).
% 1.03/1.26  thf('204', plain, ((l3_lattices @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('205', plain, ((v4_lattice3 @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('206', plain, ((v10_lattices @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('207', plain,
% 1.03/1.26      ((m1_subset_1 @ 
% 1.03/1.26        (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26         (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26        (u1_struct_0 @ sk_A))),
% 1.03/1.26      inference('clc', [status(thm)], ['176', '177'])).
% 1.03/1.26  thf('208', plain,
% 1.03/1.26      (((r3_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26         (a_2_2_lattice3 @ sk_A @ sk_B))
% 1.03/1.26        | (v2_struct_0 @ sk_A)
% 1.03/1.26        | (r1_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26            (k15_lattice3 @ sk_A @ sk_B) @ sk_A)))),
% 1.03/1.26      inference('demod', [status(thm)], ['203', '204', '205', '206', '207'])).
% 1.03/1.26  thf('209', plain, (~ (v2_struct_0 @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('210', plain,
% 1.03/1.26      (((r1_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26         (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26          (k15_lattice3 @ sk_A @ sk_B) @ sk_A))
% 1.03/1.26        | (r3_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26           (a_2_2_lattice3 @ sk_A @ sk_B)))),
% 1.03/1.26      inference('clc', [status(thm)], ['208', '209'])).
% 1.03/1.26  thf('211', plain,
% 1.03/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.26         (~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 1.03/1.26             (sk_D @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 1.03/1.26          | (r3_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 1.03/1.26          | ~ (l3_lattices @ X0)
% 1.03/1.26          | (v2_struct_0 @ X0))),
% 1.03/1.26      inference('simplify', [status(thm)], ['42'])).
% 1.03/1.26  thf('212', plain,
% 1.03/1.26      (((r3_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26         (a_2_2_lattice3 @ sk_A @ sk_B))
% 1.03/1.26        | (v2_struct_0 @ sk_A)
% 1.03/1.26        | ~ (l3_lattices @ sk_A)
% 1.03/1.26        | (r3_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26           (a_2_2_lattice3 @ sk_A @ sk_B)))),
% 1.03/1.26      inference('sup-', [status(thm)], ['210', '211'])).
% 1.03/1.26  thf('213', plain, ((l3_lattices @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('214', plain,
% 1.03/1.26      (((r3_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26         (a_2_2_lattice3 @ sk_A @ sk_B))
% 1.03/1.26        | (v2_struct_0 @ sk_A)
% 1.03/1.26        | (r3_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26           (a_2_2_lattice3 @ sk_A @ sk_B)))),
% 1.03/1.26      inference('demod', [status(thm)], ['212', '213'])).
% 1.03/1.26  thf('215', plain,
% 1.03/1.26      (((v2_struct_0 @ sk_A)
% 1.03/1.26        | (r3_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26           (a_2_2_lattice3 @ sk_A @ sk_B)))),
% 1.03/1.26      inference('simplify', [status(thm)], ['214'])).
% 1.03/1.26  thf('216', plain, (~ (v2_struct_0 @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('217', plain,
% 1.03/1.26      ((r3_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26        (a_2_2_lattice3 @ sk_A @ sk_B))),
% 1.03/1.26      inference('clc', [status(thm)], ['215', '216'])).
% 1.03/1.26  thf('218', plain,
% 1.03/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.26         (~ (r3_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 1.03/1.26          | (r3_lattice3 @ X0 @ 
% 1.03/1.26             (sk_D_3 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X2)
% 1.03/1.26          | ((k15_lattice3 @ X0 @ X1) = (k16_lattice3 @ X0 @ X2))
% 1.03/1.26          | ~ (v4_lattice3 @ X0)
% 1.03/1.26          | ~ (v10_lattices @ X0)
% 1.03/1.26          | ~ (l3_lattices @ X0)
% 1.03/1.26          | (v2_struct_0 @ X0))),
% 1.03/1.26      inference('simplify', [status(thm)], ['52'])).
% 1.03/1.26  thf('219', plain,
% 1.03/1.26      (((v2_struct_0 @ sk_A)
% 1.03/1.26        | ~ (l3_lattices @ sk_A)
% 1.03/1.26        | ~ (v10_lattices @ sk_A)
% 1.03/1.26        | ~ (v4_lattice3 @ sk_A)
% 1.03/1.26        | ((k15_lattice3 @ sk_A @ sk_B)
% 1.03/1.26            = (k16_lattice3 @ sk_A @ (a_2_2_lattice3 @ sk_A @ sk_B)))
% 1.03/1.26        | (r3_lattice3 @ sk_A @ 
% 1.03/1.26           (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26           (a_2_2_lattice3 @ sk_A @ sk_B)))),
% 1.03/1.26      inference('sup-', [status(thm)], ['217', '218'])).
% 1.03/1.26  thf('220', plain, ((l3_lattices @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('221', plain, ((v10_lattices @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('222', plain, ((v4_lattice3 @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('223', plain,
% 1.03/1.26      (((v2_struct_0 @ sk_A)
% 1.03/1.26        | ((k15_lattice3 @ sk_A @ sk_B)
% 1.03/1.26            = (k16_lattice3 @ sk_A @ (a_2_2_lattice3 @ sk_A @ sk_B)))
% 1.03/1.26        | (r3_lattice3 @ sk_A @ 
% 1.03/1.26           (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26           (a_2_2_lattice3 @ sk_A @ sk_B)))),
% 1.03/1.26      inference('demod', [status(thm)], ['219', '220', '221', '222'])).
% 1.03/1.26  thf('224', plain,
% 1.03/1.26      (((k15_lattice3 @ sk_A @ sk_B)
% 1.03/1.26         != (k16_lattice3 @ sk_A @ (a_2_2_lattice3 @ sk_A @ sk_B)))),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('225', plain,
% 1.03/1.26      (((v2_struct_0 @ sk_A)
% 1.03/1.26        | (r3_lattice3 @ sk_A @ 
% 1.03/1.26           (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26           (a_2_2_lattice3 @ sk_A @ sk_B)))),
% 1.03/1.26      inference('simplify_reflect-', [status(thm)], ['223', '224'])).
% 1.03/1.26  thf('226', plain, (~ (v2_struct_0 @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('227', plain,
% 1.03/1.26      ((r3_lattice3 @ sk_A @ 
% 1.03/1.26        (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26         (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26        (a_2_2_lattice3 @ sk_A @ sk_B))),
% 1.03/1.26      inference('clc', [status(thm)], ['225', '226'])).
% 1.03/1.26  thf('228', plain,
% 1.03/1.26      ((r3_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26        (a_2_2_lattice3 @ sk_A @ sk_B))),
% 1.03/1.26      inference('clc', [status(thm)], ['215', '216'])).
% 1.03/1.26  thf('229', plain,
% 1.03/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.26         (~ (r3_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 1.03/1.26          | (m1_subset_1 @ (sk_D_3 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 1.03/1.26             (u1_struct_0 @ X0))
% 1.03/1.26          | ((k15_lattice3 @ X0 @ X1) = (k16_lattice3 @ X0 @ X2))
% 1.03/1.26          | ~ (v4_lattice3 @ X0)
% 1.03/1.26          | ~ (v10_lattices @ X0)
% 1.03/1.26          | ~ (l3_lattices @ X0)
% 1.03/1.26          | (v2_struct_0 @ X0))),
% 1.03/1.26      inference('simplify', [status(thm)], ['121'])).
% 1.03/1.26  thf('230', plain,
% 1.03/1.26      (((v2_struct_0 @ sk_A)
% 1.03/1.26        | ~ (l3_lattices @ sk_A)
% 1.03/1.26        | ~ (v10_lattices @ sk_A)
% 1.03/1.26        | ~ (v4_lattice3 @ sk_A)
% 1.03/1.26        | ((k15_lattice3 @ sk_A @ sk_B)
% 1.03/1.26            = (k16_lattice3 @ sk_A @ (a_2_2_lattice3 @ sk_A @ sk_B)))
% 1.03/1.26        | (m1_subset_1 @ 
% 1.03/1.26           (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26           (u1_struct_0 @ sk_A)))),
% 1.03/1.26      inference('sup-', [status(thm)], ['228', '229'])).
% 1.03/1.26  thf('231', plain, ((l3_lattices @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('232', plain, ((v10_lattices @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('233', plain, ((v4_lattice3 @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('234', plain,
% 1.03/1.26      (((v2_struct_0 @ sk_A)
% 1.03/1.26        | ((k15_lattice3 @ sk_A @ sk_B)
% 1.03/1.26            = (k16_lattice3 @ sk_A @ (a_2_2_lattice3 @ sk_A @ sk_B)))
% 1.03/1.26        | (m1_subset_1 @ 
% 1.03/1.26           (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26           (u1_struct_0 @ sk_A)))),
% 1.03/1.26      inference('demod', [status(thm)], ['230', '231', '232', '233'])).
% 1.03/1.26  thf('235', plain,
% 1.03/1.26      (((k15_lattice3 @ sk_A @ sk_B)
% 1.03/1.26         != (k16_lattice3 @ sk_A @ (a_2_2_lattice3 @ sk_A @ sk_B)))),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('236', plain,
% 1.03/1.26      (((v2_struct_0 @ sk_A)
% 1.03/1.26        | (m1_subset_1 @ 
% 1.03/1.26           (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26           (u1_struct_0 @ sk_A)))),
% 1.03/1.26      inference('simplify_reflect-', [status(thm)], ['234', '235'])).
% 1.03/1.26  thf('237', plain, (~ (v2_struct_0 @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('238', plain,
% 1.03/1.26      ((m1_subset_1 @ 
% 1.03/1.26        (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26         (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26        (u1_struct_0 @ sk_A))),
% 1.03/1.26      inference('clc', [status(thm)], ['236', '237'])).
% 1.03/1.26  thf('239', plain,
% 1.03/1.26      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 1.03/1.26         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 1.03/1.26          | ~ (r3_lattice3 @ X5 @ X4 @ X6)
% 1.03/1.26          | ~ (r2_hidden @ X7 @ X6)
% 1.03/1.26          | (r1_lattices @ X5 @ X4 @ X7)
% 1.03/1.26          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X5))
% 1.03/1.26          | ~ (l3_lattices @ X5)
% 1.03/1.26          | (v2_struct_0 @ X5))),
% 1.03/1.26      inference('cnf', [status(esa)], [d16_lattice3])).
% 1.03/1.26  thf('240', plain,
% 1.03/1.26      (![X0 : $i, X1 : $i]:
% 1.03/1.26         ((v2_struct_0 @ sk_A)
% 1.03/1.26          | ~ (l3_lattices @ sk_A)
% 1.03/1.26          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.03/1.26          | (r1_lattices @ sk_A @ 
% 1.03/1.26             (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26              (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26             X0)
% 1.03/1.26          | ~ (r2_hidden @ X0 @ X1)
% 1.03/1.26          | ~ (r3_lattice3 @ sk_A @ 
% 1.03/1.26               (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26                (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26               X1))),
% 1.03/1.26      inference('sup-', [status(thm)], ['238', '239'])).
% 1.03/1.26  thf('241', plain, ((l3_lattices @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('242', plain,
% 1.03/1.26      (![X0 : $i, X1 : $i]:
% 1.03/1.26         ((v2_struct_0 @ sk_A)
% 1.03/1.26          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.03/1.26          | (r1_lattices @ sk_A @ 
% 1.03/1.26             (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26              (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26             X0)
% 1.03/1.26          | ~ (r2_hidden @ X0 @ X1)
% 1.03/1.26          | ~ (r3_lattice3 @ sk_A @ 
% 1.03/1.26               (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26                (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26               X1))),
% 1.03/1.26      inference('demod', [status(thm)], ['240', '241'])).
% 1.03/1.26  thf('243', plain,
% 1.03/1.26      (![X0 : $i]:
% 1.03/1.26         (~ (r2_hidden @ X0 @ (a_2_2_lattice3 @ sk_A @ sk_B))
% 1.03/1.26          | (r1_lattices @ sk_A @ 
% 1.03/1.26             (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26              (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26             X0)
% 1.03/1.26          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.03/1.26          | (v2_struct_0 @ sk_A))),
% 1.03/1.26      inference('sup-', [status(thm)], ['227', '242'])).
% 1.03/1.26  thf('244', plain,
% 1.03/1.26      (((v2_struct_0 @ sk_A)
% 1.03/1.26        | ~ (l3_lattices @ sk_A)
% 1.03/1.26        | ~ (v10_lattices @ sk_A)
% 1.03/1.26        | ~ (v4_lattice3 @ sk_A)
% 1.03/1.26        | (v2_struct_0 @ sk_A)
% 1.03/1.26        | ~ (m1_subset_1 @ (k15_lattice3 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.03/1.26        | (r1_lattices @ sk_A @ 
% 1.03/1.26           (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26           (k15_lattice3 @ sk_A @ sk_B)))),
% 1.03/1.26      inference('sup-', [status(thm)], ['14', '243'])).
% 1.03/1.26  thf('245', plain, ((l3_lattices @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('246', plain, ((v10_lattices @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('247', plain, ((v4_lattice3 @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('248', plain,
% 1.03/1.26      (((v2_struct_0 @ sk_A)
% 1.03/1.26        | (v2_struct_0 @ sk_A)
% 1.03/1.26        | ~ (m1_subset_1 @ (k15_lattice3 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.03/1.26        | (r1_lattices @ sk_A @ 
% 1.03/1.26           (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26           (k15_lattice3 @ sk_A @ sk_B)))),
% 1.03/1.26      inference('demod', [status(thm)], ['244', '245', '246', '247'])).
% 1.03/1.26  thf('249', plain,
% 1.03/1.26      (((r1_lattices @ sk_A @ 
% 1.03/1.26         (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26          (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26         (k15_lattice3 @ sk_A @ sk_B))
% 1.03/1.26        | ~ (m1_subset_1 @ (k15_lattice3 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.03/1.26        | (v2_struct_0 @ sk_A))),
% 1.03/1.26      inference('simplify', [status(thm)], ['248'])).
% 1.03/1.26  thf('250', plain, (~ (v2_struct_0 @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('251', plain,
% 1.03/1.26      ((~ (m1_subset_1 @ (k15_lattice3 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.03/1.26        | (r1_lattices @ sk_A @ 
% 1.03/1.26           (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26           (k15_lattice3 @ sk_A @ sk_B)))),
% 1.03/1.26      inference('clc', [status(thm)], ['249', '250'])).
% 1.03/1.26  thf('252', plain,
% 1.03/1.26      (((v2_struct_0 @ sk_A)
% 1.03/1.26        | ~ (l3_lattices @ sk_A)
% 1.03/1.26        | (r1_lattices @ sk_A @ 
% 1.03/1.26           (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26           (k15_lattice3 @ sk_A @ sk_B)))),
% 1.03/1.26      inference('sup-', [status(thm)], ['2', '251'])).
% 1.03/1.26  thf('253', plain, ((l3_lattices @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('254', plain,
% 1.03/1.26      (((v2_struct_0 @ sk_A)
% 1.03/1.26        | (r1_lattices @ sk_A @ 
% 1.03/1.26           (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26           (k15_lattice3 @ sk_A @ sk_B)))),
% 1.03/1.26      inference('demod', [status(thm)], ['252', '253'])).
% 1.03/1.26  thf('255', plain, (~ (v2_struct_0 @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('256', plain,
% 1.03/1.26      ((r1_lattices @ sk_A @ 
% 1.03/1.26        (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26         (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26        (k15_lattice3 @ sk_A @ sk_B))),
% 1.03/1.26      inference('clc', [status(thm)], ['254', '255'])).
% 1.03/1.26  thf('257', plain,
% 1.03/1.26      ((m1_subset_1 @ 
% 1.03/1.26        (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26         (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26        (u1_struct_0 @ sk_A))),
% 1.03/1.26      inference('clc', [status(thm)], ['236', '237'])).
% 1.03/1.26  thf('258', plain,
% 1.03/1.26      (![X1 : $i, X2 : $i, X3 : $i]:
% 1.03/1.26         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 1.03/1.26          | ~ (l3_lattices @ X2)
% 1.03/1.26          | ~ (v9_lattices @ X2)
% 1.03/1.26          | ~ (v8_lattices @ X2)
% 1.03/1.26          | ~ (v6_lattices @ X2)
% 1.03/1.26          | (v2_struct_0 @ X2)
% 1.03/1.26          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 1.03/1.26          | (r3_lattices @ X2 @ X1 @ X3)
% 1.03/1.26          | ~ (r1_lattices @ X2 @ X1 @ X3))),
% 1.03/1.26      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 1.03/1.26  thf('259', plain,
% 1.03/1.26      (![X0 : $i]:
% 1.03/1.26         (~ (r1_lattices @ sk_A @ 
% 1.03/1.26             (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26              (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26             X0)
% 1.03/1.26          | (r3_lattices @ sk_A @ 
% 1.03/1.26             (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26              (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26             X0)
% 1.03/1.26          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.03/1.26          | (v2_struct_0 @ sk_A)
% 1.03/1.26          | ~ (v6_lattices @ sk_A)
% 1.03/1.26          | ~ (v8_lattices @ sk_A)
% 1.03/1.26          | ~ (v9_lattices @ sk_A)
% 1.03/1.26          | ~ (l3_lattices @ sk_A))),
% 1.03/1.26      inference('sup-', [status(thm)], ['257', '258'])).
% 1.03/1.26  thf('260', plain, ((v6_lattices @ sk_A)),
% 1.03/1.26      inference('demod', [status(thm)], ['134', '135', '136'])).
% 1.03/1.26  thf('261', plain, ((v8_lattices @ sk_A)),
% 1.03/1.26      inference('demod', [status(thm)], ['140', '141', '142'])).
% 1.03/1.26  thf('262', plain, ((v9_lattices @ sk_A)),
% 1.03/1.26      inference('demod', [status(thm)], ['146', '147', '148'])).
% 1.03/1.26  thf('263', plain, ((l3_lattices @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('264', plain,
% 1.03/1.26      (![X0 : $i]:
% 1.03/1.26         (~ (r1_lattices @ sk_A @ 
% 1.03/1.26             (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26              (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26             X0)
% 1.03/1.26          | (r3_lattices @ sk_A @ 
% 1.03/1.26             (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26              (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26             X0)
% 1.03/1.26          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.03/1.26          | (v2_struct_0 @ sk_A))),
% 1.03/1.26      inference('demod', [status(thm)], ['259', '260', '261', '262', '263'])).
% 1.03/1.26  thf('265', plain,
% 1.03/1.26      (((v2_struct_0 @ sk_A)
% 1.03/1.26        | ~ (m1_subset_1 @ (k15_lattice3 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.03/1.26        | (r3_lattices @ sk_A @ 
% 1.03/1.26           (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26           (k15_lattice3 @ sk_A @ sk_B)))),
% 1.03/1.26      inference('sup-', [status(thm)], ['256', '264'])).
% 1.03/1.26  thf('266', plain, (~ (v2_struct_0 @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('267', plain,
% 1.03/1.26      (((r3_lattices @ sk_A @ 
% 1.03/1.26         (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26          (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26         (k15_lattice3 @ sk_A @ sk_B))
% 1.03/1.26        | ~ (m1_subset_1 @ (k15_lattice3 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.03/1.26      inference('clc', [status(thm)], ['265', '266'])).
% 1.03/1.26  thf('268', plain,
% 1.03/1.26      (((v2_struct_0 @ sk_A)
% 1.03/1.26        | ~ (l3_lattices @ sk_A)
% 1.03/1.26        | (r3_lattices @ sk_A @ 
% 1.03/1.26           (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26           (k15_lattice3 @ sk_A @ sk_B)))),
% 1.03/1.26      inference('sup-', [status(thm)], ['1', '267'])).
% 1.03/1.26  thf('269', plain, ((l3_lattices @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('270', plain,
% 1.03/1.26      (((v2_struct_0 @ sk_A)
% 1.03/1.26        | (r3_lattices @ sk_A @ 
% 1.03/1.26           (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26            (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26           (k15_lattice3 @ sk_A @ sk_B)))),
% 1.03/1.26      inference('demod', [status(thm)], ['268', '269'])).
% 1.03/1.26  thf('271', plain, (~ (v2_struct_0 @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('272', plain,
% 1.03/1.26      ((r3_lattices @ sk_A @ 
% 1.03/1.26        (sk_D_3 @ (a_2_2_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26         (k15_lattice3 @ sk_A @ sk_B) @ sk_A) @ 
% 1.03/1.26        (k15_lattice3 @ sk_A @ sk_B))),
% 1.03/1.26      inference('clc', [status(thm)], ['270', '271'])).
% 1.03/1.26  thf('273', plain,
% 1.03/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.26         (~ (r3_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 1.03/1.26          | ~ (r3_lattices @ X0 @ 
% 1.03/1.26               (sk_D_3 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 1.03/1.26               (k15_lattice3 @ X0 @ X1))
% 1.03/1.26          | ((k15_lattice3 @ X0 @ X1) = (k16_lattice3 @ X0 @ X2))
% 1.03/1.26          | ~ (v4_lattice3 @ X0)
% 1.03/1.26          | ~ (v10_lattices @ X0)
% 1.03/1.26          | ~ (l3_lattices @ X0)
% 1.03/1.26          | (v2_struct_0 @ X0))),
% 1.03/1.26      inference('simplify', [status(thm)], ['161'])).
% 1.03/1.26  thf('274', plain,
% 1.03/1.26      (((v2_struct_0 @ sk_A)
% 1.03/1.26        | ~ (l3_lattices @ sk_A)
% 1.03/1.26        | ~ (v10_lattices @ sk_A)
% 1.03/1.26        | ~ (v4_lattice3 @ sk_A)
% 1.03/1.26        | ((k15_lattice3 @ sk_A @ sk_B)
% 1.03/1.26            = (k16_lattice3 @ sk_A @ (a_2_2_lattice3 @ sk_A @ sk_B)))
% 1.03/1.26        | ~ (r3_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26             (a_2_2_lattice3 @ sk_A @ sk_B)))),
% 1.03/1.26      inference('sup-', [status(thm)], ['272', '273'])).
% 1.03/1.26  thf('275', plain, ((l3_lattices @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('276', plain, ((v10_lattices @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('277', plain, ((v4_lattice3 @ sk_A)),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('278', plain,
% 1.03/1.26      ((r3_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 1.03/1.26        (a_2_2_lattice3 @ sk_A @ sk_B))),
% 1.03/1.26      inference('clc', [status(thm)], ['215', '216'])).
% 1.03/1.26  thf('279', plain,
% 1.03/1.26      (((v2_struct_0 @ sk_A)
% 1.03/1.26        | ((k15_lattice3 @ sk_A @ sk_B)
% 1.03/1.26            = (k16_lattice3 @ sk_A @ (a_2_2_lattice3 @ sk_A @ sk_B))))),
% 1.03/1.26      inference('demod', [status(thm)], ['274', '275', '276', '277', '278'])).
% 1.03/1.26  thf('280', plain,
% 1.03/1.26      (((k15_lattice3 @ sk_A @ sk_B)
% 1.03/1.26         != (k16_lattice3 @ sk_A @ (a_2_2_lattice3 @ sk_A @ sk_B)))),
% 1.03/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.26  thf('281', plain, ((v2_struct_0 @ sk_A)),
% 1.03/1.26      inference('simplify_reflect-', [status(thm)], ['279', '280'])).
% 1.03/1.26  thf('282', plain, ($false), inference('demod', [status(thm)], ['0', '281'])).
% 1.03/1.26  
% 1.03/1.26  % SZS output end Refutation
% 1.03/1.26  
% 1.08/1.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
