%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TUtVbxHW3I

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:29 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   77 (  98 expanded)
%              Number of leaves         :   23 (  38 expanded)
%              Depth                    :   27
%              Number of atoms          : 1230 (1750 expanded)
%              Number of equality atoms :   31 (  33 expanded)
%              Maximal formula depth    :   21 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(a_2_1_lattice3_type,type,(
    a_2_1_lattice3: $i > $i > $i )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r4_lattice3_type,type,(
    r4_lattice3: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(r3_lattice3_type,type,(
    r3_lattice3: $i > $i > $i > $o )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t40_lattice3,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v4_lattice3 @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( r3_lattice3 @ A @ B @ C )
               => ( r3_lattices @ A @ B @ ( k16_lattice3 @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t40_lattice3])).

thf('0',plain,(
    ~ ( r3_lattices @ sk_A @ sk_B_1 @ ( k16_lattice3 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r3_lattice3 @ sk_A @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d22_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( k16_lattice3 @ A @ B )
          = ( k15_lattice3 @ A @ ( a_2_1_lattice3 @ A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k16_lattice3 @ X8 @ X9 )
        = ( k15_lattice3 @ X8 @ ( a_2_1_lattice3 @ X8 @ X9 ) ) )
      | ~ ( l3_lattices @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d22_lattice3])).

thf(d18_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( ( v4_lattice3 @ A )
      <=> ! [B: $i] :
          ? [C: $i] :
            ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ( ( r4_lattice3 @ A @ D @ B )
                 => ( r1_lattices @ A @ C @ D ) ) )
            & ( r4_lattice3 @ A @ C @ B )
            & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v4_lattice3 @ X1 )
      | ( r4_lattice3 @ X1 @ ( sk_C @ X2 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('5',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v4_lattice3 @ X1 )
      | ( m1_subset_1 @ ( sk_C @ X2 @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('6',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v4_lattice3 @ X1 )
      | ( r4_lattice3 @ X1 @ ( sk_C @ X2 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('7',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v4_lattice3 @ X1 )
      | ( m1_subset_1 @ ( sk_C @ X2 @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

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
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( v10_lattices @ X4 )
      | ~ ( v4_lattice3 @ X4 )
      | ~ ( l3_lattices @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ~ ( r4_lattice3 @ X4 @ X5 @ X6 )
      | ( r4_lattice3 @ X4 @ ( sk_D_1 @ X5 @ X6 @ X4 ) @ X6 )
      | ( X5
        = ( k15_lattice3 @ X4 @ X6 ) )
      | ~ ( l3_lattices @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( X5
        = ( k15_lattice3 @ X4 @ X6 ) )
      | ( r4_lattice3 @ X4 @ ( sk_D_1 @ X5 @ X6 @ X4 ) @ X6 )
      | ~ ( r4_lattice3 @ X4 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l3_lattices @ X4 )
      | ~ ( v4_lattice3 @ X4 )
      | ~ ( v10_lattices @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r4_lattice3 @ X0 @ ( sk_D_1 @ ( sk_C @ X1 @ X0 ) @ X2 @ X0 ) @ X2 )
      | ( ( sk_C @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X2 ) )
      | ( r4_lattice3 @ X0 @ ( sk_D_1 @ ( sk_C @ X1 @ X0 ) @ X2 @ X0 ) @ X2 )
      | ~ ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( r4_lattice3 @ X1 @ ( sk_D_1 @ ( sk_C @ X0 @ X1 ) @ X0 @ X1 ) @ X0 )
      | ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) )
      | ( r4_lattice3 @ X1 @ ( sk_D_1 @ ( sk_C @ X0 @ X1 ) @ X0 @ X1 ) @ X0 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v4_lattice3 @ X1 )
      | ( r4_lattice3 @ X1 @ ( sk_C @ X2 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('15',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v4_lattice3 @ X1 )
      | ( m1_subset_1 @ ( sk_C @ X2 @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('16',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( v10_lattices @ X4 )
      | ~ ( v4_lattice3 @ X4 )
      | ~ ( l3_lattices @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ~ ( r4_lattice3 @ X4 @ X5 @ X6 )
      | ( m1_subset_1 @ ( sk_D_1 @ X5 @ X6 @ X4 ) @ ( u1_struct_0 @ X4 ) )
      | ( X5
        = ( k15_lattice3 @ X4 @ X6 ) )
      | ~ ( l3_lattices @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('17',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( X5
        = ( k15_lattice3 @ X4 @ X6 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X5 @ X6 @ X4 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( r4_lattice3 @ X4 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l3_lattices @ X4 )
      | ~ ( v4_lattice3 @ X4 )
      | ~ ( v10_lattices @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( m1_subset_1 @ ( sk_D_1 @ ( sk_C @ X1 @ X0 ) @ X2 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( sk_C @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X2 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ ( sk_C @ X1 @ X0 ) @ X2 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( m1_subset_1 @ ( sk_D_1 @ ( sk_C @ X0 @ X1 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ ( sk_C @ X0 @ X1 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v4_lattice3 @ X1 )
      | ~ ( r4_lattice3 @ X1 @ X3 @ X2 )
      | ( r1_lattices @ X1 @ ( sk_C @ X2 @ X1 ) @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( ( sk_C @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r1_lattices @ X0 @ ( sk_C @ X2 @ X0 ) @ ( sk_D_1 @ ( sk_C @ X1 @ X0 ) @ X1 @ X0 ) )
      | ~ ( r4_lattice3 @ X0 @ ( sk_D_1 @ ( sk_C @ X1 @ X0 ) @ X1 @ X0 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r4_lattice3 @ X0 @ ( sk_D_1 @ ( sk_C @ X1 @ X0 ) @ X1 @ X0 ) @ X2 )
      | ( r1_lattices @ X0 @ ( sk_C @ X2 @ X0 ) @ ( sk_D_1 @ ( sk_C @ X1 @ X0 ) @ X1 @ X0 ) )
      | ( ( sk_C @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) )
      | ( r1_lattices @ X1 @ ( sk_C @ X0 @ X1 ) @ ( sk_D_1 @ ( sk_C @ X0 @ X1 ) @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['13','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattices @ X1 @ ( sk_C @ X0 @ X1 ) @ ( sk_D_1 @ ( sk_C @ X0 @ X1 ) @ X0 @ X1 ) )
      | ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( v10_lattices @ X4 )
      | ~ ( v4_lattice3 @ X4 )
      | ~ ( l3_lattices @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ~ ( r4_lattice3 @ X4 @ X5 @ X6 )
      | ~ ( r1_lattices @ X4 @ X5 @ ( sk_D_1 @ X5 @ X6 @ X4 ) )
      | ( X5
        = ( k15_lattice3 @ X4 @ X6 ) )
      | ~ ( l3_lattices @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('28',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( X5
        = ( k15_lattice3 @ X4 @ X6 ) )
      | ~ ( r1_lattices @ X4 @ X5 @ ( sk_D_1 @ X5 @ X6 @ X4 ) )
      | ~ ( r4_lattice3 @ X4 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l3_lattices @ X4 )
      | ~ ( v4_lattice3 @ X4 )
      | ~ ( v10_lattices @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( ( sk_C @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ ( sk_C @ X1 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ ( sk_C @ X1 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( sk_C @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( ( sk_C @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v4_lattice3 @ X1 )
      | ( m1_subset_1 @ ( sk_C @ X2 @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k15_lattice3 @ X1 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X1 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k16_lattice3 @ X1 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X1 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

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

thf('40',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ( X10
       != ( k16_lattice3 @ X11 @ X12 ) )
      | ~ ( r3_lattice3 @ X11 @ X13 @ X12 )
      | ( r3_lattices @ X11 @ X13 @ X10 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l3_lattices @ X11 )
      | ~ ( v4_lattice3 @ X11 )
      | ~ ( v10_lattices @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('41',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v10_lattices @ X11 )
      | ~ ( v4_lattice3 @ X11 )
      | ~ ( l3_lattices @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ( r3_lattices @ X11 @ X13 @ ( k16_lattice3 @ X11 @ X12 ) )
      | ~ ( r3_lattice3 @ X11 @ X13 @ X12 )
      | ~ ( m1_subset_1 @ ( k16_lattice3 @ X11 @ X12 ) @ ( u1_struct_0 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( r3_lattice3 @ X0 @ X2 @ X1 )
      | ( r3_lattices @ X0 @ X2 @ ( k16_lattice3 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r3_lattices @ X0 @ X2 @ ( k16_lattice3 @ X0 @ X1 ) )
      | ~ ( r3_lattice3 @ X0 @ X2 @ X1 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( r3_lattice3 @ sk_A @ sk_B_1 @ X0 )
      | ( r3_lattices @ sk_A @ sk_B_1 @ ( k16_lattice3 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','43'])).

thf('45',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r3_lattice3 @ sk_A @ sk_B_1 @ X0 )
      | ( r3_lattices @ sk_A @ sk_B_1 @ ( k16_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['44','45','46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_A @ sk_B_1 @ ( k16_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattice3 @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    r3_lattices @ sk_A @ sk_B_1 @ ( k16_lattice3 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['0','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TUtVbxHW3I
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:12:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.40/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.58  % Solved by: fo/fo7.sh
% 0.40/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.58  % done 96 iterations in 0.126s
% 0.40/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.58  % SZS output start Refutation
% 0.40/0.58  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 0.40/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.40/0.58  thf(a_2_1_lattice3_type, type, a_2_1_lattice3: $i > $i > $i).
% 0.40/0.58  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 0.40/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.58  thf(r4_lattice3_type, type, r4_lattice3: $i > $i > $i > $o).
% 0.40/0.58  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.40/0.58  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.40/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.40/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.40/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.58  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.40/0.58  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.40/0.58  thf(r3_lattice3_type, type, r3_lattice3: $i > $i > $i > $o).
% 0.40/0.58  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 0.40/0.58  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 0.40/0.58  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.40/0.58  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.40/0.58  thf(t40_lattice3, conjecture,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.40/0.58         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.40/0.58       ( ![B:$i]:
% 0.40/0.58         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.58           ( ![C:$i]:
% 0.40/0.58             ( ( r3_lattice3 @ A @ B @ C ) =>
% 0.40/0.58               ( r3_lattices @ A @ B @ ( k16_lattice3 @ A @ C ) ) ) ) ) ) ))).
% 0.40/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.58    (~( ![A:$i]:
% 0.40/0.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.40/0.58            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.40/0.58          ( ![B:$i]:
% 0.40/0.58            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.58              ( ![C:$i]:
% 0.40/0.58                ( ( r3_lattice3 @ A @ B @ C ) =>
% 0.40/0.58                  ( r3_lattices @ A @ B @ ( k16_lattice3 @ A @ C ) ) ) ) ) ) ) )),
% 0.40/0.58    inference('cnf.neg', [status(esa)], [t40_lattice3])).
% 0.40/0.58  thf('0', plain,
% 0.40/0.58      (~ (r3_lattices @ sk_A @ sk_B_1 @ (k16_lattice3 @ sk_A @ sk_C_1))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('1', plain, ((r3_lattice3 @ sk_A @ sk_B_1 @ sk_C_1)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('2', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(d22_lattice3, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.40/0.58       ( ![B:$i]:
% 0.40/0.58         ( ( k16_lattice3 @ A @ B ) =
% 0.40/0.58           ( k15_lattice3 @ A @ ( a_2_1_lattice3 @ A @ B ) ) ) ) ))).
% 0.40/0.58  thf('3', plain,
% 0.40/0.58      (![X8 : $i, X9 : $i]:
% 0.40/0.58         (((k16_lattice3 @ X8 @ X9)
% 0.40/0.58            = (k15_lattice3 @ X8 @ (a_2_1_lattice3 @ X8 @ X9)))
% 0.40/0.58          | ~ (l3_lattices @ X8)
% 0.40/0.58          | (v2_struct_0 @ X8))),
% 0.40/0.58      inference('cnf', [status(esa)], [d22_lattice3])).
% 0.40/0.58  thf(d18_lattice3, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.40/0.58       ( ( v4_lattice3 @ A ) <=>
% 0.40/0.58         ( ![B:$i]:
% 0.40/0.58           ( ?[C:$i]:
% 0.40/0.58             ( ( ![D:$i]:
% 0.40/0.58                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.58                   ( ( r4_lattice3 @ A @ D @ B ) => ( r1_lattices @ A @ C @ D ) ) ) ) & 
% 0.40/0.58               ( r4_lattice3 @ A @ C @ B ) & 
% 0.40/0.58               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.40/0.58  thf('4', plain,
% 0.40/0.58      (![X1 : $i, X2 : $i]:
% 0.40/0.58         (~ (v4_lattice3 @ X1)
% 0.40/0.58          | (r4_lattice3 @ X1 @ (sk_C @ X2 @ X1) @ X2)
% 0.40/0.58          | ~ (l3_lattices @ X1)
% 0.40/0.58          | (v2_struct_0 @ X1))),
% 0.40/0.58      inference('cnf', [status(esa)], [d18_lattice3])).
% 0.40/0.58  thf('5', plain,
% 0.40/0.58      (![X1 : $i, X2 : $i]:
% 0.40/0.58         (~ (v4_lattice3 @ X1)
% 0.40/0.58          | (m1_subset_1 @ (sk_C @ X2 @ X1) @ (u1_struct_0 @ X1))
% 0.40/0.58          | ~ (l3_lattices @ X1)
% 0.40/0.58          | (v2_struct_0 @ X1))),
% 0.40/0.58      inference('cnf', [status(esa)], [d18_lattice3])).
% 0.40/0.58  thf('6', plain,
% 0.40/0.58      (![X1 : $i, X2 : $i]:
% 0.40/0.58         (~ (v4_lattice3 @ X1)
% 0.40/0.58          | (r4_lattice3 @ X1 @ (sk_C @ X2 @ X1) @ X2)
% 0.40/0.58          | ~ (l3_lattices @ X1)
% 0.40/0.58          | (v2_struct_0 @ X1))),
% 0.40/0.58      inference('cnf', [status(esa)], [d18_lattice3])).
% 0.40/0.58  thf('7', plain,
% 0.40/0.58      (![X1 : $i, X2 : $i]:
% 0.40/0.58         (~ (v4_lattice3 @ X1)
% 0.40/0.58          | (m1_subset_1 @ (sk_C @ X2 @ X1) @ (u1_struct_0 @ X1))
% 0.40/0.58          | ~ (l3_lattices @ X1)
% 0.40/0.58          | (v2_struct_0 @ X1))),
% 0.40/0.58      inference('cnf', [status(esa)], [d18_lattice3])).
% 0.40/0.58  thf(d21_lattice3, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.40/0.58       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.40/0.58           ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.40/0.58         ( ![B:$i,C:$i]:
% 0.40/0.58           ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.58             ( ( ( C ) = ( k15_lattice3 @ A @ B ) ) <=>
% 0.40/0.58               ( ( r4_lattice3 @ A @ C @ B ) & 
% 0.40/0.58                 ( ![D:$i]:
% 0.40/0.58                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.58                     ( ( r4_lattice3 @ A @ D @ B ) =>
% 0.40/0.58                       ( r1_lattices @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.40/0.58  thf('8', plain,
% 0.40/0.58      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.40/0.58         ((v2_struct_0 @ X4)
% 0.40/0.58          | ~ (v10_lattices @ X4)
% 0.40/0.58          | ~ (v4_lattice3 @ X4)
% 0.40/0.58          | ~ (l3_lattices @ X4)
% 0.40/0.58          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.40/0.58          | ~ (r4_lattice3 @ X4 @ X5 @ X6)
% 0.40/0.58          | (r4_lattice3 @ X4 @ (sk_D_1 @ X5 @ X6 @ X4) @ X6)
% 0.40/0.58          | ((X5) = (k15_lattice3 @ X4 @ X6))
% 0.40/0.58          | ~ (l3_lattices @ X4)
% 0.40/0.58          | (v2_struct_0 @ X4))),
% 0.40/0.58      inference('cnf', [status(esa)], [d21_lattice3])).
% 0.40/0.58  thf('9', plain,
% 0.40/0.58      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.40/0.58         (((X5) = (k15_lattice3 @ X4 @ X6))
% 0.40/0.58          | (r4_lattice3 @ X4 @ (sk_D_1 @ X5 @ X6 @ X4) @ X6)
% 0.40/0.58          | ~ (r4_lattice3 @ X4 @ X5 @ X6)
% 0.40/0.58          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.40/0.58          | ~ (l3_lattices @ X4)
% 0.40/0.58          | ~ (v4_lattice3 @ X4)
% 0.40/0.58          | ~ (v10_lattices @ X4)
% 0.40/0.58          | (v2_struct_0 @ X4))),
% 0.40/0.58      inference('simplify', [status(thm)], ['8'])).
% 0.40/0.58  thf('10', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.58         ((v2_struct_0 @ X0)
% 0.40/0.58          | ~ (l3_lattices @ X0)
% 0.40/0.58          | ~ (v4_lattice3 @ X0)
% 0.40/0.58          | (v2_struct_0 @ X0)
% 0.40/0.58          | ~ (v10_lattices @ X0)
% 0.40/0.58          | ~ (v4_lattice3 @ X0)
% 0.40/0.58          | ~ (l3_lattices @ X0)
% 0.40/0.58          | ~ (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 0.40/0.58          | (r4_lattice3 @ X0 @ (sk_D_1 @ (sk_C @ X1 @ X0) @ X2 @ X0) @ X2)
% 0.40/0.58          | ((sk_C @ X1 @ X0) = (k15_lattice3 @ X0 @ X2)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['7', '9'])).
% 0.40/0.58  thf('11', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.58         (((sk_C @ X1 @ X0) = (k15_lattice3 @ X0 @ X2))
% 0.40/0.58          | (r4_lattice3 @ X0 @ (sk_D_1 @ (sk_C @ X1 @ X0) @ X2 @ X0) @ X2)
% 0.40/0.58          | ~ (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 0.40/0.58          | ~ (v10_lattices @ X0)
% 0.40/0.58          | ~ (v4_lattice3 @ X0)
% 0.40/0.58          | ~ (l3_lattices @ X0)
% 0.40/0.58          | (v2_struct_0 @ X0))),
% 0.40/0.58      inference('simplify', [status(thm)], ['10'])).
% 0.40/0.58  thf('12', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((v2_struct_0 @ X1)
% 0.40/0.58          | ~ (l3_lattices @ X1)
% 0.40/0.58          | ~ (v4_lattice3 @ X1)
% 0.40/0.58          | (v2_struct_0 @ X1)
% 0.40/0.58          | ~ (l3_lattices @ X1)
% 0.40/0.58          | ~ (v4_lattice3 @ X1)
% 0.40/0.58          | ~ (v10_lattices @ X1)
% 0.40/0.58          | (r4_lattice3 @ X1 @ (sk_D_1 @ (sk_C @ X0 @ X1) @ X0 @ X1) @ X0)
% 0.40/0.58          | ((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['6', '11'])).
% 0.40/0.58  thf('13', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0))
% 0.40/0.58          | (r4_lattice3 @ X1 @ (sk_D_1 @ (sk_C @ X0 @ X1) @ X0 @ X1) @ X0)
% 0.40/0.58          | ~ (v10_lattices @ X1)
% 0.40/0.58          | ~ (v4_lattice3 @ X1)
% 0.40/0.58          | ~ (l3_lattices @ X1)
% 0.40/0.58          | (v2_struct_0 @ X1))),
% 0.40/0.58      inference('simplify', [status(thm)], ['12'])).
% 0.40/0.58  thf('14', plain,
% 0.40/0.58      (![X1 : $i, X2 : $i]:
% 0.40/0.58         (~ (v4_lattice3 @ X1)
% 0.40/0.58          | (r4_lattice3 @ X1 @ (sk_C @ X2 @ X1) @ X2)
% 0.40/0.58          | ~ (l3_lattices @ X1)
% 0.40/0.58          | (v2_struct_0 @ X1))),
% 0.40/0.58      inference('cnf', [status(esa)], [d18_lattice3])).
% 0.40/0.58  thf('15', plain,
% 0.40/0.58      (![X1 : $i, X2 : $i]:
% 0.40/0.58         (~ (v4_lattice3 @ X1)
% 0.40/0.58          | (m1_subset_1 @ (sk_C @ X2 @ X1) @ (u1_struct_0 @ X1))
% 0.40/0.58          | ~ (l3_lattices @ X1)
% 0.40/0.58          | (v2_struct_0 @ X1))),
% 0.40/0.58      inference('cnf', [status(esa)], [d18_lattice3])).
% 0.40/0.58  thf('16', plain,
% 0.40/0.58      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.40/0.58         ((v2_struct_0 @ X4)
% 0.40/0.58          | ~ (v10_lattices @ X4)
% 0.40/0.58          | ~ (v4_lattice3 @ X4)
% 0.40/0.58          | ~ (l3_lattices @ X4)
% 0.40/0.58          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.40/0.58          | ~ (r4_lattice3 @ X4 @ X5 @ X6)
% 0.40/0.58          | (m1_subset_1 @ (sk_D_1 @ X5 @ X6 @ X4) @ (u1_struct_0 @ X4))
% 0.40/0.58          | ((X5) = (k15_lattice3 @ X4 @ X6))
% 0.40/0.58          | ~ (l3_lattices @ X4)
% 0.40/0.58          | (v2_struct_0 @ X4))),
% 0.40/0.58      inference('cnf', [status(esa)], [d21_lattice3])).
% 0.40/0.58  thf('17', plain,
% 0.40/0.58      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.40/0.58         (((X5) = (k15_lattice3 @ X4 @ X6))
% 0.40/0.58          | (m1_subset_1 @ (sk_D_1 @ X5 @ X6 @ X4) @ (u1_struct_0 @ X4))
% 0.40/0.58          | ~ (r4_lattice3 @ X4 @ X5 @ X6)
% 0.40/0.58          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.40/0.58          | ~ (l3_lattices @ X4)
% 0.40/0.58          | ~ (v4_lattice3 @ X4)
% 0.40/0.58          | ~ (v10_lattices @ X4)
% 0.40/0.58          | (v2_struct_0 @ X4))),
% 0.40/0.58      inference('simplify', [status(thm)], ['16'])).
% 0.40/0.58  thf('18', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.58         ((v2_struct_0 @ X0)
% 0.40/0.58          | ~ (l3_lattices @ X0)
% 0.40/0.58          | ~ (v4_lattice3 @ X0)
% 0.40/0.58          | (v2_struct_0 @ X0)
% 0.40/0.58          | ~ (v10_lattices @ X0)
% 0.40/0.58          | ~ (v4_lattice3 @ X0)
% 0.40/0.58          | ~ (l3_lattices @ X0)
% 0.40/0.58          | ~ (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 0.40/0.58          | (m1_subset_1 @ (sk_D_1 @ (sk_C @ X1 @ X0) @ X2 @ X0) @ 
% 0.40/0.58             (u1_struct_0 @ X0))
% 0.40/0.58          | ((sk_C @ X1 @ X0) = (k15_lattice3 @ X0 @ X2)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['15', '17'])).
% 0.40/0.58  thf('19', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.58         (((sk_C @ X1 @ X0) = (k15_lattice3 @ X0 @ X2))
% 0.40/0.58          | (m1_subset_1 @ (sk_D_1 @ (sk_C @ X1 @ X0) @ X2 @ X0) @ 
% 0.40/0.58             (u1_struct_0 @ X0))
% 0.40/0.58          | ~ (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 0.40/0.58          | ~ (v10_lattices @ X0)
% 0.40/0.58          | ~ (v4_lattice3 @ X0)
% 0.40/0.58          | ~ (l3_lattices @ X0)
% 0.40/0.58          | (v2_struct_0 @ X0))),
% 0.40/0.58      inference('simplify', [status(thm)], ['18'])).
% 0.40/0.58  thf('20', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((v2_struct_0 @ X1)
% 0.40/0.58          | ~ (l3_lattices @ X1)
% 0.40/0.58          | ~ (v4_lattice3 @ X1)
% 0.40/0.58          | (v2_struct_0 @ X1)
% 0.40/0.58          | ~ (l3_lattices @ X1)
% 0.40/0.58          | ~ (v4_lattice3 @ X1)
% 0.40/0.58          | ~ (v10_lattices @ X1)
% 0.40/0.58          | (m1_subset_1 @ (sk_D_1 @ (sk_C @ X0 @ X1) @ X0 @ X1) @ 
% 0.40/0.58             (u1_struct_0 @ X1))
% 0.40/0.58          | ((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['14', '19'])).
% 0.40/0.58  thf('21', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0))
% 0.40/0.58          | (m1_subset_1 @ (sk_D_1 @ (sk_C @ X0 @ X1) @ X0 @ X1) @ 
% 0.40/0.58             (u1_struct_0 @ X1))
% 0.40/0.58          | ~ (v10_lattices @ X1)
% 0.40/0.58          | ~ (v4_lattice3 @ X1)
% 0.40/0.58          | ~ (l3_lattices @ X1)
% 0.40/0.58          | (v2_struct_0 @ X1))),
% 0.40/0.58      inference('simplify', [status(thm)], ['20'])).
% 0.40/0.58  thf('22', plain,
% 0.40/0.58      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.40/0.58         (~ (v4_lattice3 @ X1)
% 0.40/0.58          | ~ (r4_lattice3 @ X1 @ X3 @ X2)
% 0.40/0.58          | (r1_lattices @ X1 @ (sk_C @ X2 @ X1) @ X3)
% 0.40/0.58          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.40/0.58          | ~ (l3_lattices @ X1)
% 0.40/0.58          | (v2_struct_0 @ X1))),
% 0.40/0.58      inference('cnf', [status(esa)], [d18_lattice3])).
% 0.40/0.58  thf('23', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.58         ((v2_struct_0 @ X0)
% 0.40/0.58          | ~ (l3_lattices @ X0)
% 0.40/0.58          | ~ (v4_lattice3 @ X0)
% 0.40/0.58          | ~ (v10_lattices @ X0)
% 0.40/0.58          | ((sk_C @ X1 @ X0) = (k15_lattice3 @ X0 @ X1))
% 0.40/0.58          | (v2_struct_0 @ X0)
% 0.40/0.58          | ~ (l3_lattices @ X0)
% 0.40/0.58          | (r1_lattices @ X0 @ (sk_C @ X2 @ X0) @ 
% 0.40/0.58             (sk_D_1 @ (sk_C @ X1 @ X0) @ X1 @ X0))
% 0.40/0.58          | ~ (r4_lattice3 @ X0 @ (sk_D_1 @ (sk_C @ X1 @ X0) @ X1 @ X0) @ X2)
% 0.40/0.58          | ~ (v4_lattice3 @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['21', '22'])).
% 0.40/0.58  thf('24', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.58         (~ (r4_lattice3 @ X0 @ (sk_D_1 @ (sk_C @ X1 @ X0) @ X1 @ X0) @ X2)
% 0.40/0.58          | (r1_lattices @ X0 @ (sk_C @ X2 @ X0) @ 
% 0.40/0.58             (sk_D_1 @ (sk_C @ X1 @ X0) @ X1 @ X0))
% 0.40/0.58          | ((sk_C @ X1 @ X0) = (k15_lattice3 @ X0 @ X1))
% 0.40/0.58          | ~ (v10_lattices @ X0)
% 0.40/0.58          | ~ (v4_lattice3 @ X0)
% 0.40/0.58          | ~ (l3_lattices @ X0)
% 0.40/0.58          | (v2_struct_0 @ X0))),
% 0.40/0.58      inference('simplify', [status(thm)], ['23'])).
% 0.40/0.58  thf('25', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((v2_struct_0 @ X1)
% 0.40/0.58          | ~ (l3_lattices @ X1)
% 0.40/0.58          | ~ (v4_lattice3 @ X1)
% 0.40/0.58          | ~ (v10_lattices @ X1)
% 0.40/0.58          | ((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0))
% 0.40/0.58          | (v2_struct_0 @ X1)
% 0.40/0.58          | ~ (l3_lattices @ X1)
% 0.40/0.58          | ~ (v4_lattice3 @ X1)
% 0.40/0.58          | ~ (v10_lattices @ X1)
% 0.40/0.58          | ((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0))
% 0.40/0.58          | (r1_lattices @ X1 @ (sk_C @ X0 @ X1) @ 
% 0.40/0.58             (sk_D_1 @ (sk_C @ X0 @ X1) @ X0 @ X1)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['13', '24'])).
% 0.40/0.58  thf('26', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((r1_lattices @ X1 @ (sk_C @ X0 @ X1) @ 
% 0.40/0.58           (sk_D_1 @ (sk_C @ X0 @ X1) @ X0 @ X1))
% 0.40/0.58          | ((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0))
% 0.40/0.58          | ~ (v10_lattices @ X1)
% 0.40/0.58          | ~ (v4_lattice3 @ X1)
% 0.40/0.58          | ~ (l3_lattices @ X1)
% 0.40/0.58          | (v2_struct_0 @ X1))),
% 0.40/0.58      inference('simplify', [status(thm)], ['25'])).
% 0.40/0.58  thf('27', plain,
% 0.40/0.58      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.40/0.58         ((v2_struct_0 @ X4)
% 0.40/0.58          | ~ (v10_lattices @ X4)
% 0.40/0.58          | ~ (v4_lattice3 @ X4)
% 0.40/0.58          | ~ (l3_lattices @ X4)
% 0.40/0.58          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.40/0.58          | ~ (r4_lattice3 @ X4 @ X5 @ X6)
% 0.40/0.58          | ~ (r1_lattices @ X4 @ X5 @ (sk_D_1 @ X5 @ X6 @ X4))
% 0.40/0.58          | ((X5) = (k15_lattice3 @ X4 @ X6))
% 0.40/0.58          | ~ (l3_lattices @ X4)
% 0.40/0.58          | (v2_struct_0 @ X4))),
% 0.40/0.58      inference('cnf', [status(esa)], [d21_lattice3])).
% 0.40/0.58  thf('28', plain,
% 0.40/0.58      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.40/0.58         (((X5) = (k15_lattice3 @ X4 @ X6))
% 0.40/0.58          | ~ (r1_lattices @ X4 @ X5 @ (sk_D_1 @ X5 @ X6 @ X4))
% 0.40/0.58          | ~ (r4_lattice3 @ X4 @ X5 @ X6)
% 0.40/0.58          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.40/0.58          | ~ (l3_lattices @ X4)
% 0.40/0.58          | ~ (v4_lattice3 @ X4)
% 0.40/0.58          | ~ (v10_lattices @ X4)
% 0.40/0.58          | (v2_struct_0 @ X4))),
% 0.40/0.58      inference('simplify', [status(thm)], ['27'])).
% 0.40/0.58  thf('29', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((v2_struct_0 @ X0)
% 0.40/0.58          | ~ (l3_lattices @ X0)
% 0.40/0.58          | ~ (v4_lattice3 @ X0)
% 0.40/0.58          | ~ (v10_lattices @ X0)
% 0.40/0.58          | ((sk_C @ X1 @ X0) = (k15_lattice3 @ X0 @ X1))
% 0.40/0.58          | (v2_struct_0 @ X0)
% 0.40/0.58          | ~ (v10_lattices @ X0)
% 0.40/0.58          | ~ (v4_lattice3 @ X0)
% 0.40/0.58          | ~ (l3_lattices @ X0)
% 0.40/0.58          | ~ (m1_subset_1 @ (sk_C @ X1 @ X0) @ (u1_struct_0 @ X0))
% 0.40/0.58          | ~ (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X1)
% 0.40/0.58          | ((sk_C @ X1 @ X0) = (k15_lattice3 @ X0 @ X1)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['26', '28'])).
% 0.40/0.58  thf('30', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (~ (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X1)
% 0.40/0.58          | ~ (m1_subset_1 @ (sk_C @ X1 @ X0) @ (u1_struct_0 @ X0))
% 0.40/0.58          | ((sk_C @ X1 @ X0) = (k15_lattice3 @ X0 @ X1))
% 0.40/0.58          | ~ (v10_lattices @ X0)
% 0.40/0.58          | ~ (v4_lattice3 @ X0)
% 0.40/0.58          | ~ (l3_lattices @ X0)
% 0.40/0.58          | (v2_struct_0 @ X0))),
% 0.40/0.58      inference('simplify', [status(thm)], ['29'])).
% 0.40/0.58  thf('31', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((v2_struct_0 @ X0)
% 0.40/0.58          | ~ (l3_lattices @ X0)
% 0.40/0.58          | ~ (v4_lattice3 @ X0)
% 0.40/0.58          | (v2_struct_0 @ X0)
% 0.40/0.58          | ~ (l3_lattices @ X0)
% 0.40/0.58          | ~ (v4_lattice3 @ X0)
% 0.40/0.58          | ~ (v10_lattices @ X0)
% 0.40/0.58          | ((sk_C @ X1 @ X0) = (k15_lattice3 @ X0 @ X1))
% 0.40/0.58          | ~ (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X1))),
% 0.40/0.58      inference('sup-', [status(thm)], ['5', '30'])).
% 0.40/0.58  thf('32', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (~ (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X1)
% 0.40/0.58          | ((sk_C @ X1 @ X0) = (k15_lattice3 @ X0 @ X1))
% 0.40/0.58          | ~ (v10_lattices @ X0)
% 0.40/0.58          | ~ (v4_lattice3 @ X0)
% 0.40/0.58          | ~ (l3_lattices @ X0)
% 0.40/0.58          | (v2_struct_0 @ X0))),
% 0.40/0.58      inference('simplify', [status(thm)], ['31'])).
% 0.40/0.58  thf('33', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((v2_struct_0 @ X1)
% 0.40/0.58          | ~ (l3_lattices @ X1)
% 0.40/0.58          | ~ (v4_lattice3 @ X1)
% 0.40/0.58          | (v2_struct_0 @ X1)
% 0.40/0.58          | ~ (l3_lattices @ X1)
% 0.40/0.58          | ~ (v4_lattice3 @ X1)
% 0.40/0.58          | ~ (v10_lattices @ X1)
% 0.40/0.58          | ((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['4', '32'])).
% 0.40/0.58  thf('34', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0))
% 0.40/0.58          | ~ (v10_lattices @ X1)
% 0.40/0.58          | ~ (v4_lattice3 @ X1)
% 0.40/0.58          | ~ (l3_lattices @ X1)
% 0.40/0.58          | (v2_struct_0 @ X1))),
% 0.40/0.58      inference('simplify', [status(thm)], ['33'])).
% 0.40/0.58  thf('35', plain,
% 0.40/0.58      (![X1 : $i, X2 : $i]:
% 0.40/0.58         (~ (v4_lattice3 @ X1)
% 0.40/0.58          | (m1_subset_1 @ (sk_C @ X2 @ X1) @ (u1_struct_0 @ X1))
% 0.40/0.58          | ~ (l3_lattices @ X1)
% 0.40/0.58          | (v2_struct_0 @ X1))),
% 0.40/0.58      inference('cnf', [status(esa)], [d18_lattice3])).
% 0.40/0.58  thf('36', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((m1_subset_1 @ (k15_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1))
% 0.40/0.58          | (v2_struct_0 @ X1)
% 0.40/0.58          | ~ (l3_lattices @ X1)
% 0.40/0.58          | ~ (v4_lattice3 @ X1)
% 0.40/0.58          | ~ (v10_lattices @ X1)
% 0.40/0.58          | (v2_struct_0 @ X1)
% 0.40/0.58          | ~ (l3_lattices @ X1)
% 0.40/0.58          | ~ (v4_lattice3 @ X1))),
% 0.40/0.58      inference('sup+', [status(thm)], ['34', '35'])).
% 0.40/0.58  thf('37', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (~ (v10_lattices @ X1)
% 0.40/0.58          | ~ (v4_lattice3 @ X1)
% 0.40/0.58          | ~ (l3_lattices @ X1)
% 0.40/0.58          | (v2_struct_0 @ X1)
% 0.40/0.58          | (m1_subset_1 @ (k15_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1)))),
% 0.40/0.58      inference('simplify', [status(thm)], ['36'])).
% 0.40/0.58  thf('38', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((m1_subset_1 @ (k16_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1))
% 0.40/0.58          | (v2_struct_0 @ X1)
% 0.40/0.58          | ~ (l3_lattices @ X1)
% 0.40/0.58          | (v2_struct_0 @ X1)
% 0.40/0.58          | ~ (l3_lattices @ X1)
% 0.40/0.58          | ~ (v4_lattice3 @ X1)
% 0.40/0.58          | ~ (v10_lattices @ X1))),
% 0.40/0.58      inference('sup+', [status(thm)], ['3', '37'])).
% 0.40/0.58  thf('39', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (~ (v10_lattices @ X1)
% 0.40/0.58          | ~ (v4_lattice3 @ X1)
% 0.40/0.58          | ~ (l3_lattices @ X1)
% 0.40/0.58          | (v2_struct_0 @ X1)
% 0.40/0.58          | (m1_subset_1 @ (k16_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1)))),
% 0.40/0.58      inference('simplify', [status(thm)], ['38'])).
% 0.40/0.58  thf(t34_lattice3, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.40/0.58         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.40/0.58       ( ![B:$i]:
% 0.40/0.58         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.58           ( ![C:$i]:
% 0.40/0.58             ( ( ( B ) = ( k16_lattice3 @ A @ C ) ) <=>
% 0.40/0.58               ( ( r3_lattice3 @ A @ B @ C ) & 
% 0.40/0.58                 ( ![D:$i]:
% 0.40/0.58                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.58                     ( ( r3_lattice3 @ A @ D @ C ) =>
% 0.40/0.58                       ( r3_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.40/0.58  thf('40', plain,
% 0.40/0.58      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.40/0.58          | ((X10) != (k16_lattice3 @ X11 @ X12))
% 0.40/0.58          | ~ (r3_lattice3 @ X11 @ X13 @ X12)
% 0.40/0.58          | (r3_lattices @ X11 @ X13 @ X10)
% 0.40/0.58          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 0.40/0.58          | ~ (l3_lattices @ X11)
% 0.40/0.58          | ~ (v4_lattice3 @ X11)
% 0.40/0.58          | ~ (v10_lattices @ X11)
% 0.40/0.58          | (v2_struct_0 @ X11))),
% 0.40/0.58      inference('cnf', [status(esa)], [t34_lattice3])).
% 0.40/0.58  thf('41', plain,
% 0.40/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.40/0.58         ((v2_struct_0 @ X11)
% 0.40/0.58          | ~ (v10_lattices @ X11)
% 0.40/0.58          | ~ (v4_lattice3 @ X11)
% 0.40/0.58          | ~ (l3_lattices @ X11)
% 0.40/0.58          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 0.40/0.58          | (r3_lattices @ X11 @ X13 @ (k16_lattice3 @ X11 @ X12))
% 0.40/0.58          | ~ (r3_lattice3 @ X11 @ X13 @ X12)
% 0.40/0.58          | ~ (m1_subset_1 @ (k16_lattice3 @ X11 @ X12) @ (u1_struct_0 @ X11)))),
% 0.40/0.58      inference('simplify', [status(thm)], ['40'])).
% 0.40/0.58  thf('42', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.58         ((v2_struct_0 @ X0)
% 0.40/0.58          | ~ (l3_lattices @ X0)
% 0.40/0.58          | ~ (v4_lattice3 @ X0)
% 0.40/0.58          | ~ (v10_lattices @ X0)
% 0.40/0.58          | ~ (r3_lattice3 @ X0 @ X2 @ X1)
% 0.40/0.58          | (r3_lattices @ X0 @ X2 @ (k16_lattice3 @ X0 @ X1))
% 0.40/0.58          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.40/0.58          | ~ (l3_lattices @ X0)
% 0.40/0.58          | ~ (v4_lattice3 @ X0)
% 0.40/0.58          | ~ (v10_lattices @ X0)
% 0.40/0.58          | (v2_struct_0 @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['39', '41'])).
% 0.40/0.58  thf('43', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.40/0.58          | (r3_lattices @ X0 @ X2 @ (k16_lattice3 @ X0 @ X1))
% 0.40/0.58          | ~ (r3_lattice3 @ X0 @ X2 @ X1)
% 0.40/0.58          | ~ (v10_lattices @ X0)
% 0.40/0.58          | ~ (v4_lattice3 @ X0)
% 0.40/0.58          | ~ (l3_lattices @ X0)
% 0.40/0.58          | (v2_struct_0 @ X0))),
% 0.40/0.58      inference('simplify', [status(thm)], ['42'])).
% 0.40/0.58  thf('44', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((v2_struct_0 @ sk_A)
% 0.40/0.58          | ~ (l3_lattices @ sk_A)
% 0.40/0.58          | ~ (v4_lattice3 @ sk_A)
% 0.40/0.58          | ~ (v10_lattices @ sk_A)
% 0.40/0.58          | ~ (r3_lattice3 @ sk_A @ sk_B_1 @ X0)
% 0.40/0.58          | (r3_lattices @ sk_A @ sk_B_1 @ (k16_lattice3 @ sk_A @ X0)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['2', '43'])).
% 0.40/0.58  thf('45', plain, ((l3_lattices @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('46', plain, ((v4_lattice3 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('47', plain, ((v10_lattices @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('48', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((v2_struct_0 @ sk_A)
% 0.40/0.58          | ~ (r3_lattice3 @ sk_A @ sk_B_1 @ X0)
% 0.40/0.58          | (r3_lattices @ sk_A @ sk_B_1 @ (k16_lattice3 @ sk_A @ X0)))),
% 0.40/0.58      inference('demod', [status(thm)], ['44', '45', '46', '47'])).
% 0.40/0.58  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('50', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((r3_lattices @ sk_A @ sk_B_1 @ (k16_lattice3 @ sk_A @ X0))
% 0.40/0.58          | ~ (r3_lattice3 @ sk_A @ sk_B_1 @ X0))),
% 0.40/0.58      inference('clc', [status(thm)], ['48', '49'])).
% 0.40/0.58  thf('51', plain,
% 0.40/0.58      ((r3_lattices @ sk_A @ sk_B_1 @ (k16_lattice3 @ sk_A @ sk_C_1))),
% 0.40/0.58      inference('sup-', [status(thm)], ['1', '50'])).
% 0.40/0.58  thf('52', plain, ($false), inference('demod', [status(thm)], ['0', '51'])).
% 0.40/0.58  
% 0.40/0.58  % SZS output end Refutation
% 0.40/0.58  
% 0.40/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
