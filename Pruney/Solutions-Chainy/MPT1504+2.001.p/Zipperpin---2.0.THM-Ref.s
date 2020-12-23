%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qBpulIhqfz

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:27 EST 2020

% Result     : Theorem 2.72s
% Output     : Refutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :  464 (9412 expanded)
%              Number of leaves         :   35 (2351 expanded)
%              Depth                    :  106
%              Number of atoms          : 8187 (223665 expanded)
%              Number of equality atoms :  112 (5489 expanded)
%              Maximal formula depth    :   24 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(sk_D_4_type,type,(
    sk_D_4: $i > $i > $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r3_lattice3_type,type,(
    r3_lattice3: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(r4_lattice3_type,type,(
    r4_lattice3: $i > $i > $i > $o )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(a_2_2_lattice3_type,type,(
    a_2_2_lattice3: $i > $i > $i )).

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

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v4_lattice3 @ X10 )
      | ( r4_lattice3 @ X10 @ ( sk_C @ X11 @ X10 ) @ X11 )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v4_lattice3 @ X10 )
      | ( m1_subset_1 @ ( sk_C @ X11 @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v4_lattice3 @ X10 )
      | ( r4_lattice3 @ X10 @ ( sk_C @ X11 @ X10 ) @ X11 )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v4_lattice3 @ X10 )
      | ( m1_subset_1 @ ( sk_C @ X11 @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
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

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v10_lattices @ X13 )
      | ~ ( v4_lattice3 @ X13 )
      | ~ ( l3_lattices @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r4_lattice3 @ X13 @ X14 @ X15 )
      | ( r4_lattice3 @ X13 @ ( sk_D_2 @ X14 @ X15 @ X13 ) @ X15 )
      | ( X14
        = ( k15_lattice3 @ X13 @ X15 ) )
      | ~ ( l3_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('6',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( X14
        = ( k15_lattice3 @ X13 @ X15 ) )
      | ( r4_lattice3 @ X13 @ ( sk_D_2 @ X14 @ X15 @ X13 ) @ X15 )
      | ~ ( r4_lattice3 @ X13 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l3_lattices @ X13 )
      | ~ ( v4_lattice3 @ X13 )
      | ~ ( v10_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r4_lattice3 @ X0 @ ( sk_D_2 @ ( sk_C @ X1 @ X0 ) @ X2 @ X0 ) @ X2 )
      | ( ( sk_C @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X2 ) )
      | ( r4_lattice3 @ X0 @ ( sk_D_2 @ ( sk_C @ X1 @ X0 ) @ X2 @ X0 ) @ X2 )
      | ~ ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( r4_lattice3 @ X1 @ ( sk_D_2 @ ( sk_C @ X0 @ X1 ) @ X0 @ X1 ) @ X0 )
      | ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) )
      | ( r4_lattice3 @ X1 @ ( sk_D_2 @ ( sk_C @ X0 @ X1 ) @ X0 @ X1 ) @ X0 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v4_lattice3 @ X10 )
      | ( r4_lattice3 @ X10 @ ( sk_C @ X11 @ X10 ) @ X11 )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v4_lattice3 @ X10 )
      | ( m1_subset_1 @ ( sk_C @ X11 @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('13',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v10_lattices @ X13 )
      | ~ ( v4_lattice3 @ X13 )
      | ~ ( l3_lattices @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r4_lattice3 @ X13 @ X14 @ X15 )
      | ( m1_subset_1 @ ( sk_D_2 @ X14 @ X15 @ X13 ) @ ( u1_struct_0 @ X13 ) )
      | ( X14
        = ( k15_lattice3 @ X13 @ X15 ) )
      | ~ ( l3_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('14',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( X14
        = ( k15_lattice3 @ X13 @ X15 ) )
      | ( m1_subset_1 @ ( sk_D_2 @ X14 @ X15 @ X13 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( r4_lattice3 @ X13 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l3_lattices @ X13 )
      | ~ ( v4_lattice3 @ X13 )
      | ~ ( v10_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( m1_subset_1 @ ( sk_D_2 @ ( sk_C @ X1 @ X0 ) @ X2 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( sk_C @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X2 ) )
      | ( m1_subset_1 @ ( sk_D_2 @ ( sk_C @ X1 @ X0 ) @ X2 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( m1_subset_1 @ ( sk_D_2 @ ( sk_C @ X0 @ X1 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( sk_D_2 @ ( sk_C @ X0 @ X1 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v4_lattice3 @ X10 )
      | ~ ( r4_lattice3 @ X10 @ X12 @ X11 )
      | ( r1_lattices @ X10 @ ( sk_C @ X11 @ X10 ) @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( ( sk_C @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r1_lattices @ X0 @ ( sk_C @ X2 @ X0 ) @ ( sk_D_2 @ ( sk_C @ X1 @ X0 ) @ X1 @ X0 ) )
      | ~ ( r4_lattice3 @ X0 @ ( sk_D_2 @ ( sk_C @ X1 @ X0 ) @ X1 @ X0 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r4_lattice3 @ X0 @ ( sk_D_2 @ ( sk_C @ X1 @ X0 ) @ X1 @ X0 ) @ X2 )
      | ( r1_lattices @ X0 @ ( sk_C @ X2 @ X0 ) @ ( sk_D_2 @ ( sk_C @ X1 @ X0 ) @ X1 @ X0 ) )
      | ( ( sk_C @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
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
      | ( r1_lattices @ X1 @ ( sk_C @ X0 @ X1 ) @ ( sk_D_2 @ ( sk_C @ X0 @ X1 ) @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['10','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattices @ X1 @ ( sk_C @ X0 @ X1 ) @ ( sk_D_2 @ ( sk_C @ X0 @ X1 ) @ X0 @ X1 ) )
      | ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v10_lattices @ X13 )
      | ~ ( v4_lattice3 @ X13 )
      | ~ ( l3_lattices @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r4_lattice3 @ X13 @ X14 @ X15 )
      | ~ ( r1_lattices @ X13 @ X14 @ ( sk_D_2 @ X14 @ X15 @ X13 ) )
      | ( X14
        = ( k15_lattice3 @ X13 @ X15 ) )
      | ~ ( l3_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('25',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( X14
        = ( k15_lattice3 @ X13 @ X15 ) )
      | ~ ( r1_lattices @ X13 @ X14 @ ( sk_D_2 @ X14 @ X15 @ X13 ) )
      | ~ ( r4_lattice3 @ X13 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l3_lattices @ X13 )
      | ~ ( v4_lattice3 @ X13 )
      | ~ ( v10_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
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
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ ( sk_C @ X1 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( sk_C @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
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
    inference('sup-',[status(thm)],['2','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
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
    inference('sup-',[status(thm)],['1','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v4_lattice3 @ X10 )
      | ( m1_subset_1 @ ( sk_C @ X11 @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k15_lattice3 @ X1 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X1 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X1 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('37',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v4_lattice3 @ X10 )
      | ( r4_lattice3 @ X10 @ ( sk_C @ X11 @ X10 ) @ X11 )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('38',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v4_lattice3 @ X10 )
      | ( m1_subset_1 @ ( sk_C @ X11 @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

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

thf('39',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( l3_lattices @ X17 )
      | ~ ( v4_lattice3 @ X17 )
      | ~ ( v10_lattices @ X17 )
      | ( v2_struct_0 @ X17 )
      | ( r2_hidden @ X19 @ ( a_2_2_lattice3 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X17 ) )
      | ( X19 != X20 )
      | ~ ( r4_lattice3 @ X17 @ X20 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_2_lattice3])).

thf('40',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ~ ( r4_lattice3 @ X17 @ X20 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X17 ) )
      | ( r2_hidden @ X20 @ ( a_2_2_lattice3 @ X17 @ X18 ) )
      | ( v2_struct_0 @ X17 )
      | ~ ( v10_lattices @ X17 )
      | ~ ( v4_lattice3 @ X17 )
      | ~ ( l3_lattices @ X17 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( a_2_2_lattice3 @ X0 @ X2 ) )
      | ~ ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( a_2_2_lattice3 @ X0 @ X2 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( a_2_2_lattice3 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k15_lattice3 @ X1 @ X0 ) @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( r2_hidden @ ( k15_lattice3 @ X1 @ X0 ) @ ( a_2_2_lattice3 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('49',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v4_lattice3 @ X10 )
      | ( m1_subset_1 @ ( sk_C @ X11 @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

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

thf('50',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( m1_subset_1 @ ( sk_D @ X8 @ X4 @ X5 ) @ ( u1_struct_0 @ X5 ) )
      | ( r3_lattice3 @ X5 @ X4 @ X8 )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( m1_subset_1 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X2 @ ( k15_lattice3 @ X1 @ X0 ) @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ( r3_lattice3 @ X1 @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['48','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r3_lattice3 @ X1 @ ( sk_C @ X0 @ X1 ) @ X2 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( m1_subset_1 @ ( sk_D @ X2 @ ( k15_lattice3 @ X1 @ X0 ) @ X1 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('56',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v4_lattice3 @ X10 )
      | ( m1_subset_1 @ ( sk_C @ X11 @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('57',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X4 @ X5 ) @ X8 )
      | ( r3_lattice3 @ X5 @ X4 @ X8 )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X2 )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( l3_lattices @ X17 )
      | ~ ( v4_lattice3 @ X17 )
      | ~ ( v10_lattices @ X17 )
      | ( v2_struct_0 @ X17 )
      | ( X19
        = ( sk_D_3 @ X18 @ X17 @ X19 ) )
      | ~ ( r2_hidden @ X19 @ ( a_2_2_lattice3 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_2_lattice3])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( l3_lattices @ X2 )
      | ~ ( v4_lattice3 @ X2 )
      | ( r3_lattice3 @ X2 @ ( sk_C @ X3 @ X2 ) @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ( ( sk_D @ ( a_2_2_lattice3 @ X1 @ X0 ) @ ( sk_C @ X3 @ X2 ) @ X2 )
        = ( sk_D_3 @ X0 @ X1 @ ( sk_D @ ( a_2_2_lattice3 @ X1 @ X0 ) @ ( sk_C @ X3 @ X2 ) @ X2 ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X2 )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('63',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( l3_lattices @ X17 )
      | ~ ( v4_lattice3 @ X17 )
      | ~ ( v10_lattices @ X17 )
      | ( v2_struct_0 @ X17 )
      | ( r4_lattice3 @ X17 @ ( sk_D_3 @ X18 @ X17 @ X19 ) @ X18 )
      | ~ ( r2_hidden @ X19 @ ( a_2_2_lattice3 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_2_lattice3])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( l3_lattices @ X2 )
      | ~ ( v4_lattice3 @ X2 )
      | ( r3_lattice3 @ X2 @ ( sk_C @ X3 @ X2 ) @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ( r4_lattice3 @ X1 @ ( sk_D_3 @ X0 @ X1 @ ( sk_D @ ( a_2_2_lattice3 @ X1 @ X0 ) @ ( sk_C @ X3 @ X2 ) @ X2 ) ) @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r4_lattice3 @ X3 @ ( sk_D @ ( a_2_2_lattice3 @ X3 @ X2 ) @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X2 )
      | ~ ( l3_lattices @ X3 )
      | ~ ( v4_lattice3 @ X3 )
      | ~ ( v10_lattices @ X3 )
      | ( v2_struct_0 @ X3 )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ ( a_2_2_lattice3 @ X3 @ X2 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X3 )
      | ~ ( v4_lattice3 @ X3 )
      | ~ ( v10_lattices @ X3 )
      | ( v2_struct_0 @ X3 )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ ( a_2_2_lattice3 @ X3 @ X2 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ ( a_2_2_lattice3 @ X3 @ X2 ) )
      | ( v2_struct_0 @ X3 )
      | ~ ( v10_lattices @ X3 )
      | ~ ( v4_lattice3 @ X3 )
      | ~ ( l3_lattices @ X3 )
      | ( r4_lattice3 @ X3 @ ( sk_D @ ( a_2_2_lattice3 @ X3 @ X2 ) @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r4_lattice3 @ X3 @ ( sk_D @ ( a_2_2_lattice3 @ X3 @ X2 ) @ ( k15_lattice3 @ X1 @ X0 ) @ X1 ) @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( l3_lattices @ X3 )
      | ~ ( v4_lattice3 @ X3 )
      | ~ ( v10_lattices @ X3 )
      | ( v2_struct_0 @ X3 )
      | ( r3_lattice3 @ X1 @ ( sk_C @ X0 @ X1 ) @ ( a_2_2_lattice3 @ X3 @ X2 ) )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['55','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r3_lattice3 @ X1 @ ( sk_C @ X0 @ X1 ) @ ( a_2_2_lattice3 @ X3 @ X2 ) )
      | ( v2_struct_0 @ X3 )
      | ~ ( v10_lattices @ X3 )
      | ~ ( v4_lattice3 @ X3 )
      | ~ ( l3_lattices @ X3 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( r4_lattice3 @ X3 @ ( sk_D @ ( a_2_2_lattice3 @ X3 @ X2 ) @ ( k15_lattice3 @ X1 @ X0 ) @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( l3_lattices @ X2 )
      | ~ ( v4_lattice3 @ X2 )
      | ( r3_lattice3 @ X2 @ ( sk_C @ X3 @ X2 ) @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ( ( sk_D @ ( a_2_2_lattice3 @ X1 @ X0 ) @ ( sk_C @ X3 @ X2 ) @ X2 )
        = ( sk_D_3 @ X0 @ X1 @ ( sk_D @ ( a_2_2_lattice3 @ X1 @ X0 ) @ ( sk_C @ X3 @ X2 ) @ X2 ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r3_lattice3 @ X1 @ ( sk_C @ X0 @ X1 ) @ ( a_2_2_lattice3 @ X3 @ X2 ) )
      | ( v2_struct_0 @ X3 )
      | ~ ( v10_lattices @ X3 )
      | ~ ( v4_lattice3 @ X3 )
      | ~ ( l3_lattices @ X3 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( r4_lattice3 @ X3 @ ( sk_D @ ( a_2_2_lattice3 @ X3 @ X2 ) @ ( k15_lattice3 @ X1 @ X0 ) @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r3_lattice3 @ X1 @ ( sk_C @ X0 @ X1 ) @ X2 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( m1_subset_1 @ ( sk_D @ X2 @ ( k15_lattice3 @ X1 @ X0 ) @ X1 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X1 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('75',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v10_lattices @ X13 )
      | ~ ( v4_lattice3 @ X13 )
      | ~ ( l3_lattices @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ( X14
       != ( k15_lattice3 @ X13 @ X15 ) )
      | ~ ( r4_lattice3 @ X13 @ X16 @ X15 )
      | ( r1_lattices @ X13 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l3_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('76',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X13 ) )
      | ( r1_lattices @ X13 @ ( k15_lattice3 @ X13 @ X15 ) @ X16 )
      | ~ ( r4_lattice3 @ X13 @ X16 @ X15 )
      | ~ ( m1_subset_1 @ ( k15_lattice3 @ X13 @ X15 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( l3_lattices @ X13 )
      | ~ ( v4_lattice3 @ X13 )
      | ~ ( v10_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r4_lattice3 @ X0 @ X2 @ X1 )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['74','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r4_lattice3 @ X0 @ X2 @ X1 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( r4_lattice3 @ X0 @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X3 )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X3 ) @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['73','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X3 ) @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ~ ( r4_lattice3 @ X0 @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X3 )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( r3_lattice3 @ X1 @ ( sk_C @ X2 @ X1 ) @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( r3_lattice3 @ X1 @ ( sk_C @ X2 @ X1 ) @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ( r1_lattices @ X1 @ ( k15_lattice3 @ X1 @ X0 ) @ ( sk_D @ ( a_2_2_lattice3 @ X1 @ X0 ) @ ( k15_lattice3 @ X1 @ X2 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['72','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_lattices @ X1 @ ( k15_lattice3 @ X1 @ X0 ) @ ( sk_D @ ( a_2_2_lattice3 @ X1 @ X0 ) @ ( k15_lattice3 @ X1 @ X2 ) @ X1 ) )
      | ( r3_lattice3 @ X1 @ ( sk_C @ X2 @ X1 ) @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('85',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v4_lattice3 @ X10 )
      | ( m1_subset_1 @ ( sk_C @ X11 @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('86',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r1_lattices @ X5 @ X4 @ ( sk_D @ X8 @ X4 @ X5 ) )
      | ( r3_lattice3 @ X5 @ X4 @ X8 )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( r1_lattices @ X0 @ ( sk_C @ X1 @ X0 ) @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattices @ X0 @ ( sk_C @ X1 @ X0 ) @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattices @ X1 @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X2 @ ( k15_lattice3 @ X1 @ X0 ) @ X1 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ( r3_lattice3 @ X1 @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['84','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r3_lattice3 @ X1 @ ( sk_C @ X0 @ X1 ) @ X2 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( r1_lattices @ X1 @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X2 @ ( k15_lattice3 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattices @ X1 @ ( k15_lattice3 @ X1 @ X0 ) @ ( sk_D @ X2 @ ( k15_lattice3 @ X1 @ X0 ) @ X1 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( r3_lattice3 @ X1 @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['83','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r3_lattice3 @ X1 @ ( sk_C @ X0 @ X1 ) @ X2 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( r1_lattices @ X1 @ ( k15_lattice3 @ X1 @ X0 ) @ ( sk_D @ X2 @ ( k15_lattice3 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ ( a_2_2_lattice3 @ X0 @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ ( a_2_2_lattice3 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['82','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ ( a_2_2_lattice3 @ X0 @ X1 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ X1 @ ( k15_lattice3 @ X1 @ X0 ) @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 ) ) ),
    inference('sup+',[status(thm)],['71','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( r3_lattice3 @ X1 @ ( k15_lattice3 @ X1 @ X0 ) @ ( a_2_2_lattice3 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X1 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X1 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( r2_hidden @ ( k15_lattice3 @ X1 @ X0 ) @ ( a_2_2_lattice3 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('103',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( l3_lattices @ X17 )
      | ~ ( v4_lattice3 @ X17 )
      | ~ ( v10_lattices @ X17 )
      | ( v2_struct_0 @ X17 )
      | ( X19
        = ( sk_D_3 @ X18 @ X17 @ X19 ) )
      | ~ ( r2_hidden @ X19 @ ( a_2_2_lattice3 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_2_lattice3])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( ( sk_C @ X0 @ X1 )
        = ( sk_D_3 @ X0 @ X1 @ ( sk_C @ X0 @ X1 ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = ( sk_D_3 @ X0 @ X1 @ ( sk_C @ X0 @ X1 ) ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = ( sk_D_3 @ X0 @ X1 @ ( sk_C @ X0 @ X1 ) ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = ( sk_D_3 @ X0 @ X1 @ ( sk_C @ X0 @ X1 ) ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('109',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( l3_lattices @ X17 )
      | ~ ( v4_lattice3 @ X17 )
      | ~ ( v10_lattices @ X17 )
      | ( v2_struct_0 @ X17 )
      | ( m1_subset_1 @ ( sk_D_3 @ X18 @ X17 @ X19 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( r2_hidden @ X19 @ ( a_2_2_lattice3 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_2_lattice3])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( m1_subset_1 @ ( sk_D_3 @ X0 @ X1 @ ( sk_C @ X0 @ X1 ) ) @ ( u1_struct_0 @ X1 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_D_3 @ X0 @ X1 @ ( sk_C @ X0 @ X1 ) ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X4 @ X5 ) @ X8 )
      | ( r3_lattice3 @ X5 @ X4 @ X8 )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( sk_D_3 @ X1 @ X0 @ ( sk_C @ X1 @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ ( sk_D_3 @ X1 @ X0 @ ( sk_C @ X1 @ X0 ) ) @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( sk_D_3 @ X1 @ X0 @ ( sk_C @ X1 @ X0 ) ) @ X0 ) @ X2 )
      | ( r3_lattice3 @ X0 @ ( sk_D_3 @ X1 @ X0 @ ( sk_C @ X1 @ X0 ) ) @ X2 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( sk_D_3 @ X1 @ X0 @ ( sk_C @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['107','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r3_lattice3 @ X0 @ ( sk_D_3 @ X1 @ X0 @ ( sk_C @ X1 @ X0 ) ) @ X2 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r2_hidden @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_D_3 @ X0 @ X1 @ ( sk_C @ X0 @ X1 ) ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['110'])).

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

thf('118',plain,(
    ! [X21: $i,X22: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( r3_lattice3 @ X22 @ X21 @ X25 )
      | ( r3_lattice3 @ X22 @ ( sk_D_4 @ X25 @ X21 @ X22 ) @ X25 )
      | ( X21
        = ( k16_lattice3 @ X22 @ X25 ) )
      | ~ ( l3_lattices @ X22 )
      | ~ ( v4_lattice3 @ X22 )
      | ~ ( v10_lattices @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( ( sk_D_3 @ X1 @ X0 @ ( sk_C @ X1 @ X0 ) )
        = ( k16_lattice3 @ X0 @ X2 ) )
      | ( r3_lattice3 @ X0 @ ( sk_D_4 @ X2 @ ( sk_D_3 @ X1 @ X0 @ ( sk_C @ X1 @ X0 ) ) @ X0 ) @ X2 )
      | ~ ( r3_lattice3 @ X0 @ ( sk_D_3 @ X1 @ X0 @ ( sk_C @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r3_lattice3 @ X0 @ ( sk_D_3 @ X1 @ X0 @ ( sk_C @ X1 @ X0 ) ) @ X2 )
      | ( r3_lattice3 @ X0 @ ( sk_D_4 @ X2 @ ( sk_D_3 @ X1 @ X0 @ ( sk_C @ X1 @ X0 ) ) @ X0 ) @ X2 )
      | ( ( sk_D_3 @ X1 @ X0 @ ( sk_C @ X1 @ X0 ) )
        = ( k16_lattice3 @ X0 @ X2 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ ( sk_C @ X2 @ X1 ) @ X1 ) @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( ( sk_D_3 @ X2 @ X1 @ ( sk_C @ X2 @ X1 ) )
        = ( k16_lattice3 @ X1 @ X0 ) )
      | ( r3_lattice3 @ X1 @ ( sk_D_4 @ X0 @ ( sk_D_3 @ X2 @ X1 @ ( sk_C @ X2 @ X1 ) ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['116','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r3_lattice3 @ X1 @ ( sk_D_4 @ X0 @ ( sk_D_3 @ X2 @ X1 @ ( sk_C @ X2 @ X1 ) ) @ X1 ) @ X0 )
      | ( ( sk_D_3 @ X2 @ X1 @ ( sk_C @ X2 @ X1 ) )
        = ( k16_lattice3 @ X1 @ X0 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( r2_hidden @ ( sk_D @ X0 @ ( sk_C @ X2 @ X1 ) @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r3_lattice3 @ X0 @ ( sk_D_4 @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( r2_hidden @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( ( sk_D_3 @ X1 @ X0 @ ( sk_C @ X1 @ X0 ) )
        = ( k16_lattice3 @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['106','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_D_3 @ X1 @ X0 @ ( sk_C @ X1 @ X0 ) )
        = ( k16_lattice3 @ X0 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X2 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r3_lattice3 @ X0 @ ( sk_D_4 @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    ( k15_lattice3 @ sk_A @ sk_B_1 )
 != ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( ( k15_lattice3 @ sk_A @ sk_B_1 )
       != ( sk_D_3 @ X0 @ sk_A @ ( sk_C @ X0 @ sk_A ) ) )
      | ( r3_lattice3 @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( ( k15_lattice3 @ sk_A @ sk_B_1 )
       != ( sk_D_3 @ X0 @ sk_A @ ( sk_C @ X0 @ sk_A ) ) )
      | ( r3_lattice3 @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['126','127','128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( ( k15_lattice3 @ sk_A @ sk_B_1 )
       != ( sk_C @ X0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['105','130'])).

thf('132',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( ( k15_lattice3 @ sk_A @ sk_B_1 )
       != ( sk_C @ X0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['131','132','133','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( r3_lattice3 @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
      | ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( k15_lattice3 @ sk_A @ sk_B_1 )
       != ( sk_C @ X0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( ( k15_lattice3 @ sk_A @ sk_B_1 )
       != ( k15_lattice3 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
      | ( r3_lattice3 @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['101','136'])).

thf('138',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( ( k15_lattice3 @ sk_A @ sk_B_1 )
       != ( k15_lattice3 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
      | ( r3_lattice3 @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['137','138','139','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( r3_lattice3 @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
      | ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( k15_lattice3 @ sk_A @ sk_B_1 )
       != ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
    | ( r3_lattice3 @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference(eq_res,[status(thm)],['142'])).

thf('144',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( r3_lattice3 @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['143','144'])).

thf('146',plain,
    ( ( r3_lattice3 @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['100','145'])).

thf('147',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( r3_lattice3 @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['146','147','148','149'])).

thf('151',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
    | ( r3_lattice3 @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = ( sk_D_3 @ X0 @ X1 @ ( sk_C @ X0 @ X1 ) ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = ( sk_D_3 @ X0 @ X1 @ ( sk_C @ X0 @ X1 ) ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = ( sk_D_3 @ X0 @ X1 @ ( sk_C @ X0 @ X1 ) ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_D_3 @ X0 @ X1 @ ( sk_C @ X0 @ X1 ) ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('160',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( m1_subset_1 @ ( sk_D @ X8 @ X4 @ X5 ) @ ( u1_struct_0 @ X5 ) )
      | ( r3_lattice3 @ X5 @ X4 @ X8 )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('161',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( sk_D_3 @ X1 @ X0 @ ( sk_C @ X1 @ X0 ) ) @ X2 )
      | ( m1_subset_1 @ ( sk_D @ X2 @ ( sk_D_3 @ X1 @ X0 @ ( sk_C @ X1 @ X0 ) ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X2 @ ( sk_D_3 @ X1 @ X0 @ ( sk_C @ X1 @ X0 ) ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r3_lattice3 @ X0 @ ( sk_D_3 @ X1 @ X0 @ ( sk_C @ X1 @ X0 ) ) @ X2 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( sk_D_3 @ X1 @ X0 @ ( sk_C @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['158','162'])).

thf('164',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r3_lattice3 @ X0 @ ( sk_D_3 @ X1 @ X0 @ ( sk_C @ X1 @ X0 ) ) @ X2 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['163'])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_D_3 @ X0 @ X1 @ ( sk_C @ X0 @ X1 ) ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('166',plain,(
    ! [X21: $i,X22: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( r3_lattice3 @ X22 @ X21 @ X25 )
      | ( m1_subset_1 @ ( sk_D_4 @ X25 @ X21 @ X22 ) @ ( u1_struct_0 @ X22 ) )
      | ( X21
        = ( k16_lattice3 @ X22 @ X25 ) )
      | ~ ( l3_lattices @ X22 )
      | ~ ( v4_lattice3 @ X22 )
      | ~ ( v10_lattices @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('167',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( ( sk_D_3 @ X1 @ X0 @ ( sk_C @ X1 @ X0 ) )
        = ( k16_lattice3 @ X0 @ X2 ) )
      | ( m1_subset_1 @ ( sk_D_4 @ X2 @ ( sk_D_3 @ X1 @ X0 @ ( sk_C @ X1 @ X0 ) ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r3_lattice3 @ X0 @ ( sk_D_3 @ X1 @ X0 @ ( sk_C @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r3_lattice3 @ X0 @ ( sk_D_3 @ X1 @ X0 @ ( sk_C @ X1 @ X0 ) ) @ X2 )
      | ( m1_subset_1 @ ( sk_D_4 @ X2 @ ( sk_D_3 @ X1 @ X0 @ ( sk_C @ X1 @ X0 ) ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( sk_D_3 @ X1 @ X0 @ ( sk_C @ X1 @ X0 ) )
        = ( k16_lattice3 @ X0 @ X2 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X0 @ ( sk_C @ X2 @ X1 ) @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( ( sk_D_3 @ X2 @ X1 @ ( sk_C @ X2 @ X1 ) )
        = ( k16_lattice3 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( sk_D_4 @ X0 @ ( sk_D_3 @ X2 @ X1 @ ( sk_C @ X2 @ X1 ) ) @ X1 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['164','168'])).

thf('170',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D_4 @ X0 @ ( sk_D_3 @ X2 @ X1 @ ( sk_C @ X2 @ X1 ) ) @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ( ( sk_D_3 @ X2 @ X1 @ ( sk_C @ X2 @ X1 ) )
        = ( k16_lattice3 @ X1 @ X0 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ ( sk_C @ X2 @ X1 ) @ X1 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['169'])).

thf('171',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D_4 @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( ( sk_D_3 @ X1 @ X0 @ ( sk_C @ X1 @ X0 ) )
        = ( k16_lattice3 @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['157','170'])).

thf('172',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_D_3 @ X1 @ X0 @ ( sk_C @ X1 @ X0 ) )
        = ( k16_lattice3 @ X0 @ X2 ) )
      | ( m1_subset_1 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_D_4 @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,(
    ( k15_lattice3 @ sk_A @ sk_B_1 )
 != ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( ( k15_lattice3 @ sk_A @ sk_B_1 )
       != ( sk_D_3 @ X0 @ sk_A @ ( sk_C @ X0 @ sk_A ) ) )
      | ( m1_subset_1 @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( ( k15_lattice3 @ sk_A @ sk_B_1 )
       != ( sk_D_3 @ X0 @ sk_A @ ( sk_C @ X0 @ sk_A ) ) )
      | ( m1_subset_1 @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['174','175','176','177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( ( k15_lattice3 @ sk_A @ sk_B_1 )
       != ( sk_C @ X0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['156','178'])).

thf('180',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    ! [X0: $i] :
      ( ( ( k15_lattice3 @ sk_A @ sk_B_1 )
       != ( sk_C @ X0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['179','180','181','182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( k15_lattice3 @ sk_A @ sk_B_1 )
       != ( sk_C @ X0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['183'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( ( k15_lattice3 @ sk_A @ sk_B_1 )
       != ( k15_lattice3 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['155','184'])).

thf('186',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( ( k15_lattice3 @ sk_A @ sk_B_1 )
       != ( k15_lattice3 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['185','186','187','188'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( k15_lattice3 @ sk_A @ sk_B_1 )
       != ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['189'])).

thf('191',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(eq_res,[status(thm)],['190'])).

thf('192',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( m1_subset_1 @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['191','192'])).

thf('194',plain,
    ( ( m1_subset_1 @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['154','193'])).

thf('195',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,
    ( ( m1_subset_1 @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['194','195','196','197'])).

thf('199',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['198','199'])).

thf('201',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ( m1_subset_1 @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['153','200'])).

thf('202',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['201','202','203','204'])).

thf('206',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ( m1_subset_1 @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['205','206'])).

thf('208',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r3_lattice3 @ X5 @ X4 @ X6 )
      | ~ ( r2_hidden @ X7 @ X6 )
      | ( r1_lattices @ X5 @ X4 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('209',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['207','208'])).

thf('210',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ X1 ) ) ),
    inference(demod,[status(thm)],['209','210'])).

thf('212',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
      | ( r1_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['152','211'])).

thf('213',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['99','212'])).

thf('214',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['213','214','215','216'])).

thf('218',plain,
    ( ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
    | ( r1_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) )
    | ~ ( m1_subset_1 @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['217'])).

thf('219',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['98','218'])).

thf('220',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['219','220','221','222'])).

thf('224',plain,
    ( ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
    | ( r1_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['223'])).

thf('225',plain,
    ( ( m1_subset_1 @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['205','206'])).

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

thf('226',plain,(
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

thf('227',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ X0 )
      | ( r3_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['225','226'])).

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

thf('228',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('229',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['228','229'])).

thf('231',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['230','231','232'])).

thf('234',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('235',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['234','235'])).

thf('237',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['236','237','238'])).

thf('240',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('241',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['240','241'])).

thf('243',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['242','243','244'])).

thf('246',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ X0 )
      | ( r3_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['227','233','239','245','246'])).

thf('248',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( r3_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['224','247'])).

thf('249',plain,
    ( ( r3_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) )
    | ~ ( m1_subset_1 @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['248'])).

thf('250',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
    | ( r3_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['97','249'])).

thf('251',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
    | ( r3_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['250','251','252','253'])).

thf('255',plain,
    ( ( r3_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['254'])).

thf('256',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X1 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('257',plain,(
    ! [X21: $i,X22: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( r3_lattice3 @ X22 @ X21 @ X25 )
      | ~ ( r3_lattices @ X22 @ ( sk_D_4 @ X25 @ X21 @ X22 ) @ X21 )
      | ( X21
        = ( k16_lattice3 @ X22 @ X25 ) )
      | ~ ( l3_lattices @ X22 )
      | ~ ( v4_lattice3 @ X22 )
      | ~ ( v10_lattices @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('258',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( ( k15_lattice3 @ X0 @ X1 )
        = ( k16_lattice3 @ X0 @ X2 ) )
      | ~ ( r3_lattices @ X0 @ ( sk_D_4 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( r3_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['256','257'])).

thf('259',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r3_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r3_lattices @ X0 @ ( sk_D_4 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ( ( k15_lattice3 @ X0 @ X1 )
        = ( k16_lattice3 @ X0 @ X2 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['258'])).

thf('260',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ( ( k15_lattice3 @ sk_A @ sk_B_1 )
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) )
    | ~ ( r3_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['255','259'])).

thf('261',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( k15_lattice3 @ sk_A @ sk_B_1 )
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) )
    | ~ ( r3_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['260','261','262','263'])).

thf('265',plain,
    ( ~ ( r3_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
    | ( ( k15_lattice3 @ sk_A @ sk_B_1 )
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) )
    | ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['264'])).

thf('266',plain,(
    ( k15_lattice3 @ sk_A @ sk_B_1 )
 != ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,
    ( ~ ( r3_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['265','266'])).

thf('268',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['96','267'])).

thf('269',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('270',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('271',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('272',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['268','269','270','271'])).

thf('273',plain,
    ( ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['272'])).

thf('274',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('275',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['273','274'])).

thf('276',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( l3_lattices @ X17 )
      | ~ ( v4_lattice3 @ X17 )
      | ~ ( v10_lattices @ X17 )
      | ( v2_struct_0 @ X17 )
      | ( m1_subset_1 @ ( sk_D_3 @ X18 @ X17 @ X19 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( r2_hidden @ X19 @ ( a_2_2_lattice3 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_2_lattice3])).

thf('277',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D_3 @ sk_B_1 @ sk_A @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['275','276'])).

thf('278',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('280',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D_3 @ sk_B_1 @ sk_A @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['277','278','279','280'])).

thf('282',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('283',plain,
    ( ( m1_subset_1 @ ( sk_D_3 @ sk_B_1 @ sk_A @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['281','282'])).

thf('284',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r3_lattice3 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['70','283'])).

thf('285',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('286',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('287',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('288',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('289',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('290',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r3_lattice3 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['284','285','286','287','288','289'])).

thf('291',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r3_lattice3 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['290'])).

thf('292',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r3_lattice3 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['69','291'])).

thf('293',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('294',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('295',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('296',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r3_lattice3 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['292','293','294','295'])).

thf('297',plain,
    ( ( r3_lattice3 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['296'])).

thf('298',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('299',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r3_lattice3 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['297','298'])).

thf('300',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ~ ( r4_lattice3 @ X17 @ X20 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X17 ) )
      | ( r2_hidden @ X20 @ ( a_2_2_lattice3 @ X17 @ X18 ) )
      | ( v2_struct_0 @ X17 )
      | ~ ( v10_lattices @ X17 )
      | ~ ( v4_lattice3 @ X17 )
      | ~ ( l3_lattices @ X17 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('301',plain,(
    ! [X0: $i] :
      ( ( r3_lattice3 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ X0 ) )
      | ~ ( r4_lattice3 @ sk_A @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['299','300'])).

thf('302',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('303',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('304',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('305',plain,(
    ! [X0: $i] :
      ( ( r3_lattice3 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ X0 ) )
      | ~ ( r4_lattice3 @ sk_A @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['301','302','303','304'])).

thf('306',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r3_lattice3 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( r3_lattice3 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['68','305'])).

thf('307',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('308',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('309',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('310',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('311',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('312',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('313',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r3_lattice3 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( r3_lattice3 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['306','307','308','309','310','311','312'])).

thf('314',plain,
    ( ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
    | ( r3_lattice3 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['313'])).

thf('315',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('316',plain,
    ( ( r3_lattice3 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['314','315'])).

thf('317',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( r3_lattice3 @ X1 @ ( k15_lattice3 @ X1 @ X0 ) @ ( a_2_2_lattice3 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('318',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X1 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('319',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r3_lattice3 @ X5 @ X4 @ X6 )
      | ~ ( r2_hidden @ X7 @ X6 )
      | ( r1_lattices @ X5 @ X4 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('320',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r3_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['318','319'])).

thf('321',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r3_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X3 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['320'])).

thf('322',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r1_lattices @ X1 @ ( k15_lattice3 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X2 @ ( a_2_2_lattice3 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['317','321'])).

thf('323',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ( r1_lattices @ X1 @ ( k15_lattice3 @ X1 @ X0 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['322'])).

thf('324',plain,
    ( ( r3_lattice3 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['316','323'])).

thf('325',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('326',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('327',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('328',plain,
    ( ( r3_lattice3 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['324','325','326','327'])).

thf('329',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ( r3_lattice3 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
    | ( r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r3_lattice3 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['54','328'])).

thf('330',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('331',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('332',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('333',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_lattice3 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
    | ( r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r3_lattice3 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['329','330','331','332'])).

thf('334',plain,
    ( ( r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) )
    | ( r3_lattice3 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['333'])).

thf('335',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('336',plain,
    ( ( r3_lattice3 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
    | ( r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['334','335'])).

thf('337',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r3_lattice3 @ X1 @ ( sk_C @ X0 @ X1 ) @ X2 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( r1_lattices @ X1 @ ( k15_lattice3 @ X1 @ X0 ) @ ( sk_D @ X2 @ ( k15_lattice3 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('338',plain,
    ( ( r3_lattice3 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ( r3_lattice3 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['336','337'])).

thf('339',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('340',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('341',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('342',plain,
    ( ( r3_lattice3 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( r3_lattice3 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['338','339','340','341'])).

thf('343',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_lattice3 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['342'])).

thf('344',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('345',plain,(
    r3_lattice3 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['343','344'])).

thf('346',plain,
    ( ( r3_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup+',[status(thm)],['47','345'])).

thf('347',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('348',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('349',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('350',plain,
    ( ( r3_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['346','347','348','349'])).

thf('351',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('352',plain,(
    r3_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['350','351'])).

thf('353',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X1 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('354',plain,(
    ! [X21: $i,X22: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( r3_lattice3 @ X22 @ X21 @ X25 )
      | ( r3_lattice3 @ X22 @ ( sk_D_4 @ X25 @ X21 @ X22 ) @ X25 )
      | ( X21
        = ( k16_lattice3 @ X22 @ X25 ) )
      | ~ ( l3_lattices @ X22 )
      | ~ ( v4_lattice3 @ X22 )
      | ~ ( v10_lattices @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('355',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( ( k15_lattice3 @ X0 @ X1 )
        = ( k16_lattice3 @ X0 @ X2 ) )
      | ( r3_lattice3 @ X0 @ ( sk_D_4 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 )
      | ~ ( r3_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['353','354'])).

thf('356',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r3_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( r3_lattice3 @ X0 @ ( sk_D_4 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 )
      | ( ( k15_lattice3 @ X0 @ X1 )
        = ( k16_lattice3 @ X0 @ X2 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['355'])).

thf('357',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ( ( k15_lattice3 @ sk_A @ sk_B_1 )
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) )
    | ( r3_lattice3 @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['352','356'])).

thf('358',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('359',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('360',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('361',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k15_lattice3 @ sk_A @ sk_B_1 )
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) )
    | ( r3_lattice3 @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['357','358','359','360'])).

thf('362',plain,(
    ( k15_lattice3 @ sk_A @ sk_B_1 )
 != ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('363',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_lattice3 @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['361','362'])).

thf('364',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('365',plain,(
    r3_lattice3 @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['363','364'])).

thf('366',plain,(
    r3_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['350','351'])).

thf('367',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X1 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('368',plain,(
    ! [X21: $i,X22: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( r3_lattice3 @ X22 @ X21 @ X25 )
      | ( m1_subset_1 @ ( sk_D_4 @ X25 @ X21 @ X22 ) @ ( u1_struct_0 @ X22 ) )
      | ( X21
        = ( k16_lattice3 @ X22 @ X25 ) )
      | ~ ( l3_lattices @ X22 )
      | ~ ( v4_lattice3 @ X22 )
      | ~ ( v10_lattices @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('369',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( ( k15_lattice3 @ X0 @ X1 )
        = ( k16_lattice3 @ X0 @ X2 ) )
      | ( m1_subset_1 @ ( sk_D_4 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r3_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['367','368'])).

thf('370',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r3_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( m1_subset_1 @ ( sk_D_4 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k15_lattice3 @ X0 @ X1 )
        = ( k16_lattice3 @ X0 @ X2 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['369'])).

thf('371',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ( ( k15_lattice3 @ sk_A @ sk_B_1 )
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) )
    | ( m1_subset_1 @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['366','370'])).

thf('372',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('373',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('374',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('375',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k15_lattice3 @ sk_A @ sk_B_1 )
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) )
    | ( m1_subset_1 @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['371','372','373','374'])).

thf('376',plain,(
    ( k15_lattice3 @ sk_A @ sk_B_1 )
 != ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('377',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['375','376'])).

thf('378',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('379',plain,(
    m1_subset_1 @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['377','378'])).

thf('380',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r3_lattice3 @ X5 @ X4 @ X6 )
      | ~ ( r2_hidden @ X7 @ X6 )
      | ( r1_lattices @ X5 @ X4 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('381',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['379','380'])).

thf('382',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('383',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ X1 ) ) ),
    inference(demod,[status(thm)],['381','382'])).

thf('384',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) )
      | ( r1_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['365','383'])).

thf('385',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['46','384'])).

thf('386',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('387',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('388',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('389',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['385','386','387','388'])).

thf('390',plain,
    ( ( r1_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) )
    | ~ ( m1_subset_1 @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['389'])).

thf('391',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('392',plain,
    ( ~ ( m1_subset_1 @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['390','391'])).

thf('393',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ( r1_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['35','392'])).

thf('394',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('395',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('396',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('397',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['393','394','395','396'])).

thf('398',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('399',plain,(
    r1_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['397','398'])).

thf('400',plain,(
    m1_subset_1 @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['377','378'])).

thf('401',plain,(
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

thf('402',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ X0 )
      | ( r3_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['400','401'])).

thf('403',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['230','231','232'])).

thf('404',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['236','237','238'])).

thf('405',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['242','243','244'])).

thf('406',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('407',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ X0 )
      | ( r3_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['402','403','404','405','406'])).

thf('408',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( r3_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['399','407'])).

thf('409',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('410',plain,
    ( ( r3_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) )
    | ~ ( m1_subset_1 @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['408','409'])).

thf('411',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ( r3_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['34','410'])).

thf('412',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('413',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('414',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('415',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['411','412','413','414'])).

thf('416',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('417',plain,(
    r3_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['415','416'])).

thf('418',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r3_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r3_lattices @ X0 @ ( sk_D_4 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ( ( k15_lattice3 @ X0 @ X1 )
        = ( k16_lattice3 @ X0 @ X2 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['258'])).

thf('419',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ( ( k15_lattice3 @ sk_A @ sk_B_1 )
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) )
    | ~ ( r3_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['417','418'])).

thf('420',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('421',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('422',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('423',plain,(
    r3_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B_1 ) @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['350','351'])).

thf('424',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k15_lattice3 @ sk_A @ sk_B_1 )
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['419','420','421','422','423'])).

thf('425',plain,(
    ( k15_lattice3 @ sk_A @ sk_B_1 )
 != ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('426',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['424','425'])).

thf('427',plain,(
    $false ),
    inference(demod,[status(thm)],['0','426'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qBpulIhqfz
% 0.13/0.38  % Computer   : n007.cluster.edu
% 0.13/0.38  % Model      : x86_64 x86_64
% 0.13/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.38  % Memory     : 8042.1875MB
% 0.13/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.38  % CPULimit   : 60
% 0.13/0.38  % DateTime   : Tue Dec  1 20:58:21 EST 2020
% 0.13/0.38  % CPUTime    : 
% 0.13/0.38  % Running portfolio for 600 s
% 0.13/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.38  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 2.72/2.92  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.72/2.92  % Solved by: fo/fo7.sh
% 2.72/2.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.72/2.92  % done 2020 iterations in 2.414s
% 2.72/2.92  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.72/2.92  % SZS output start Refutation
% 2.72/2.92  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 2.72/2.92  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 2.72/2.92  thf(sk_A_type, type, sk_A: $i).
% 2.72/2.92  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 2.72/2.92  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 2.72/2.92  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.72/2.92  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 2.72/2.92  thf(sk_D_4_type, type, sk_D_4: $i > $i > $i > $i).
% 2.72/2.92  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 2.72/2.92  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.72/2.92  thf(r3_lattice3_type, type, r3_lattice3: $i > $i > $i > $o).
% 2.72/2.92  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.72/2.92  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.72/2.92  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i > $i).
% 2.72/2.92  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.72/2.92  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 2.72/2.92  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 2.72/2.92  thf(r4_lattice3_type, type, r4_lattice3: $i > $i > $i > $o).
% 2.72/2.92  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 2.72/2.92  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 2.72/2.92  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 2.72/2.92  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 2.72/2.92  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 2.72/2.92  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 2.72/2.92  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 2.72/2.92  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.72/2.92  thf(a_2_2_lattice3_type, type, a_2_2_lattice3: $i > $i > $i).
% 2.72/2.92  thf(t37_lattice3, conjecture,
% 2.72/2.92    (![A:$i]:
% 2.72/2.92     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.72/2.92         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 2.72/2.92       ( ![B:$i]:
% 2.72/2.92         ( ( k15_lattice3 @ A @ B ) =
% 2.72/2.92           ( k16_lattice3 @ A @ ( a_2_2_lattice3 @ A @ B ) ) ) ) ))).
% 2.72/2.92  thf(zf_stmt_0, negated_conjecture,
% 2.72/2.92    (~( ![A:$i]:
% 2.72/2.92        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.72/2.92            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 2.72/2.92          ( ![B:$i]:
% 2.72/2.92            ( ( k15_lattice3 @ A @ B ) =
% 2.72/2.92              ( k16_lattice3 @ A @ ( a_2_2_lattice3 @ A @ B ) ) ) ) ) )),
% 2.72/2.92    inference('cnf.neg', [status(esa)], [t37_lattice3])).
% 2.72/2.92  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf(d18_lattice3, axiom,
% 2.72/2.92    (![A:$i]:
% 2.72/2.92     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 2.72/2.92       ( ( v4_lattice3 @ A ) <=>
% 2.72/2.92         ( ![B:$i]:
% 2.72/2.92           ( ?[C:$i]:
% 2.72/2.92             ( ( ![D:$i]:
% 2.72/2.92                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 2.72/2.92                   ( ( r4_lattice3 @ A @ D @ B ) => ( r1_lattices @ A @ C @ D ) ) ) ) & 
% 2.72/2.92               ( r4_lattice3 @ A @ C @ B ) & 
% 2.72/2.92               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 2.72/2.92  thf('1', plain,
% 2.72/2.92      (![X10 : $i, X11 : $i]:
% 2.72/2.92         (~ (v4_lattice3 @ X10)
% 2.72/2.92          | (r4_lattice3 @ X10 @ (sk_C @ X11 @ X10) @ X11)
% 2.72/2.92          | ~ (l3_lattices @ X10)
% 2.72/2.92          | (v2_struct_0 @ X10))),
% 2.72/2.92      inference('cnf', [status(esa)], [d18_lattice3])).
% 2.72/2.92  thf('2', plain,
% 2.72/2.92      (![X10 : $i, X11 : $i]:
% 2.72/2.92         (~ (v4_lattice3 @ X10)
% 2.72/2.92          | (m1_subset_1 @ (sk_C @ X11 @ X10) @ (u1_struct_0 @ X10))
% 2.72/2.92          | ~ (l3_lattices @ X10)
% 2.72/2.92          | (v2_struct_0 @ X10))),
% 2.72/2.92      inference('cnf', [status(esa)], [d18_lattice3])).
% 2.72/2.92  thf('3', plain,
% 2.72/2.92      (![X10 : $i, X11 : $i]:
% 2.72/2.92         (~ (v4_lattice3 @ X10)
% 2.72/2.92          | (r4_lattice3 @ X10 @ (sk_C @ X11 @ X10) @ X11)
% 2.72/2.92          | ~ (l3_lattices @ X10)
% 2.72/2.92          | (v2_struct_0 @ X10))),
% 2.72/2.92      inference('cnf', [status(esa)], [d18_lattice3])).
% 2.72/2.92  thf('4', plain,
% 2.72/2.92      (![X10 : $i, X11 : $i]:
% 2.72/2.92         (~ (v4_lattice3 @ X10)
% 2.72/2.92          | (m1_subset_1 @ (sk_C @ X11 @ X10) @ (u1_struct_0 @ X10))
% 2.72/2.92          | ~ (l3_lattices @ X10)
% 2.72/2.92          | (v2_struct_0 @ X10))),
% 2.72/2.92      inference('cnf', [status(esa)], [d18_lattice3])).
% 2.72/2.92  thf(d21_lattice3, axiom,
% 2.72/2.92    (![A:$i]:
% 2.72/2.92     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 2.72/2.92       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.72/2.92           ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 2.72/2.92         ( ![B:$i,C:$i]:
% 2.72/2.92           ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.72/2.92             ( ( ( C ) = ( k15_lattice3 @ A @ B ) ) <=>
% 2.72/2.92               ( ( r4_lattice3 @ A @ C @ B ) & 
% 2.72/2.92                 ( ![D:$i]:
% 2.72/2.92                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 2.72/2.92                     ( ( r4_lattice3 @ A @ D @ B ) =>
% 2.72/2.92                       ( r1_lattices @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 2.72/2.92  thf('5', plain,
% 2.72/2.92      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.72/2.92         ((v2_struct_0 @ X13)
% 2.72/2.92          | ~ (v10_lattices @ X13)
% 2.72/2.92          | ~ (v4_lattice3 @ X13)
% 2.72/2.92          | ~ (l3_lattices @ X13)
% 2.72/2.92          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 2.72/2.92          | ~ (r4_lattice3 @ X13 @ X14 @ X15)
% 2.72/2.92          | (r4_lattice3 @ X13 @ (sk_D_2 @ X14 @ X15 @ X13) @ X15)
% 2.72/2.92          | ((X14) = (k15_lattice3 @ X13 @ X15))
% 2.72/2.92          | ~ (l3_lattices @ X13)
% 2.72/2.92          | (v2_struct_0 @ X13))),
% 2.72/2.92      inference('cnf', [status(esa)], [d21_lattice3])).
% 2.72/2.92  thf('6', plain,
% 2.72/2.92      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.72/2.92         (((X14) = (k15_lattice3 @ X13 @ X15))
% 2.72/2.92          | (r4_lattice3 @ X13 @ (sk_D_2 @ X14 @ X15 @ X13) @ X15)
% 2.72/2.92          | ~ (r4_lattice3 @ X13 @ X14 @ X15)
% 2.72/2.92          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 2.72/2.92          | ~ (l3_lattices @ X13)
% 2.72/2.92          | ~ (v4_lattice3 @ X13)
% 2.72/2.92          | ~ (v10_lattices @ X13)
% 2.72/2.92          | (v2_struct_0 @ X13))),
% 2.72/2.92      inference('simplify', [status(thm)], ['5'])).
% 2.72/2.92  thf('7', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         ((v2_struct_0 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | (v2_struct_0 @ X0)
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | ~ (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 2.72/2.92          | (r4_lattice3 @ X0 @ (sk_D_2 @ (sk_C @ X1 @ X0) @ X2 @ X0) @ X2)
% 2.72/2.92          | ((sk_C @ X1 @ X0) = (k15_lattice3 @ X0 @ X2)))),
% 2.72/2.92      inference('sup-', [status(thm)], ['4', '6'])).
% 2.72/2.92  thf('8', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         (((sk_C @ X1 @ X0) = (k15_lattice3 @ X0 @ X2))
% 2.72/2.92          | (r4_lattice3 @ X0 @ (sk_D_2 @ (sk_C @ X1 @ X0) @ X2 @ X0) @ X2)
% 2.72/2.92          | ~ (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | (v2_struct_0 @ X0))),
% 2.72/2.92      inference('simplify', [status(thm)], ['7'])).
% 2.72/2.92  thf('9', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         ((v2_struct_0 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | (r4_lattice3 @ X1 @ (sk_D_2 @ (sk_C @ X0 @ X1) @ X0 @ X1) @ X0)
% 2.72/2.92          | ((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0)))),
% 2.72/2.92      inference('sup-', [status(thm)], ['3', '8'])).
% 2.72/2.92  thf('10', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         (((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0))
% 2.72/2.92          | (r4_lattice3 @ X1 @ (sk_D_2 @ (sk_C @ X0 @ X1) @ X0 @ X1) @ X0)
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1))),
% 2.72/2.92      inference('simplify', [status(thm)], ['9'])).
% 2.72/2.92  thf('11', plain,
% 2.72/2.92      (![X10 : $i, X11 : $i]:
% 2.72/2.92         (~ (v4_lattice3 @ X10)
% 2.72/2.92          | (r4_lattice3 @ X10 @ (sk_C @ X11 @ X10) @ X11)
% 2.72/2.92          | ~ (l3_lattices @ X10)
% 2.72/2.92          | (v2_struct_0 @ X10))),
% 2.72/2.92      inference('cnf', [status(esa)], [d18_lattice3])).
% 2.72/2.92  thf('12', plain,
% 2.72/2.92      (![X10 : $i, X11 : $i]:
% 2.72/2.92         (~ (v4_lattice3 @ X10)
% 2.72/2.92          | (m1_subset_1 @ (sk_C @ X11 @ X10) @ (u1_struct_0 @ X10))
% 2.72/2.92          | ~ (l3_lattices @ X10)
% 2.72/2.92          | (v2_struct_0 @ X10))),
% 2.72/2.92      inference('cnf', [status(esa)], [d18_lattice3])).
% 2.72/2.92  thf('13', plain,
% 2.72/2.92      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.72/2.92         ((v2_struct_0 @ X13)
% 2.72/2.92          | ~ (v10_lattices @ X13)
% 2.72/2.92          | ~ (v4_lattice3 @ X13)
% 2.72/2.92          | ~ (l3_lattices @ X13)
% 2.72/2.92          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 2.72/2.92          | ~ (r4_lattice3 @ X13 @ X14 @ X15)
% 2.72/2.92          | (m1_subset_1 @ (sk_D_2 @ X14 @ X15 @ X13) @ (u1_struct_0 @ X13))
% 2.72/2.92          | ((X14) = (k15_lattice3 @ X13 @ X15))
% 2.72/2.92          | ~ (l3_lattices @ X13)
% 2.72/2.92          | (v2_struct_0 @ X13))),
% 2.72/2.92      inference('cnf', [status(esa)], [d21_lattice3])).
% 2.72/2.92  thf('14', plain,
% 2.72/2.92      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.72/2.92         (((X14) = (k15_lattice3 @ X13 @ X15))
% 2.72/2.92          | (m1_subset_1 @ (sk_D_2 @ X14 @ X15 @ X13) @ (u1_struct_0 @ X13))
% 2.72/2.92          | ~ (r4_lattice3 @ X13 @ X14 @ X15)
% 2.72/2.92          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 2.72/2.92          | ~ (l3_lattices @ X13)
% 2.72/2.92          | ~ (v4_lattice3 @ X13)
% 2.72/2.92          | ~ (v10_lattices @ X13)
% 2.72/2.92          | (v2_struct_0 @ X13))),
% 2.72/2.92      inference('simplify', [status(thm)], ['13'])).
% 2.72/2.92  thf('15', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         ((v2_struct_0 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | (v2_struct_0 @ X0)
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | ~ (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 2.72/2.92          | (m1_subset_1 @ (sk_D_2 @ (sk_C @ X1 @ X0) @ X2 @ X0) @ 
% 2.72/2.92             (u1_struct_0 @ X0))
% 2.72/2.92          | ((sk_C @ X1 @ X0) = (k15_lattice3 @ X0 @ X2)))),
% 2.72/2.92      inference('sup-', [status(thm)], ['12', '14'])).
% 2.72/2.92  thf('16', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         (((sk_C @ X1 @ X0) = (k15_lattice3 @ X0 @ X2))
% 2.72/2.92          | (m1_subset_1 @ (sk_D_2 @ (sk_C @ X1 @ X0) @ X2 @ X0) @ 
% 2.72/2.92             (u1_struct_0 @ X0))
% 2.72/2.92          | ~ (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | (v2_struct_0 @ X0))),
% 2.72/2.92      inference('simplify', [status(thm)], ['15'])).
% 2.72/2.92  thf('17', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         ((v2_struct_0 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | (m1_subset_1 @ (sk_D_2 @ (sk_C @ X0 @ X1) @ X0 @ X1) @ 
% 2.72/2.92             (u1_struct_0 @ X1))
% 2.72/2.92          | ((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0)))),
% 2.72/2.92      inference('sup-', [status(thm)], ['11', '16'])).
% 2.72/2.92  thf('18', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         (((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0))
% 2.72/2.92          | (m1_subset_1 @ (sk_D_2 @ (sk_C @ X0 @ X1) @ X0 @ X1) @ 
% 2.72/2.92             (u1_struct_0 @ X1))
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1))),
% 2.72/2.92      inference('simplify', [status(thm)], ['17'])).
% 2.72/2.92  thf('19', plain,
% 2.72/2.92      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.72/2.92         (~ (v4_lattice3 @ X10)
% 2.72/2.92          | ~ (r4_lattice3 @ X10 @ X12 @ X11)
% 2.72/2.92          | (r1_lattices @ X10 @ (sk_C @ X11 @ X10) @ X12)
% 2.72/2.92          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X10))
% 2.72/2.92          | ~ (l3_lattices @ X10)
% 2.72/2.92          | (v2_struct_0 @ X10))),
% 2.72/2.92      inference('cnf', [status(esa)], [d18_lattice3])).
% 2.72/2.92  thf('20', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         ((v2_struct_0 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | ((sk_C @ X1 @ X0) = (k15_lattice3 @ X0 @ X1))
% 2.72/2.92          | (v2_struct_0 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | (r1_lattices @ X0 @ (sk_C @ X2 @ X0) @ 
% 2.72/2.92             (sk_D_2 @ (sk_C @ X1 @ X0) @ X1 @ X0))
% 2.72/2.92          | ~ (r4_lattice3 @ X0 @ (sk_D_2 @ (sk_C @ X1 @ X0) @ X1 @ X0) @ X2)
% 2.72/2.92          | ~ (v4_lattice3 @ X0))),
% 2.72/2.92      inference('sup-', [status(thm)], ['18', '19'])).
% 2.72/2.92  thf('21', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         (~ (r4_lattice3 @ X0 @ (sk_D_2 @ (sk_C @ X1 @ X0) @ X1 @ X0) @ X2)
% 2.72/2.92          | (r1_lattices @ X0 @ (sk_C @ X2 @ X0) @ 
% 2.72/2.92             (sk_D_2 @ (sk_C @ X1 @ X0) @ X1 @ X0))
% 2.72/2.92          | ((sk_C @ X1 @ X0) = (k15_lattice3 @ X0 @ X1))
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | (v2_struct_0 @ X0))),
% 2.72/2.92      inference('simplify', [status(thm)], ['20'])).
% 2.72/2.92  thf('22', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         ((v2_struct_0 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0))
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0))
% 2.72/2.92          | (r1_lattices @ X1 @ (sk_C @ X0 @ X1) @ 
% 2.72/2.92             (sk_D_2 @ (sk_C @ X0 @ X1) @ X0 @ X1)))),
% 2.72/2.92      inference('sup-', [status(thm)], ['10', '21'])).
% 2.72/2.92  thf('23', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         ((r1_lattices @ X1 @ (sk_C @ X0 @ X1) @ 
% 2.72/2.92           (sk_D_2 @ (sk_C @ X0 @ X1) @ X0 @ X1))
% 2.72/2.92          | ((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0))
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1))),
% 2.72/2.92      inference('simplify', [status(thm)], ['22'])).
% 2.72/2.92  thf('24', plain,
% 2.72/2.92      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.72/2.92         ((v2_struct_0 @ X13)
% 2.72/2.92          | ~ (v10_lattices @ X13)
% 2.72/2.92          | ~ (v4_lattice3 @ X13)
% 2.72/2.92          | ~ (l3_lattices @ X13)
% 2.72/2.92          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 2.72/2.92          | ~ (r4_lattice3 @ X13 @ X14 @ X15)
% 2.72/2.92          | ~ (r1_lattices @ X13 @ X14 @ (sk_D_2 @ X14 @ X15 @ X13))
% 2.72/2.92          | ((X14) = (k15_lattice3 @ X13 @ X15))
% 2.72/2.92          | ~ (l3_lattices @ X13)
% 2.72/2.92          | (v2_struct_0 @ X13))),
% 2.72/2.92      inference('cnf', [status(esa)], [d21_lattice3])).
% 2.72/2.92  thf('25', plain,
% 2.72/2.92      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.72/2.92         (((X14) = (k15_lattice3 @ X13 @ X15))
% 2.72/2.92          | ~ (r1_lattices @ X13 @ X14 @ (sk_D_2 @ X14 @ X15 @ X13))
% 2.72/2.92          | ~ (r4_lattice3 @ X13 @ X14 @ X15)
% 2.72/2.92          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 2.72/2.92          | ~ (l3_lattices @ X13)
% 2.72/2.92          | ~ (v4_lattice3 @ X13)
% 2.72/2.92          | ~ (v10_lattices @ X13)
% 2.72/2.92          | (v2_struct_0 @ X13))),
% 2.72/2.92      inference('simplify', [status(thm)], ['24'])).
% 2.72/2.92  thf('26', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         ((v2_struct_0 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | ((sk_C @ X1 @ X0) = (k15_lattice3 @ X0 @ X1))
% 2.72/2.92          | (v2_struct_0 @ X0)
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | ~ (m1_subset_1 @ (sk_C @ X1 @ X0) @ (u1_struct_0 @ X0))
% 2.72/2.92          | ~ (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X1)
% 2.72/2.92          | ((sk_C @ X1 @ X0) = (k15_lattice3 @ X0 @ X1)))),
% 2.72/2.92      inference('sup-', [status(thm)], ['23', '25'])).
% 2.72/2.92  thf('27', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         (~ (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X1)
% 2.72/2.92          | ~ (m1_subset_1 @ (sk_C @ X1 @ X0) @ (u1_struct_0 @ X0))
% 2.72/2.92          | ((sk_C @ X1 @ X0) = (k15_lattice3 @ X0 @ X1))
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | (v2_struct_0 @ X0))),
% 2.72/2.92      inference('simplify', [status(thm)], ['26'])).
% 2.72/2.92  thf('28', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         ((v2_struct_0 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | (v2_struct_0 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | ((sk_C @ X1 @ X0) = (k15_lattice3 @ X0 @ X1))
% 2.72/2.92          | ~ (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X1))),
% 2.72/2.92      inference('sup-', [status(thm)], ['2', '27'])).
% 2.72/2.92  thf('29', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         (~ (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X1)
% 2.72/2.92          | ((sk_C @ X1 @ X0) = (k15_lattice3 @ X0 @ X1))
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | (v2_struct_0 @ X0))),
% 2.72/2.92      inference('simplify', [status(thm)], ['28'])).
% 2.72/2.92  thf('30', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         ((v2_struct_0 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0)))),
% 2.72/2.92      inference('sup-', [status(thm)], ['1', '29'])).
% 2.72/2.92  thf('31', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         (((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0))
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1))),
% 2.72/2.92      inference('simplify', [status(thm)], ['30'])).
% 2.72/2.92  thf('32', plain,
% 2.72/2.92      (![X10 : $i, X11 : $i]:
% 2.72/2.92         (~ (v4_lattice3 @ X10)
% 2.72/2.92          | (m1_subset_1 @ (sk_C @ X11 @ X10) @ (u1_struct_0 @ X10))
% 2.72/2.92          | ~ (l3_lattices @ X10)
% 2.72/2.92          | (v2_struct_0 @ X10))),
% 2.72/2.92      inference('cnf', [status(esa)], [d18_lattice3])).
% 2.72/2.92  thf('33', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         ((m1_subset_1 @ (k15_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1))
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1))),
% 2.72/2.92      inference('sup+', [status(thm)], ['31', '32'])).
% 2.72/2.92  thf('34', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         (~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | (m1_subset_1 @ (k15_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1)))),
% 2.72/2.92      inference('simplify', [status(thm)], ['33'])).
% 2.72/2.92  thf('35', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         (~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | (m1_subset_1 @ (k15_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1)))),
% 2.72/2.92      inference('simplify', [status(thm)], ['33'])).
% 2.72/2.92  thf('36', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         (((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0))
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1))),
% 2.72/2.92      inference('simplify', [status(thm)], ['30'])).
% 2.72/2.92  thf('37', plain,
% 2.72/2.92      (![X10 : $i, X11 : $i]:
% 2.72/2.92         (~ (v4_lattice3 @ X10)
% 2.72/2.92          | (r4_lattice3 @ X10 @ (sk_C @ X11 @ X10) @ X11)
% 2.72/2.92          | ~ (l3_lattices @ X10)
% 2.72/2.92          | (v2_struct_0 @ X10))),
% 2.72/2.92      inference('cnf', [status(esa)], [d18_lattice3])).
% 2.72/2.92  thf('38', plain,
% 2.72/2.92      (![X10 : $i, X11 : $i]:
% 2.72/2.92         (~ (v4_lattice3 @ X10)
% 2.72/2.92          | (m1_subset_1 @ (sk_C @ X11 @ X10) @ (u1_struct_0 @ X10))
% 2.72/2.92          | ~ (l3_lattices @ X10)
% 2.72/2.92          | (v2_struct_0 @ X10))),
% 2.72/2.92      inference('cnf', [status(esa)], [d18_lattice3])).
% 2.72/2.92  thf(fraenkel_a_2_2_lattice3, axiom,
% 2.72/2.92    (![A:$i,B:$i,C:$i]:
% 2.72/2.92     ( ( ( ~( v2_struct_0 @ B ) ) & ( v10_lattices @ B ) & 
% 2.72/2.92         ( v4_lattice3 @ B ) & ( l3_lattices @ B ) ) =>
% 2.72/2.92       ( ( r2_hidden @ A @ ( a_2_2_lattice3 @ B @ C ) ) <=>
% 2.72/2.92         ( ?[D:$i]:
% 2.72/2.92           ( ( r4_lattice3 @ B @ D @ C ) & ( ( A ) = ( D ) ) & 
% 2.72/2.92             ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 2.72/2.92  thf('39', plain,
% 2.72/2.92      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 2.72/2.92         (~ (l3_lattices @ X17)
% 2.72/2.92          | ~ (v4_lattice3 @ X17)
% 2.72/2.92          | ~ (v10_lattices @ X17)
% 2.72/2.92          | (v2_struct_0 @ X17)
% 2.72/2.92          | (r2_hidden @ X19 @ (a_2_2_lattice3 @ X17 @ X18))
% 2.72/2.92          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X17))
% 2.72/2.92          | ((X19) != (X20))
% 2.72/2.92          | ~ (r4_lattice3 @ X17 @ X20 @ X18))),
% 2.72/2.92      inference('cnf', [status(esa)], [fraenkel_a_2_2_lattice3])).
% 2.72/2.92  thf('40', plain,
% 2.72/2.92      (![X17 : $i, X18 : $i, X20 : $i]:
% 2.72/2.92         (~ (r4_lattice3 @ X17 @ X20 @ X18)
% 2.72/2.92          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X17))
% 2.72/2.92          | (r2_hidden @ X20 @ (a_2_2_lattice3 @ X17 @ X18))
% 2.72/2.92          | (v2_struct_0 @ X17)
% 2.72/2.92          | ~ (v10_lattices @ X17)
% 2.72/2.92          | ~ (v4_lattice3 @ X17)
% 2.72/2.92          | ~ (l3_lattices @ X17))),
% 2.72/2.92      inference('simplify', [status(thm)], ['39'])).
% 2.72/2.92  thf('41', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         ((v2_struct_0 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | (v2_struct_0 @ X0)
% 2.72/2.92          | (r2_hidden @ (sk_C @ X1 @ X0) @ (a_2_2_lattice3 @ X0 @ X2))
% 2.72/2.92          | ~ (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2))),
% 2.72/2.92      inference('sup-', [status(thm)], ['38', '40'])).
% 2.72/2.92  thf('42', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         (~ (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 2.72/2.92          | (r2_hidden @ (sk_C @ X1 @ X0) @ (a_2_2_lattice3 @ X0 @ X2))
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | (v2_struct_0 @ X0))),
% 2.72/2.92      inference('simplify', [status(thm)], ['41'])).
% 2.72/2.92  thf('43', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         ((v2_struct_0 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | (r2_hidden @ (sk_C @ X0 @ X1) @ (a_2_2_lattice3 @ X1 @ X0)))),
% 2.72/2.92      inference('sup-', [status(thm)], ['37', '42'])).
% 2.72/2.92  thf('44', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         ((r2_hidden @ (sk_C @ X0 @ X1) @ (a_2_2_lattice3 @ X1 @ X0))
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1))),
% 2.72/2.92      inference('simplify', [status(thm)], ['43'])).
% 2.72/2.92  thf('45', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         ((r2_hidden @ (k15_lattice3 @ X1 @ X0) @ (a_2_2_lattice3 @ X1 @ X0))
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (v10_lattices @ X1))),
% 2.72/2.92      inference('sup+', [status(thm)], ['36', '44'])).
% 2.72/2.92  thf('46', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         (~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | (r2_hidden @ (k15_lattice3 @ X1 @ X0) @ (a_2_2_lattice3 @ X1 @ X0)))),
% 2.72/2.92      inference('simplify', [status(thm)], ['45'])).
% 2.72/2.92  thf('47', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         (((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0))
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1))),
% 2.72/2.92      inference('simplify', [status(thm)], ['30'])).
% 2.72/2.92  thf('48', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         (((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0))
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1))),
% 2.72/2.92      inference('simplify', [status(thm)], ['30'])).
% 2.72/2.92  thf('49', plain,
% 2.72/2.92      (![X10 : $i, X11 : $i]:
% 2.72/2.92         (~ (v4_lattice3 @ X10)
% 2.72/2.92          | (m1_subset_1 @ (sk_C @ X11 @ X10) @ (u1_struct_0 @ X10))
% 2.72/2.92          | ~ (l3_lattices @ X10)
% 2.72/2.92          | (v2_struct_0 @ X10))),
% 2.72/2.92      inference('cnf', [status(esa)], [d18_lattice3])).
% 2.72/2.92  thf(d16_lattice3, axiom,
% 2.72/2.92    (![A:$i]:
% 2.72/2.92     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 2.72/2.92       ( ![B:$i]:
% 2.72/2.92         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.72/2.92           ( ![C:$i]:
% 2.72/2.92             ( ( r3_lattice3 @ A @ B @ C ) <=>
% 2.72/2.92               ( ![D:$i]:
% 2.72/2.92                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 2.72/2.92                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 2.72/2.92  thf('50', plain,
% 2.72/2.92      (![X4 : $i, X5 : $i, X8 : $i]:
% 2.72/2.92         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 2.72/2.92          | (m1_subset_1 @ (sk_D @ X8 @ X4 @ X5) @ (u1_struct_0 @ X5))
% 2.72/2.92          | (r3_lattice3 @ X5 @ X4 @ X8)
% 2.72/2.92          | ~ (l3_lattices @ X5)
% 2.72/2.92          | (v2_struct_0 @ X5))),
% 2.72/2.92      inference('cnf', [status(esa)], [d16_lattice3])).
% 2.72/2.92  thf('51', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         ((v2_struct_0 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | (v2_struct_0 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 2.72/2.92          | (m1_subset_1 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ 
% 2.72/2.92             (u1_struct_0 @ X0)))),
% 2.72/2.92      inference('sup-', [status(thm)], ['49', '50'])).
% 2.72/2.92  thf('52', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         ((m1_subset_1 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ 
% 2.72/2.92           (u1_struct_0 @ X0))
% 2.72/2.92          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | (v2_struct_0 @ X0))),
% 2.72/2.92      inference('simplify', [status(thm)], ['51'])).
% 2.72/2.92  thf('53', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         ((m1_subset_1 @ (sk_D @ X2 @ (k15_lattice3 @ X1 @ X0) @ X1) @ 
% 2.72/2.92           (u1_struct_0 @ X1))
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | (r3_lattice3 @ X1 @ (sk_C @ X0 @ X1) @ X2))),
% 2.72/2.92      inference('sup+', [status(thm)], ['48', '52'])).
% 2.72/2.92  thf('54', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         ((r3_lattice3 @ X1 @ (sk_C @ X0 @ X1) @ X2)
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | (m1_subset_1 @ (sk_D @ X2 @ (k15_lattice3 @ X1 @ X0) @ X1) @ 
% 2.72/2.92             (u1_struct_0 @ X1)))),
% 2.72/2.92      inference('simplify', [status(thm)], ['53'])).
% 2.72/2.92  thf('55', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         (((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0))
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1))),
% 2.72/2.92      inference('simplify', [status(thm)], ['30'])).
% 2.72/2.92  thf('56', plain,
% 2.72/2.92      (![X10 : $i, X11 : $i]:
% 2.72/2.92         (~ (v4_lattice3 @ X10)
% 2.72/2.92          | (m1_subset_1 @ (sk_C @ X11 @ X10) @ (u1_struct_0 @ X10))
% 2.72/2.92          | ~ (l3_lattices @ X10)
% 2.72/2.92          | (v2_struct_0 @ X10))),
% 2.72/2.92      inference('cnf', [status(esa)], [d18_lattice3])).
% 2.72/2.92  thf('57', plain,
% 2.72/2.92      (![X4 : $i, X5 : $i, X8 : $i]:
% 2.72/2.92         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 2.72/2.92          | (r2_hidden @ (sk_D @ X8 @ X4 @ X5) @ X8)
% 2.72/2.92          | (r3_lattice3 @ X5 @ X4 @ X8)
% 2.72/2.92          | ~ (l3_lattices @ X5)
% 2.72/2.92          | (v2_struct_0 @ X5))),
% 2.72/2.92      inference('cnf', [status(esa)], [d16_lattice3])).
% 2.72/2.92  thf('58', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         ((v2_struct_0 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | (v2_struct_0 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 2.72/2.92          | (r2_hidden @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X2))),
% 2.72/2.92      inference('sup-', [status(thm)], ['56', '57'])).
% 2.72/2.92  thf('59', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         ((r2_hidden @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X2)
% 2.72/2.92          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | (v2_struct_0 @ X0))),
% 2.72/2.92      inference('simplify', [status(thm)], ['58'])).
% 2.72/2.92  thf('60', plain,
% 2.72/2.92      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.72/2.92         (~ (l3_lattices @ X17)
% 2.72/2.92          | ~ (v4_lattice3 @ X17)
% 2.72/2.92          | ~ (v10_lattices @ X17)
% 2.72/2.92          | (v2_struct_0 @ X17)
% 2.72/2.92          | ((X19) = (sk_D_3 @ X18 @ X17 @ X19))
% 2.72/2.92          | ~ (r2_hidden @ X19 @ (a_2_2_lattice3 @ X17 @ X18)))),
% 2.72/2.92      inference('cnf', [status(esa)], [fraenkel_a_2_2_lattice3])).
% 2.72/2.92  thf('61', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.72/2.92         ((v2_struct_0 @ X2)
% 2.72/2.92          | ~ (l3_lattices @ X2)
% 2.72/2.92          | ~ (v4_lattice3 @ X2)
% 2.72/2.92          | (r3_lattice3 @ X2 @ (sk_C @ X3 @ X2) @ (a_2_2_lattice3 @ X1 @ X0))
% 2.72/2.92          | ((sk_D @ (a_2_2_lattice3 @ X1 @ X0) @ (sk_C @ X3 @ X2) @ X2)
% 2.72/2.92              = (sk_D_3 @ X0 @ X1 @ 
% 2.72/2.92                 (sk_D @ (a_2_2_lattice3 @ X1 @ X0) @ (sk_C @ X3 @ X2) @ X2)))
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1))),
% 2.72/2.92      inference('sup-', [status(thm)], ['59', '60'])).
% 2.72/2.92  thf('62', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         ((r2_hidden @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X2)
% 2.72/2.92          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | (v2_struct_0 @ X0))),
% 2.72/2.92      inference('simplify', [status(thm)], ['58'])).
% 2.72/2.92  thf('63', plain,
% 2.72/2.92      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.72/2.92         (~ (l3_lattices @ X17)
% 2.72/2.92          | ~ (v4_lattice3 @ X17)
% 2.72/2.92          | ~ (v10_lattices @ X17)
% 2.72/2.92          | (v2_struct_0 @ X17)
% 2.72/2.92          | (r4_lattice3 @ X17 @ (sk_D_3 @ X18 @ X17 @ X19) @ X18)
% 2.72/2.92          | ~ (r2_hidden @ X19 @ (a_2_2_lattice3 @ X17 @ X18)))),
% 2.72/2.92      inference('cnf', [status(esa)], [fraenkel_a_2_2_lattice3])).
% 2.72/2.92  thf('64', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.72/2.92         ((v2_struct_0 @ X2)
% 2.72/2.92          | ~ (l3_lattices @ X2)
% 2.72/2.92          | ~ (v4_lattice3 @ X2)
% 2.72/2.92          | (r3_lattice3 @ X2 @ (sk_C @ X3 @ X2) @ (a_2_2_lattice3 @ X1 @ X0))
% 2.72/2.92          | (r4_lattice3 @ X1 @ 
% 2.72/2.92             (sk_D_3 @ X0 @ X1 @ 
% 2.72/2.92              (sk_D @ (a_2_2_lattice3 @ X1 @ X0) @ (sk_C @ X3 @ X2) @ X2)) @ 
% 2.72/2.92             X0)
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1))),
% 2.72/2.92      inference('sup-', [status(thm)], ['62', '63'])).
% 2.72/2.92  thf('65', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.72/2.92         ((r4_lattice3 @ X3 @ 
% 2.72/2.92           (sk_D @ (a_2_2_lattice3 @ X3 @ X2) @ (sk_C @ X1 @ X0) @ X0) @ X2)
% 2.72/2.92          | ~ (l3_lattices @ X3)
% 2.72/2.92          | ~ (v4_lattice3 @ X3)
% 2.72/2.92          | ~ (v10_lattices @ X3)
% 2.72/2.92          | (v2_struct_0 @ X3)
% 2.72/2.92          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ (a_2_2_lattice3 @ X3 @ X2))
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | (v2_struct_0 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X3)
% 2.72/2.92          | ~ (v4_lattice3 @ X3)
% 2.72/2.92          | ~ (v10_lattices @ X3)
% 2.72/2.92          | (v2_struct_0 @ X3)
% 2.72/2.92          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ (a_2_2_lattice3 @ X3 @ X2))
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | (v2_struct_0 @ X0))),
% 2.72/2.92      inference('sup+', [status(thm)], ['61', '64'])).
% 2.72/2.92  thf('66', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.72/2.92         ((v2_struct_0 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ (a_2_2_lattice3 @ X3 @ X2))
% 2.72/2.92          | (v2_struct_0 @ X3)
% 2.72/2.92          | ~ (v10_lattices @ X3)
% 2.72/2.92          | ~ (v4_lattice3 @ X3)
% 2.72/2.92          | ~ (l3_lattices @ X3)
% 2.72/2.92          | (r4_lattice3 @ X3 @ 
% 2.72/2.92             (sk_D @ (a_2_2_lattice3 @ X3 @ X2) @ (sk_C @ X1 @ X0) @ X0) @ X2))),
% 2.72/2.92      inference('simplify', [status(thm)], ['65'])).
% 2.72/2.92  thf('67', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.72/2.92         ((r4_lattice3 @ X3 @ 
% 2.72/2.92           (sk_D @ (a_2_2_lattice3 @ X3 @ X2) @ (k15_lattice3 @ X1 @ X0) @ X1) @ 
% 2.72/2.92           X2)
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X3)
% 2.72/2.92          | ~ (v4_lattice3 @ X3)
% 2.72/2.92          | ~ (v10_lattices @ X3)
% 2.72/2.92          | (v2_struct_0 @ X3)
% 2.72/2.92          | (r3_lattice3 @ X1 @ (sk_C @ X0 @ X1) @ (a_2_2_lattice3 @ X3 @ X2))
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1))),
% 2.72/2.92      inference('sup+', [status(thm)], ['55', '66'])).
% 2.72/2.92  thf('68', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.72/2.92         ((r3_lattice3 @ X1 @ (sk_C @ X0 @ X1) @ (a_2_2_lattice3 @ X3 @ X2))
% 2.72/2.92          | (v2_struct_0 @ X3)
% 2.72/2.92          | ~ (v10_lattices @ X3)
% 2.72/2.92          | ~ (v4_lattice3 @ X3)
% 2.72/2.92          | ~ (l3_lattices @ X3)
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | (r4_lattice3 @ X3 @ 
% 2.72/2.92             (sk_D @ (a_2_2_lattice3 @ X3 @ X2) @ (k15_lattice3 @ X1 @ X0) @ X1) @ 
% 2.72/2.92             X2))),
% 2.72/2.92      inference('simplify', [status(thm)], ['67'])).
% 2.72/2.92  thf('69', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         (((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0))
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1))),
% 2.72/2.92      inference('simplify', [status(thm)], ['30'])).
% 2.72/2.92  thf('70', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.72/2.92         ((v2_struct_0 @ X2)
% 2.72/2.92          | ~ (l3_lattices @ X2)
% 2.72/2.92          | ~ (v4_lattice3 @ X2)
% 2.72/2.92          | (r3_lattice3 @ X2 @ (sk_C @ X3 @ X2) @ (a_2_2_lattice3 @ X1 @ X0))
% 2.72/2.92          | ((sk_D @ (a_2_2_lattice3 @ X1 @ X0) @ (sk_C @ X3 @ X2) @ X2)
% 2.72/2.92              = (sk_D_3 @ X0 @ X1 @ 
% 2.72/2.92                 (sk_D @ (a_2_2_lattice3 @ X1 @ X0) @ (sk_C @ X3 @ X2) @ X2)))
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1))),
% 2.72/2.92      inference('sup-', [status(thm)], ['59', '60'])).
% 2.72/2.92  thf('71', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         (((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0))
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1))),
% 2.72/2.92      inference('simplify', [status(thm)], ['30'])).
% 2.72/2.92  thf('72', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.72/2.92         ((r3_lattice3 @ X1 @ (sk_C @ X0 @ X1) @ (a_2_2_lattice3 @ X3 @ X2))
% 2.72/2.92          | (v2_struct_0 @ X3)
% 2.72/2.92          | ~ (v10_lattices @ X3)
% 2.72/2.92          | ~ (v4_lattice3 @ X3)
% 2.72/2.92          | ~ (l3_lattices @ X3)
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | (r4_lattice3 @ X3 @ 
% 2.72/2.92             (sk_D @ (a_2_2_lattice3 @ X3 @ X2) @ (k15_lattice3 @ X1 @ X0) @ X1) @ 
% 2.72/2.92             X2))),
% 2.72/2.92      inference('simplify', [status(thm)], ['67'])).
% 2.72/2.92  thf('73', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         ((r3_lattice3 @ X1 @ (sk_C @ X0 @ X1) @ X2)
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | (m1_subset_1 @ (sk_D @ X2 @ (k15_lattice3 @ X1 @ X0) @ X1) @ 
% 2.72/2.92             (u1_struct_0 @ X1)))),
% 2.72/2.92      inference('simplify', [status(thm)], ['53'])).
% 2.72/2.92  thf('74', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         (~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | (m1_subset_1 @ (k15_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1)))),
% 2.72/2.92      inference('simplify', [status(thm)], ['33'])).
% 2.72/2.92  thf('75', plain,
% 2.72/2.92      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 2.72/2.92         ((v2_struct_0 @ X13)
% 2.72/2.92          | ~ (v10_lattices @ X13)
% 2.72/2.92          | ~ (v4_lattice3 @ X13)
% 2.72/2.92          | ~ (l3_lattices @ X13)
% 2.72/2.92          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 2.72/2.92          | ((X14) != (k15_lattice3 @ X13 @ X15))
% 2.72/2.92          | ~ (r4_lattice3 @ X13 @ X16 @ X15)
% 2.72/2.92          | (r1_lattices @ X13 @ X14 @ X16)
% 2.72/2.92          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X13))
% 2.72/2.92          | ~ (l3_lattices @ X13)
% 2.72/2.92          | (v2_struct_0 @ X13))),
% 2.72/2.92      inference('cnf', [status(esa)], [d21_lattice3])).
% 2.72/2.92  thf('76', plain,
% 2.72/2.92      (![X13 : $i, X15 : $i, X16 : $i]:
% 2.72/2.92         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X13))
% 2.72/2.92          | (r1_lattices @ X13 @ (k15_lattice3 @ X13 @ X15) @ X16)
% 2.72/2.92          | ~ (r4_lattice3 @ X13 @ X16 @ X15)
% 2.72/2.92          | ~ (m1_subset_1 @ (k15_lattice3 @ X13 @ X15) @ (u1_struct_0 @ X13))
% 2.72/2.92          | ~ (l3_lattices @ X13)
% 2.72/2.92          | ~ (v4_lattice3 @ X13)
% 2.72/2.92          | ~ (v10_lattices @ X13)
% 2.72/2.92          | (v2_struct_0 @ X13))),
% 2.72/2.92      inference('simplify', [status(thm)], ['75'])).
% 2.72/2.92  thf('77', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         ((v2_struct_0 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | (v2_struct_0 @ X0)
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | ~ (r4_lattice3 @ X0 @ X2 @ X1)
% 2.72/2.92          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.72/2.92          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0)))),
% 2.72/2.92      inference('sup-', [status(thm)], ['74', '76'])).
% 2.72/2.92  thf('78', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         (~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.72/2.92          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.72/2.92          | ~ (r4_lattice3 @ X0 @ X2 @ X1)
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | (v2_struct_0 @ X0))),
% 2.72/2.92      inference('simplify', [status(thm)], ['77'])).
% 2.72/2.92  thf('79', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.72/2.92         ((v2_struct_0 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 2.72/2.92          | (v2_struct_0 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | ~ (r4_lattice3 @ X0 @ 
% 2.72/2.92               (sk_D @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X3)
% 2.72/2.92          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X3) @ 
% 2.72/2.92             (sk_D @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0)))),
% 2.72/2.92      inference('sup-', [status(thm)], ['73', '78'])).
% 2.72/2.92  thf('80', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.72/2.92         ((r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X3) @ 
% 2.72/2.92           (sk_D @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 2.72/2.92          | ~ (r4_lattice3 @ X0 @ 
% 2.72/2.92               (sk_D @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X3)
% 2.72/2.92          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | (v2_struct_0 @ X0))),
% 2.72/2.92      inference('simplify', [status(thm)], ['79'])).
% 2.72/2.92  thf('81', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         ((v2_struct_0 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | (r3_lattice3 @ X1 @ (sk_C @ X2 @ X1) @ (a_2_2_lattice3 @ X1 @ X0))
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | (r3_lattice3 @ X1 @ (sk_C @ X2 @ X1) @ (a_2_2_lattice3 @ X1 @ X0))
% 2.72/2.92          | (r1_lattices @ X1 @ (k15_lattice3 @ X1 @ X0) @ 
% 2.72/2.92             (sk_D @ (a_2_2_lattice3 @ X1 @ X0) @ (k15_lattice3 @ X1 @ X2) @ X1)))),
% 2.72/2.92      inference('sup-', [status(thm)], ['72', '80'])).
% 2.72/2.92  thf('82', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         ((r1_lattices @ X1 @ (k15_lattice3 @ X1 @ X0) @ 
% 2.72/2.92           (sk_D @ (a_2_2_lattice3 @ X1 @ X0) @ (k15_lattice3 @ X1 @ X2) @ X1))
% 2.72/2.92          | (r3_lattice3 @ X1 @ (sk_C @ X2 @ X1) @ (a_2_2_lattice3 @ X1 @ X0))
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1))),
% 2.72/2.92      inference('simplify', [status(thm)], ['81'])).
% 2.72/2.92  thf('83', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         (((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0))
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1))),
% 2.72/2.92      inference('simplify', [status(thm)], ['30'])).
% 2.72/2.92  thf('84', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         (((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0))
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1))),
% 2.72/2.92      inference('simplify', [status(thm)], ['30'])).
% 2.72/2.92  thf('85', plain,
% 2.72/2.92      (![X10 : $i, X11 : $i]:
% 2.72/2.92         (~ (v4_lattice3 @ X10)
% 2.72/2.92          | (m1_subset_1 @ (sk_C @ X11 @ X10) @ (u1_struct_0 @ X10))
% 2.72/2.92          | ~ (l3_lattices @ X10)
% 2.72/2.92          | (v2_struct_0 @ X10))),
% 2.72/2.92      inference('cnf', [status(esa)], [d18_lattice3])).
% 2.72/2.92  thf('86', plain,
% 2.72/2.92      (![X4 : $i, X5 : $i, X8 : $i]:
% 2.72/2.92         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 2.72/2.92          | ~ (r1_lattices @ X5 @ X4 @ (sk_D @ X8 @ X4 @ X5))
% 2.72/2.92          | (r3_lattice3 @ X5 @ X4 @ X8)
% 2.72/2.92          | ~ (l3_lattices @ X5)
% 2.72/2.92          | (v2_struct_0 @ X5))),
% 2.72/2.92      inference('cnf', [status(esa)], [d16_lattice3])).
% 2.72/2.92  thf('87', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         ((v2_struct_0 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | (v2_struct_0 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 2.72/2.92          | ~ (r1_lattices @ X0 @ (sk_C @ X1 @ X0) @ 
% 2.72/2.92               (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0)))),
% 2.72/2.92      inference('sup-', [status(thm)], ['85', '86'])).
% 2.72/2.92  thf('88', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         (~ (r1_lattices @ X0 @ (sk_C @ X1 @ X0) @ 
% 2.72/2.92             (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0))
% 2.72/2.92          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | (v2_struct_0 @ X0))),
% 2.72/2.92      inference('simplify', [status(thm)], ['87'])).
% 2.72/2.92  thf('89', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         (~ (r1_lattices @ X1 @ (sk_C @ X0 @ X1) @ 
% 2.72/2.92             (sk_D @ X2 @ (k15_lattice3 @ X1 @ X0) @ X1))
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | (r3_lattice3 @ X1 @ (sk_C @ X0 @ X1) @ X2))),
% 2.72/2.92      inference('sup-', [status(thm)], ['84', '88'])).
% 2.72/2.92  thf('90', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         ((r3_lattice3 @ X1 @ (sk_C @ X0 @ X1) @ X2)
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | ~ (r1_lattices @ X1 @ (sk_C @ X0 @ X1) @ 
% 2.72/2.92               (sk_D @ X2 @ (k15_lattice3 @ X1 @ X0) @ X1)))),
% 2.72/2.92      inference('simplify', [status(thm)], ['89'])).
% 2.72/2.92  thf('91', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         (~ (r1_lattices @ X1 @ (k15_lattice3 @ X1 @ X0) @ 
% 2.72/2.92             (sk_D @ X2 @ (k15_lattice3 @ X1 @ X0) @ X1))
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | (r3_lattice3 @ X1 @ (sk_C @ X0 @ X1) @ X2))),
% 2.72/2.92      inference('sup-', [status(thm)], ['83', '90'])).
% 2.72/2.92  thf('92', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         ((r3_lattice3 @ X1 @ (sk_C @ X0 @ X1) @ X2)
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | ~ (r1_lattices @ X1 @ (k15_lattice3 @ X1 @ X0) @ 
% 2.72/2.92               (sk_D @ X2 @ (k15_lattice3 @ X1 @ X0) @ X1)))),
% 2.72/2.92      inference('simplify', [status(thm)], ['91'])).
% 2.72/2.92  thf('93', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         ((v2_struct_0 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ (a_2_2_lattice3 @ X0 @ X1))
% 2.72/2.92          | (v2_struct_0 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ (a_2_2_lattice3 @ X0 @ X1)))),
% 2.72/2.92      inference('sup-', [status(thm)], ['82', '92'])).
% 2.72/2.92  thf('94', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         ((r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ (a_2_2_lattice3 @ X0 @ X1))
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | (v2_struct_0 @ X0))),
% 2.72/2.92      inference('simplify', [status(thm)], ['93'])).
% 2.72/2.92  thf('95', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         ((r3_lattice3 @ X1 @ (k15_lattice3 @ X1 @ X0) @ 
% 2.72/2.92           (a_2_2_lattice3 @ X1 @ X0))
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (v10_lattices @ X1))),
% 2.72/2.92      inference('sup+', [status(thm)], ['71', '94'])).
% 2.72/2.92  thf('96', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         (~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | (r3_lattice3 @ X1 @ (k15_lattice3 @ X1 @ X0) @ 
% 2.72/2.92             (a_2_2_lattice3 @ X1 @ X0)))),
% 2.72/2.92      inference('simplify', [status(thm)], ['95'])).
% 2.72/2.92  thf('97', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         (~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | (m1_subset_1 @ (k15_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1)))),
% 2.72/2.92      inference('simplify', [status(thm)], ['33'])).
% 2.72/2.92  thf('98', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         (~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | (m1_subset_1 @ (k15_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1)))),
% 2.72/2.92      inference('simplify', [status(thm)], ['33'])).
% 2.72/2.92  thf('99', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         (~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | (r2_hidden @ (k15_lattice3 @ X1 @ X0) @ (a_2_2_lattice3 @ X1 @ X0)))),
% 2.72/2.92      inference('simplify', [status(thm)], ['45'])).
% 2.72/2.92  thf('100', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         (((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0))
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1))),
% 2.72/2.92      inference('simplify', [status(thm)], ['30'])).
% 2.72/2.92  thf('101', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         (((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0))
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1))),
% 2.72/2.92      inference('simplify', [status(thm)], ['30'])).
% 2.72/2.92  thf('102', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         ((r2_hidden @ (sk_C @ X0 @ X1) @ (a_2_2_lattice3 @ X1 @ X0))
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1))),
% 2.72/2.92      inference('simplify', [status(thm)], ['43'])).
% 2.72/2.92  thf('103', plain,
% 2.72/2.92      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.72/2.92         (~ (l3_lattices @ X17)
% 2.72/2.92          | ~ (v4_lattice3 @ X17)
% 2.72/2.92          | ~ (v10_lattices @ X17)
% 2.72/2.92          | (v2_struct_0 @ X17)
% 2.72/2.92          | ((X19) = (sk_D_3 @ X18 @ X17 @ X19))
% 2.72/2.92          | ~ (r2_hidden @ X19 @ (a_2_2_lattice3 @ X17 @ X18)))),
% 2.72/2.92      inference('cnf', [status(esa)], [fraenkel_a_2_2_lattice3])).
% 2.72/2.92  thf('104', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         ((v2_struct_0 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ((sk_C @ X0 @ X1) = (sk_D_3 @ X0 @ X1 @ (sk_C @ X0 @ X1)))
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1))),
% 2.72/2.92      inference('sup-', [status(thm)], ['102', '103'])).
% 2.72/2.92  thf('105', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         (((sk_C @ X0 @ X1) = (sk_D_3 @ X0 @ X1 @ (sk_C @ X0 @ X1)))
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1))),
% 2.72/2.92      inference('simplify', [status(thm)], ['104'])).
% 2.72/2.92  thf('106', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         (((sk_C @ X0 @ X1) = (sk_D_3 @ X0 @ X1 @ (sk_C @ X0 @ X1)))
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1))),
% 2.72/2.92      inference('simplify', [status(thm)], ['104'])).
% 2.72/2.92  thf('107', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         (((sk_C @ X0 @ X1) = (sk_D_3 @ X0 @ X1 @ (sk_C @ X0 @ X1)))
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1))),
% 2.72/2.92      inference('simplify', [status(thm)], ['104'])).
% 2.72/2.92  thf('108', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         ((r2_hidden @ (sk_C @ X0 @ X1) @ (a_2_2_lattice3 @ X1 @ X0))
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1))),
% 2.72/2.92      inference('simplify', [status(thm)], ['43'])).
% 2.72/2.92  thf('109', plain,
% 2.72/2.92      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.72/2.92         (~ (l3_lattices @ X17)
% 2.72/2.92          | ~ (v4_lattice3 @ X17)
% 2.72/2.92          | ~ (v10_lattices @ X17)
% 2.72/2.92          | (v2_struct_0 @ X17)
% 2.72/2.92          | (m1_subset_1 @ (sk_D_3 @ X18 @ X17 @ X19) @ (u1_struct_0 @ X17))
% 2.72/2.92          | ~ (r2_hidden @ X19 @ (a_2_2_lattice3 @ X17 @ X18)))),
% 2.72/2.92      inference('cnf', [status(esa)], [fraenkel_a_2_2_lattice3])).
% 2.72/2.92  thf('110', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         ((v2_struct_0 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | (m1_subset_1 @ (sk_D_3 @ X0 @ X1 @ (sk_C @ X0 @ X1)) @ 
% 2.72/2.92             (u1_struct_0 @ X1))
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1))),
% 2.72/2.92      inference('sup-', [status(thm)], ['108', '109'])).
% 2.72/2.92  thf('111', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         ((m1_subset_1 @ (sk_D_3 @ X0 @ X1 @ (sk_C @ X0 @ X1)) @ 
% 2.72/2.92           (u1_struct_0 @ X1))
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1))),
% 2.72/2.92      inference('simplify', [status(thm)], ['110'])).
% 2.72/2.92  thf('112', plain,
% 2.72/2.92      (![X4 : $i, X5 : $i, X8 : $i]:
% 2.72/2.92         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 2.72/2.92          | (r2_hidden @ (sk_D @ X8 @ X4 @ X5) @ X8)
% 2.72/2.92          | (r3_lattice3 @ X5 @ X4 @ X8)
% 2.72/2.92          | ~ (l3_lattices @ X5)
% 2.72/2.92          | (v2_struct_0 @ X5))),
% 2.72/2.92      inference('cnf', [status(esa)], [d16_lattice3])).
% 2.72/2.92  thf('113', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         ((v2_struct_0 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | (v2_struct_0 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | (r3_lattice3 @ X0 @ (sk_D_3 @ X1 @ X0 @ (sk_C @ X1 @ X0)) @ X2)
% 2.72/2.92          | (r2_hidden @ 
% 2.72/2.92             (sk_D @ X2 @ (sk_D_3 @ X1 @ X0 @ (sk_C @ X1 @ X0)) @ X0) @ X2))),
% 2.72/2.92      inference('sup-', [status(thm)], ['111', '112'])).
% 2.72/2.92  thf('114', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         ((r2_hidden @ 
% 2.72/2.92           (sk_D @ X2 @ (sk_D_3 @ X1 @ X0 @ (sk_C @ X1 @ X0)) @ X0) @ X2)
% 2.72/2.92          | (r3_lattice3 @ X0 @ (sk_D_3 @ X1 @ X0 @ (sk_C @ X1 @ X0)) @ X2)
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | (v2_struct_0 @ X0))),
% 2.72/2.92      inference('simplify', [status(thm)], ['113'])).
% 2.72/2.92  thf('115', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         ((r2_hidden @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X2)
% 2.72/2.92          | (v2_struct_0 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | (v2_struct_0 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | (r3_lattice3 @ X0 @ (sk_D_3 @ X1 @ X0 @ (sk_C @ X1 @ X0)) @ X2))),
% 2.72/2.92      inference('sup+', [status(thm)], ['107', '114'])).
% 2.72/2.92  thf('116', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         ((r3_lattice3 @ X0 @ (sk_D_3 @ X1 @ X0 @ (sk_C @ X1 @ X0)) @ X2)
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | (v2_struct_0 @ X0)
% 2.72/2.92          | (r2_hidden @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X2))),
% 2.72/2.92      inference('simplify', [status(thm)], ['115'])).
% 2.72/2.92  thf('117', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         ((m1_subset_1 @ (sk_D_3 @ X0 @ X1 @ (sk_C @ X0 @ X1)) @ 
% 2.72/2.92           (u1_struct_0 @ X1))
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1))),
% 2.72/2.92      inference('simplify', [status(thm)], ['110'])).
% 2.72/2.92  thf(t34_lattice3, axiom,
% 2.72/2.92    (![A:$i]:
% 2.72/2.92     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.72/2.92         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 2.72/2.92       ( ![B:$i]:
% 2.72/2.92         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.72/2.92           ( ![C:$i]:
% 2.72/2.92             ( ( ( B ) = ( k16_lattice3 @ A @ C ) ) <=>
% 2.72/2.92               ( ( r3_lattice3 @ A @ B @ C ) & 
% 2.72/2.92                 ( ![D:$i]:
% 2.72/2.92                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 2.72/2.92                     ( ( r3_lattice3 @ A @ D @ C ) =>
% 2.72/2.92                       ( r3_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 2.72/2.92  thf('118', plain,
% 2.72/2.92      (![X21 : $i, X22 : $i, X25 : $i]:
% 2.72/2.92         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 2.72/2.92          | ~ (r3_lattice3 @ X22 @ X21 @ X25)
% 2.72/2.92          | (r3_lattice3 @ X22 @ (sk_D_4 @ X25 @ X21 @ X22) @ X25)
% 2.72/2.92          | ((X21) = (k16_lattice3 @ X22 @ X25))
% 2.72/2.92          | ~ (l3_lattices @ X22)
% 2.72/2.92          | ~ (v4_lattice3 @ X22)
% 2.72/2.92          | ~ (v10_lattices @ X22)
% 2.72/2.92          | (v2_struct_0 @ X22))),
% 2.72/2.92      inference('cnf', [status(esa)], [t34_lattice3])).
% 2.72/2.92  thf('119', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         ((v2_struct_0 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | (v2_struct_0 @ X0)
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | ((sk_D_3 @ X1 @ X0 @ (sk_C @ X1 @ X0)) = (k16_lattice3 @ X0 @ X2))
% 2.72/2.92          | (r3_lattice3 @ X0 @ 
% 2.72/2.92             (sk_D_4 @ X2 @ (sk_D_3 @ X1 @ X0 @ (sk_C @ X1 @ X0)) @ X0) @ X2)
% 2.72/2.92          | ~ (r3_lattice3 @ X0 @ (sk_D_3 @ X1 @ X0 @ (sk_C @ X1 @ X0)) @ X2))),
% 2.72/2.92      inference('sup-', [status(thm)], ['117', '118'])).
% 2.72/2.92  thf('120', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         (~ (r3_lattice3 @ X0 @ (sk_D_3 @ X1 @ X0 @ (sk_C @ X1 @ X0)) @ X2)
% 2.72/2.92          | (r3_lattice3 @ X0 @ 
% 2.72/2.92             (sk_D_4 @ X2 @ (sk_D_3 @ X1 @ X0 @ (sk_C @ X1 @ X0)) @ X0) @ X2)
% 2.72/2.92          | ((sk_D_3 @ X1 @ X0 @ (sk_C @ X1 @ X0)) = (k16_lattice3 @ X0 @ X2))
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | (v2_struct_0 @ X0))),
% 2.72/2.92      inference('simplify', [status(thm)], ['119'])).
% 2.72/2.92  thf('121', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         ((r2_hidden @ (sk_D @ X0 @ (sk_C @ X2 @ X1) @ X1) @ X0)
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ((sk_D_3 @ X2 @ X1 @ (sk_C @ X2 @ X1)) = (k16_lattice3 @ X1 @ X0))
% 2.72/2.92          | (r3_lattice3 @ X1 @ 
% 2.72/2.92             (sk_D_4 @ X0 @ (sk_D_3 @ X2 @ X1 @ (sk_C @ X2 @ X1)) @ X1) @ X0))),
% 2.72/2.92      inference('sup-', [status(thm)], ['116', '120'])).
% 2.72/2.92  thf('122', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         ((r3_lattice3 @ X1 @ 
% 2.72/2.92           (sk_D_4 @ X0 @ (sk_D_3 @ X2 @ X1 @ (sk_C @ X2 @ X1)) @ X1) @ X0)
% 2.72/2.92          | ((sk_D_3 @ X2 @ X1 @ (sk_C @ X2 @ X1)) = (k16_lattice3 @ X1 @ X0))
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | (r2_hidden @ (sk_D @ X0 @ (sk_C @ X2 @ X1) @ X1) @ X0))),
% 2.72/2.92      inference('simplify', [status(thm)], ['121'])).
% 2.72/2.92  thf('123', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         ((r3_lattice3 @ X0 @ (sk_D_4 @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X2)
% 2.72/2.92          | (v2_struct_0 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | (r2_hidden @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X2)
% 2.72/2.92          | (v2_struct_0 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | ((sk_D_3 @ X1 @ X0 @ (sk_C @ X1 @ X0)) = (k16_lattice3 @ X0 @ X2)))),
% 2.72/2.92      inference('sup+', [status(thm)], ['106', '122'])).
% 2.72/2.92  thf('124', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         (((sk_D_3 @ X1 @ X0 @ (sk_C @ X1 @ X0)) = (k16_lattice3 @ X0 @ X2))
% 2.72/2.92          | (r2_hidden @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X2)
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | (v2_struct_0 @ X0)
% 2.72/2.92          | (r3_lattice3 @ X0 @ (sk_D_4 @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X2))),
% 2.72/2.92      inference('simplify', [status(thm)], ['123'])).
% 2.72/2.92  thf('125', plain,
% 2.72/2.92      (((k15_lattice3 @ sk_A @ sk_B_1)
% 2.72/2.92         != (k16_lattice3 @ sk_A @ (a_2_2_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('126', plain,
% 2.72/2.92      (![X0 : $i]:
% 2.72/2.92         (((k15_lattice3 @ sk_A @ sk_B_1)
% 2.72/2.92            != (sk_D_3 @ X0 @ sk_A @ (sk_C @ X0 @ sk_A)))
% 2.72/2.92          | (r3_lattice3 @ sk_A @ 
% 2.72/2.92             (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ X0 @ sk_A) @ 
% 2.72/2.92              sk_A) @ 
% 2.72/2.92             (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.92          | (v2_struct_0 @ sk_A)
% 2.72/2.92          | ~ (l3_lattices @ sk_A)
% 2.72/2.92          | ~ (v4_lattice3 @ sk_A)
% 2.72/2.92          | ~ (v10_lattices @ sk_A)
% 2.72/2.92          | (r2_hidden @ 
% 2.72/2.92             (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ X0 @ sk_A) @ 
% 2.72/2.92              sk_A) @ 
% 2.72/2.92             (a_2_2_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.92      inference('sup-', [status(thm)], ['124', '125'])).
% 2.72/2.92  thf('127', plain, ((l3_lattices @ sk_A)),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('128', plain, ((v4_lattice3 @ sk_A)),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('129', plain, ((v10_lattices @ sk_A)),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('130', plain,
% 2.72/2.92      (![X0 : $i]:
% 2.72/2.92         (((k15_lattice3 @ sk_A @ sk_B_1)
% 2.72/2.92            != (sk_D_3 @ X0 @ sk_A @ (sk_C @ X0 @ sk_A)))
% 2.72/2.92          | (r3_lattice3 @ sk_A @ 
% 2.72/2.92             (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ X0 @ sk_A) @ 
% 2.72/2.92              sk_A) @ 
% 2.72/2.92             (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.92          | (v2_struct_0 @ sk_A)
% 2.72/2.92          | (r2_hidden @ 
% 2.72/2.92             (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ X0 @ sk_A) @ 
% 2.72/2.92              sk_A) @ 
% 2.72/2.92             (a_2_2_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.92      inference('demod', [status(thm)], ['126', '127', '128', '129'])).
% 2.72/2.92  thf('131', plain,
% 2.72/2.92      (![X0 : $i]:
% 2.72/2.92         (((k15_lattice3 @ sk_A @ sk_B_1) != (sk_C @ X0 @ sk_A))
% 2.72/2.92          | (v2_struct_0 @ sk_A)
% 2.72/2.92          | ~ (l3_lattices @ sk_A)
% 2.72/2.92          | ~ (v4_lattice3 @ sk_A)
% 2.72/2.92          | ~ (v10_lattices @ sk_A)
% 2.72/2.92          | (r2_hidden @ 
% 2.72/2.92             (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ X0 @ sk_A) @ 
% 2.72/2.92              sk_A) @ 
% 2.72/2.92             (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.92          | (v2_struct_0 @ sk_A)
% 2.72/2.92          | (r3_lattice3 @ sk_A @ 
% 2.72/2.92             (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ X0 @ sk_A) @ 
% 2.72/2.92              sk_A) @ 
% 2.72/2.92             (a_2_2_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.92      inference('sup-', [status(thm)], ['105', '130'])).
% 2.72/2.92  thf('132', plain, ((l3_lattices @ sk_A)),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('133', plain, ((v4_lattice3 @ sk_A)),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('134', plain, ((v10_lattices @ sk_A)),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('135', plain,
% 2.72/2.92      (![X0 : $i]:
% 2.72/2.92         (((k15_lattice3 @ sk_A @ sk_B_1) != (sk_C @ X0 @ sk_A))
% 2.72/2.92          | (v2_struct_0 @ sk_A)
% 2.72/2.92          | (r2_hidden @ 
% 2.72/2.92             (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ X0 @ sk_A) @ 
% 2.72/2.92              sk_A) @ 
% 2.72/2.92             (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.92          | (v2_struct_0 @ sk_A)
% 2.72/2.92          | (r3_lattice3 @ sk_A @ 
% 2.72/2.92             (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ X0 @ sk_A) @ 
% 2.72/2.92              sk_A) @ 
% 2.72/2.92             (a_2_2_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.92      inference('demod', [status(thm)], ['131', '132', '133', '134'])).
% 2.72/2.92  thf('136', plain,
% 2.72/2.92      (![X0 : $i]:
% 2.72/2.92         ((r3_lattice3 @ sk_A @ 
% 2.72/2.92           (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ X0 @ sk_A) @ 
% 2.72/2.92            sk_A) @ 
% 2.72/2.92           (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.92          | (r2_hidden @ 
% 2.72/2.92             (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ X0 @ sk_A) @ 
% 2.72/2.92              sk_A) @ 
% 2.72/2.92             (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.92          | (v2_struct_0 @ sk_A)
% 2.72/2.92          | ((k15_lattice3 @ sk_A @ sk_B_1) != (sk_C @ X0 @ sk_A)))),
% 2.72/2.92      inference('simplify', [status(thm)], ['135'])).
% 2.72/2.92  thf('137', plain,
% 2.72/2.92      (![X0 : $i]:
% 2.72/2.92         (((k15_lattice3 @ sk_A @ sk_B_1) != (k15_lattice3 @ sk_A @ X0))
% 2.72/2.92          | (v2_struct_0 @ sk_A)
% 2.72/2.92          | ~ (l3_lattices @ sk_A)
% 2.72/2.92          | ~ (v4_lattice3 @ sk_A)
% 2.72/2.92          | ~ (v10_lattices @ sk_A)
% 2.72/2.92          | (v2_struct_0 @ sk_A)
% 2.72/2.92          | (r2_hidden @ 
% 2.72/2.92             (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ X0 @ sk_A) @ 
% 2.72/2.92              sk_A) @ 
% 2.72/2.92             (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.92          | (r3_lattice3 @ sk_A @ 
% 2.72/2.92             (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ X0 @ sk_A) @ 
% 2.72/2.92              sk_A) @ 
% 2.72/2.92             (a_2_2_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.92      inference('sup-', [status(thm)], ['101', '136'])).
% 2.72/2.92  thf('138', plain, ((l3_lattices @ sk_A)),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('139', plain, ((v4_lattice3 @ sk_A)),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('140', plain, ((v10_lattices @ sk_A)),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('141', plain,
% 2.72/2.92      (![X0 : $i]:
% 2.72/2.92         (((k15_lattice3 @ sk_A @ sk_B_1) != (k15_lattice3 @ sk_A @ X0))
% 2.72/2.92          | (v2_struct_0 @ sk_A)
% 2.72/2.92          | (v2_struct_0 @ sk_A)
% 2.72/2.92          | (r2_hidden @ 
% 2.72/2.92             (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ X0 @ sk_A) @ 
% 2.72/2.92              sk_A) @ 
% 2.72/2.92             (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.92          | (r3_lattice3 @ sk_A @ 
% 2.72/2.92             (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ X0 @ sk_A) @ 
% 2.72/2.92              sk_A) @ 
% 2.72/2.92             (a_2_2_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.92      inference('demod', [status(thm)], ['137', '138', '139', '140'])).
% 2.72/2.92  thf('142', plain,
% 2.72/2.92      (![X0 : $i]:
% 2.72/2.92         ((r3_lattice3 @ sk_A @ 
% 2.72/2.92           (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ X0 @ sk_A) @ 
% 2.72/2.92            sk_A) @ 
% 2.72/2.92           (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.92          | (r2_hidden @ 
% 2.72/2.92             (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ X0 @ sk_A) @ 
% 2.72/2.92              sk_A) @ 
% 2.72/2.92             (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.92          | (v2_struct_0 @ sk_A)
% 2.72/2.92          | ((k15_lattice3 @ sk_A @ sk_B_1) != (k15_lattice3 @ sk_A @ X0)))),
% 2.72/2.92      inference('simplify', [status(thm)], ['141'])).
% 2.72/2.92  thf('143', plain,
% 2.72/2.92      (((v2_struct_0 @ sk_A)
% 2.72/2.92        | (r2_hidden @ 
% 2.72/2.92           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.92            sk_A) @ 
% 2.72/2.92           (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.92        | (r3_lattice3 @ sk_A @ 
% 2.72/2.92           (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.92            (sk_C @ sk_B_1 @ sk_A) @ sk_A) @ 
% 2.72/2.92           (a_2_2_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.92      inference('eq_res', [status(thm)], ['142'])).
% 2.72/2.92  thf('144', plain, (~ (v2_struct_0 @ sk_A)),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('145', plain,
% 2.72/2.92      (((r3_lattice3 @ sk_A @ 
% 2.72/2.92         (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.92          sk_A) @ 
% 2.72/2.92         (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.92        | (r2_hidden @ 
% 2.72/2.92           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.92            sk_A) @ 
% 2.72/2.92           (a_2_2_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.92      inference('clc', [status(thm)], ['143', '144'])).
% 2.72/2.92  thf('146', plain,
% 2.72/2.92      (((r3_lattice3 @ sk_A @ 
% 2.72/2.92         (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.92          (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.92         (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.92        | (v2_struct_0 @ sk_A)
% 2.72/2.92        | ~ (l3_lattices @ sk_A)
% 2.72/2.92        | ~ (v4_lattice3 @ sk_A)
% 2.72/2.92        | ~ (v10_lattices @ sk_A)
% 2.72/2.92        | (r2_hidden @ 
% 2.72/2.92           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.92            sk_A) @ 
% 2.72/2.92           (a_2_2_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.92      inference('sup+', [status(thm)], ['100', '145'])).
% 2.72/2.92  thf('147', plain, ((l3_lattices @ sk_A)),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('148', plain, ((v4_lattice3 @ sk_A)),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('149', plain, ((v10_lattices @ sk_A)),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('150', plain,
% 2.72/2.92      (((r3_lattice3 @ sk_A @ 
% 2.72/2.92         (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.92          (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.92         (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.92        | (v2_struct_0 @ sk_A)
% 2.72/2.92        | (r2_hidden @ 
% 2.72/2.92           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.92            sk_A) @ 
% 2.72/2.92           (a_2_2_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.92      inference('demod', [status(thm)], ['146', '147', '148', '149'])).
% 2.72/2.92  thf('151', plain, (~ (v2_struct_0 @ sk_A)),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('152', plain,
% 2.72/2.92      (((r2_hidden @ 
% 2.72/2.92         (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.92          sk_A) @ 
% 2.72/2.92         (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.92        | (r3_lattice3 @ sk_A @ 
% 2.72/2.92           (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.92            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.92           (a_2_2_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.92      inference('clc', [status(thm)], ['150', '151'])).
% 2.72/2.92  thf('153', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         (((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0))
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1))),
% 2.72/2.92      inference('simplify', [status(thm)], ['30'])).
% 2.72/2.92  thf('154', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         (((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0))
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1))),
% 2.72/2.92      inference('simplify', [status(thm)], ['30'])).
% 2.72/2.92  thf('155', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         (((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0))
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1))),
% 2.72/2.92      inference('simplify', [status(thm)], ['30'])).
% 2.72/2.92  thf('156', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         (((sk_C @ X0 @ X1) = (sk_D_3 @ X0 @ X1 @ (sk_C @ X0 @ X1)))
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1))),
% 2.72/2.92      inference('simplify', [status(thm)], ['104'])).
% 2.72/2.92  thf('157', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         (((sk_C @ X0 @ X1) = (sk_D_3 @ X0 @ X1 @ (sk_C @ X0 @ X1)))
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1))),
% 2.72/2.92      inference('simplify', [status(thm)], ['104'])).
% 2.72/2.92  thf('158', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         (((sk_C @ X0 @ X1) = (sk_D_3 @ X0 @ X1 @ (sk_C @ X0 @ X1)))
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1))),
% 2.72/2.92      inference('simplify', [status(thm)], ['104'])).
% 2.72/2.92  thf('159', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         ((m1_subset_1 @ (sk_D_3 @ X0 @ X1 @ (sk_C @ X0 @ X1)) @ 
% 2.72/2.92           (u1_struct_0 @ X1))
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1))),
% 2.72/2.92      inference('simplify', [status(thm)], ['110'])).
% 2.72/2.92  thf('160', plain,
% 2.72/2.92      (![X4 : $i, X5 : $i, X8 : $i]:
% 2.72/2.92         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 2.72/2.92          | (m1_subset_1 @ (sk_D @ X8 @ X4 @ X5) @ (u1_struct_0 @ X5))
% 2.72/2.92          | (r3_lattice3 @ X5 @ X4 @ X8)
% 2.72/2.92          | ~ (l3_lattices @ X5)
% 2.72/2.92          | (v2_struct_0 @ X5))),
% 2.72/2.92      inference('cnf', [status(esa)], [d16_lattice3])).
% 2.72/2.92  thf('161', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         ((v2_struct_0 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | (v2_struct_0 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | (r3_lattice3 @ X0 @ (sk_D_3 @ X1 @ X0 @ (sk_C @ X1 @ X0)) @ X2)
% 2.72/2.92          | (m1_subset_1 @ 
% 2.72/2.92             (sk_D @ X2 @ (sk_D_3 @ X1 @ X0 @ (sk_C @ X1 @ X0)) @ X0) @ 
% 2.72/2.92             (u1_struct_0 @ X0)))),
% 2.72/2.92      inference('sup-', [status(thm)], ['159', '160'])).
% 2.72/2.92  thf('162', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         ((m1_subset_1 @ 
% 2.72/2.92           (sk_D @ X2 @ (sk_D_3 @ X1 @ X0 @ (sk_C @ X1 @ X0)) @ X0) @ 
% 2.72/2.92           (u1_struct_0 @ X0))
% 2.72/2.92          | (r3_lattice3 @ X0 @ (sk_D_3 @ X1 @ X0 @ (sk_C @ X1 @ X0)) @ X2)
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | (v2_struct_0 @ X0))),
% 2.72/2.92      inference('simplify', [status(thm)], ['161'])).
% 2.72/2.92  thf('163', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         ((m1_subset_1 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ 
% 2.72/2.92           (u1_struct_0 @ X0))
% 2.72/2.92          | (v2_struct_0 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | (v2_struct_0 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | (r3_lattice3 @ X0 @ (sk_D_3 @ X1 @ X0 @ (sk_C @ X1 @ X0)) @ X2))),
% 2.72/2.92      inference('sup+', [status(thm)], ['158', '162'])).
% 2.72/2.92  thf('164', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         ((r3_lattice3 @ X0 @ (sk_D_3 @ X1 @ X0 @ (sk_C @ X1 @ X0)) @ X2)
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | (v2_struct_0 @ X0)
% 2.72/2.92          | (m1_subset_1 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ 
% 2.72/2.92             (u1_struct_0 @ X0)))),
% 2.72/2.92      inference('simplify', [status(thm)], ['163'])).
% 2.72/2.92  thf('165', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         ((m1_subset_1 @ (sk_D_3 @ X0 @ X1 @ (sk_C @ X0 @ X1)) @ 
% 2.72/2.92           (u1_struct_0 @ X1))
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1))),
% 2.72/2.92      inference('simplify', [status(thm)], ['110'])).
% 2.72/2.92  thf('166', plain,
% 2.72/2.92      (![X21 : $i, X22 : $i, X25 : $i]:
% 2.72/2.92         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 2.72/2.92          | ~ (r3_lattice3 @ X22 @ X21 @ X25)
% 2.72/2.92          | (m1_subset_1 @ (sk_D_4 @ X25 @ X21 @ X22) @ (u1_struct_0 @ X22))
% 2.72/2.92          | ((X21) = (k16_lattice3 @ X22 @ X25))
% 2.72/2.92          | ~ (l3_lattices @ X22)
% 2.72/2.92          | ~ (v4_lattice3 @ X22)
% 2.72/2.92          | ~ (v10_lattices @ X22)
% 2.72/2.92          | (v2_struct_0 @ X22))),
% 2.72/2.92      inference('cnf', [status(esa)], [t34_lattice3])).
% 2.72/2.92  thf('167', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         ((v2_struct_0 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | (v2_struct_0 @ X0)
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | ((sk_D_3 @ X1 @ X0 @ (sk_C @ X1 @ X0)) = (k16_lattice3 @ X0 @ X2))
% 2.72/2.92          | (m1_subset_1 @ 
% 2.72/2.92             (sk_D_4 @ X2 @ (sk_D_3 @ X1 @ X0 @ (sk_C @ X1 @ X0)) @ X0) @ 
% 2.72/2.92             (u1_struct_0 @ X0))
% 2.72/2.92          | ~ (r3_lattice3 @ X0 @ (sk_D_3 @ X1 @ X0 @ (sk_C @ X1 @ X0)) @ X2))),
% 2.72/2.92      inference('sup-', [status(thm)], ['165', '166'])).
% 2.72/2.92  thf('168', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         (~ (r3_lattice3 @ X0 @ (sk_D_3 @ X1 @ X0 @ (sk_C @ X1 @ X0)) @ X2)
% 2.72/2.92          | (m1_subset_1 @ 
% 2.72/2.92             (sk_D_4 @ X2 @ (sk_D_3 @ X1 @ X0 @ (sk_C @ X1 @ X0)) @ X0) @ 
% 2.72/2.92             (u1_struct_0 @ X0))
% 2.72/2.92          | ((sk_D_3 @ X1 @ X0 @ (sk_C @ X1 @ X0)) = (k16_lattice3 @ X0 @ X2))
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | (v2_struct_0 @ X0))),
% 2.72/2.92      inference('simplify', [status(thm)], ['167'])).
% 2.72/2.92  thf('169', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         ((m1_subset_1 @ (sk_D @ X0 @ (sk_C @ X2 @ X1) @ X1) @ 
% 2.72/2.92           (u1_struct_0 @ X1))
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ((sk_D_3 @ X2 @ X1 @ (sk_C @ X2 @ X1)) = (k16_lattice3 @ X1 @ X0))
% 2.72/2.92          | (m1_subset_1 @ 
% 2.72/2.92             (sk_D_4 @ X0 @ (sk_D_3 @ X2 @ X1 @ (sk_C @ X2 @ X1)) @ X1) @ 
% 2.72/2.92             (u1_struct_0 @ X1)))),
% 2.72/2.92      inference('sup-', [status(thm)], ['164', '168'])).
% 2.72/2.92  thf('170', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         ((m1_subset_1 @ 
% 2.72/2.92           (sk_D_4 @ X0 @ (sk_D_3 @ X2 @ X1 @ (sk_C @ X2 @ X1)) @ X1) @ 
% 2.72/2.92           (u1_struct_0 @ X1))
% 2.72/2.92          | ((sk_D_3 @ X2 @ X1 @ (sk_C @ X2 @ X1)) = (k16_lattice3 @ X1 @ X0))
% 2.72/2.92          | ~ (v10_lattices @ X1)
% 2.72/2.92          | ~ (v4_lattice3 @ X1)
% 2.72/2.92          | ~ (l3_lattices @ X1)
% 2.72/2.92          | (v2_struct_0 @ X1)
% 2.72/2.92          | (m1_subset_1 @ (sk_D @ X0 @ (sk_C @ X2 @ X1) @ X1) @ 
% 2.72/2.92             (u1_struct_0 @ X1)))),
% 2.72/2.92      inference('simplify', [status(thm)], ['169'])).
% 2.72/2.92  thf('171', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         ((m1_subset_1 @ (sk_D_4 @ X2 @ (sk_C @ X1 @ X0) @ X0) @ 
% 2.72/2.92           (u1_struct_0 @ X0))
% 2.72/2.92          | (v2_struct_0 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | (m1_subset_1 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ 
% 2.72/2.92             (u1_struct_0 @ X0))
% 2.72/2.92          | (v2_struct_0 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | ((sk_D_3 @ X1 @ X0 @ (sk_C @ X1 @ X0)) = (k16_lattice3 @ X0 @ X2)))),
% 2.72/2.92      inference('sup+', [status(thm)], ['157', '170'])).
% 2.72/2.92  thf('172', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.92         (((sk_D_3 @ X1 @ X0 @ (sk_C @ X1 @ X0)) = (k16_lattice3 @ X0 @ X2))
% 2.72/2.92          | (m1_subset_1 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ 
% 2.72/2.92             (u1_struct_0 @ X0))
% 2.72/2.92          | ~ (v10_lattices @ X0)
% 2.72/2.92          | ~ (v4_lattice3 @ X0)
% 2.72/2.92          | ~ (l3_lattices @ X0)
% 2.72/2.92          | (v2_struct_0 @ X0)
% 2.72/2.92          | (m1_subset_1 @ (sk_D_4 @ X2 @ (sk_C @ X1 @ X0) @ X0) @ 
% 2.72/2.92             (u1_struct_0 @ X0)))),
% 2.72/2.92      inference('simplify', [status(thm)], ['171'])).
% 2.72/2.92  thf('173', plain,
% 2.72/2.92      (((k15_lattice3 @ sk_A @ sk_B_1)
% 2.72/2.92         != (k16_lattice3 @ sk_A @ (a_2_2_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('174', plain,
% 2.72/2.92      (![X0 : $i]:
% 2.72/2.92         (((k15_lattice3 @ sk_A @ sk_B_1)
% 2.72/2.92            != (sk_D_3 @ X0 @ sk_A @ (sk_C @ X0 @ sk_A)))
% 2.72/2.92          | (m1_subset_1 @ 
% 2.72/2.92             (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ X0 @ sk_A) @ 
% 2.72/2.92              sk_A) @ 
% 2.72/2.92             (u1_struct_0 @ sk_A))
% 2.72/2.92          | (v2_struct_0 @ sk_A)
% 2.72/2.92          | ~ (l3_lattices @ sk_A)
% 2.72/2.92          | ~ (v4_lattice3 @ sk_A)
% 2.72/2.92          | ~ (v10_lattices @ sk_A)
% 2.72/2.92          | (m1_subset_1 @ 
% 2.72/2.92             (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ X0 @ sk_A) @ 
% 2.72/2.92              sk_A) @ 
% 2.72/2.92             (u1_struct_0 @ sk_A)))),
% 2.72/2.92      inference('sup-', [status(thm)], ['172', '173'])).
% 2.72/2.92  thf('175', plain, ((l3_lattices @ sk_A)),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('176', plain, ((v4_lattice3 @ sk_A)),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('177', plain, ((v10_lattices @ sk_A)),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('178', plain,
% 2.72/2.92      (![X0 : $i]:
% 2.72/2.92         (((k15_lattice3 @ sk_A @ sk_B_1)
% 2.72/2.92            != (sk_D_3 @ X0 @ sk_A @ (sk_C @ X0 @ sk_A)))
% 2.72/2.92          | (m1_subset_1 @ 
% 2.72/2.92             (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ X0 @ sk_A) @ 
% 2.72/2.92              sk_A) @ 
% 2.72/2.92             (u1_struct_0 @ sk_A))
% 2.72/2.92          | (v2_struct_0 @ sk_A)
% 2.72/2.92          | (m1_subset_1 @ 
% 2.72/2.92             (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ X0 @ sk_A) @ 
% 2.72/2.92              sk_A) @ 
% 2.72/2.92             (u1_struct_0 @ sk_A)))),
% 2.72/2.92      inference('demod', [status(thm)], ['174', '175', '176', '177'])).
% 2.72/2.92  thf('179', plain,
% 2.72/2.92      (![X0 : $i]:
% 2.72/2.92         (((k15_lattice3 @ sk_A @ sk_B_1) != (sk_C @ X0 @ sk_A))
% 2.72/2.92          | (v2_struct_0 @ sk_A)
% 2.72/2.92          | ~ (l3_lattices @ sk_A)
% 2.72/2.92          | ~ (v4_lattice3 @ sk_A)
% 2.72/2.92          | ~ (v10_lattices @ sk_A)
% 2.72/2.92          | (m1_subset_1 @ 
% 2.72/2.92             (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ X0 @ sk_A) @ 
% 2.72/2.92              sk_A) @ 
% 2.72/2.92             (u1_struct_0 @ sk_A))
% 2.72/2.92          | (v2_struct_0 @ sk_A)
% 2.72/2.92          | (m1_subset_1 @ 
% 2.72/2.92             (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ X0 @ sk_A) @ 
% 2.72/2.92              sk_A) @ 
% 2.72/2.92             (u1_struct_0 @ sk_A)))),
% 2.72/2.92      inference('sup-', [status(thm)], ['156', '178'])).
% 2.72/2.92  thf('180', plain, ((l3_lattices @ sk_A)),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('181', plain, ((v4_lattice3 @ sk_A)),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('182', plain, ((v10_lattices @ sk_A)),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('183', plain,
% 2.72/2.92      (![X0 : $i]:
% 2.72/2.92         (((k15_lattice3 @ sk_A @ sk_B_1) != (sk_C @ X0 @ sk_A))
% 2.72/2.92          | (v2_struct_0 @ sk_A)
% 2.72/2.92          | (m1_subset_1 @ 
% 2.72/2.92             (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ X0 @ sk_A) @ 
% 2.72/2.92              sk_A) @ 
% 2.72/2.92             (u1_struct_0 @ sk_A))
% 2.72/2.92          | (v2_struct_0 @ sk_A)
% 2.72/2.92          | (m1_subset_1 @ 
% 2.72/2.92             (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ X0 @ sk_A) @ 
% 2.72/2.92              sk_A) @ 
% 2.72/2.92             (u1_struct_0 @ sk_A)))),
% 2.72/2.92      inference('demod', [status(thm)], ['179', '180', '181', '182'])).
% 2.72/2.92  thf('184', plain,
% 2.72/2.92      (![X0 : $i]:
% 2.72/2.92         ((m1_subset_1 @ 
% 2.72/2.92           (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ X0 @ sk_A) @ 
% 2.72/2.92            sk_A) @ 
% 2.72/2.92           (u1_struct_0 @ sk_A))
% 2.72/2.92          | (m1_subset_1 @ 
% 2.72/2.92             (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ X0 @ sk_A) @ 
% 2.72/2.92              sk_A) @ 
% 2.72/2.92             (u1_struct_0 @ sk_A))
% 2.72/2.92          | (v2_struct_0 @ sk_A)
% 2.72/2.92          | ((k15_lattice3 @ sk_A @ sk_B_1) != (sk_C @ X0 @ sk_A)))),
% 2.72/2.92      inference('simplify', [status(thm)], ['183'])).
% 2.72/2.92  thf('185', plain,
% 2.72/2.92      (![X0 : $i]:
% 2.72/2.92         (((k15_lattice3 @ sk_A @ sk_B_1) != (k15_lattice3 @ sk_A @ X0))
% 2.72/2.92          | (v2_struct_0 @ sk_A)
% 2.72/2.92          | ~ (l3_lattices @ sk_A)
% 2.72/2.92          | ~ (v4_lattice3 @ sk_A)
% 2.72/2.92          | ~ (v10_lattices @ sk_A)
% 2.72/2.92          | (v2_struct_0 @ sk_A)
% 2.72/2.92          | (m1_subset_1 @ 
% 2.72/2.92             (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ X0 @ sk_A) @ 
% 2.72/2.92              sk_A) @ 
% 2.72/2.92             (u1_struct_0 @ sk_A))
% 2.72/2.92          | (m1_subset_1 @ 
% 2.72/2.92             (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ X0 @ sk_A) @ 
% 2.72/2.92              sk_A) @ 
% 2.72/2.92             (u1_struct_0 @ sk_A)))),
% 2.72/2.92      inference('sup-', [status(thm)], ['155', '184'])).
% 2.72/2.92  thf('186', plain, ((l3_lattices @ sk_A)),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('187', plain, ((v4_lattice3 @ sk_A)),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('188', plain, ((v10_lattices @ sk_A)),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('189', plain,
% 2.72/2.92      (![X0 : $i]:
% 2.72/2.92         (((k15_lattice3 @ sk_A @ sk_B_1) != (k15_lattice3 @ sk_A @ X0))
% 2.72/2.92          | (v2_struct_0 @ sk_A)
% 2.72/2.92          | (v2_struct_0 @ sk_A)
% 2.72/2.92          | (m1_subset_1 @ 
% 2.72/2.92             (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ X0 @ sk_A) @ 
% 2.72/2.92              sk_A) @ 
% 2.72/2.92             (u1_struct_0 @ sk_A))
% 2.72/2.92          | (m1_subset_1 @ 
% 2.72/2.92             (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ X0 @ sk_A) @ 
% 2.72/2.92              sk_A) @ 
% 2.72/2.92             (u1_struct_0 @ sk_A)))),
% 2.72/2.92      inference('demod', [status(thm)], ['185', '186', '187', '188'])).
% 2.72/2.92  thf('190', plain,
% 2.72/2.92      (![X0 : $i]:
% 2.72/2.92         ((m1_subset_1 @ 
% 2.72/2.92           (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ X0 @ sk_A) @ 
% 2.72/2.92            sk_A) @ 
% 2.72/2.92           (u1_struct_0 @ sk_A))
% 2.72/2.92          | (m1_subset_1 @ 
% 2.72/2.92             (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ X0 @ sk_A) @ 
% 2.72/2.92              sk_A) @ 
% 2.72/2.92             (u1_struct_0 @ sk_A))
% 2.72/2.92          | (v2_struct_0 @ sk_A)
% 2.72/2.92          | ((k15_lattice3 @ sk_A @ sk_B_1) != (k15_lattice3 @ sk_A @ X0)))),
% 2.72/2.92      inference('simplify', [status(thm)], ['189'])).
% 2.72/2.92  thf('191', plain,
% 2.72/2.92      (((v2_struct_0 @ sk_A)
% 2.72/2.92        | (m1_subset_1 @ 
% 2.72/2.92           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.92            sk_A) @ 
% 2.72/2.92           (u1_struct_0 @ sk_A))
% 2.72/2.92        | (m1_subset_1 @ 
% 2.72/2.92           (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.92            (sk_C @ sk_B_1 @ sk_A) @ sk_A) @ 
% 2.72/2.92           (u1_struct_0 @ sk_A)))),
% 2.72/2.92      inference('eq_res', [status(thm)], ['190'])).
% 2.72/2.92  thf('192', plain, (~ (v2_struct_0 @ sk_A)),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('193', plain,
% 2.72/2.92      (((m1_subset_1 @ 
% 2.72/2.92         (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.92          sk_A) @ 
% 2.72/2.92         (u1_struct_0 @ sk_A))
% 2.72/2.92        | (m1_subset_1 @ 
% 2.72/2.92           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.92            sk_A) @ 
% 2.72/2.92           (u1_struct_0 @ sk_A)))),
% 2.72/2.92      inference('clc', [status(thm)], ['191', '192'])).
% 2.72/2.92  thf('194', plain,
% 2.72/2.92      (((m1_subset_1 @ 
% 2.72/2.92         (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.92          (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.92         (u1_struct_0 @ sk_A))
% 2.72/2.92        | (v2_struct_0 @ sk_A)
% 2.72/2.92        | ~ (l3_lattices @ sk_A)
% 2.72/2.92        | ~ (v4_lattice3 @ sk_A)
% 2.72/2.92        | ~ (v10_lattices @ sk_A)
% 2.72/2.92        | (m1_subset_1 @ 
% 2.72/2.92           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.92            sk_A) @ 
% 2.72/2.92           (u1_struct_0 @ sk_A)))),
% 2.72/2.92      inference('sup+', [status(thm)], ['154', '193'])).
% 2.72/2.92  thf('195', plain, ((l3_lattices @ sk_A)),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('196', plain, ((v4_lattice3 @ sk_A)),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('197', plain, ((v10_lattices @ sk_A)),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('198', plain,
% 2.72/2.92      (((m1_subset_1 @ 
% 2.72/2.92         (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.92          (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.92         (u1_struct_0 @ sk_A))
% 2.72/2.92        | (v2_struct_0 @ sk_A)
% 2.72/2.92        | (m1_subset_1 @ 
% 2.72/2.92           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.92            sk_A) @ 
% 2.72/2.92           (u1_struct_0 @ sk_A)))),
% 2.72/2.92      inference('demod', [status(thm)], ['194', '195', '196', '197'])).
% 2.72/2.92  thf('199', plain, (~ (v2_struct_0 @ sk_A)),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('200', plain,
% 2.72/2.92      (((m1_subset_1 @ 
% 2.72/2.92         (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.92          sk_A) @ 
% 2.72/2.92         (u1_struct_0 @ sk_A))
% 2.72/2.92        | (m1_subset_1 @ 
% 2.72/2.93           (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (u1_struct_0 @ sk_A)))),
% 2.72/2.93      inference('clc', [status(thm)], ['198', '199'])).
% 2.72/2.93  thf('201', plain,
% 2.72/2.93      (((m1_subset_1 @ 
% 2.72/2.93         (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93          (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93         (u1_struct_0 @ sk_A))
% 2.72/2.93        | (v2_struct_0 @ sk_A)
% 2.72/2.93        | ~ (l3_lattices @ sk_A)
% 2.72/2.93        | ~ (v4_lattice3 @ sk_A)
% 2.72/2.93        | ~ (v10_lattices @ sk_A)
% 2.72/2.93        | (m1_subset_1 @ 
% 2.72/2.93           (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (u1_struct_0 @ sk_A)))),
% 2.72/2.93      inference('sup+', [status(thm)], ['153', '200'])).
% 2.72/2.93  thf('202', plain, ((l3_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('203', plain, ((v4_lattice3 @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('204', plain, ((v10_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('205', plain,
% 2.72/2.93      (((m1_subset_1 @ 
% 2.72/2.93         (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93          (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93         (u1_struct_0 @ sk_A))
% 2.72/2.93        | (v2_struct_0 @ sk_A)
% 2.72/2.93        | (m1_subset_1 @ 
% 2.72/2.93           (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (u1_struct_0 @ sk_A)))),
% 2.72/2.93      inference('demod', [status(thm)], ['201', '202', '203', '204'])).
% 2.72/2.93  thf('206', plain, (~ (v2_struct_0 @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('207', plain,
% 2.72/2.93      (((m1_subset_1 @ 
% 2.72/2.93         (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93          (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93         (u1_struct_0 @ sk_A))
% 2.72/2.93        | (m1_subset_1 @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (u1_struct_0 @ sk_A)))),
% 2.72/2.93      inference('clc', [status(thm)], ['205', '206'])).
% 2.72/2.93  thf('208', plain,
% 2.72/2.93      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 2.72/2.93         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 2.72/2.93          | ~ (r3_lattice3 @ X5 @ X4 @ X6)
% 2.72/2.93          | ~ (r2_hidden @ X7 @ X6)
% 2.72/2.93          | (r1_lattices @ X5 @ X4 @ X7)
% 2.72/2.93          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X5))
% 2.72/2.93          | ~ (l3_lattices @ X5)
% 2.72/2.93          | (v2_struct_0 @ X5))),
% 2.72/2.93      inference('cnf', [status(esa)], [d16_lattice3])).
% 2.72/2.93  thf('209', plain,
% 2.72/2.93      (![X0 : $i, X1 : $i]:
% 2.72/2.93         ((m1_subset_1 @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (u1_struct_0 @ sk_A))
% 2.72/2.93          | (v2_struct_0 @ sk_A)
% 2.72/2.93          | ~ (l3_lattices @ sk_A)
% 2.72/2.93          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.72/2.93          | (r1_lattices @ sk_A @ 
% 2.72/2.93             (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93              (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93             X0)
% 2.72/2.93          | ~ (r2_hidden @ X0 @ X1)
% 2.72/2.93          | ~ (r3_lattice3 @ sk_A @ 
% 2.72/2.93               (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93                (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93               X1))),
% 2.72/2.93      inference('sup-', [status(thm)], ['207', '208'])).
% 2.72/2.93  thf('210', plain, ((l3_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('211', plain,
% 2.72/2.93      (![X0 : $i, X1 : $i]:
% 2.72/2.93         ((m1_subset_1 @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (u1_struct_0 @ sk_A))
% 2.72/2.93          | (v2_struct_0 @ sk_A)
% 2.72/2.93          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.72/2.93          | (r1_lattices @ sk_A @ 
% 2.72/2.93             (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93              (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93             X0)
% 2.72/2.93          | ~ (r2_hidden @ X0 @ X1)
% 2.72/2.93          | ~ (r3_lattice3 @ sk_A @ 
% 2.72/2.93               (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93                (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93               X1))),
% 2.72/2.93      inference('demod', [status(thm)], ['209', '210'])).
% 2.72/2.93  thf('212', plain,
% 2.72/2.93      (![X0 : $i]:
% 2.72/2.93         ((r2_hidden @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93            sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93          | ~ (r2_hidden @ X0 @ (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93          | (r1_lattices @ sk_A @ 
% 2.72/2.93             (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93              (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93             X0)
% 2.72/2.93          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.72/2.93          | (v2_struct_0 @ sk_A)
% 2.72/2.93          | (m1_subset_1 @ 
% 2.72/2.93             (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93              (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93             (u1_struct_0 @ sk_A)))),
% 2.72/2.93      inference('sup-', [status(thm)], ['152', '211'])).
% 2.72/2.93  thf('213', plain,
% 2.72/2.93      (((v2_struct_0 @ sk_A)
% 2.72/2.93        | ~ (l3_lattices @ sk_A)
% 2.72/2.93        | ~ (v4_lattice3 @ sk_A)
% 2.72/2.93        | ~ (v10_lattices @ sk_A)
% 2.72/2.93        | (m1_subset_1 @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (u1_struct_0 @ sk_A))
% 2.72/2.93        | (v2_struct_0 @ sk_A)
% 2.72/2.93        | ~ (m1_subset_1 @ (k15_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93             (u1_struct_0 @ sk_A))
% 2.72/2.93        | (r1_lattices @ sk_A @ 
% 2.72/2.93           (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (k15_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | (r2_hidden @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93            sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.93      inference('sup-', [status(thm)], ['99', '212'])).
% 2.72/2.93  thf('214', plain, ((l3_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('215', plain, ((v4_lattice3 @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('216', plain, ((v10_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('217', plain,
% 2.72/2.93      (((v2_struct_0 @ sk_A)
% 2.72/2.93        | (m1_subset_1 @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (u1_struct_0 @ sk_A))
% 2.72/2.93        | (v2_struct_0 @ sk_A)
% 2.72/2.93        | ~ (m1_subset_1 @ (k15_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93             (u1_struct_0 @ sk_A))
% 2.72/2.93        | (r1_lattices @ sk_A @ 
% 2.72/2.93           (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (k15_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | (r2_hidden @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93            sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.93      inference('demod', [status(thm)], ['213', '214', '215', '216'])).
% 2.72/2.93  thf('218', plain,
% 2.72/2.93      (((r2_hidden @ 
% 2.72/2.93         (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93          sk_A) @ 
% 2.72/2.93         (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | (r1_lattices @ sk_A @ 
% 2.72/2.93           (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (k15_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | ~ (m1_subset_1 @ (k15_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93             (u1_struct_0 @ sk_A))
% 2.72/2.93        | (m1_subset_1 @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (u1_struct_0 @ sk_A))
% 2.72/2.93        | (v2_struct_0 @ sk_A))),
% 2.72/2.93      inference('simplify', [status(thm)], ['217'])).
% 2.72/2.93  thf('219', plain,
% 2.72/2.93      (((v2_struct_0 @ sk_A)
% 2.72/2.93        | ~ (l3_lattices @ sk_A)
% 2.72/2.93        | ~ (v4_lattice3 @ sk_A)
% 2.72/2.93        | ~ (v10_lattices @ sk_A)
% 2.72/2.93        | (v2_struct_0 @ sk_A)
% 2.72/2.93        | (m1_subset_1 @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (u1_struct_0 @ sk_A))
% 2.72/2.93        | (r1_lattices @ sk_A @ 
% 2.72/2.93           (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (k15_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | (r2_hidden @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93            sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.93      inference('sup-', [status(thm)], ['98', '218'])).
% 2.72/2.93  thf('220', plain, ((l3_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('221', plain, ((v4_lattice3 @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('222', plain, ((v10_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('223', plain,
% 2.72/2.93      (((v2_struct_0 @ sk_A)
% 2.72/2.93        | (v2_struct_0 @ sk_A)
% 2.72/2.93        | (m1_subset_1 @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (u1_struct_0 @ sk_A))
% 2.72/2.93        | (r1_lattices @ sk_A @ 
% 2.72/2.93           (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (k15_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | (r2_hidden @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93            sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.93      inference('demod', [status(thm)], ['219', '220', '221', '222'])).
% 2.72/2.93  thf('224', plain,
% 2.72/2.93      (((r2_hidden @ 
% 2.72/2.93         (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93          sk_A) @ 
% 2.72/2.93         (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | (r1_lattices @ sk_A @ 
% 2.72/2.93           (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (k15_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | (m1_subset_1 @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (u1_struct_0 @ sk_A))
% 2.72/2.93        | (v2_struct_0 @ sk_A))),
% 2.72/2.93      inference('simplify', [status(thm)], ['223'])).
% 2.72/2.93  thf('225', plain,
% 2.72/2.93      (((m1_subset_1 @ 
% 2.72/2.93         (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93          (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93         (u1_struct_0 @ sk_A))
% 2.72/2.93        | (m1_subset_1 @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (u1_struct_0 @ sk_A)))),
% 2.72/2.93      inference('clc', [status(thm)], ['205', '206'])).
% 2.72/2.93  thf(redefinition_r3_lattices, axiom,
% 2.72/2.93    (![A:$i,B:$i,C:$i]:
% 2.72/2.93     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 2.72/2.93         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 2.72/2.93         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 2.72/2.93         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 2.72/2.93       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 2.72/2.93  thf('226', plain,
% 2.72/2.93      (![X1 : $i, X2 : $i, X3 : $i]:
% 2.72/2.93         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 2.72/2.93          | ~ (l3_lattices @ X2)
% 2.72/2.93          | ~ (v9_lattices @ X2)
% 2.72/2.93          | ~ (v8_lattices @ X2)
% 2.72/2.93          | ~ (v6_lattices @ X2)
% 2.72/2.93          | (v2_struct_0 @ X2)
% 2.72/2.93          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 2.72/2.93          | (r3_lattices @ X2 @ X1 @ X3)
% 2.72/2.93          | ~ (r1_lattices @ X2 @ X1 @ X3))),
% 2.72/2.93      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 2.72/2.93  thf('227', plain,
% 2.72/2.93      (![X0 : $i]:
% 2.72/2.93         ((m1_subset_1 @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (u1_struct_0 @ sk_A))
% 2.72/2.93          | ~ (r1_lattices @ sk_A @ 
% 2.72/2.93               (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93                (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93               X0)
% 2.72/2.93          | (r3_lattices @ sk_A @ 
% 2.72/2.93             (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93              (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93             X0)
% 2.72/2.93          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.72/2.93          | (v2_struct_0 @ sk_A)
% 2.72/2.93          | ~ (v6_lattices @ sk_A)
% 2.72/2.93          | ~ (v8_lattices @ sk_A)
% 2.72/2.93          | ~ (v9_lattices @ sk_A)
% 2.72/2.93          | ~ (l3_lattices @ sk_A))),
% 2.72/2.93      inference('sup-', [status(thm)], ['225', '226'])).
% 2.72/2.93  thf(cc1_lattices, axiom,
% 2.72/2.93    (![A:$i]:
% 2.72/2.93     ( ( l3_lattices @ A ) =>
% 2.72/2.93       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 2.72/2.93         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 2.72/2.93           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 2.72/2.93           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 2.72/2.93  thf('228', plain,
% 2.72/2.93      (![X0 : $i]:
% 2.72/2.93         ((v2_struct_0 @ X0)
% 2.72/2.93          | ~ (v10_lattices @ X0)
% 2.72/2.93          | (v6_lattices @ X0)
% 2.72/2.93          | ~ (l3_lattices @ X0))),
% 2.72/2.93      inference('cnf', [status(esa)], [cc1_lattices])).
% 2.72/2.93  thf('229', plain, (~ (v2_struct_0 @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('230', plain,
% 2.72/2.93      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 2.72/2.93      inference('sup-', [status(thm)], ['228', '229'])).
% 2.72/2.93  thf('231', plain, ((l3_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('232', plain, ((v10_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('233', plain, ((v6_lattices @ sk_A)),
% 2.72/2.93      inference('demod', [status(thm)], ['230', '231', '232'])).
% 2.72/2.93  thf('234', plain,
% 2.72/2.93      (![X0 : $i]:
% 2.72/2.93         ((v2_struct_0 @ X0)
% 2.72/2.93          | ~ (v10_lattices @ X0)
% 2.72/2.93          | (v8_lattices @ X0)
% 2.72/2.93          | ~ (l3_lattices @ X0))),
% 2.72/2.93      inference('cnf', [status(esa)], [cc1_lattices])).
% 2.72/2.93  thf('235', plain, (~ (v2_struct_0 @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('236', plain,
% 2.72/2.93      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 2.72/2.93      inference('sup-', [status(thm)], ['234', '235'])).
% 2.72/2.93  thf('237', plain, ((l3_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('238', plain, ((v10_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('239', plain, ((v8_lattices @ sk_A)),
% 2.72/2.93      inference('demod', [status(thm)], ['236', '237', '238'])).
% 2.72/2.93  thf('240', plain,
% 2.72/2.93      (![X0 : $i]:
% 2.72/2.93         ((v2_struct_0 @ X0)
% 2.72/2.93          | ~ (v10_lattices @ X0)
% 2.72/2.93          | (v9_lattices @ X0)
% 2.72/2.93          | ~ (l3_lattices @ X0))),
% 2.72/2.93      inference('cnf', [status(esa)], [cc1_lattices])).
% 2.72/2.93  thf('241', plain, (~ (v2_struct_0 @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('242', plain,
% 2.72/2.93      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 2.72/2.93      inference('sup-', [status(thm)], ['240', '241'])).
% 2.72/2.93  thf('243', plain, ((l3_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('244', plain, ((v10_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('245', plain, ((v9_lattices @ sk_A)),
% 2.72/2.93      inference('demod', [status(thm)], ['242', '243', '244'])).
% 2.72/2.93  thf('246', plain, ((l3_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('247', plain,
% 2.72/2.93      (![X0 : $i]:
% 2.72/2.93         ((m1_subset_1 @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (u1_struct_0 @ sk_A))
% 2.72/2.93          | ~ (r1_lattices @ sk_A @ 
% 2.72/2.93               (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93                (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93               X0)
% 2.72/2.93          | (r3_lattices @ sk_A @ 
% 2.72/2.93             (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93              (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93             X0)
% 2.72/2.93          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.72/2.93          | (v2_struct_0 @ sk_A))),
% 2.72/2.93      inference('demod', [status(thm)], ['227', '233', '239', '245', '246'])).
% 2.72/2.93  thf('248', plain,
% 2.72/2.93      (((v2_struct_0 @ sk_A)
% 2.72/2.93        | (m1_subset_1 @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (u1_struct_0 @ sk_A))
% 2.72/2.93        | (r2_hidden @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93            sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | (v2_struct_0 @ sk_A)
% 2.72/2.93        | ~ (m1_subset_1 @ (k15_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93             (u1_struct_0 @ sk_A))
% 2.72/2.93        | (r3_lattices @ sk_A @ 
% 2.72/2.93           (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (k15_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | (m1_subset_1 @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (u1_struct_0 @ sk_A)))),
% 2.72/2.93      inference('sup-', [status(thm)], ['224', '247'])).
% 2.72/2.93  thf('249', plain,
% 2.72/2.93      (((r3_lattices @ sk_A @ 
% 2.72/2.93         (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93          (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93         (k15_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | ~ (m1_subset_1 @ (k15_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93             (u1_struct_0 @ sk_A))
% 2.72/2.93        | (r2_hidden @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93            sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | (m1_subset_1 @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (u1_struct_0 @ sk_A))
% 2.72/2.93        | (v2_struct_0 @ sk_A))),
% 2.72/2.93      inference('simplify', [status(thm)], ['248'])).
% 2.72/2.93  thf('250', plain,
% 2.72/2.93      (((v2_struct_0 @ sk_A)
% 2.72/2.93        | ~ (l3_lattices @ sk_A)
% 2.72/2.93        | ~ (v4_lattice3 @ sk_A)
% 2.72/2.93        | ~ (v10_lattices @ sk_A)
% 2.72/2.93        | (v2_struct_0 @ sk_A)
% 2.72/2.93        | (m1_subset_1 @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (u1_struct_0 @ sk_A))
% 2.72/2.93        | (r2_hidden @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93            sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | (r3_lattices @ sk_A @ 
% 2.72/2.93           (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (k15_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.93      inference('sup-', [status(thm)], ['97', '249'])).
% 2.72/2.93  thf('251', plain, ((l3_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('252', plain, ((v4_lattice3 @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('253', plain, ((v10_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('254', plain,
% 2.72/2.93      (((v2_struct_0 @ sk_A)
% 2.72/2.93        | (v2_struct_0 @ sk_A)
% 2.72/2.93        | (m1_subset_1 @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (u1_struct_0 @ sk_A))
% 2.72/2.93        | (r2_hidden @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93            sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | (r3_lattices @ sk_A @ 
% 2.72/2.93           (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (k15_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.93      inference('demod', [status(thm)], ['250', '251', '252', '253'])).
% 2.72/2.93  thf('255', plain,
% 2.72/2.93      (((r3_lattices @ sk_A @ 
% 2.72/2.93         (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93          (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93         (k15_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | (r2_hidden @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93            sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | (m1_subset_1 @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (u1_struct_0 @ sk_A))
% 2.72/2.93        | (v2_struct_0 @ sk_A))),
% 2.72/2.93      inference('simplify', [status(thm)], ['254'])).
% 2.72/2.93  thf('256', plain,
% 2.72/2.93      (![X0 : $i, X1 : $i]:
% 2.72/2.93         (~ (v10_lattices @ X1)
% 2.72/2.93          | ~ (v4_lattice3 @ X1)
% 2.72/2.93          | ~ (l3_lattices @ X1)
% 2.72/2.93          | (v2_struct_0 @ X1)
% 2.72/2.93          | (m1_subset_1 @ (k15_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1)))),
% 2.72/2.93      inference('simplify', [status(thm)], ['33'])).
% 2.72/2.93  thf('257', plain,
% 2.72/2.93      (![X21 : $i, X22 : $i, X25 : $i]:
% 2.72/2.93         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 2.72/2.93          | ~ (r3_lattice3 @ X22 @ X21 @ X25)
% 2.72/2.93          | ~ (r3_lattices @ X22 @ (sk_D_4 @ X25 @ X21 @ X22) @ X21)
% 2.72/2.93          | ((X21) = (k16_lattice3 @ X22 @ X25))
% 2.72/2.93          | ~ (l3_lattices @ X22)
% 2.72/2.93          | ~ (v4_lattice3 @ X22)
% 2.72/2.93          | ~ (v10_lattices @ X22)
% 2.72/2.93          | (v2_struct_0 @ X22))),
% 2.72/2.93      inference('cnf', [status(esa)], [t34_lattice3])).
% 2.72/2.93  thf('258', plain,
% 2.72/2.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.93         ((v2_struct_0 @ X0)
% 2.72/2.93          | ~ (l3_lattices @ X0)
% 2.72/2.93          | ~ (v4_lattice3 @ X0)
% 2.72/2.93          | ~ (v10_lattices @ X0)
% 2.72/2.93          | (v2_struct_0 @ X0)
% 2.72/2.93          | ~ (v10_lattices @ X0)
% 2.72/2.93          | ~ (v4_lattice3 @ X0)
% 2.72/2.93          | ~ (l3_lattices @ X0)
% 2.72/2.93          | ((k15_lattice3 @ X0 @ X1) = (k16_lattice3 @ X0 @ X2))
% 2.72/2.93          | ~ (r3_lattices @ X0 @ 
% 2.72/2.93               (sk_D_4 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 2.72/2.93               (k15_lattice3 @ X0 @ X1))
% 2.72/2.93          | ~ (r3_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))),
% 2.72/2.93      inference('sup-', [status(thm)], ['256', '257'])).
% 2.72/2.93  thf('259', plain,
% 2.72/2.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.93         (~ (r3_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.72/2.93          | ~ (r3_lattices @ X0 @ 
% 2.72/2.93               (sk_D_4 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 2.72/2.93               (k15_lattice3 @ X0 @ X1))
% 2.72/2.93          | ((k15_lattice3 @ X0 @ X1) = (k16_lattice3 @ X0 @ X2))
% 2.72/2.93          | ~ (v10_lattices @ X0)
% 2.72/2.93          | ~ (v4_lattice3 @ X0)
% 2.72/2.93          | ~ (l3_lattices @ X0)
% 2.72/2.93          | (v2_struct_0 @ X0))),
% 2.72/2.93      inference('simplify', [status(thm)], ['258'])).
% 2.72/2.93  thf('260', plain,
% 2.72/2.93      (((v2_struct_0 @ sk_A)
% 2.72/2.93        | (m1_subset_1 @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (u1_struct_0 @ sk_A))
% 2.72/2.93        | (r2_hidden @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93            sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | (v2_struct_0 @ sk_A)
% 2.72/2.93        | ~ (l3_lattices @ sk_A)
% 2.72/2.93        | ~ (v4_lattice3 @ sk_A)
% 2.72/2.93        | ~ (v10_lattices @ sk_A)
% 2.72/2.93        | ((k15_lattice3 @ sk_A @ sk_B_1)
% 2.72/2.93            = (k16_lattice3 @ sk_A @ (a_2_2_lattice3 @ sk_A @ sk_B_1)))
% 2.72/2.93        | ~ (r3_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93             (a_2_2_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.93      inference('sup-', [status(thm)], ['255', '259'])).
% 2.72/2.93  thf('261', plain, ((l3_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('262', plain, ((v4_lattice3 @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('263', plain, ((v10_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('264', plain,
% 2.72/2.93      (((v2_struct_0 @ sk_A)
% 2.72/2.93        | (m1_subset_1 @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (u1_struct_0 @ sk_A))
% 2.72/2.93        | (r2_hidden @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93            sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | (v2_struct_0 @ sk_A)
% 2.72/2.93        | ((k15_lattice3 @ sk_A @ sk_B_1)
% 2.72/2.93            = (k16_lattice3 @ sk_A @ (a_2_2_lattice3 @ sk_A @ sk_B_1)))
% 2.72/2.93        | ~ (r3_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93             (a_2_2_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.93      inference('demod', [status(thm)], ['260', '261', '262', '263'])).
% 2.72/2.93  thf('265', plain,
% 2.72/2.93      ((~ (r3_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | ((k15_lattice3 @ sk_A @ sk_B_1)
% 2.72/2.93            = (k16_lattice3 @ sk_A @ (a_2_2_lattice3 @ sk_A @ sk_B_1)))
% 2.72/2.93        | (r2_hidden @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93            sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | (m1_subset_1 @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (u1_struct_0 @ sk_A))
% 2.72/2.93        | (v2_struct_0 @ sk_A))),
% 2.72/2.93      inference('simplify', [status(thm)], ['264'])).
% 2.72/2.93  thf('266', plain,
% 2.72/2.93      (((k15_lattice3 @ sk_A @ sk_B_1)
% 2.72/2.93         != (k16_lattice3 @ sk_A @ (a_2_2_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('267', plain,
% 2.72/2.93      ((~ (r3_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | (r2_hidden @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93            sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | (m1_subset_1 @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (u1_struct_0 @ sk_A))
% 2.72/2.93        | (v2_struct_0 @ sk_A))),
% 2.72/2.93      inference('simplify_reflect-', [status(thm)], ['265', '266'])).
% 2.72/2.93  thf('268', plain,
% 2.72/2.93      (((v2_struct_0 @ sk_A)
% 2.72/2.93        | ~ (l3_lattices @ sk_A)
% 2.72/2.93        | ~ (v4_lattice3 @ sk_A)
% 2.72/2.93        | ~ (v10_lattices @ sk_A)
% 2.72/2.93        | (v2_struct_0 @ sk_A)
% 2.72/2.93        | (m1_subset_1 @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (u1_struct_0 @ sk_A))
% 2.72/2.93        | (r2_hidden @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93            sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.93      inference('sup-', [status(thm)], ['96', '267'])).
% 2.72/2.93  thf('269', plain, ((l3_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('270', plain, ((v4_lattice3 @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('271', plain, ((v10_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('272', plain,
% 2.72/2.93      (((v2_struct_0 @ sk_A)
% 2.72/2.93        | (v2_struct_0 @ sk_A)
% 2.72/2.93        | (m1_subset_1 @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (u1_struct_0 @ sk_A))
% 2.72/2.93        | (r2_hidden @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93            sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.93      inference('demod', [status(thm)], ['268', '269', '270', '271'])).
% 2.72/2.93  thf('273', plain,
% 2.72/2.93      (((r2_hidden @ 
% 2.72/2.93         (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93          sk_A) @ 
% 2.72/2.93         (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | (m1_subset_1 @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (u1_struct_0 @ sk_A))
% 2.72/2.93        | (v2_struct_0 @ sk_A))),
% 2.72/2.93      inference('simplify', [status(thm)], ['272'])).
% 2.72/2.93  thf('274', plain, (~ (v2_struct_0 @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('275', plain,
% 2.72/2.93      (((m1_subset_1 @ 
% 2.72/2.93         (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93          (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93         (u1_struct_0 @ sk_A))
% 2.72/2.93        | (r2_hidden @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93            sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.93      inference('clc', [status(thm)], ['273', '274'])).
% 2.72/2.93  thf('276', plain,
% 2.72/2.93      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.72/2.93         (~ (l3_lattices @ X17)
% 2.72/2.93          | ~ (v4_lattice3 @ X17)
% 2.72/2.93          | ~ (v10_lattices @ X17)
% 2.72/2.93          | (v2_struct_0 @ X17)
% 2.72/2.93          | (m1_subset_1 @ (sk_D_3 @ X18 @ X17 @ X19) @ (u1_struct_0 @ X17))
% 2.72/2.93          | ~ (r2_hidden @ X19 @ (a_2_2_lattice3 @ X17 @ X18)))),
% 2.72/2.93      inference('cnf', [status(esa)], [fraenkel_a_2_2_lattice3])).
% 2.72/2.93  thf('277', plain,
% 2.72/2.93      (((m1_subset_1 @ 
% 2.72/2.93         (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93          (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93         (u1_struct_0 @ sk_A))
% 2.72/2.93        | (m1_subset_1 @ 
% 2.72/2.93           (sk_D_3 @ sk_B_1 @ sk_A @ 
% 2.72/2.93            (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93             (sk_C @ sk_B_1 @ sk_A) @ sk_A)) @ 
% 2.72/2.93           (u1_struct_0 @ sk_A))
% 2.72/2.93        | (v2_struct_0 @ sk_A)
% 2.72/2.93        | ~ (v10_lattices @ sk_A)
% 2.72/2.93        | ~ (v4_lattice3 @ sk_A)
% 2.72/2.93        | ~ (l3_lattices @ sk_A))),
% 2.72/2.93      inference('sup-', [status(thm)], ['275', '276'])).
% 2.72/2.93  thf('278', plain, ((v10_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('279', plain, ((v4_lattice3 @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('280', plain, ((l3_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('281', plain,
% 2.72/2.93      (((m1_subset_1 @ 
% 2.72/2.93         (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93          (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93         (u1_struct_0 @ sk_A))
% 2.72/2.93        | (m1_subset_1 @ 
% 2.72/2.93           (sk_D_3 @ sk_B_1 @ sk_A @ 
% 2.72/2.93            (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93             (sk_C @ sk_B_1 @ sk_A) @ sk_A)) @ 
% 2.72/2.93           (u1_struct_0 @ sk_A))
% 2.72/2.93        | (v2_struct_0 @ sk_A))),
% 2.72/2.93      inference('demod', [status(thm)], ['277', '278', '279', '280'])).
% 2.72/2.93  thf('282', plain, (~ (v2_struct_0 @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('283', plain,
% 2.72/2.93      (((m1_subset_1 @ 
% 2.72/2.93         (sk_D_3 @ sk_B_1 @ sk_A @ 
% 2.72/2.93          (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93           sk_A)) @ 
% 2.72/2.93         (u1_struct_0 @ sk_A))
% 2.72/2.93        | (m1_subset_1 @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (u1_struct_0 @ sk_A)))),
% 2.72/2.93      inference('clc', [status(thm)], ['281', '282'])).
% 2.72/2.93  thf('284', plain,
% 2.72/2.93      (((m1_subset_1 @ 
% 2.72/2.93         (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93          sk_A) @ 
% 2.72/2.93         (u1_struct_0 @ sk_A))
% 2.72/2.93        | ~ (l3_lattices @ sk_A)
% 2.72/2.93        | ~ (v4_lattice3 @ sk_A)
% 2.72/2.93        | ~ (v10_lattices @ sk_A)
% 2.72/2.93        | (v2_struct_0 @ sk_A)
% 2.72/2.93        | (r3_lattice3 @ sk_A @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | ~ (v4_lattice3 @ sk_A)
% 2.72/2.93        | ~ (l3_lattices @ sk_A)
% 2.72/2.93        | (v2_struct_0 @ sk_A)
% 2.72/2.93        | (m1_subset_1 @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (u1_struct_0 @ sk_A)))),
% 2.72/2.93      inference('sup+', [status(thm)], ['70', '283'])).
% 2.72/2.93  thf('285', plain, ((l3_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('286', plain, ((v4_lattice3 @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('287', plain, ((v10_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('288', plain, ((v4_lattice3 @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('289', plain, ((l3_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('290', plain,
% 2.72/2.93      (((m1_subset_1 @ 
% 2.72/2.93         (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93          sk_A) @ 
% 2.72/2.93         (u1_struct_0 @ sk_A))
% 2.72/2.93        | (v2_struct_0 @ sk_A)
% 2.72/2.93        | (r3_lattice3 @ sk_A @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | (v2_struct_0 @ sk_A)
% 2.72/2.93        | (m1_subset_1 @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (u1_struct_0 @ sk_A)))),
% 2.72/2.93      inference('demod', [status(thm)],
% 2.72/2.93                ['284', '285', '286', '287', '288', '289'])).
% 2.72/2.93  thf('291', plain,
% 2.72/2.93      (((m1_subset_1 @ 
% 2.72/2.93         (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93          (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93         (u1_struct_0 @ sk_A))
% 2.72/2.93        | (r3_lattice3 @ sk_A @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | (v2_struct_0 @ sk_A)
% 2.72/2.93        | (m1_subset_1 @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93            sk_A) @ 
% 2.72/2.93           (u1_struct_0 @ sk_A)))),
% 2.72/2.93      inference('simplify', [status(thm)], ['290'])).
% 2.72/2.93  thf('292', plain,
% 2.72/2.93      (((m1_subset_1 @ 
% 2.72/2.93         (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93          (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93         (u1_struct_0 @ sk_A))
% 2.72/2.93        | (v2_struct_0 @ sk_A)
% 2.72/2.93        | ~ (l3_lattices @ sk_A)
% 2.72/2.93        | ~ (v4_lattice3 @ sk_A)
% 2.72/2.93        | ~ (v10_lattices @ sk_A)
% 2.72/2.93        | (v2_struct_0 @ sk_A)
% 2.72/2.93        | (r3_lattice3 @ sk_A @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | (m1_subset_1 @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (u1_struct_0 @ sk_A)))),
% 2.72/2.93      inference('sup+', [status(thm)], ['69', '291'])).
% 2.72/2.93  thf('293', plain, ((l3_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('294', plain, ((v4_lattice3 @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('295', plain, ((v10_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('296', plain,
% 2.72/2.93      (((m1_subset_1 @ 
% 2.72/2.93         (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93          (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93         (u1_struct_0 @ sk_A))
% 2.72/2.93        | (v2_struct_0 @ sk_A)
% 2.72/2.93        | (v2_struct_0 @ sk_A)
% 2.72/2.93        | (r3_lattice3 @ sk_A @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | (m1_subset_1 @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (u1_struct_0 @ sk_A)))),
% 2.72/2.93      inference('demod', [status(thm)], ['292', '293', '294', '295'])).
% 2.72/2.93  thf('297', plain,
% 2.72/2.93      (((r3_lattice3 @ sk_A @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93         (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | (v2_struct_0 @ sk_A)
% 2.72/2.93        | (m1_subset_1 @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (u1_struct_0 @ sk_A)))),
% 2.72/2.93      inference('simplify', [status(thm)], ['296'])).
% 2.72/2.93  thf('298', plain, (~ (v2_struct_0 @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('299', plain,
% 2.72/2.93      (((m1_subset_1 @ 
% 2.72/2.93         (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93          (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93         (u1_struct_0 @ sk_A))
% 2.72/2.93        | (r3_lattice3 @ sk_A @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.93      inference('clc', [status(thm)], ['297', '298'])).
% 2.72/2.93  thf('300', plain,
% 2.72/2.93      (![X17 : $i, X18 : $i, X20 : $i]:
% 2.72/2.93         (~ (r4_lattice3 @ X17 @ X20 @ X18)
% 2.72/2.93          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X17))
% 2.72/2.93          | (r2_hidden @ X20 @ (a_2_2_lattice3 @ X17 @ X18))
% 2.72/2.93          | (v2_struct_0 @ X17)
% 2.72/2.93          | ~ (v10_lattices @ X17)
% 2.72/2.93          | ~ (v4_lattice3 @ X17)
% 2.72/2.93          | ~ (l3_lattices @ X17))),
% 2.72/2.93      inference('simplify', [status(thm)], ['39'])).
% 2.72/2.93  thf('301', plain,
% 2.72/2.93      (![X0 : $i]:
% 2.72/2.93         ((r3_lattice3 @ sk_A @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93          | ~ (l3_lattices @ sk_A)
% 2.72/2.93          | ~ (v4_lattice3 @ sk_A)
% 2.72/2.93          | ~ (v10_lattices @ sk_A)
% 2.72/2.93          | (v2_struct_0 @ sk_A)
% 2.72/2.93          | (r2_hidden @ 
% 2.72/2.93             (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93              (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93             (a_2_2_lattice3 @ sk_A @ X0))
% 2.72/2.93          | ~ (r4_lattice3 @ sk_A @ 
% 2.72/2.93               (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93                (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93               X0))),
% 2.72/2.93      inference('sup-', [status(thm)], ['299', '300'])).
% 2.72/2.93  thf('302', plain, ((l3_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('303', plain, ((v4_lattice3 @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('304', plain, ((v10_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('305', plain,
% 2.72/2.93      (![X0 : $i]:
% 2.72/2.93         ((r3_lattice3 @ sk_A @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93          | (v2_struct_0 @ sk_A)
% 2.72/2.93          | (r2_hidden @ 
% 2.72/2.93             (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93              (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93             (a_2_2_lattice3 @ sk_A @ X0))
% 2.72/2.93          | ~ (r4_lattice3 @ sk_A @ 
% 2.72/2.93               (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93                (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93               X0))),
% 2.72/2.93      inference('demod', [status(thm)], ['301', '302', '303', '304'])).
% 2.72/2.93  thf('306', plain,
% 2.72/2.93      (((v2_struct_0 @ sk_A)
% 2.72/2.93        | ~ (l3_lattices @ sk_A)
% 2.72/2.93        | ~ (v4_lattice3 @ sk_A)
% 2.72/2.93        | ~ (v10_lattices @ sk_A)
% 2.72/2.93        | ~ (l3_lattices @ sk_A)
% 2.72/2.93        | ~ (v4_lattice3 @ sk_A)
% 2.72/2.93        | ~ (v10_lattices @ sk_A)
% 2.72/2.93        | (v2_struct_0 @ sk_A)
% 2.72/2.93        | (r3_lattice3 @ sk_A @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | (r2_hidden @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | (v2_struct_0 @ sk_A)
% 2.72/2.93        | (r3_lattice3 @ sk_A @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.93      inference('sup-', [status(thm)], ['68', '305'])).
% 2.72/2.93  thf('307', plain, ((l3_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('308', plain, ((v4_lattice3 @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('309', plain, ((v10_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('310', plain, ((l3_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('311', plain, ((v4_lattice3 @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('312', plain, ((v10_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('313', plain,
% 2.72/2.93      (((v2_struct_0 @ sk_A)
% 2.72/2.93        | (v2_struct_0 @ sk_A)
% 2.72/2.93        | (r3_lattice3 @ sk_A @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | (r2_hidden @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | (v2_struct_0 @ sk_A)
% 2.72/2.93        | (r3_lattice3 @ sk_A @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.93      inference('demod', [status(thm)],
% 2.72/2.93                ['306', '307', '308', '309', '310', '311', '312'])).
% 2.72/2.93  thf('314', plain,
% 2.72/2.93      (((r2_hidden @ 
% 2.72/2.93         (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93          (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93         (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | (r3_lattice3 @ sk_A @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | (v2_struct_0 @ sk_A))),
% 2.72/2.93      inference('simplify', [status(thm)], ['313'])).
% 2.72/2.93  thf('315', plain, (~ (v2_struct_0 @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('316', plain,
% 2.72/2.93      (((r3_lattice3 @ sk_A @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93         (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | (r2_hidden @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.93      inference('clc', [status(thm)], ['314', '315'])).
% 2.72/2.93  thf('317', plain,
% 2.72/2.93      (![X0 : $i, X1 : $i]:
% 2.72/2.93         (~ (v10_lattices @ X1)
% 2.72/2.93          | ~ (v4_lattice3 @ X1)
% 2.72/2.93          | ~ (l3_lattices @ X1)
% 2.72/2.93          | (v2_struct_0 @ X1)
% 2.72/2.93          | (r3_lattice3 @ X1 @ (k15_lattice3 @ X1 @ X0) @ 
% 2.72/2.93             (a_2_2_lattice3 @ X1 @ X0)))),
% 2.72/2.93      inference('simplify', [status(thm)], ['95'])).
% 2.72/2.93  thf('318', plain,
% 2.72/2.93      (![X0 : $i, X1 : $i]:
% 2.72/2.93         (~ (v10_lattices @ X1)
% 2.72/2.93          | ~ (v4_lattice3 @ X1)
% 2.72/2.93          | ~ (l3_lattices @ X1)
% 2.72/2.93          | (v2_struct_0 @ X1)
% 2.72/2.93          | (m1_subset_1 @ (k15_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1)))),
% 2.72/2.93      inference('simplify', [status(thm)], ['33'])).
% 2.72/2.93  thf('319', plain,
% 2.72/2.93      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 2.72/2.93         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 2.72/2.93          | ~ (r3_lattice3 @ X5 @ X4 @ X6)
% 2.72/2.93          | ~ (r2_hidden @ X7 @ X6)
% 2.72/2.93          | (r1_lattices @ X5 @ X4 @ X7)
% 2.72/2.93          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X5))
% 2.72/2.93          | ~ (l3_lattices @ X5)
% 2.72/2.93          | (v2_struct_0 @ X5))),
% 2.72/2.93      inference('cnf', [status(esa)], [d16_lattice3])).
% 2.72/2.93  thf('320', plain,
% 2.72/2.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.72/2.93         ((v2_struct_0 @ X0)
% 2.72/2.93          | ~ (l3_lattices @ X0)
% 2.72/2.93          | ~ (v4_lattice3 @ X0)
% 2.72/2.93          | ~ (v10_lattices @ X0)
% 2.72/2.93          | (v2_struct_0 @ X0)
% 2.72/2.93          | ~ (l3_lattices @ X0)
% 2.72/2.93          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.72/2.93          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.72/2.93          | ~ (r2_hidden @ X2 @ X3)
% 2.72/2.93          | ~ (r3_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X3))),
% 2.72/2.93      inference('sup-', [status(thm)], ['318', '319'])).
% 2.72/2.93  thf('321', plain,
% 2.72/2.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.72/2.93         (~ (r3_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X3)
% 2.72/2.93          | ~ (r2_hidden @ X2 @ X3)
% 2.72/2.93          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.72/2.93          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.72/2.93          | ~ (v10_lattices @ X0)
% 2.72/2.93          | ~ (v4_lattice3 @ X0)
% 2.72/2.93          | ~ (l3_lattices @ X0)
% 2.72/2.93          | (v2_struct_0 @ X0))),
% 2.72/2.93      inference('simplify', [status(thm)], ['320'])).
% 2.72/2.93  thf('322', plain,
% 2.72/2.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.93         ((v2_struct_0 @ X1)
% 2.72/2.93          | ~ (l3_lattices @ X1)
% 2.72/2.93          | ~ (v4_lattice3 @ X1)
% 2.72/2.93          | ~ (v10_lattices @ X1)
% 2.72/2.93          | (v2_struct_0 @ X1)
% 2.72/2.93          | ~ (l3_lattices @ X1)
% 2.72/2.93          | ~ (v4_lattice3 @ X1)
% 2.72/2.93          | ~ (v10_lattices @ X1)
% 2.72/2.93          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 2.72/2.93          | (r1_lattices @ X1 @ (k15_lattice3 @ X1 @ X0) @ X2)
% 2.72/2.93          | ~ (r2_hidden @ X2 @ (a_2_2_lattice3 @ X1 @ X0)))),
% 2.72/2.93      inference('sup-', [status(thm)], ['317', '321'])).
% 2.72/2.93  thf('323', plain,
% 2.72/2.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.93         (~ (r2_hidden @ X2 @ (a_2_2_lattice3 @ X1 @ X0))
% 2.72/2.93          | (r1_lattices @ X1 @ (k15_lattice3 @ X1 @ X0) @ X2)
% 2.72/2.93          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 2.72/2.93          | ~ (v10_lattices @ X1)
% 2.72/2.93          | ~ (v4_lattice3 @ X1)
% 2.72/2.93          | ~ (l3_lattices @ X1)
% 2.72/2.93          | (v2_struct_0 @ X1))),
% 2.72/2.93      inference('simplify', [status(thm)], ['322'])).
% 2.72/2.93  thf('324', plain,
% 2.72/2.93      (((r3_lattice3 @ sk_A @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93         (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | (v2_struct_0 @ sk_A)
% 2.72/2.93        | ~ (l3_lattices @ sk_A)
% 2.72/2.93        | ~ (v4_lattice3 @ sk_A)
% 2.72/2.93        | ~ (v10_lattices @ sk_A)
% 2.72/2.93        | ~ (m1_subset_1 @ 
% 2.72/2.93             (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93              (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93             (u1_struct_0 @ sk_A))
% 2.72/2.93        | (r1_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A)))),
% 2.72/2.93      inference('sup-', [status(thm)], ['316', '323'])).
% 2.72/2.93  thf('325', plain, ((l3_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('326', plain, ((v4_lattice3 @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('327', plain, ((v10_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('328', plain,
% 2.72/2.93      (((r3_lattice3 @ sk_A @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93         (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | (v2_struct_0 @ sk_A)
% 2.72/2.93        | ~ (m1_subset_1 @ 
% 2.72/2.93             (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93              (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93             (u1_struct_0 @ sk_A))
% 2.72/2.93        | (r1_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A)))),
% 2.72/2.93      inference('demod', [status(thm)], ['324', '325', '326', '327'])).
% 2.72/2.93  thf('329', plain,
% 2.72/2.93      (((v2_struct_0 @ sk_A)
% 2.72/2.93        | ~ (l3_lattices @ sk_A)
% 2.72/2.93        | ~ (v4_lattice3 @ sk_A)
% 2.72/2.93        | ~ (v10_lattices @ sk_A)
% 2.72/2.93        | (r3_lattice3 @ sk_A @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | (r1_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A))
% 2.72/2.93        | (v2_struct_0 @ sk_A)
% 2.72/2.93        | (r3_lattice3 @ sk_A @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.93      inference('sup-', [status(thm)], ['54', '328'])).
% 2.72/2.93  thf('330', plain, ((l3_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('331', plain, ((v4_lattice3 @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('332', plain, ((v10_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('333', plain,
% 2.72/2.93      (((v2_struct_0 @ sk_A)
% 2.72/2.93        | (r3_lattice3 @ sk_A @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | (r1_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A))
% 2.72/2.93        | (v2_struct_0 @ sk_A)
% 2.72/2.93        | (r3_lattice3 @ sk_A @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.93      inference('demod', [status(thm)], ['329', '330', '331', '332'])).
% 2.72/2.93  thf('334', plain,
% 2.72/2.93      (((r1_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93         (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93          (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A))
% 2.72/2.93        | (r3_lattice3 @ sk_A @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | (v2_struct_0 @ sk_A))),
% 2.72/2.93      inference('simplify', [status(thm)], ['333'])).
% 2.72/2.93  thf('335', plain, (~ (v2_struct_0 @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('336', plain,
% 2.72/2.93      (((r3_lattice3 @ sk_A @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93         (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | (r1_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93           (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A)))),
% 2.72/2.93      inference('clc', [status(thm)], ['334', '335'])).
% 2.72/2.93  thf('337', plain,
% 2.72/2.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.93         ((r3_lattice3 @ X1 @ (sk_C @ X0 @ X1) @ X2)
% 2.72/2.93          | ~ (v10_lattices @ X1)
% 2.72/2.93          | ~ (v4_lattice3 @ X1)
% 2.72/2.93          | ~ (l3_lattices @ X1)
% 2.72/2.93          | (v2_struct_0 @ X1)
% 2.72/2.93          | ~ (r1_lattices @ X1 @ (k15_lattice3 @ X1 @ X0) @ 
% 2.72/2.93               (sk_D @ X2 @ (k15_lattice3 @ X1 @ X0) @ X1)))),
% 2.72/2.93      inference('simplify', [status(thm)], ['91'])).
% 2.72/2.93  thf('338', plain,
% 2.72/2.93      (((r3_lattice3 @ sk_A @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93         (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | (v2_struct_0 @ sk_A)
% 2.72/2.93        | ~ (l3_lattices @ sk_A)
% 2.72/2.93        | ~ (v4_lattice3 @ sk_A)
% 2.72/2.93        | ~ (v10_lattices @ sk_A)
% 2.72/2.93        | (r3_lattice3 @ sk_A @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.93      inference('sup-', [status(thm)], ['336', '337'])).
% 2.72/2.93  thf('339', plain, ((l3_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('340', plain, ((v4_lattice3 @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('341', plain, ((v10_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('342', plain,
% 2.72/2.93      (((r3_lattice3 @ sk_A @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93         (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | (v2_struct_0 @ sk_A)
% 2.72/2.93        | (r3_lattice3 @ sk_A @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.93      inference('demod', [status(thm)], ['338', '339', '340', '341'])).
% 2.72/2.93  thf('343', plain,
% 2.72/2.93      (((v2_struct_0 @ sk_A)
% 2.72/2.93        | (r3_lattice3 @ sk_A @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.93      inference('simplify', [status(thm)], ['342'])).
% 2.72/2.93  thf('344', plain, (~ (v2_struct_0 @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('345', plain,
% 2.72/2.93      ((r3_lattice3 @ sk_A @ (sk_C @ sk_B_1 @ sk_A) @ 
% 2.72/2.93        (a_2_2_lattice3 @ sk_A @ sk_B_1))),
% 2.72/2.93      inference('clc', [status(thm)], ['343', '344'])).
% 2.72/2.93  thf('346', plain,
% 2.72/2.93      (((r3_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93         (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | (v2_struct_0 @ sk_A)
% 2.72/2.93        | ~ (l3_lattices @ sk_A)
% 2.72/2.93        | ~ (v4_lattice3 @ sk_A)
% 2.72/2.93        | ~ (v10_lattices @ sk_A))),
% 2.72/2.93      inference('sup+', [status(thm)], ['47', '345'])).
% 2.72/2.93  thf('347', plain, ((l3_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('348', plain, ((v4_lattice3 @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('349', plain, ((v10_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('350', plain,
% 2.72/2.93      (((r3_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93         (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | (v2_struct_0 @ sk_A))),
% 2.72/2.93      inference('demod', [status(thm)], ['346', '347', '348', '349'])).
% 2.72/2.93  thf('351', plain, (~ (v2_struct_0 @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('352', plain,
% 2.72/2.93      ((r3_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93        (a_2_2_lattice3 @ sk_A @ sk_B_1))),
% 2.72/2.93      inference('clc', [status(thm)], ['350', '351'])).
% 2.72/2.93  thf('353', plain,
% 2.72/2.93      (![X0 : $i, X1 : $i]:
% 2.72/2.93         (~ (v10_lattices @ X1)
% 2.72/2.93          | ~ (v4_lattice3 @ X1)
% 2.72/2.93          | ~ (l3_lattices @ X1)
% 2.72/2.93          | (v2_struct_0 @ X1)
% 2.72/2.93          | (m1_subset_1 @ (k15_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1)))),
% 2.72/2.93      inference('simplify', [status(thm)], ['33'])).
% 2.72/2.93  thf('354', plain,
% 2.72/2.93      (![X21 : $i, X22 : $i, X25 : $i]:
% 2.72/2.93         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 2.72/2.93          | ~ (r3_lattice3 @ X22 @ X21 @ X25)
% 2.72/2.93          | (r3_lattice3 @ X22 @ (sk_D_4 @ X25 @ X21 @ X22) @ X25)
% 2.72/2.93          | ((X21) = (k16_lattice3 @ X22 @ X25))
% 2.72/2.93          | ~ (l3_lattices @ X22)
% 2.72/2.93          | ~ (v4_lattice3 @ X22)
% 2.72/2.93          | ~ (v10_lattices @ X22)
% 2.72/2.93          | (v2_struct_0 @ X22))),
% 2.72/2.93      inference('cnf', [status(esa)], [t34_lattice3])).
% 2.72/2.93  thf('355', plain,
% 2.72/2.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.93         ((v2_struct_0 @ X0)
% 2.72/2.93          | ~ (l3_lattices @ X0)
% 2.72/2.93          | ~ (v4_lattice3 @ X0)
% 2.72/2.93          | ~ (v10_lattices @ X0)
% 2.72/2.93          | (v2_struct_0 @ X0)
% 2.72/2.93          | ~ (v10_lattices @ X0)
% 2.72/2.93          | ~ (v4_lattice3 @ X0)
% 2.72/2.93          | ~ (l3_lattices @ X0)
% 2.72/2.93          | ((k15_lattice3 @ X0 @ X1) = (k16_lattice3 @ X0 @ X2))
% 2.72/2.93          | (r3_lattice3 @ X0 @ 
% 2.72/2.93             (sk_D_4 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X2)
% 2.72/2.93          | ~ (r3_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))),
% 2.72/2.93      inference('sup-', [status(thm)], ['353', '354'])).
% 2.72/2.93  thf('356', plain,
% 2.72/2.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.93         (~ (r3_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.72/2.93          | (r3_lattice3 @ X0 @ 
% 2.72/2.93             (sk_D_4 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X2)
% 2.72/2.93          | ((k15_lattice3 @ X0 @ X1) = (k16_lattice3 @ X0 @ X2))
% 2.72/2.93          | ~ (v10_lattices @ X0)
% 2.72/2.93          | ~ (v4_lattice3 @ X0)
% 2.72/2.93          | ~ (l3_lattices @ X0)
% 2.72/2.93          | (v2_struct_0 @ X0))),
% 2.72/2.93      inference('simplify', [status(thm)], ['355'])).
% 2.72/2.93  thf('357', plain,
% 2.72/2.93      (((v2_struct_0 @ sk_A)
% 2.72/2.93        | ~ (l3_lattices @ sk_A)
% 2.72/2.93        | ~ (v4_lattice3 @ sk_A)
% 2.72/2.93        | ~ (v10_lattices @ sk_A)
% 2.72/2.93        | ((k15_lattice3 @ sk_A @ sk_B_1)
% 2.72/2.93            = (k16_lattice3 @ sk_A @ (a_2_2_lattice3 @ sk_A @ sk_B_1)))
% 2.72/2.93        | (r3_lattice3 @ sk_A @ 
% 2.72/2.93           (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.93      inference('sup-', [status(thm)], ['352', '356'])).
% 2.72/2.93  thf('358', plain, ((l3_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('359', plain, ((v4_lattice3 @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('360', plain, ((v10_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('361', plain,
% 2.72/2.93      (((v2_struct_0 @ sk_A)
% 2.72/2.93        | ((k15_lattice3 @ sk_A @ sk_B_1)
% 2.72/2.93            = (k16_lattice3 @ sk_A @ (a_2_2_lattice3 @ sk_A @ sk_B_1)))
% 2.72/2.93        | (r3_lattice3 @ sk_A @ 
% 2.72/2.93           (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.93      inference('demod', [status(thm)], ['357', '358', '359', '360'])).
% 2.72/2.93  thf('362', plain,
% 2.72/2.93      (((k15_lattice3 @ sk_A @ sk_B_1)
% 2.72/2.93         != (k16_lattice3 @ sk_A @ (a_2_2_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('363', plain,
% 2.72/2.93      (((v2_struct_0 @ sk_A)
% 2.72/2.93        | (r3_lattice3 @ sk_A @ 
% 2.72/2.93           (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (a_2_2_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.93      inference('simplify_reflect-', [status(thm)], ['361', '362'])).
% 2.72/2.93  thf('364', plain, (~ (v2_struct_0 @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('365', plain,
% 2.72/2.93      ((r3_lattice3 @ sk_A @ 
% 2.72/2.93        (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93         (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93        (a_2_2_lattice3 @ sk_A @ sk_B_1))),
% 2.72/2.93      inference('clc', [status(thm)], ['363', '364'])).
% 2.72/2.93  thf('366', plain,
% 2.72/2.93      ((r3_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93        (a_2_2_lattice3 @ sk_A @ sk_B_1))),
% 2.72/2.93      inference('clc', [status(thm)], ['350', '351'])).
% 2.72/2.93  thf('367', plain,
% 2.72/2.93      (![X0 : $i, X1 : $i]:
% 2.72/2.93         (~ (v10_lattices @ X1)
% 2.72/2.93          | ~ (v4_lattice3 @ X1)
% 2.72/2.93          | ~ (l3_lattices @ X1)
% 2.72/2.93          | (v2_struct_0 @ X1)
% 2.72/2.93          | (m1_subset_1 @ (k15_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1)))),
% 2.72/2.93      inference('simplify', [status(thm)], ['33'])).
% 2.72/2.93  thf('368', plain,
% 2.72/2.93      (![X21 : $i, X22 : $i, X25 : $i]:
% 2.72/2.93         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 2.72/2.93          | ~ (r3_lattice3 @ X22 @ X21 @ X25)
% 2.72/2.93          | (m1_subset_1 @ (sk_D_4 @ X25 @ X21 @ X22) @ (u1_struct_0 @ X22))
% 2.72/2.93          | ((X21) = (k16_lattice3 @ X22 @ X25))
% 2.72/2.93          | ~ (l3_lattices @ X22)
% 2.72/2.93          | ~ (v4_lattice3 @ X22)
% 2.72/2.93          | ~ (v10_lattices @ X22)
% 2.72/2.93          | (v2_struct_0 @ X22))),
% 2.72/2.93      inference('cnf', [status(esa)], [t34_lattice3])).
% 2.72/2.93  thf('369', plain,
% 2.72/2.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.93         ((v2_struct_0 @ X0)
% 2.72/2.93          | ~ (l3_lattices @ X0)
% 2.72/2.93          | ~ (v4_lattice3 @ X0)
% 2.72/2.93          | ~ (v10_lattices @ X0)
% 2.72/2.93          | (v2_struct_0 @ X0)
% 2.72/2.93          | ~ (v10_lattices @ X0)
% 2.72/2.93          | ~ (v4_lattice3 @ X0)
% 2.72/2.93          | ~ (l3_lattices @ X0)
% 2.72/2.93          | ((k15_lattice3 @ X0 @ X1) = (k16_lattice3 @ X0 @ X2))
% 2.72/2.93          | (m1_subset_1 @ (sk_D_4 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 2.72/2.93             (u1_struct_0 @ X0))
% 2.72/2.93          | ~ (r3_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))),
% 2.72/2.93      inference('sup-', [status(thm)], ['367', '368'])).
% 2.72/2.93  thf('370', plain,
% 2.72/2.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.93         (~ (r3_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.72/2.93          | (m1_subset_1 @ (sk_D_4 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 2.72/2.93             (u1_struct_0 @ X0))
% 2.72/2.93          | ((k15_lattice3 @ X0 @ X1) = (k16_lattice3 @ X0 @ X2))
% 2.72/2.93          | ~ (v10_lattices @ X0)
% 2.72/2.93          | ~ (v4_lattice3 @ X0)
% 2.72/2.93          | ~ (l3_lattices @ X0)
% 2.72/2.93          | (v2_struct_0 @ X0))),
% 2.72/2.93      inference('simplify', [status(thm)], ['369'])).
% 2.72/2.93  thf('371', plain,
% 2.72/2.93      (((v2_struct_0 @ sk_A)
% 2.72/2.93        | ~ (l3_lattices @ sk_A)
% 2.72/2.93        | ~ (v4_lattice3 @ sk_A)
% 2.72/2.93        | ~ (v10_lattices @ sk_A)
% 2.72/2.93        | ((k15_lattice3 @ sk_A @ sk_B_1)
% 2.72/2.93            = (k16_lattice3 @ sk_A @ (a_2_2_lattice3 @ sk_A @ sk_B_1)))
% 2.72/2.93        | (m1_subset_1 @ 
% 2.72/2.93           (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (u1_struct_0 @ sk_A)))),
% 2.72/2.93      inference('sup-', [status(thm)], ['366', '370'])).
% 2.72/2.93  thf('372', plain, ((l3_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('373', plain, ((v4_lattice3 @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('374', plain, ((v10_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('375', plain,
% 2.72/2.93      (((v2_struct_0 @ sk_A)
% 2.72/2.93        | ((k15_lattice3 @ sk_A @ sk_B_1)
% 2.72/2.93            = (k16_lattice3 @ sk_A @ (a_2_2_lattice3 @ sk_A @ sk_B_1)))
% 2.72/2.93        | (m1_subset_1 @ 
% 2.72/2.93           (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (u1_struct_0 @ sk_A)))),
% 2.72/2.93      inference('demod', [status(thm)], ['371', '372', '373', '374'])).
% 2.72/2.93  thf('376', plain,
% 2.72/2.93      (((k15_lattice3 @ sk_A @ sk_B_1)
% 2.72/2.93         != (k16_lattice3 @ sk_A @ (a_2_2_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('377', plain,
% 2.72/2.93      (((v2_struct_0 @ sk_A)
% 2.72/2.93        | (m1_subset_1 @ 
% 2.72/2.93           (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (u1_struct_0 @ sk_A)))),
% 2.72/2.93      inference('simplify_reflect-', [status(thm)], ['375', '376'])).
% 2.72/2.93  thf('378', plain, (~ (v2_struct_0 @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('379', plain,
% 2.72/2.93      ((m1_subset_1 @ 
% 2.72/2.93        (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93         (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93        (u1_struct_0 @ sk_A))),
% 2.72/2.93      inference('clc', [status(thm)], ['377', '378'])).
% 2.72/2.93  thf('380', plain,
% 2.72/2.93      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 2.72/2.93         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 2.72/2.93          | ~ (r3_lattice3 @ X5 @ X4 @ X6)
% 2.72/2.93          | ~ (r2_hidden @ X7 @ X6)
% 2.72/2.93          | (r1_lattices @ X5 @ X4 @ X7)
% 2.72/2.93          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X5))
% 2.72/2.93          | ~ (l3_lattices @ X5)
% 2.72/2.93          | (v2_struct_0 @ X5))),
% 2.72/2.93      inference('cnf', [status(esa)], [d16_lattice3])).
% 2.72/2.93  thf('381', plain,
% 2.72/2.93      (![X0 : $i, X1 : $i]:
% 2.72/2.93         ((v2_struct_0 @ sk_A)
% 2.72/2.93          | ~ (l3_lattices @ sk_A)
% 2.72/2.93          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.72/2.93          | (r1_lattices @ sk_A @ 
% 2.72/2.93             (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93              (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93             X0)
% 2.72/2.93          | ~ (r2_hidden @ X0 @ X1)
% 2.72/2.93          | ~ (r3_lattice3 @ sk_A @ 
% 2.72/2.93               (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93                (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93               X1))),
% 2.72/2.93      inference('sup-', [status(thm)], ['379', '380'])).
% 2.72/2.93  thf('382', plain, ((l3_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('383', plain,
% 2.72/2.93      (![X0 : $i, X1 : $i]:
% 2.72/2.93         ((v2_struct_0 @ sk_A)
% 2.72/2.93          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.72/2.93          | (r1_lattices @ sk_A @ 
% 2.72/2.93             (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93              (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93             X0)
% 2.72/2.93          | ~ (r2_hidden @ X0 @ X1)
% 2.72/2.93          | ~ (r3_lattice3 @ sk_A @ 
% 2.72/2.93               (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93                (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93               X1))),
% 2.72/2.93      inference('demod', [status(thm)], ['381', '382'])).
% 2.72/2.93  thf('384', plain,
% 2.72/2.93      (![X0 : $i]:
% 2.72/2.93         (~ (r2_hidden @ X0 @ (a_2_2_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93          | (r1_lattices @ sk_A @ 
% 2.72/2.93             (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93              (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93             X0)
% 2.72/2.93          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.72/2.93          | (v2_struct_0 @ sk_A))),
% 2.72/2.93      inference('sup-', [status(thm)], ['365', '383'])).
% 2.72/2.93  thf('385', plain,
% 2.72/2.93      (((v2_struct_0 @ sk_A)
% 2.72/2.93        | ~ (l3_lattices @ sk_A)
% 2.72/2.93        | ~ (v4_lattice3 @ sk_A)
% 2.72/2.93        | ~ (v10_lattices @ sk_A)
% 2.72/2.93        | (v2_struct_0 @ sk_A)
% 2.72/2.93        | ~ (m1_subset_1 @ (k15_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93             (u1_struct_0 @ sk_A))
% 2.72/2.93        | (r1_lattices @ sk_A @ 
% 2.72/2.93           (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (k15_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.93      inference('sup-', [status(thm)], ['46', '384'])).
% 2.72/2.93  thf('386', plain, ((l3_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('387', plain, ((v4_lattice3 @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('388', plain, ((v10_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('389', plain,
% 2.72/2.93      (((v2_struct_0 @ sk_A)
% 2.72/2.93        | (v2_struct_0 @ sk_A)
% 2.72/2.93        | ~ (m1_subset_1 @ (k15_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93             (u1_struct_0 @ sk_A))
% 2.72/2.93        | (r1_lattices @ sk_A @ 
% 2.72/2.93           (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (k15_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.93      inference('demod', [status(thm)], ['385', '386', '387', '388'])).
% 2.72/2.93  thf('390', plain,
% 2.72/2.93      (((r1_lattices @ sk_A @ 
% 2.72/2.93         (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93          (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93         (k15_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | ~ (m1_subset_1 @ (k15_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93             (u1_struct_0 @ sk_A))
% 2.72/2.93        | (v2_struct_0 @ sk_A))),
% 2.72/2.93      inference('simplify', [status(thm)], ['389'])).
% 2.72/2.93  thf('391', plain, (~ (v2_struct_0 @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('392', plain,
% 2.72/2.93      ((~ (m1_subset_1 @ (k15_lattice3 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 2.72/2.93        | (r1_lattices @ sk_A @ 
% 2.72/2.93           (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (k15_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.93      inference('clc', [status(thm)], ['390', '391'])).
% 2.72/2.93  thf('393', plain,
% 2.72/2.93      (((v2_struct_0 @ sk_A)
% 2.72/2.93        | ~ (l3_lattices @ sk_A)
% 2.72/2.93        | ~ (v4_lattice3 @ sk_A)
% 2.72/2.93        | ~ (v10_lattices @ sk_A)
% 2.72/2.93        | (r1_lattices @ sk_A @ 
% 2.72/2.93           (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (k15_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.93      inference('sup-', [status(thm)], ['35', '392'])).
% 2.72/2.93  thf('394', plain, ((l3_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('395', plain, ((v4_lattice3 @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('396', plain, ((v10_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('397', plain,
% 2.72/2.93      (((v2_struct_0 @ sk_A)
% 2.72/2.93        | (r1_lattices @ sk_A @ 
% 2.72/2.93           (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (k15_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.93      inference('demod', [status(thm)], ['393', '394', '395', '396'])).
% 2.72/2.93  thf('398', plain, (~ (v2_struct_0 @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('399', plain,
% 2.72/2.93      ((r1_lattices @ sk_A @ 
% 2.72/2.93        (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93         (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93        (k15_lattice3 @ sk_A @ sk_B_1))),
% 2.72/2.93      inference('clc', [status(thm)], ['397', '398'])).
% 2.72/2.93  thf('400', plain,
% 2.72/2.93      ((m1_subset_1 @ 
% 2.72/2.93        (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93         (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93        (u1_struct_0 @ sk_A))),
% 2.72/2.93      inference('clc', [status(thm)], ['377', '378'])).
% 2.72/2.93  thf('401', plain,
% 2.72/2.93      (![X1 : $i, X2 : $i, X3 : $i]:
% 2.72/2.93         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 2.72/2.93          | ~ (l3_lattices @ X2)
% 2.72/2.93          | ~ (v9_lattices @ X2)
% 2.72/2.93          | ~ (v8_lattices @ X2)
% 2.72/2.93          | ~ (v6_lattices @ X2)
% 2.72/2.93          | (v2_struct_0 @ X2)
% 2.72/2.93          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 2.72/2.93          | (r3_lattices @ X2 @ X1 @ X3)
% 2.72/2.93          | ~ (r1_lattices @ X2 @ X1 @ X3))),
% 2.72/2.93      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 2.72/2.93  thf('402', plain,
% 2.72/2.93      (![X0 : $i]:
% 2.72/2.93         (~ (r1_lattices @ sk_A @ 
% 2.72/2.93             (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93              (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93             X0)
% 2.72/2.93          | (r3_lattices @ sk_A @ 
% 2.72/2.93             (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93              (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93             X0)
% 2.72/2.93          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.72/2.93          | (v2_struct_0 @ sk_A)
% 2.72/2.93          | ~ (v6_lattices @ sk_A)
% 2.72/2.93          | ~ (v8_lattices @ sk_A)
% 2.72/2.93          | ~ (v9_lattices @ sk_A)
% 2.72/2.93          | ~ (l3_lattices @ sk_A))),
% 2.72/2.93      inference('sup-', [status(thm)], ['400', '401'])).
% 2.72/2.93  thf('403', plain, ((v6_lattices @ sk_A)),
% 2.72/2.93      inference('demod', [status(thm)], ['230', '231', '232'])).
% 2.72/2.93  thf('404', plain, ((v8_lattices @ sk_A)),
% 2.72/2.93      inference('demod', [status(thm)], ['236', '237', '238'])).
% 2.72/2.93  thf('405', plain, ((v9_lattices @ sk_A)),
% 2.72/2.93      inference('demod', [status(thm)], ['242', '243', '244'])).
% 2.72/2.93  thf('406', plain, ((l3_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('407', plain,
% 2.72/2.93      (![X0 : $i]:
% 2.72/2.93         (~ (r1_lattices @ sk_A @ 
% 2.72/2.93             (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93              (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93             X0)
% 2.72/2.93          | (r3_lattices @ sk_A @ 
% 2.72/2.93             (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93              (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93             X0)
% 2.72/2.93          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.72/2.93          | (v2_struct_0 @ sk_A))),
% 2.72/2.93      inference('demod', [status(thm)], ['402', '403', '404', '405', '406'])).
% 2.72/2.93  thf('408', plain,
% 2.72/2.93      (((v2_struct_0 @ sk_A)
% 2.72/2.93        | ~ (m1_subset_1 @ (k15_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93             (u1_struct_0 @ sk_A))
% 2.72/2.93        | (r3_lattices @ sk_A @ 
% 2.72/2.93           (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (k15_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.93      inference('sup-', [status(thm)], ['399', '407'])).
% 2.72/2.93  thf('409', plain, (~ (v2_struct_0 @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('410', plain,
% 2.72/2.93      (((r3_lattices @ sk_A @ 
% 2.72/2.93         (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93          (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93         (k15_lattice3 @ sk_A @ sk_B_1))
% 2.72/2.93        | ~ (m1_subset_1 @ (k15_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93             (u1_struct_0 @ sk_A)))),
% 2.72/2.93      inference('clc', [status(thm)], ['408', '409'])).
% 2.72/2.93  thf('411', plain,
% 2.72/2.93      (((v2_struct_0 @ sk_A)
% 2.72/2.93        | ~ (l3_lattices @ sk_A)
% 2.72/2.93        | ~ (v4_lattice3 @ sk_A)
% 2.72/2.93        | ~ (v10_lattices @ sk_A)
% 2.72/2.93        | (r3_lattices @ sk_A @ 
% 2.72/2.93           (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (k15_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.93      inference('sup-', [status(thm)], ['34', '410'])).
% 2.72/2.93  thf('412', plain, ((l3_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('413', plain, ((v4_lattice3 @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('414', plain, ((v10_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('415', plain,
% 2.72/2.93      (((v2_struct_0 @ sk_A)
% 2.72/2.93        | (r3_lattices @ sk_A @ 
% 2.72/2.93           (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93            (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93           (k15_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.93      inference('demod', [status(thm)], ['411', '412', '413', '414'])).
% 2.72/2.93  thf('416', plain, (~ (v2_struct_0 @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('417', plain,
% 2.72/2.93      ((r3_lattices @ sk_A @ 
% 2.72/2.93        (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93         (k15_lattice3 @ sk_A @ sk_B_1) @ sk_A) @ 
% 2.72/2.93        (k15_lattice3 @ sk_A @ sk_B_1))),
% 2.72/2.93      inference('clc', [status(thm)], ['415', '416'])).
% 2.72/2.93  thf('418', plain,
% 2.72/2.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.93         (~ (r3_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.72/2.93          | ~ (r3_lattices @ X0 @ 
% 2.72/2.93               (sk_D_4 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 2.72/2.93               (k15_lattice3 @ X0 @ X1))
% 2.72/2.93          | ((k15_lattice3 @ X0 @ X1) = (k16_lattice3 @ X0 @ X2))
% 2.72/2.93          | ~ (v10_lattices @ X0)
% 2.72/2.93          | ~ (v4_lattice3 @ X0)
% 2.72/2.93          | ~ (l3_lattices @ X0)
% 2.72/2.93          | (v2_struct_0 @ X0))),
% 2.72/2.93      inference('simplify', [status(thm)], ['258'])).
% 2.72/2.93  thf('419', plain,
% 2.72/2.93      (((v2_struct_0 @ sk_A)
% 2.72/2.93        | ~ (l3_lattices @ sk_A)
% 2.72/2.93        | ~ (v4_lattice3 @ sk_A)
% 2.72/2.93        | ~ (v10_lattices @ sk_A)
% 2.72/2.93        | ((k15_lattice3 @ sk_A @ sk_B_1)
% 2.72/2.93            = (k16_lattice3 @ sk_A @ (a_2_2_lattice3 @ sk_A @ sk_B_1)))
% 2.72/2.93        | ~ (r3_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93             (a_2_2_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.93      inference('sup-', [status(thm)], ['417', '418'])).
% 2.72/2.93  thf('420', plain, ((l3_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('421', plain, ((v4_lattice3 @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('422', plain, ((v10_lattices @ sk_A)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('423', plain,
% 2.72/2.93      ((r3_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ sk_B_1) @ 
% 2.72/2.93        (a_2_2_lattice3 @ sk_A @ sk_B_1))),
% 2.72/2.93      inference('clc', [status(thm)], ['350', '351'])).
% 2.72/2.93  thf('424', plain,
% 2.72/2.93      (((v2_struct_0 @ sk_A)
% 2.72/2.93        | ((k15_lattice3 @ sk_A @ sk_B_1)
% 2.72/2.93            = (k16_lattice3 @ sk_A @ (a_2_2_lattice3 @ sk_A @ sk_B_1))))),
% 2.72/2.93      inference('demod', [status(thm)], ['419', '420', '421', '422', '423'])).
% 2.72/2.93  thf('425', plain,
% 2.72/2.93      (((k15_lattice3 @ sk_A @ sk_B_1)
% 2.72/2.93         != (k16_lattice3 @ sk_A @ (a_2_2_lattice3 @ sk_A @ sk_B_1)))),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('426', plain, ((v2_struct_0 @ sk_A)),
% 2.72/2.93      inference('simplify_reflect-', [status(thm)], ['424', '425'])).
% 2.72/2.93  thf('427', plain, ($false), inference('demod', [status(thm)], ['0', '426'])).
% 2.72/2.93  
% 2.72/2.93  % SZS output end Refutation
% 2.72/2.93  
% 2.72/2.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
