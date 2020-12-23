%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ppMHWQTSMd

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:32 EST 2020

% Result     : Theorem 2.04s
% Output     : Refutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :  258 (1810 expanded)
%              Number of leaves         :   31 ( 506 expanded)
%              Depth                    :   45
%              Number of atoms          : 3212 (31428 expanded)
%              Number of equality atoms :   64 ( 972 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(a_2_1_lattice3_type,type,(
    a_2_1_lattice3: $i > $i > $i )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(r3_lattice3_type,type,(
    r3_lattice3: $i > $i > $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_4_type,type,(
    sk_D_4: $i > $i > $i > $i )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i > $i )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(r4_lattice3_type,type,(
    r4_lattice3: $i > $i > $i > $o )).

thf(a_2_2_lattice3_type,type,(
    a_2_2_lattice3: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t42_lattice3,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v4_lattice3 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ( r2_hidden @ B @ C )
                & ( r3_lattice3 @ A @ B @ C ) )
             => ( ( k16_lattice3 @ A @ C )
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
                  & ( r3_lattice3 @ A @ B @ C ) )
               => ( ( k16_lattice3 @ A @ C )
                  = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t42_lattice3])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r3_lattice3 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('3',plain,(
    ! [X18: $i,X19: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( r3_lattice3 @ X19 @ X18 @ X22 )
      | ( r3_lattice3 @ X19 @ ( sk_D_4 @ X22 @ X18 @ X19 ) @ X22 )
      | ( X18
        = ( k16_lattice3 @ X19 @ X22 ) )
      | ~ ( l3_lattices @ X19 )
      | ~ ( v4_lattice3 @ X19 )
      | ~ ( v10_lattices @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( sk_B
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ( r3_lattice3 @ sk_A @ ( sk_D_4 @ X0 @ sk_B @ sk_A ) @ X0 )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ( r3_lattice3 @ sk_A @ ( sk_D_4 @ X0 @ sk_B @ sk_A ) @ X0 )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('9',plain,
    ( ( r3_lattice3 @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    ( k16_lattice3 @ sk_A @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r3_lattice3 @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r3_lattice3 @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ sk_C ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    r3_lattice3 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X18: $i,X19: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( r3_lattice3 @ X19 @ X18 @ X22 )
      | ( m1_subset_1 @ ( sk_D_4 @ X22 @ X18 @ X19 ) @ ( u1_struct_0 @ X19 ) )
      | ( X18
        = ( k16_lattice3 @ X19 @ X22 ) )
      | ~ ( l3_lattices @ X19 )
      | ~ ( v4_lattice3 @ X19 )
      | ~ ( v10_lattices @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( sk_B
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_D_4 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_D_4 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18','19','20'])).

thf('22',plain,
    ( ( m1_subset_1 @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('23',plain,(
    ( k16_lattice3 @ sk_A @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( m1_subset_1 @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

thf(fraenkel_a_2_1_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( l3_lattices @ B ) )
     => ( ( r2_hidden @ A @ ( a_2_1_lattice3 @ B @ C ) )
      <=> ? [D: $i] :
            ( ( r3_lattice3 @ B @ D @ C )
            & ( A = D )
            & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('27',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( r2_hidden @ X12 @ ( a_2_1_lattice3 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X10 ) )
      | ( X12 != X13 )
      | ~ ( r3_lattice3 @ X10 @ X13 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_lattice3])).

thf('28',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ~ ( r3_lattice3 @ X10 @ X13 @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X10 ) )
      | ( r2_hidden @ X13 @ ( a_2_1_lattice3 @ X10 @ X11 ) )
      | ( v2_struct_0 @ X10 )
      | ~ ( l3_lattices @ X10 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattice3 @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ ( a_2_1_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    r2_hidden @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['13','33'])).

thf('35',plain,(
    m1_subset_1 @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('36',plain,(
    m1_subset_1 @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

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

thf('37',plain,(
    ! [X0: $i,X1: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X4 @ X0 @ X1 ) @ X4 )
      | ( r3_lattice3 @ X1 @ X0 @ X4 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r3_lattice3 @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ X0 )
      | ( r3_lattice3 @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(clc,[status(thm)],['40','41'])).

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

thf('43',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( l3_lattices @ X14 )
      | ~ ( v4_lattice3 @ X14 )
      | ~ ( v10_lattices @ X14 )
      | ( v2_struct_0 @ X14 )
      | ( X16
        = ( sk_D_3 @ X15 @ X14 @ X16 ) )
      | ~ ( r2_hidden @ X16 @ ( a_2_2_lattice3 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_2_lattice3])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ( ( sk_D @ ( a_2_2_lattice3 @ X1 @ X0 ) @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ sk_A )
        = ( sk_D_3 @ X0 @ X1 @ ( sk_D @ ( a_2_2_lattice3 @ X1 @ X0 ) @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ X0 )
      | ( r3_lattice3 @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('46',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( l3_lattices @ X14 )
      | ~ ( v4_lattice3 @ X14 )
      | ~ ( v10_lattices @ X14 )
      | ( v2_struct_0 @ X14 )
      | ( r4_lattice3 @ X14 @ ( sk_D_3 @ X15 @ X14 @ X16 ) @ X15 )
      | ~ ( r2_hidden @ X16 @ ( a_2_2_lattice3 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_2_lattice3])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ( r4_lattice3 @ X1 @ ( sk_D_3 @ X0 @ X1 @ ( sk_D @ ( a_2_2_lattice3 @ X1 @ X0 ) @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ X1 @ ( sk_D @ ( a_2_2_lattice3 @ X1 @ X0 ) @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ X0 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( r3_lattice3 @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( r3_lattice3 @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ ( a_2_2_lattice3 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( r4_lattice3 @ X1 @ ( sk_D @ ( a_2_2_lattice3 @ X1 @ X0 ) @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    m1_subset_1 @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ( m1_subset_1 @ ( sk_D @ X4 @ X0 @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ( r3_lattice3 @ X1 @ X0 @ X4 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r3_lattice3 @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X0 @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_lattice3 @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(clc,[status(thm)],['54','55'])).

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

thf('57',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ~ ( r4_lattice3 @ X6 @ X5 @ X7 )
      | ~ ( r2_hidden @ X8 @ X7 )
      | ( r1_lattices @ X6 @ X8 @ X5 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r3_lattice3 @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ X1 @ ( sk_D @ X0 @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r4_lattice3 @ sk_A @ ( sk_D @ X0 @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r3_lattice3 @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ X1 @ ( sk_D @ X0 @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r4_lattice3 @ sk_A @ ( sk_D @ X0 @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ X2 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r1_lattices @ sk_A @ X1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ X0 ) @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','60'])).

thf('62',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r1_lattices @ sk_A @ X1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ X0 ) @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['61','62','63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ X1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ X0 ) @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r3_lattice3 @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ( r1_lattices @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ X0 ) @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','66'])).

thf('68',plain,
    ( ( r1_lattices @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
    | ( r3_lattice3 @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','67'])).

thf('69',plain,(
    m1_subset_1 @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_lattices @ X1 @ X0 @ ( sk_D @ X4 @ X0 @ X1 ) )
      | ( r3_lattice3 @ X1 @ X0 @ X4 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r3_lattice3 @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ~ ( r1_lattices @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ ( sk_D @ X0 @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ~ ( r1_lattices @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ ( sk_D @ X0 @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ ( sk_D @ X0 @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ( r3_lattice3 @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_lattice3 @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['68','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    r3_lattice3 @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ( r2_hidden @ ( sk_D_1 @ X9 @ X5 @ X6 ) @ X9 )
      | ( r4_lattice3 @ X6 @ X5 @ X9 )
      | ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( X12
        = ( sk_D_2 @ X11 @ X10 @ X12 ) )
      | ~ ( r2_hidden @ X12 @ ( a_2_1_lattice3 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_lattice3])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ X1 @ X0 ) )
      | ( ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A )
        = ( sk_D_2 @ X0 @ X1 @ ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('91',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( r3_lattice3 @ X10 @ ( sk_D_2 @ X11 @ X10 @ X12 ) @ X11 )
      | ~ ( r2_hidden @ X12 @ ( a_2_1_lattice3 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_lattice3])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ X1 @ X0 ) )
      | ( r3_lattice3 @ X1 @ ( sk_D_2 @ X0 @ X1 @ ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A ) ) @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ X1 @ ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A ) @ X0 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['89','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ X1 @ X0 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( r3_lattice3 @ X1 @ ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X9 @ X5 @ X6 ) @ ( u1_struct_0 @ X6 ) )
      | ( r4_lattice3 @ X6 @ X5 @ X9 )
      | ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r3_lattice3 @ X1 @ X0 @ X2 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r1_lattices @ X1 @ X0 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X1 )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X1 )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X2 ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ X0 ) @ sk_B @ sk_A ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['94','105'])).

thf('107',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ X0 ) @ sk_B @ sk_A ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ X0 ) @ sk_B @ sk_A ) @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ X0 ) @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['80','109'])).

thf('111',plain,
    ( ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_B @ sk_A ) @ sk_B )
    | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['79','110'])).

thf('112',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ~ ( r1_lattices @ X6 @ ( sk_D_1 @ X9 @ X5 @ X6 ) @ X5 )
      | ( r4_lattice3 @ X6 @ X5 @ X9 )
      | ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['111','118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_lattice3,axiom,(
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

thf('123',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X26 ) )
      | ( ( k15_lattice3 @ X26 @ X27 )
        = X25 )
      | ~ ( r4_lattice3 @ X26 @ X25 @ X27 )
      | ~ ( r2_hidden @ X25 @ X27 )
      | ~ ( l3_lattices @ X26 )
      | ~ ( v4_lattice3 @ X26 )
      | ~ ( v10_lattices @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t41_lattice3])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( ( k15_lattice3 @ sk_A @ X0 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( ( k15_lattice3 @ sk_A @ X0 )
        = sk_B ) ) ),
    inference(demod,[status(thm)],['124','125','126','127'])).

thf('129',plain,
    ( ( ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
      = sk_B )
    | ~ ( r2_hidden @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['121','128'])).

thf('130',plain,(
    r3_lattice3 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ~ ( r3_lattice3 @ X10 @ X13 @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X10 ) )
      | ( r2_hidden @ X13 @ ( a_2_1_lattice3 @ X10 @ X11 ) )
      | ( v2_struct_0 @ X10 )
      | ~ ( l3_lattices @ X10 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(clc,[status(thm)],['135','136'])).

thf('138',plain,(
    r2_hidden @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['130','137'])).

thf('139',plain,
    ( ( ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
      = sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['129','138'])).

thf('140',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
    = sk_B ),
    inference(clc,[status(thm)],['139','140'])).

thf(t37_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v4_lattice3 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( k15_lattice3 @ A @ B )
          = ( k16_lattice3 @ A @ ( a_2_2_lattice3 @ A @ B ) ) ) ) )).

thf('142',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k15_lattice3 @ X23 @ X24 )
        = ( k16_lattice3 @ X23 @ ( a_2_2_lattice3 @ X23 @ X24 ) ) )
      | ~ ( l3_lattices @ X23 )
      | ~ ( v4_lattice3 @ X23 )
      | ~ ( v10_lattices @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t37_lattice3])).

thf('143',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ( X18
       != ( k16_lattice3 @ X19 @ X20 ) )
      | ~ ( r3_lattice3 @ X19 @ X21 @ X20 )
      | ( r3_lattices @ X19 @ X21 @ X18 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l3_lattices @ X19 )
      | ~ ( v4_lattice3 @ X19 )
      | ~ ( v10_lattices @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('144',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v10_lattices @ X19 )
      | ~ ( v4_lattice3 @ X19 )
      | ~ ( l3_lattices @ X19 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X19 ) )
      | ( r3_lattices @ X19 @ X21 @ ( k16_lattice3 @ X19 @ X20 ) )
      | ~ ( r3_lattice3 @ X19 @ X21 @ X20 )
      | ~ ( m1_subset_1 @ ( k16_lattice3 @ X19 @ X20 ) @ ( u1_struct_0 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( k15_lattice3 @ X1 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( r3_lattice3 @ X1 @ X2 @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ( r3_lattices @ X1 @ X2 @ ( k16_lattice3 @ X1 @ ( a_2_2_lattice3 @ X1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['142','144'])).

thf('146',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r3_lattices @ X1 @ X2 @ ( k16_lattice3 @ X1 @ ( a_2_2_lattice3 @ X1 @ X0 ) ) )
      | ~ ( r3_lattice3 @ X1 @ X2 @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_subset_1 @ ( k15_lattice3 @ X1 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r3_lattice3 @ sk_A @ X0 @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
      | ( r3_lattices @ sk_A @ X0 @ ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['141','146'])).

thf('148',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r3_lattice3 @ sk_A @ X0 @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
      | ( r3_lattices @ sk_A @ X0 @ ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['147','148','149','150','151'])).

thf('153',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k15_lattice3 @ X23 @ X24 )
        = ( k16_lattice3 @ X23 @ ( a_2_2_lattice3 @ X23 @ X24 ) ) )
      | ~ ( l3_lattices @ X23 )
      | ~ ( v4_lattice3 @ X23 )
      | ~ ( v10_lattices @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t37_lattice3])).

thf('154',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k15_lattice3 @ X23 @ X24 )
        = ( k16_lattice3 @ X23 @ ( a_2_2_lattice3 @ X23 @ X24 ) ) )
      | ~ ( l3_lattices @ X23 )
      | ~ ( v4_lattice3 @ X23 )
      | ~ ( v10_lattices @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t37_lattice3])).

thf('155',plain,
    ( ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
    = sk_B ),
    inference(clc,[status(thm)],['139','140'])).

thf('156',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k15_lattice3 @ X23 @ X24 )
        = ( k16_lattice3 @ X23 @ ( a_2_2_lattice3 @ X23 @ X24 ) ) )
      | ~ ( l3_lattices @ X23 )
      | ~ ( v4_lattice3 @ X23 )
      | ~ ( v10_lattices @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t37_lattice3])).

thf('157',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ( X18
       != ( k16_lattice3 @ X19 @ X20 ) )
      | ( r3_lattice3 @ X19 @ X18 @ X20 )
      | ~ ( l3_lattices @ X19 )
      | ~ ( v4_lattice3 @ X19 )
      | ~ ( v10_lattices @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('158',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v10_lattices @ X19 )
      | ~ ( v4_lattice3 @ X19 )
      | ~ ( l3_lattices @ X19 )
      | ( r3_lattice3 @ X19 @ ( k16_lattice3 @ X19 @ X20 ) @ X20 )
      | ~ ( m1_subset_1 @ ( k16_lattice3 @ X19 @ X20 ) @ ( u1_struct_0 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( k15_lattice3 @ X1 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( r3_lattice3 @ X1 @ ( k16_lattice3 @ X1 @ ( a_2_2_lattice3 @ X1 @ X0 ) ) @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['156','158'])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ X1 @ ( k16_lattice3 @ X1 @ ( a_2_2_lattice3 @ X1 @ X0 ) ) @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_subset_1 @ ( k15_lattice3 @ X1 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( r3_lattice3 @ sk_A @ ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['155','160'])).

thf('162',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_lattice3 @ sk_A @ ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['161','162','163','164','165'])).

thf('167',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    r3_lattice3 @ sk_A @ ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['166','167'])).

thf('169',plain,
    ( ( r3_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup+',[status(thm)],['154','168'])).

thf('170',plain,
    ( ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
    = sk_B ),
    inference(clc,[status(thm)],['139','140'])).

thf('171',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( r3_lattice3 @ sk_A @ sk_B @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['169','170','171','172','173'])).

thf('175',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    r3_lattice3 @ sk_A @ sk_B @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_D_4 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18','19','20'])).

thf('178',plain,
    ( ( m1_subset_1 @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,
    ( ( sk_B
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
    | ( m1_subset_1 @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['178','179'])).

thf('181',plain,(
    r3_lattice3 @ sk_A @ sk_B @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['174','175'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ( r3_lattice3 @ sk_A @ ( sk_D_4 @ X0 @ sk_B @ sk_A ) @ X0 )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('183',plain,
    ( ( r3_lattice3 @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
    | ( sk_B
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( ( sk_B
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
    | ( r3_lattice3 @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['183','184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r3_lattice3 @ sk_A @ X0 @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
      | ( r3_lattices @ sk_A @ X0 @ ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['147','148','149','150','151'])).

thf('187',plain,
    ( ( sk_B
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
    | ~ ( m1_subset_1 @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r3_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,
    ( ( sk_B
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( r3_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
    | ( sk_B
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['180','187'])).

thf('189',plain,
    ( ( r3_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ) ),
    inference(simplify,[status(thm)],['188'])).

thf('190',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( sk_B
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
    | ( r3_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ) ),
    inference(clc,[status(thm)],['189','190'])).

thf('192',plain,
    ( ( r3_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( sk_B
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup+',[status(thm)],['153','191'])).

thf('193',plain,
    ( ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
    = sk_B ),
    inference(clc,[status(thm)],['139','140'])).

thf('194',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ( r3_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['192','193','194','195','196'])).

thf('198',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,
    ( ( sk_B
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
    | ( r3_lattices @ sk_A @ ( sk_D_4 @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['197','198'])).

thf('200',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    ! [X18: $i,X19: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( r3_lattice3 @ X19 @ X18 @ X22 )
      | ~ ( r3_lattices @ X19 @ ( sk_D_4 @ X22 @ X18 @ X19 ) @ X18 )
      | ( X18
        = ( k16_lattice3 @ X19 @ X22 ) )
      | ~ ( l3_lattices @ X19 )
      | ~ ( v4_lattice3 @ X19 )
      | ~ ( v10_lattices @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('202',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( sk_B
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattices @ sk_A @ ( sk_D_4 @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattices @ sk_A @ ( sk_D_4 @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['202','203','204','205'])).

thf('207',plain,
    ( ( sk_B
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
    | ~ ( r3_lattice3 @ sk_A @ sk_B @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
    | ( sk_B
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['199','206'])).

thf('208',plain,(
    r3_lattice3 @ sk_A @ sk_B @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['174','175'])).

thf('209',plain,
    ( ( sk_B
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
    | ( sk_B
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['207','208'])).

thf('210',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ) ),
    inference(simplify,[status(thm)],['209'])).

thf('211',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,
    ( sk_B
    = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['210','211'])).

thf('213',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r3_lattice3 @ sk_A @ X0 @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
      | ( r3_lattices @ sk_A @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['152','212'])).

thf('214',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r3_lattices @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['78','213'])).

thf('215',plain,(
    m1_subset_1 @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('216',plain,
    ( ( r3_lattices @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['214','215'])).

thf('217',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    r3_lattices @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference(clc,[status(thm)],['216','217'])).

thf('219',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattices @ sk_A @ ( sk_D_4 @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['202','203','204','205'])).

thf('220',plain,
    ( ~ ( r3_lattice3 @ sk_A @ sk_B @ sk_C )
    | ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['218','219'])).

thf('221',plain,(
    r3_lattice3 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,
    ( ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['220','221'])).

thf('223',plain,(
    ( k16_lattice3 @ sk_A @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['222','223'])).

thf('225',plain,(
    $false ),
    inference(demod,[status(thm)],['0','224'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ppMHWQTSMd
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:18:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.04/2.28  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.04/2.28  % Solved by: fo/fo7.sh
% 2.04/2.28  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.04/2.28  % done 1372 iterations in 1.829s
% 2.04/2.28  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.04/2.28  % SZS output start Refutation
% 2.04/2.28  thf(a_2_1_lattice3_type, type, a_2_1_lattice3: $i > $i > $i).
% 2.04/2.28  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 2.04/2.28  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 2.04/2.28  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 2.04/2.28  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.04/2.28  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 2.04/2.28  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.04/2.28  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 2.04/2.28  thf(r3_lattice3_type, type, r3_lattice3: $i > $i > $i > $o).
% 2.04/2.28  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 2.04/2.28  thf(sk_A_type, type, sk_A: $i).
% 2.04/2.28  thf(sk_D_4_type, type, sk_D_4: $i > $i > $i > $i).
% 2.04/2.28  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 2.04/2.28  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 2.04/2.28  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i > $i).
% 2.04/2.28  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 2.04/2.28  thf(r4_lattice3_type, type, r4_lattice3: $i > $i > $i > $o).
% 2.04/2.28  thf(a_2_2_lattice3_type, type, a_2_2_lattice3: $i > $i > $i).
% 2.04/2.28  thf(sk_B_type, type, sk_B: $i).
% 2.04/2.28  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 2.04/2.28  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.04/2.28  thf(sk_C_type, type, sk_C: $i).
% 2.04/2.28  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.04/2.28  thf(t42_lattice3, conjecture,
% 2.04/2.28    (![A:$i]:
% 2.04/2.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.04/2.28         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 2.04/2.28       ( ![B:$i]:
% 2.04/2.28         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.04/2.28           ( ![C:$i]:
% 2.04/2.28             ( ( ( r2_hidden @ B @ C ) & ( r3_lattice3 @ A @ B @ C ) ) =>
% 2.04/2.28               ( ( k16_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ))).
% 2.04/2.28  thf(zf_stmt_0, negated_conjecture,
% 2.04/2.28    (~( ![A:$i]:
% 2.04/2.28        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.04/2.28            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 2.04/2.28          ( ![B:$i]:
% 2.04/2.28            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.04/2.28              ( ![C:$i]:
% 2.04/2.28                ( ( ( r2_hidden @ B @ C ) & ( r3_lattice3 @ A @ B @ C ) ) =>
% 2.04/2.28                  ( ( k16_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ) )),
% 2.04/2.28    inference('cnf.neg', [status(esa)], [t42_lattice3])).
% 2.04/2.28  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 2.04/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.28  thf('1', plain, ((r3_lattice3 @ sk_A @ sk_B @ sk_C)),
% 2.04/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.28  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.04/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.28  thf(t34_lattice3, axiom,
% 2.04/2.28    (![A:$i]:
% 2.04/2.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.04/2.28         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 2.04/2.28       ( ![B:$i]:
% 2.04/2.28         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.04/2.28           ( ![C:$i]:
% 2.04/2.28             ( ( ( B ) = ( k16_lattice3 @ A @ C ) ) <=>
% 2.04/2.28               ( ( r3_lattice3 @ A @ B @ C ) & 
% 2.04/2.28                 ( ![D:$i]:
% 2.04/2.28                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 2.04/2.28                     ( ( r3_lattice3 @ A @ D @ C ) =>
% 2.04/2.28                       ( r3_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 2.04/2.28  thf('3', plain,
% 2.04/2.28      (![X18 : $i, X19 : $i, X22 : $i]:
% 2.04/2.28         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 2.04/2.28          | ~ (r3_lattice3 @ X19 @ X18 @ X22)
% 2.04/2.28          | (r3_lattice3 @ X19 @ (sk_D_4 @ X22 @ X18 @ X19) @ X22)
% 2.04/2.28          | ((X18) = (k16_lattice3 @ X19 @ X22))
% 2.04/2.28          | ~ (l3_lattices @ X19)
% 2.04/2.28          | ~ (v4_lattice3 @ X19)
% 2.04/2.28          | ~ (v10_lattices @ X19)
% 2.04/2.28          | (v2_struct_0 @ X19))),
% 2.04/2.28      inference('cnf', [status(esa)], [t34_lattice3])).
% 2.04/2.28  thf('4', plain,
% 2.04/2.28      (![X0 : $i]:
% 2.04/2.28         ((v2_struct_0 @ sk_A)
% 2.04/2.28          | ~ (v10_lattices @ sk_A)
% 2.04/2.28          | ~ (v4_lattice3 @ sk_A)
% 2.04/2.28          | ~ (l3_lattices @ sk_A)
% 2.04/2.28          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 2.04/2.28          | (r3_lattice3 @ sk_A @ (sk_D_4 @ X0 @ sk_B @ sk_A) @ X0)
% 2.04/2.28          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 2.04/2.28      inference('sup-', [status(thm)], ['2', '3'])).
% 2.04/2.28  thf('5', plain, ((v10_lattices @ sk_A)),
% 2.04/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.28  thf('6', plain, ((v4_lattice3 @ sk_A)),
% 2.04/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.28  thf('7', plain, ((l3_lattices @ sk_A)),
% 2.04/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.28  thf('8', plain,
% 2.04/2.28      (![X0 : $i]:
% 2.04/2.28         ((v2_struct_0 @ sk_A)
% 2.04/2.28          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 2.04/2.28          | (r3_lattice3 @ sk_A @ (sk_D_4 @ X0 @ sk_B @ sk_A) @ X0)
% 2.04/2.28          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 2.04/2.28      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 2.04/2.28  thf('9', plain,
% 2.04/2.28      (((r3_lattice3 @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 2.04/2.28        | ((sk_B) = (k16_lattice3 @ sk_A @ sk_C))
% 2.04/2.28        | (v2_struct_0 @ sk_A))),
% 2.04/2.28      inference('sup-', [status(thm)], ['1', '8'])).
% 2.04/2.28  thf('10', plain, (((k16_lattice3 @ sk_A @ sk_C) != (sk_B))),
% 2.04/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.28  thf('11', plain,
% 2.04/2.28      (((r3_lattice3 @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 2.04/2.28        | (v2_struct_0 @ sk_A))),
% 2.04/2.28      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 2.04/2.28  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 2.04/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.28  thf('13', plain,
% 2.04/2.28      ((r3_lattice3 @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ sk_C)),
% 2.04/2.28      inference('clc', [status(thm)], ['11', '12'])).
% 2.04/2.28  thf('14', plain, ((r3_lattice3 @ sk_A @ sk_B @ sk_C)),
% 2.04/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.28  thf('15', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.04/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.28  thf('16', plain,
% 2.04/2.28      (![X18 : $i, X19 : $i, X22 : $i]:
% 2.04/2.28         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 2.04/2.28          | ~ (r3_lattice3 @ X19 @ X18 @ X22)
% 2.04/2.28          | (m1_subset_1 @ (sk_D_4 @ X22 @ X18 @ X19) @ (u1_struct_0 @ X19))
% 2.04/2.28          | ((X18) = (k16_lattice3 @ X19 @ X22))
% 2.04/2.28          | ~ (l3_lattices @ X19)
% 2.04/2.28          | ~ (v4_lattice3 @ X19)
% 2.04/2.28          | ~ (v10_lattices @ X19)
% 2.04/2.28          | (v2_struct_0 @ X19))),
% 2.04/2.28      inference('cnf', [status(esa)], [t34_lattice3])).
% 2.04/2.28  thf('17', plain,
% 2.04/2.28      (![X0 : $i]:
% 2.04/2.28         ((v2_struct_0 @ sk_A)
% 2.04/2.28          | ~ (v10_lattices @ sk_A)
% 2.04/2.28          | ~ (v4_lattice3 @ sk_A)
% 2.04/2.28          | ~ (l3_lattices @ sk_A)
% 2.04/2.28          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 2.04/2.28          | (m1_subset_1 @ (sk_D_4 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.28          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 2.04/2.28      inference('sup-', [status(thm)], ['15', '16'])).
% 2.04/2.28  thf('18', plain, ((v10_lattices @ sk_A)),
% 2.04/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.28  thf('19', plain, ((v4_lattice3 @ sk_A)),
% 2.04/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.28  thf('20', plain, ((l3_lattices @ sk_A)),
% 2.04/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.28  thf('21', plain,
% 2.04/2.28      (![X0 : $i]:
% 2.04/2.28         ((v2_struct_0 @ sk_A)
% 2.04/2.28          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 2.04/2.28          | (m1_subset_1 @ (sk_D_4 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.28          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 2.04/2.28      inference('demod', [status(thm)], ['17', '18', '19', '20'])).
% 2.04/2.28  thf('22', plain,
% 2.04/2.28      (((m1_subset_1 @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.28        | ((sk_B) = (k16_lattice3 @ sk_A @ sk_C))
% 2.04/2.28        | (v2_struct_0 @ sk_A))),
% 2.04/2.28      inference('sup-', [status(thm)], ['14', '21'])).
% 2.04/2.28  thf('23', plain, (((k16_lattice3 @ sk_A @ sk_C) != (sk_B))),
% 2.04/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.28  thf('24', plain,
% 2.04/2.28      (((m1_subset_1 @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.28        | (v2_struct_0 @ sk_A))),
% 2.04/2.28      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 2.04/2.28  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 2.04/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.28  thf('26', plain,
% 2.04/2.28      ((m1_subset_1 @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 2.04/2.28      inference('clc', [status(thm)], ['24', '25'])).
% 2.04/2.28  thf(fraenkel_a_2_1_lattice3, axiom,
% 2.04/2.28    (![A:$i,B:$i,C:$i]:
% 2.04/2.28     ( ( ( ~( v2_struct_0 @ B ) ) & ( l3_lattices @ B ) ) =>
% 2.04/2.28       ( ( r2_hidden @ A @ ( a_2_1_lattice3 @ B @ C ) ) <=>
% 2.04/2.28         ( ?[D:$i]:
% 2.04/2.28           ( ( r3_lattice3 @ B @ D @ C ) & ( ( A ) = ( D ) ) & 
% 2.04/2.28             ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 2.04/2.28  thf('27', plain,
% 2.04/2.28      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 2.04/2.28         (~ (l3_lattices @ X10)
% 2.04/2.28          | (v2_struct_0 @ X10)
% 2.04/2.28          | (r2_hidden @ X12 @ (a_2_1_lattice3 @ X10 @ X11))
% 2.04/2.28          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X10))
% 2.04/2.28          | ((X12) != (X13))
% 2.04/2.28          | ~ (r3_lattice3 @ X10 @ X13 @ X11))),
% 2.04/2.28      inference('cnf', [status(esa)], [fraenkel_a_2_1_lattice3])).
% 2.04/2.28  thf('28', plain,
% 2.04/2.28      (![X10 : $i, X11 : $i, X13 : $i]:
% 2.04/2.28         (~ (r3_lattice3 @ X10 @ X13 @ X11)
% 2.04/2.28          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X10))
% 2.04/2.28          | (r2_hidden @ X13 @ (a_2_1_lattice3 @ X10 @ X11))
% 2.04/2.28          | (v2_struct_0 @ X10)
% 2.04/2.28          | ~ (l3_lattices @ X10))),
% 2.04/2.28      inference('simplify', [status(thm)], ['27'])).
% 2.04/2.28  thf('29', plain,
% 2.04/2.28      (![X0 : $i]:
% 2.04/2.28         (~ (l3_lattices @ sk_A)
% 2.04/2.28          | (v2_struct_0 @ sk_A)
% 2.04/2.28          | (r2_hidden @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ 
% 2.04/2.28             (a_2_1_lattice3 @ sk_A @ X0))
% 2.04/2.28          | ~ (r3_lattice3 @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ X0))),
% 2.04/2.28      inference('sup-', [status(thm)], ['26', '28'])).
% 2.04/2.28  thf('30', plain, ((l3_lattices @ sk_A)),
% 2.04/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.28  thf('31', plain,
% 2.04/2.28      (![X0 : $i]:
% 2.04/2.28         ((v2_struct_0 @ sk_A)
% 2.04/2.28          | (r2_hidden @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ 
% 2.04/2.28             (a_2_1_lattice3 @ sk_A @ X0))
% 2.04/2.28          | ~ (r3_lattice3 @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ X0))),
% 2.04/2.28      inference('demod', [status(thm)], ['29', '30'])).
% 2.04/2.28  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 2.04/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.28  thf('33', plain,
% 2.04/2.28      (![X0 : $i]:
% 2.04/2.28         (~ (r3_lattice3 @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ X0)
% 2.04/2.28          | (r2_hidden @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ 
% 2.04/2.28             (a_2_1_lattice3 @ sk_A @ X0)))),
% 2.04/2.28      inference('clc', [status(thm)], ['31', '32'])).
% 2.04/2.28  thf('34', plain,
% 2.04/2.28      ((r2_hidden @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ 
% 2.04/2.28        (a_2_1_lattice3 @ sk_A @ sk_C))),
% 2.04/2.28      inference('sup-', [status(thm)], ['13', '33'])).
% 2.04/2.28  thf('35', plain,
% 2.04/2.28      ((m1_subset_1 @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 2.04/2.28      inference('clc', [status(thm)], ['24', '25'])).
% 2.04/2.28  thf('36', plain,
% 2.04/2.28      ((m1_subset_1 @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 2.04/2.28      inference('clc', [status(thm)], ['24', '25'])).
% 2.04/2.29  thf(d16_lattice3, axiom,
% 2.04/2.29    (![A:$i]:
% 2.04/2.29     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 2.04/2.29       ( ![B:$i]:
% 2.04/2.29         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.04/2.29           ( ![C:$i]:
% 2.04/2.29             ( ( r3_lattice3 @ A @ B @ C ) <=>
% 2.04/2.29               ( ![D:$i]:
% 2.04/2.29                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 2.04/2.29                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 2.04/2.29  thf('37', plain,
% 2.04/2.29      (![X0 : $i, X1 : $i, X4 : $i]:
% 2.04/2.29         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 2.04/2.29          | (r2_hidden @ (sk_D @ X4 @ X0 @ X1) @ X4)
% 2.04/2.29          | (r3_lattice3 @ X1 @ X0 @ X4)
% 2.04/2.29          | ~ (l3_lattices @ X1)
% 2.04/2.29          | (v2_struct_0 @ X1))),
% 2.04/2.29      inference('cnf', [status(esa)], [d16_lattice3])).
% 2.04/2.29  thf('38', plain,
% 2.04/2.29      (![X0 : $i]:
% 2.04/2.29         ((v2_struct_0 @ sk_A)
% 2.04/2.29          | ~ (l3_lattices @ sk_A)
% 2.04/2.29          | (r3_lattice3 @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ X0)
% 2.04/2.29          | (r2_hidden @ (sk_D @ X0 @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ sk_A) @ 
% 2.04/2.29             X0))),
% 2.04/2.29      inference('sup-', [status(thm)], ['36', '37'])).
% 2.04/2.29  thf('39', plain, ((l3_lattices @ sk_A)),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('40', plain,
% 2.04/2.29      (![X0 : $i]:
% 2.04/2.29         ((v2_struct_0 @ sk_A)
% 2.04/2.29          | (r3_lattice3 @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ X0)
% 2.04/2.29          | (r2_hidden @ (sk_D @ X0 @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ sk_A) @ 
% 2.04/2.29             X0))),
% 2.04/2.29      inference('demod', [status(thm)], ['38', '39'])).
% 2.04/2.29  thf('41', plain, (~ (v2_struct_0 @ sk_A)),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('42', plain,
% 2.04/2.29      (![X0 : $i]:
% 2.04/2.29         ((r2_hidden @ (sk_D @ X0 @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ sk_A) @ X0)
% 2.04/2.29          | (r3_lattice3 @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ X0))),
% 2.04/2.29      inference('clc', [status(thm)], ['40', '41'])).
% 2.04/2.29  thf(fraenkel_a_2_2_lattice3, axiom,
% 2.04/2.29    (![A:$i,B:$i,C:$i]:
% 2.04/2.29     ( ( ( ~( v2_struct_0 @ B ) ) & ( v10_lattices @ B ) & 
% 2.04/2.29         ( v4_lattice3 @ B ) & ( l3_lattices @ B ) ) =>
% 2.04/2.29       ( ( r2_hidden @ A @ ( a_2_2_lattice3 @ B @ C ) ) <=>
% 2.04/2.29         ( ?[D:$i]:
% 2.04/2.29           ( ( r4_lattice3 @ B @ D @ C ) & ( ( A ) = ( D ) ) & 
% 2.04/2.29             ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 2.04/2.29  thf('43', plain,
% 2.04/2.29      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.04/2.29         (~ (l3_lattices @ X14)
% 2.04/2.29          | ~ (v4_lattice3 @ X14)
% 2.04/2.29          | ~ (v10_lattices @ X14)
% 2.04/2.29          | (v2_struct_0 @ X14)
% 2.04/2.29          | ((X16) = (sk_D_3 @ X15 @ X14 @ X16))
% 2.04/2.29          | ~ (r2_hidden @ X16 @ (a_2_2_lattice3 @ X14 @ X15)))),
% 2.04/2.29      inference('cnf', [status(esa)], [fraenkel_a_2_2_lattice3])).
% 2.04/2.29  thf('44', plain,
% 2.04/2.29      (![X0 : $i, X1 : $i]:
% 2.04/2.29         ((r3_lattice3 @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ 
% 2.04/2.29           (a_2_2_lattice3 @ X1 @ X0))
% 2.04/2.29          | ((sk_D @ (a_2_2_lattice3 @ X1 @ X0) @ 
% 2.04/2.29              (sk_D_4 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 2.04/2.29              = (sk_D_3 @ X0 @ X1 @ 
% 2.04/2.29                 (sk_D @ (a_2_2_lattice3 @ X1 @ X0) @ 
% 2.04/2.29                  (sk_D_4 @ sk_C @ sk_B @ sk_A) @ sk_A)))
% 2.04/2.29          | (v2_struct_0 @ X1)
% 2.04/2.29          | ~ (v10_lattices @ X1)
% 2.04/2.29          | ~ (v4_lattice3 @ X1)
% 2.04/2.29          | ~ (l3_lattices @ X1))),
% 2.04/2.29      inference('sup-', [status(thm)], ['42', '43'])).
% 2.04/2.29  thf('45', plain,
% 2.04/2.29      (![X0 : $i]:
% 2.04/2.29         ((r2_hidden @ (sk_D @ X0 @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ sk_A) @ X0)
% 2.04/2.29          | (r3_lattice3 @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ X0))),
% 2.04/2.29      inference('clc', [status(thm)], ['40', '41'])).
% 2.04/2.29  thf('46', plain,
% 2.04/2.29      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.04/2.29         (~ (l3_lattices @ X14)
% 2.04/2.29          | ~ (v4_lattice3 @ X14)
% 2.04/2.29          | ~ (v10_lattices @ X14)
% 2.04/2.29          | (v2_struct_0 @ X14)
% 2.04/2.29          | (r4_lattice3 @ X14 @ (sk_D_3 @ X15 @ X14 @ X16) @ X15)
% 2.04/2.29          | ~ (r2_hidden @ X16 @ (a_2_2_lattice3 @ X14 @ X15)))),
% 2.04/2.29      inference('cnf', [status(esa)], [fraenkel_a_2_2_lattice3])).
% 2.04/2.29  thf('47', plain,
% 2.04/2.29      (![X0 : $i, X1 : $i]:
% 2.04/2.29         ((r3_lattice3 @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ 
% 2.04/2.29           (a_2_2_lattice3 @ X1 @ X0))
% 2.04/2.29          | (r4_lattice3 @ X1 @ 
% 2.04/2.29             (sk_D_3 @ X0 @ X1 @ 
% 2.04/2.29              (sk_D @ (a_2_2_lattice3 @ X1 @ X0) @ 
% 2.04/2.29               (sk_D_4 @ sk_C @ sk_B @ sk_A) @ sk_A)) @ 
% 2.04/2.29             X0)
% 2.04/2.29          | (v2_struct_0 @ X1)
% 2.04/2.29          | ~ (v10_lattices @ X1)
% 2.04/2.29          | ~ (v4_lattice3 @ X1)
% 2.04/2.29          | ~ (l3_lattices @ X1))),
% 2.04/2.29      inference('sup-', [status(thm)], ['45', '46'])).
% 2.04/2.29  thf('48', plain,
% 2.04/2.29      (![X0 : $i, X1 : $i]:
% 2.04/2.29         ((r4_lattice3 @ X1 @ 
% 2.04/2.29           (sk_D @ (a_2_2_lattice3 @ X1 @ X0) @ 
% 2.04/2.29            (sk_D_4 @ sk_C @ sk_B @ sk_A) @ sk_A) @ 
% 2.04/2.29           X0)
% 2.04/2.29          | ~ (l3_lattices @ X1)
% 2.04/2.29          | ~ (v4_lattice3 @ X1)
% 2.04/2.29          | ~ (v10_lattices @ X1)
% 2.04/2.29          | (v2_struct_0 @ X1)
% 2.04/2.29          | (r3_lattice3 @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ 
% 2.04/2.29             (a_2_2_lattice3 @ X1 @ X0))
% 2.04/2.29          | ~ (l3_lattices @ X1)
% 2.04/2.29          | ~ (v4_lattice3 @ X1)
% 2.04/2.29          | ~ (v10_lattices @ X1)
% 2.04/2.29          | (v2_struct_0 @ X1)
% 2.04/2.29          | (r3_lattice3 @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ 
% 2.04/2.29             (a_2_2_lattice3 @ X1 @ X0)))),
% 2.04/2.29      inference('sup+', [status(thm)], ['44', '47'])).
% 2.04/2.29  thf('49', plain,
% 2.04/2.29      (![X0 : $i, X1 : $i]:
% 2.04/2.29         ((r3_lattice3 @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ 
% 2.04/2.29           (a_2_2_lattice3 @ X1 @ X0))
% 2.04/2.29          | (v2_struct_0 @ X1)
% 2.04/2.29          | ~ (v10_lattices @ X1)
% 2.04/2.29          | ~ (v4_lattice3 @ X1)
% 2.04/2.29          | ~ (l3_lattices @ X1)
% 2.04/2.29          | (r4_lattice3 @ X1 @ 
% 2.04/2.29             (sk_D @ (a_2_2_lattice3 @ X1 @ X0) @ 
% 2.04/2.29              (sk_D_4 @ sk_C @ sk_B @ sk_A) @ sk_A) @ 
% 2.04/2.29             X0))),
% 2.04/2.29      inference('simplify', [status(thm)], ['48'])).
% 2.04/2.29  thf('50', plain,
% 2.04/2.29      ((m1_subset_1 @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 2.04/2.29      inference('clc', [status(thm)], ['24', '25'])).
% 2.04/2.29  thf('51', plain,
% 2.04/2.29      (![X0 : $i, X1 : $i, X4 : $i]:
% 2.04/2.29         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 2.04/2.29          | (m1_subset_1 @ (sk_D @ X4 @ X0 @ X1) @ (u1_struct_0 @ X1))
% 2.04/2.29          | (r3_lattice3 @ X1 @ X0 @ X4)
% 2.04/2.29          | ~ (l3_lattices @ X1)
% 2.04/2.29          | (v2_struct_0 @ X1))),
% 2.04/2.29      inference('cnf', [status(esa)], [d16_lattice3])).
% 2.04/2.29  thf('52', plain,
% 2.04/2.29      (![X0 : $i]:
% 2.04/2.29         ((v2_struct_0 @ sk_A)
% 2.04/2.29          | ~ (l3_lattices @ sk_A)
% 2.04/2.29          | (r3_lattice3 @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ X0)
% 2.04/2.29          | (m1_subset_1 @ 
% 2.04/2.29             (sk_D @ X0 @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ sk_A) @ 
% 2.04/2.29             (u1_struct_0 @ sk_A)))),
% 2.04/2.29      inference('sup-', [status(thm)], ['50', '51'])).
% 2.04/2.29  thf('53', plain, ((l3_lattices @ sk_A)),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('54', plain,
% 2.04/2.29      (![X0 : $i]:
% 2.04/2.29         ((v2_struct_0 @ sk_A)
% 2.04/2.29          | (r3_lattice3 @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ X0)
% 2.04/2.29          | (m1_subset_1 @ 
% 2.04/2.29             (sk_D @ X0 @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ sk_A) @ 
% 2.04/2.29             (u1_struct_0 @ sk_A)))),
% 2.04/2.29      inference('demod', [status(thm)], ['52', '53'])).
% 2.04/2.29  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('56', plain,
% 2.04/2.29      (![X0 : $i]:
% 2.04/2.29         ((m1_subset_1 @ (sk_D @ X0 @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ sk_A) @ 
% 2.04/2.29           (u1_struct_0 @ sk_A))
% 2.04/2.29          | (r3_lattice3 @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ X0))),
% 2.04/2.29      inference('clc', [status(thm)], ['54', '55'])).
% 2.04/2.29  thf(d17_lattice3, axiom,
% 2.04/2.29    (![A:$i]:
% 2.04/2.29     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 2.04/2.29       ( ![B:$i]:
% 2.04/2.29         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.04/2.29           ( ![C:$i]:
% 2.04/2.29             ( ( r4_lattice3 @ A @ B @ C ) <=>
% 2.04/2.29               ( ![D:$i]:
% 2.04/2.29                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 2.04/2.29                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ))).
% 2.04/2.29  thf('57', plain,
% 2.04/2.29      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 2.04/2.29         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 2.04/2.29          | ~ (r4_lattice3 @ X6 @ X5 @ X7)
% 2.04/2.29          | ~ (r2_hidden @ X8 @ X7)
% 2.04/2.29          | (r1_lattices @ X6 @ X8 @ X5)
% 2.04/2.29          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X6))
% 2.04/2.29          | ~ (l3_lattices @ X6)
% 2.04/2.29          | (v2_struct_0 @ X6))),
% 2.04/2.29      inference('cnf', [status(esa)], [d17_lattice3])).
% 2.04/2.29  thf('58', plain,
% 2.04/2.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.04/2.29         ((r3_lattice3 @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ X0)
% 2.04/2.29          | (v2_struct_0 @ sk_A)
% 2.04/2.29          | ~ (l3_lattices @ sk_A)
% 2.04/2.29          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.04/2.29          | (r1_lattices @ sk_A @ X1 @ 
% 2.04/2.29             (sk_D @ X0 @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ sk_A))
% 2.04/2.29          | ~ (r2_hidden @ X1 @ X2)
% 2.04/2.29          | ~ (r4_lattice3 @ sk_A @ 
% 2.04/2.29               (sk_D @ X0 @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ sk_A) @ X2))),
% 2.04/2.29      inference('sup-', [status(thm)], ['56', '57'])).
% 2.04/2.29  thf('59', plain, ((l3_lattices @ sk_A)),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('60', plain,
% 2.04/2.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.04/2.29         ((r3_lattice3 @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ X0)
% 2.04/2.29          | (v2_struct_0 @ sk_A)
% 2.04/2.29          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.04/2.29          | (r1_lattices @ sk_A @ X1 @ 
% 2.04/2.29             (sk_D @ X0 @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ sk_A))
% 2.04/2.29          | ~ (r2_hidden @ X1 @ X2)
% 2.04/2.29          | ~ (r4_lattice3 @ sk_A @ 
% 2.04/2.29               (sk_D @ X0 @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ sk_A) @ X2))),
% 2.04/2.29      inference('demod', [status(thm)], ['58', '59'])).
% 2.04/2.29  thf('61', plain,
% 2.04/2.29      (![X0 : $i, X1 : $i]:
% 2.04/2.29         (~ (l3_lattices @ sk_A)
% 2.04/2.29          | ~ (v4_lattice3 @ sk_A)
% 2.04/2.29          | ~ (v10_lattices @ sk_A)
% 2.04/2.29          | (v2_struct_0 @ sk_A)
% 2.04/2.29          | (r3_lattice3 @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ 
% 2.04/2.29             (a_2_2_lattice3 @ sk_A @ X0))
% 2.04/2.29          | ~ (r2_hidden @ X1 @ X0)
% 2.04/2.29          | (r1_lattices @ sk_A @ X1 @ 
% 2.04/2.29             (sk_D @ (a_2_2_lattice3 @ sk_A @ X0) @ 
% 2.04/2.29              (sk_D_4 @ sk_C @ sk_B @ sk_A) @ sk_A))
% 2.04/2.29          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.04/2.29          | (v2_struct_0 @ sk_A)
% 2.04/2.29          | (r3_lattice3 @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ 
% 2.04/2.29             (a_2_2_lattice3 @ sk_A @ X0)))),
% 2.04/2.29      inference('sup-', [status(thm)], ['49', '60'])).
% 2.04/2.29  thf('62', plain, ((l3_lattices @ sk_A)),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('63', plain, ((v4_lattice3 @ sk_A)),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('64', plain, ((v10_lattices @ sk_A)),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('65', plain,
% 2.04/2.29      (![X0 : $i, X1 : $i]:
% 2.04/2.29         ((v2_struct_0 @ sk_A)
% 2.04/2.29          | (r3_lattice3 @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ 
% 2.04/2.29             (a_2_2_lattice3 @ sk_A @ X0))
% 2.04/2.29          | ~ (r2_hidden @ X1 @ X0)
% 2.04/2.29          | (r1_lattices @ sk_A @ X1 @ 
% 2.04/2.29             (sk_D @ (a_2_2_lattice3 @ sk_A @ X0) @ 
% 2.04/2.29              (sk_D_4 @ sk_C @ sk_B @ sk_A) @ sk_A))
% 2.04/2.29          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.04/2.29          | (v2_struct_0 @ sk_A)
% 2.04/2.29          | (r3_lattice3 @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ 
% 2.04/2.29             (a_2_2_lattice3 @ sk_A @ X0)))),
% 2.04/2.29      inference('demod', [status(thm)], ['61', '62', '63', '64'])).
% 2.04/2.29  thf('66', plain,
% 2.04/2.29      (![X0 : $i, X1 : $i]:
% 2.04/2.29         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.04/2.29          | (r1_lattices @ sk_A @ X1 @ 
% 2.04/2.29             (sk_D @ (a_2_2_lattice3 @ sk_A @ X0) @ 
% 2.04/2.29              (sk_D_4 @ sk_C @ sk_B @ sk_A) @ sk_A))
% 2.04/2.29          | ~ (r2_hidden @ X1 @ X0)
% 2.04/2.29          | (r3_lattice3 @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ 
% 2.04/2.29             (a_2_2_lattice3 @ sk_A @ X0))
% 2.04/2.29          | (v2_struct_0 @ sk_A))),
% 2.04/2.29      inference('simplify', [status(thm)], ['65'])).
% 2.04/2.29  thf('67', plain,
% 2.04/2.29      (![X0 : $i]:
% 2.04/2.29         ((v2_struct_0 @ sk_A)
% 2.04/2.29          | (r3_lattice3 @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ 
% 2.04/2.29             (a_2_2_lattice3 @ sk_A @ X0))
% 2.04/2.29          | ~ (r2_hidden @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ X0)
% 2.04/2.29          | (r1_lattices @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ 
% 2.04/2.29             (sk_D @ (a_2_2_lattice3 @ sk_A @ X0) @ 
% 2.04/2.29              (sk_D_4 @ sk_C @ sk_B @ sk_A) @ sk_A)))),
% 2.04/2.29      inference('sup-', [status(thm)], ['35', '66'])).
% 2.04/2.29  thf('68', plain,
% 2.04/2.29      (((r1_lattices @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ 
% 2.04/2.29         (sk_D @ (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) @ 
% 2.04/2.29          (sk_D_4 @ sk_C @ sk_B @ sk_A) @ sk_A))
% 2.04/2.29        | (r3_lattice3 @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ 
% 2.04/2.29           (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 2.04/2.29        | (v2_struct_0 @ sk_A))),
% 2.04/2.29      inference('sup-', [status(thm)], ['34', '67'])).
% 2.04/2.29  thf('69', plain,
% 2.04/2.29      ((m1_subset_1 @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 2.04/2.29      inference('clc', [status(thm)], ['24', '25'])).
% 2.04/2.29  thf('70', plain,
% 2.04/2.29      (![X0 : $i, X1 : $i, X4 : $i]:
% 2.04/2.29         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 2.04/2.29          | ~ (r1_lattices @ X1 @ X0 @ (sk_D @ X4 @ X0 @ X1))
% 2.04/2.29          | (r3_lattice3 @ X1 @ X0 @ X4)
% 2.04/2.29          | ~ (l3_lattices @ X1)
% 2.04/2.29          | (v2_struct_0 @ X1))),
% 2.04/2.29      inference('cnf', [status(esa)], [d16_lattice3])).
% 2.04/2.29  thf('71', plain,
% 2.04/2.29      (![X0 : $i]:
% 2.04/2.29         ((v2_struct_0 @ sk_A)
% 2.04/2.29          | ~ (l3_lattices @ sk_A)
% 2.04/2.29          | (r3_lattice3 @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ X0)
% 2.04/2.29          | ~ (r1_lattices @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ 
% 2.04/2.29               (sk_D @ X0 @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ sk_A)))),
% 2.04/2.29      inference('sup-', [status(thm)], ['69', '70'])).
% 2.04/2.29  thf('72', plain, ((l3_lattices @ sk_A)),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('73', plain,
% 2.04/2.29      (![X0 : $i]:
% 2.04/2.29         ((v2_struct_0 @ sk_A)
% 2.04/2.29          | (r3_lattice3 @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ X0)
% 2.04/2.29          | ~ (r1_lattices @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ 
% 2.04/2.29               (sk_D @ X0 @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ sk_A)))),
% 2.04/2.29      inference('demod', [status(thm)], ['71', '72'])).
% 2.04/2.29  thf('74', plain, (~ (v2_struct_0 @ sk_A)),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('75', plain,
% 2.04/2.29      (![X0 : $i]:
% 2.04/2.29         (~ (r1_lattices @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ 
% 2.04/2.29             (sk_D @ X0 @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ sk_A))
% 2.04/2.29          | (r3_lattice3 @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ X0))),
% 2.04/2.29      inference('clc', [status(thm)], ['73', '74'])).
% 2.04/2.29  thf('76', plain,
% 2.04/2.29      (((v2_struct_0 @ sk_A)
% 2.04/2.29        | (r3_lattice3 @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ 
% 2.04/2.29           (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 2.04/2.29      inference('clc', [status(thm)], ['68', '75'])).
% 2.04/2.29  thf('77', plain, (~ (v2_struct_0 @ sk_A)),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('78', plain,
% 2.04/2.29      ((r3_lattice3 @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ 
% 2.04/2.29        (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))),
% 2.04/2.29      inference('clc', [status(thm)], ['76', '77'])).
% 2.04/2.29  thf('79', plain, ((r2_hidden @ sk_B @ sk_C)),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('80', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('81', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('82', plain,
% 2.04/2.29      (![X5 : $i, X6 : $i, X9 : $i]:
% 2.04/2.29         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 2.04/2.29          | (r2_hidden @ (sk_D_1 @ X9 @ X5 @ X6) @ X9)
% 2.04/2.29          | (r4_lattice3 @ X6 @ X5 @ X9)
% 2.04/2.29          | ~ (l3_lattices @ X6)
% 2.04/2.29          | (v2_struct_0 @ X6))),
% 2.04/2.29      inference('cnf', [status(esa)], [d17_lattice3])).
% 2.04/2.29  thf('83', plain,
% 2.04/2.29      (![X0 : $i]:
% 2.04/2.29         ((v2_struct_0 @ sk_A)
% 2.04/2.29          | ~ (l3_lattices @ sk_A)
% 2.04/2.29          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 2.04/2.29          | (r2_hidden @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0))),
% 2.04/2.29      inference('sup-', [status(thm)], ['81', '82'])).
% 2.04/2.29  thf('84', plain, ((l3_lattices @ sk_A)),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('85', plain,
% 2.04/2.29      (![X0 : $i]:
% 2.04/2.29         ((v2_struct_0 @ sk_A)
% 2.04/2.29          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 2.04/2.29          | (r2_hidden @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0))),
% 2.04/2.29      inference('demod', [status(thm)], ['83', '84'])).
% 2.04/2.29  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('87', plain,
% 2.04/2.29      (![X0 : $i]:
% 2.04/2.29         ((r2_hidden @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0)
% 2.04/2.29          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 2.04/2.29      inference('clc', [status(thm)], ['85', '86'])).
% 2.04/2.29  thf('88', plain,
% 2.04/2.29      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.04/2.29         (~ (l3_lattices @ X10)
% 2.04/2.29          | (v2_struct_0 @ X10)
% 2.04/2.29          | ((X12) = (sk_D_2 @ X11 @ X10 @ X12))
% 2.04/2.29          | ~ (r2_hidden @ X12 @ (a_2_1_lattice3 @ X10 @ X11)))),
% 2.04/2.29      inference('cnf', [status(esa)], [fraenkel_a_2_1_lattice3])).
% 2.04/2.29  thf('89', plain,
% 2.04/2.29      (![X0 : $i, X1 : $i]:
% 2.04/2.29         ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0))
% 2.04/2.29          | ((sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A)
% 2.04/2.29              = (sk_D_2 @ X0 @ X1 @ 
% 2.04/2.29                 (sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A)))
% 2.04/2.29          | (v2_struct_0 @ X1)
% 2.04/2.29          | ~ (l3_lattices @ X1))),
% 2.04/2.29      inference('sup-', [status(thm)], ['87', '88'])).
% 2.04/2.29  thf('90', plain,
% 2.04/2.29      (![X0 : $i]:
% 2.04/2.29         ((r2_hidden @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0)
% 2.04/2.29          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 2.04/2.29      inference('clc', [status(thm)], ['85', '86'])).
% 2.04/2.29  thf('91', plain,
% 2.04/2.29      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.04/2.29         (~ (l3_lattices @ X10)
% 2.04/2.29          | (v2_struct_0 @ X10)
% 2.04/2.29          | (r3_lattice3 @ X10 @ (sk_D_2 @ X11 @ X10 @ X12) @ X11)
% 2.04/2.29          | ~ (r2_hidden @ X12 @ (a_2_1_lattice3 @ X10 @ X11)))),
% 2.04/2.29      inference('cnf', [status(esa)], [fraenkel_a_2_1_lattice3])).
% 2.04/2.29  thf('92', plain,
% 2.04/2.29      (![X0 : $i, X1 : $i]:
% 2.04/2.29         ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0))
% 2.04/2.29          | (r3_lattice3 @ X1 @ 
% 2.04/2.29             (sk_D_2 @ X0 @ X1 @ 
% 2.04/2.29              (sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A)) @ 
% 2.04/2.29             X0)
% 2.04/2.29          | (v2_struct_0 @ X1)
% 2.04/2.29          | ~ (l3_lattices @ X1))),
% 2.04/2.29      inference('sup-', [status(thm)], ['90', '91'])).
% 2.04/2.29  thf('93', plain,
% 2.04/2.29      (![X0 : $i, X1 : $i]:
% 2.04/2.29         ((r3_lattice3 @ X1 @ 
% 2.04/2.29           (sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A) @ X0)
% 2.04/2.29          | ~ (l3_lattices @ X1)
% 2.04/2.29          | (v2_struct_0 @ X1)
% 2.04/2.29          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0))
% 2.04/2.29          | ~ (l3_lattices @ X1)
% 2.04/2.29          | (v2_struct_0 @ X1)
% 2.04/2.29          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0)))),
% 2.04/2.29      inference('sup+', [status(thm)], ['89', '92'])).
% 2.04/2.29  thf('94', plain,
% 2.04/2.29      (![X0 : $i, X1 : $i]:
% 2.04/2.29         ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0))
% 2.04/2.29          | (v2_struct_0 @ X1)
% 2.04/2.29          | ~ (l3_lattices @ X1)
% 2.04/2.29          | (r3_lattice3 @ X1 @ 
% 2.04/2.29             (sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A) @ X0))),
% 2.04/2.29      inference('simplify', [status(thm)], ['93'])).
% 2.04/2.29  thf('95', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('96', plain,
% 2.04/2.29      (![X5 : $i, X6 : $i, X9 : $i]:
% 2.04/2.29         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 2.04/2.29          | (m1_subset_1 @ (sk_D_1 @ X9 @ X5 @ X6) @ (u1_struct_0 @ X6))
% 2.04/2.29          | (r4_lattice3 @ X6 @ X5 @ X9)
% 2.04/2.29          | ~ (l3_lattices @ X6)
% 2.04/2.29          | (v2_struct_0 @ X6))),
% 2.04/2.29      inference('cnf', [status(esa)], [d17_lattice3])).
% 2.04/2.29  thf('97', plain,
% 2.04/2.29      (![X0 : $i]:
% 2.04/2.29         ((v2_struct_0 @ sk_A)
% 2.04/2.29          | ~ (l3_lattices @ sk_A)
% 2.04/2.29          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 2.04/2.29          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.04/2.29      inference('sup-', [status(thm)], ['95', '96'])).
% 2.04/2.29  thf('98', plain, ((l3_lattices @ sk_A)),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('99', plain,
% 2.04/2.29      (![X0 : $i]:
% 2.04/2.29         ((v2_struct_0 @ sk_A)
% 2.04/2.29          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 2.04/2.29          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.04/2.29      inference('demod', [status(thm)], ['97', '98'])).
% 2.04/2.29  thf('100', plain, (~ (v2_struct_0 @ sk_A)),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('101', plain,
% 2.04/2.29      (![X0 : $i]:
% 2.04/2.29         ((m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.29          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 2.04/2.29      inference('clc', [status(thm)], ['99', '100'])).
% 2.04/2.29  thf('102', plain,
% 2.04/2.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.04/2.29         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 2.04/2.29          | ~ (r3_lattice3 @ X1 @ X0 @ X2)
% 2.04/2.29          | ~ (r2_hidden @ X3 @ X2)
% 2.04/2.29          | (r1_lattices @ X1 @ X0 @ X3)
% 2.04/2.29          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 2.04/2.29          | ~ (l3_lattices @ X1)
% 2.04/2.29          | (v2_struct_0 @ X1))),
% 2.04/2.29      inference('cnf', [status(esa)], [d16_lattice3])).
% 2.04/2.29  thf('103', plain,
% 2.04/2.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.04/2.29         ((r4_lattice3 @ sk_A @ sk_B @ X0)
% 2.04/2.29          | (v2_struct_0 @ sk_A)
% 2.04/2.29          | ~ (l3_lattices @ sk_A)
% 2.04/2.29          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.04/2.29          | (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X1)
% 2.04/2.29          | ~ (r2_hidden @ X1 @ X2)
% 2.04/2.29          | ~ (r3_lattice3 @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X2))),
% 2.04/2.29      inference('sup-', [status(thm)], ['101', '102'])).
% 2.04/2.29  thf('104', plain, ((l3_lattices @ sk_A)),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('105', plain,
% 2.04/2.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.04/2.29         ((r4_lattice3 @ sk_A @ sk_B @ X0)
% 2.04/2.29          | (v2_struct_0 @ sk_A)
% 2.04/2.29          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.04/2.29          | (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X1)
% 2.04/2.29          | ~ (r2_hidden @ X1 @ X2)
% 2.04/2.29          | ~ (r3_lattice3 @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X2))),
% 2.04/2.29      inference('demod', [status(thm)], ['103', '104'])).
% 2.04/2.29  thf('106', plain,
% 2.04/2.29      (![X0 : $i, X1 : $i]:
% 2.04/2.29         (~ (l3_lattices @ sk_A)
% 2.04/2.29          | (v2_struct_0 @ sk_A)
% 2.04/2.29          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 2.04/2.29          | ~ (r2_hidden @ X1 @ X0)
% 2.04/2.29          | (r1_lattices @ sk_A @ 
% 2.04/2.29             (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ X0) @ sk_B @ sk_A) @ X1)
% 2.04/2.29          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.04/2.29          | (v2_struct_0 @ sk_A)
% 2.04/2.29          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0)))),
% 2.04/2.29      inference('sup-', [status(thm)], ['94', '105'])).
% 2.04/2.29  thf('107', plain, ((l3_lattices @ sk_A)),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('108', plain,
% 2.04/2.29      (![X0 : $i, X1 : $i]:
% 2.04/2.29         ((v2_struct_0 @ sk_A)
% 2.04/2.29          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 2.04/2.29          | ~ (r2_hidden @ X1 @ X0)
% 2.04/2.29          | (r1_lattices @ sk_A @ 
% 2.04/2.29             (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ X0) @ sk_B @ sk_A) @ X1)
% 2.04/2.29          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.04/2.29          | (v2_struct_0 @ sk_A)
% 2.04/2.29          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0)))),
% 2.04/2.29      inference('demod', [status(thm)], ['106', '107'])).
% 2.04/2.29  thf('109', plain,
% 2.04/2.29      (![X0 : $i, X1 : $i]:
% 2.04/2.29         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.04/2.29          | (r1_lattices @ sk_A @ 
% 2.04/2.29             (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ X0) @ sk_B @ sk_A) @ X1)
% 2.04/2.29          | ~ (r2_hidden @ X1 @ X0)
% 2.04/2.29          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 2.04/2.29          | (v2_struct_0 @ sk_A))),
% 2.04/2.29      inference('simplify', [status(thm)], ['108'])).
% 2.04/2.29  thf('110', plain,
% 2.04/2.29      (![X0 : $i]:
% 2.04/2.29         ((v2_struct_0 @ sk_A)
% 2.04/2.29          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 2.04/2.29          | ~ (r2_hidden @ sk_B @ X0)
% 2.04/2.29          | (r1_lattices @ sk_A @ 
% 2.04/2.29             (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ X0) @ sk_B @ sk_A) @ sk_B))),
% 2.04/2.29      inference('sup-', [status(thm)], ['80', '109'])).
% 2.04/2.29  thf('111', plain,
% 2.04/2.29      (((r1_lattices @ sk_A @ 
% 2.04/2.29         (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_B @ sk_A) @ sk_B)
% 2.04/2.29        | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))
% 2.04/2.29        | (v2_struct_0 @ sk_A))),
% 2.04/2.29      inference('sup-', [status(thm)], ['79', '110'])).
% 2.04/2.29  thf('112', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('113', plain,
% 2.04/2.29      (![X5 : $i, X6 : $i, X9 : $i]:
% 2.04/2.29         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 2.04/2.29          | ~ (r1_lattices @ X6 @ (sk_D_1 @ X9 @ X5 @ X6) @ X5)
% 2.04/2.29          | (r4_lattice3 @ X6 @ X5 @ X9)
% 2.04/2.29          | ~ (l3_lattices @ X6)
% 2.04/2.29          | (v2_struct_0 @ X6))),
% 2.04/2.29      inference('cnf', [status(esa)], [d17_lattice3])).
% 2.04/2.29  thf('114', plain,
% 2.04/2.29      (![X0 : $i]:
% 2.04/2.29         ((v2_struct_0 @ sk_A)
% 2.04/2.29          | ~ (l3_lattices @ sk_A)
% 2.04/2.29          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 2.04/2.29          | ~ (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_B))),
% 2.04/2.29      inference('sup-', [status(thm)], ['112', '113'])).
% 2.04/2.29  thf('115', plain, ((l3_lattices @ sk_A)),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('116', plain,
% 2.04/2.29      (![X0 : $i]:
% 2.04/2.29         ((v2_struct_0 @ sk_A)
% 2.04/2.29          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 2.04/2.29          | ~ (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_B))),
% 2.04/2.29      inference('demod', [status(thm)], ['114', '115'])).
% 2.04/2.29  thf('117', plain, (~ (v2_struct_0 @ sk_A)),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('118', plain,
% 2.04/2.29      (![X0 : $i]:
% 2.04/2.29         (~ (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_B)
% 2.04/2.29          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 2.04/2.29      inference('clc', [status(thm)], ['116', '117'])).
% 2.04/2.29  thf('119', plain,
% 2.04/2.29      (((v2_struct_0 @ sk_A)
% 2.04/2.29        | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C)))),
% 2.04/2.29      inference('clc', [status(thm)], ['111', '118'])).
% 2.04/2.29  thf('120', plain, (~ (v2_struct_0 @ sk_A)),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('121', plain,
% 2.04/2.29      ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))),
% 2.04/2.29      inference('clc', [status(thm)], ['119', '120'])).
% 2.04/2.29  thf('122', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf(t41_lattice3, axiom,
% 2.04/2.29    (![A:$i]:
% 2.04/2.29     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.04/2.29         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 2.04/2.29       ( ![B:$i]:
% 2.04/2.29         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.04/2.29           ( ![C:$i]:
% 2.04/2.29             ( ( ( r2_hidden @ B @ C ) & ( r4_lattice3 @ A @ B @ C ) ) =>
% 2.04/2.29               ( ( k15_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ))).
% 2.04/2.29  thf('123', plain,
% 2.04/2.29      (![X25 : $i, X26 : $i, X27 : $i]:
% 2.04/2.29         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X26))
% 2.04/2.29          | ((k15_lattice3 @ X26 @ X27) = (X25))
% 2.04/2.29          | ~ (r4_lattice3 @ X26 @ X25 @ X27)
% 2.04/2.29          | ~ (r2_hidden @ X25 @ X27)
% 2.04/2.29          | ~ (l3_lattices @ X26)
% 2.04/2.29          | ~ (v4_lattice3 @ X26)
% 2.04/2.29          | ~ (v10_lattices @ X26)
% 2.04/2.29          | (v2_struct_0 @ X26))),
% 2.04/2.29      inference('cnf', [status(esa)], [t41_lattice3])).
% 2.04/2.29  thf('124', plain,
% 2.04/2.29      (![X0 : $i]:
% 2.04/2.29         ((v2_struct_0 @ sk_A)
% 2.04/2.29          | ~ (v10_lattices @ sk_A)
% 2.04/2.29          | ~ (v4_lattice3 @ sk_A)
% 2.04/2.29          | ~ (l3_lattices @ sk_A)
% 2.04/2.29          | ~ (r2_hidden @ sk_B @ X0)
% 2.04/2.29          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0)
% 2.04/2.29          | ((k15_lattice3 @ sk_A @ X0) = (sk_B)))),
% 2.04/2.29      inference('sup-', [status(thm)], ['122', '123'])).
% 2.04/2.29  thf('125', plain, ((v10_lattices @ sk_A)),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('126', plain, ((v4_lattice3 @ sk_A)),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('127', plain, ((l3_lattices @ sk_A)),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('128', plain,
% 2.04/2.29      (![X0 : $i]:
% 2.04/2.29         ((v2_struct_0 @ sk_A)
% 2.04/2.29          | ~ (r2_hidden @ sk_B @ X0)
% 2.04/2.29          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0)
% 2.04/2.29          | ((k15_lattice3 @ sk_A @ X0) = (sk_B)))),
% 2.04/2.29      inference('demod', [status(thm)], ['124', '125', '126', '127'])).
% 2.04/2.29  thf('129', plain,
% 2.04/2.29      ((((k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) = (sk_B))
% 2.04/2.29        | ~ (r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))
% 2.04/2.29        | (v2_struct_0 @ sk_A))),
% 2.04/2.29      inference('sup-', [status(thm)], ['121', '128'])).
% 2.04/2.29  thf('130', plain, ((r3_lattice3 @ sk_A @ sk_B @ sk_C)),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('131', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('132', plain,
% 2.04/2.29      (![X10 : $i, X11 : $i, X13 : $i]:
% 2.04/2.29         (~ (r3_lattice3 @ X10 @ X13 @ X11)
% 2.04/2.29          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X10))
% 2.04/2.29          | (r2_hidden @ X13 @ (a_2_1_lattice3 @ X10 @ X11))
% 2.04/2.29          | (v2_struct_0 @ X10)
% 2.04/2.29          | ~ (l3_lattices @ X10))),
% 2.04/2.29      inference('simplify', [status(thm)], ['27'])).
% 2.04/2.29  thf('133', plain,
% 2.04/2.29      (![X0 : $i]:
% 2.04/2.29         (~ (l3_lattices @ sk_A)
% 2.04/2.29          | (v2_struct_0 @ sk_A)
% 2.04/2.29          | (r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 2.04/2.29          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 2.04/2.29      inference('sup-', [status(thm)], ['131', '132'])).
% 2.04/2.29  thf('134', plain, ((l3_lattices @ sk_A)),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('135', plain,
% 2.04/2.29      (![X0 : $i]:
% 2.04/2.29         ((v2_struct_0 @ sk_A)
% 2.04/2.29          | (r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 2.04/2.29          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 2.04/2.29      inference('demod', [status(thm)], ['133', '134'])).
% 2.04/2.29  thf('136', plain, (~ (v2_struct_0 @ sk_A)),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('137', plain,
% 2.04/2.29      (![X0 : $i]:
% 2.04/2.29         (~ (r3_lattice3 @ sk_A @ sk_B @ X0)
% 2.04/2.29          | (r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0)))),
% 2.04/2.29      inference('clc', [status(thm)], ['135', '136'])).
% 2.04/2.29  thf('138', plain, ((r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))),
% 2.04/2.29      inference('sup-', [status(thm)], ['130', '137'])).
% 2.04/2.29  thf('139', plain,
% 2.04/2.29      ((((k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) = (sk_B))
% 2.04/2.29        | (v2_struct_0 @ sk_A))),
% 2.04/2.29      inference('demod', [status(thm)], ['129', '138'])).
% 2.04/2.29  thf('140', plain, (~ (v2_struct_0 @ sk_A)),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('141', plain,
% 2.04/2.29      (((k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) = (sk_B))),
% 2.04/2.29      inference('clc', [status(thm)], ['139', '140'])).
% 2.04/2.29  thf(t37_lattice3, axiom,
% 2.04/2.29    (![A:$i]:
% 2.04/2.29     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.04/2.29         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 2.04/2.29       ( ![B:$i]:
% 2.04/2.29         ( ( k15_lattice3 @ A @ B ) =
% 2.04/2.29           ( k16_lattice3 @ A @ ( a_2_2_lattice3 @ A @ B ) ) ) ) ))).
% 2.04/2.29  thf('142', plain,
% 2.04/2.29      (![X23 : $i, X24 : $i]:
% 2.04/2.29         (((k15_lattice3 @ X23 @ X24)
% 2.04/2.29            = (k16_lattice3 @ X23 @ (a_2_2_lattice3 @ X23 @ X24)))
% 2.04/2.29          | ~ (l3_lattices @ X23)
% 2.04/2.29          | ~ (v4_lattice3 @ X23)
% 2.04/2.29          | ~ (v10_lattices @ X23)
% 2.04/2.29          | (v2_struct_0 @ X23))),
% 2.04/2.29      inference('cnf', [status(esa)], [t37_lattice3])).
% 2.04/2.29  thf('143', plain,
% 2.04/2.29      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 2.04/2.29         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 2.04/2.29          | ((X18) != (k16_lattice3 @ X19 @ X20))
% 2.04/2.29          | ~ (r3_lattice3 @ X19 @ X21 @ X20)
% 2.04/2.29          | (r3_lattices @ X19 @ X21 @ X18)
% 2.04/2.29          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X19))
% 2.04/2.29          | ~ (l3_lattices @ X19)
% 2.04/2.29          | ~ (v4_lattice3 @ X19)
% 2.04/2.29          | ~ (v10_lattices @ X19)
% 2.04/2.29          | (v2_struct_0 @ X19))),
% 2.04/2.29      inference('cnf', [status(esa)], [t34_lattice3])).
% 2.04/2.29  thf('144', plain,
% 2.04/2.29      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.04/2.29         ((v2_struct_0 @ X19)
% 2.04/2.29          | ~ (v10_lattices @ X19)
% 2.04/2.29          | ~ (v4_lattice3 @ X19)
% 2.04/2.29          | ~ (l3_lattices @ X19)
% 2.04/2.29          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X19))
% 2.04/2.29          | (r3_lattices @ X19 @ X21 @ (k16_lattice3 @ X19 @ X20))
% 2.04/2.29          | ~ (r3_lattice3 @ X19 @ X21 @ X20)
% 2.04/2.29          | ~ (m1_subset_1 @ (k16_lattice3 @ X19 @ X20) @ (u1_struct_0 @ X19)))),
% 2.04/2.29      inference('simplify', [status(thm)], ['143'])).
% 2.04/2.29  thf('145', plain,
% 2.04/2.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.04/2.29         (~ (m1_subset_1 @ (k15_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1))
% 2.04/2.29          | (v2_struct_0 @ X1)
% 2.04/2.29          | ~ (v10_lattices @ X1)
% 2.04/2.29          | ~ (v4_lattice3 @ X1)
% 2.04/2.29          | ~ (l3_lattices @ X1)
% 2.04/2.29          | ~ (r3_lattice3 @ X1 @ X2 @ (a_2_2_lattice3 @ X1 @ X0))
% 2.04/2.29          | (r3_lattices @ X1 @ X2 @ 
% 2.04/2.29             (k16_lattice3 @ X1 @ (a_2_2_lattice3 @ X1 @ X0)))
% 2.04/2.29          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 2.04/2.29          | ~ (l3_lattices @ X1)
% 2.04/2.29          | ~ (v4_lattice3 @ X1)
% 2.04/2.29          | ~ (v10_lattices @ X1)
% 2.04/2.29          | (v2_struct_0 @ X1))),
% 2.04/2.29      inference('sup-', [status(thm)], ['142', '144'])).
% 2.04/2.29  thf('146', plain,
% 2.04/2.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.04/2.29         (~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 2.04/2.29          | (r3_lattices @ X1 @ X2 @ 
% 2.04/2.29             (k16_lattice3 @ X1 @ (a_2_2_lattice3 @ X1 @ X0)))
% 2.04/2.29          | ~ (r3_lattice3 @ X1 @ X2 @ (a_2_2_lattice3 @ X1 @ X0))
% 2.04/2.29          | ~ (l3_lattices @ X1)
% 2.04/2.29          | ~ (v4_lattice3 @ X1)
% 2.04/2.29          | ~ (v10_lattices @ X1)
% 2.04/2.29          | (v2_struct_0 @ X1)
% 2.04/2.29          | ~ (m1_subset_1 @ (k15_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1)))),
% 2.04/2.29      inference('simplify', [status(thm)], ['145'])).
% 2.04/2.29  thf('147', plain,
% 2.04/2.29      (![X0 : $i]:
% 2.04/2.29         (~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 2.04/2.29          | (v2_struct_0 @ sk_A)
% 2.04/2.29          | ~ (v10_lattices @ sk_A)
% 2.04/2.29          | ~ (v4_lattice3 @ sk_A)
% 2.04/2.29          | ~ (l3_lattices @ sk_A)
% 2.04/2.29          | ~ (r3_lattice3 @ sk_A @ X0 @ 
% 2.04/2.29               (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 2.04/2.29          | (r3_lattices @ sk_A @ X0 @ 
% 2.04/2.29             (k16_lattice3 @ sk_A @ 
% 2.04/2.29              (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))
% 2.04/2.29          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 2.04/2.29      inference('sup-', [status(thm)], ['141', '146'])).
% 2.04/2.29  thf('148', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('149', plain, ((v10_lattices @ sk_A)),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('150', plain, ((v4_lattice3 @ sk_A)),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('151', plain, ((l3_lattices @ sk_A)),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('152', plain,
% 2.04/2.29      (![X0 : $i]:
% 2.04/2.29         ((v2_struct_0 @ sk_A)
% 2.04/2.29          | ~ (r3_lattice3 @ sk_A @ X0 @ 
% 2.04/2.29               (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 2.04/2.29          | (r3_lattices @ sk_A @ X0 @ 
% 2.04/2.29             (k16_lattice3 @ sk_A @ 
% 2.04/2.29              (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))
% 2.04/2.29          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 2.04/2.29      inference('demod', [status(thm)], ['147', '148', '149', '150', '151'])).
% 2.04/2.29  thf('153', plain,
% 2.04/2.29      (![X23 : $i, X24 : $i]:
% 2.04/2.29         (((k15_lattice3 @ X23 @ X24)
% 2.04/2.29            = (k16_lattice3 @ X23 @ (a_2_2_lattice3 @ X23 @ X24)))
% 2.04/2.29          | ~ (l3_lattices @ X23)
% 2.04/2.29          | ~ (v4_lattice3 @ X23)
% 2.04/2.29          | ~ (v10_lattices @ X23)
% 2.04/2.29          | (v2_struct_0 @ X23))),
% 2.04/2.29      inference('cnf', [status(esa)], [t37_lattice3])).
% 2.04/2.29  thf('154', plain,
% 2.04/2.29      (![X23 : $i, X24 : $i]:
% 2.04/2.29         (((k15_lattice3 @ X23 @ X24)
% 2.04/2.29            = (k16_lattice3 @ X23 @ (a_2_2_lattice3 @ X23 @ X24)))
% 2.04/2.29          | ~ (l3_lattices @ X23)
% 2.04/2.29          | ~ (v4_lattice3 @ X23)
% 2.04/2.29          | ~ (v10_lattices @ X23)
% 2.04/2.29          | (v2_struct_0 @ X23))),
% 2.04/2.29      inference('cnf', [status(esa)], [t37_lattice3])).
% 2.04/2.29  thf('155', plain,
% 2.04/2.29      (((k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) = (sk_B))),
% 2.04/2.29      inference('clc', [status(thm)], ['139', '140'])).
% 2.04/2.29  thf('156', plain,
% 2.04/2.29      (![X23 : $i, X24 : $i]:
% 2.04/2.29         (((k15_lattice3 @ X23 @ X24)
% 2.04/2.29            = (k16_lattice3 @ X23 @ (a_2_2_lattice3 @ X23 @ X24)))
% 2.04/2.29          | ~ (l3_lattices @ X23)
% 2.04/2.29          | ~ (v4_lattice3 @ X23)
% 2.04/2.29          | ~ (v10_lattices @ X23)
% 2.04/2.29          | (v2_struct_0 @ X23))),
% 2.04/2.29      inference('cnf', [status(esa)], [t37_lattice3])).
% 2.04/2.29  thf('157', plain,
% 2.04/2.29      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.04/2.29         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 2.04/2.29          | ((X18) != (k16_lattice3 @ X19 @ X20))
% 2.04/2.29          | (r3_lattice3 @ X19 @ X18 @ X20)
% 2.04/2.29          | ~ (l3_lattices @ X19)
% 2.04/2.29          | ~ (v4_lattice3 @ X19)
% 2.04/2.29          | ~ (v10_lattices @ X19)
% 2.04/2.29          | (v2_struct_0 @ X19))),
% 2.04/2.29      inference('cnf', [status(esa)], [t34_lattice3])).
% 2.04/2.29  thf('158', plain,
% 2.04/2.29      (![X19 : $i, X20 : $i]:
% 2.04/2.29         ((v2_struct_0 @ X19)
% 2.04/2.29          | ~ (v10_lattices @ X19)
% 2.04/2.29          | ~ (v4_lattice3 @ X19)
% 2.04/2.29          | ~ (l3_lattices @ X19)
% 2.04/2.29          | (r3_lattice3 @ X19 @ (k16_lattice3 @ X19 @ X20) @ X20)
% 2.04/2.29          | ~ (m1_subset_1 @ (k16_lattice3 @ X19 @ X20) @ (u1_struct_0 @ X19)))),
% 2.04/2.29      inference('simplify', [status(thm)], ['157'])).
% 2.04/2.29  thf('159', plain,
% 2.04/2.29      (![X0 : $i, X1 : $i]:
% 2.04/2.29         (~ (m1_subset_1 @ (k15_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1))
% 2.04/2.29          | (v2_struct_0 @ X1)
% 2.04/2.29          | ~ (v10_lattices @ X1)
% 2.04/2.29          | ~ (v4_lattice3 @ X1)
% 2.04/2.29          | ~ (l3_lattices @ X1)
% 2.04/2.29          | (r3_lattice3 @ X1 @ 
% 2.04/2.29             (k16_lattice3 @ X1 @ (a_2_2_lattice3 @ X1 @ X0)) @ 
% 2.04/2.29             (a_2_2_lattice3 @ X1 @ X0))
% 2.04/2.29          | ~ (l3_lattices @ X1)
% 2.04/2.29          | ~ (v4_lattice3 @ X1)
% 2.04/2.29          | ~ (v10_lattices @ X1)
% 2.04/2.29          | (v2_struct_0 @ X1))),
% 2.04/2.29      inference('sup-', [status(thm)], ['156', '158'])).
% 2.04/2.29  thf('160', plain,
% 2.04/2.29      (![X0 : $i, X1 : $i]:
% 2.04/2.29         ((r3_lattice3 @ X1 @ 
% 2.04/2.29           (k16_lattice3 @ X1 @ (a_2_2_lattice3 @ X1 @ X0)) @ 
% 2.04/2.29           (a_2_2_lattice3 @ X1 @ X0))
% 2.04/2.29          | ~ (l3_lattices @ X1)
% 2.04/2.29          | ~ (v4_lattice3 @ X1)
% 2.04/2.29          | ~ (v10_lattices @ X1)
% 2.04/2.29          | (v2_struct_0 @ X1)
% 2.04/2.29          | ~ (m1_subset_1 @ (k15_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1)))),
% 2.04/2.29      inference('simplify', [status(thm)], ['159'])).
% 2.04/2.29  thf('161', plain,
% 2.04/2.29      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 2.04/2.29        | (v2_struct_0 @ sk_A)
% 2.04/2.29        | ~ (v10_lattices @ sk_A)
% 2.04/2.29        | ~ (v4_lattice3 @ sk_A)
% 2.04/2.29        | ~ (l3_lattices @ sk_A)
% 2.04/2.29        | (r3_lattice3 @ sk_A @ 
% 2.04/2.29           (k16_lattice3 @ sk_A @ 
% 2.04/2.29            (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))) @ 
% 2.04/2.29           (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 2.04/2.29      inference('sup-', [status(thm)], ['155', '160'])).
% 2.04/2.29  thf('162', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('163', plain, ((v10_lattices @ sk_A)),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('164', plain, ((v4_lattice3 @ sk_A)),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('165', plain, ((l3_lattices @ sk_A)),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('166', plain,
% 2.04/2.29      (((v2_struct_0 @ sk_A)
% 2.04/2.29        | (r3_lattice3 @ sk_A @ 
% 2.04/2.29           (k16_lattice3 @ sk_A @ 
% 2.04/2.29            (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))) @ 
% 2.04/2.29           (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 2.04/2.29      inference('demod', [status(thm)], ['161', '162', '163', '164', '165'])).
% 2.04/2.29  thf('167', plain, (~ (v2_struct_0 @ sk_A)),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('168', plain,
% 2.04/2.29      ((r3_lattice3 @ sk_A @ 
% 2.04/2.29        (k16_lattice3 @ sk_A @ 
% 2.04/2.29         (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))) @ 
% 2.04/2.29        (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))),
% 2.04/2.29      inference('clc', [status(thm)], ['166', '167'])).
% 2.04/2.29  thf('169', plain,
% 2.04/2.29      (((r3_lattice3 @ sk_A @ 
% 2.04/2.29         (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) @ 
% 2.04/2.29         (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 2.04/2.29        | (v2_struct_0 @ sk_A)
% 2.04/2.29        | ~ (v10_lattices @ sk_A)
% 2.04/2.29        | ~ (v4_lattice3 @ sk_A)
% 2.04/2.29        | ~ (l3_lattices @ sk_A))),
% 2.04/2.29      inference('sup+', [status(thm)], ['154', '168'])).
% 2.04/2.29  thf('170', plain,
% 2.04/2.29      (((k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) = (sk_B))),
% 2.04/2.29      inference('clc', [status(thm)], ['139', '140'])).
% 2.04/2.29  thf('171', plain, ((v10_lattices @ sk_A)),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('172', plain, ((v4_lattice3 @ sk_A)),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('173', plain, ((l3_lattices @ sk_A)),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('174', plain,
% 2.04/2.29      (((r3_lattice3 @ sk_A @ sk_B @ 
% 2.04/2.29         (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 2.04/2.29        | (v2_struct_0 @ sk_A))),
% 2.04/2.29      inference('demod', [status(thm)], ['169', '170', '171', '172', '173'])).
% 2.04/2.29  thf('175', plain, (~ (v2_struct_0 @ sk_A)),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('176', plain,
% 2.04/2.29      ((r3_lattice3 @ sk_A @ sk_B @ 
% 2.04/2.29        (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))),
% 2.04/2.29      inference('clc', [status(thm)], ['174', '175'])).
% 2.04/2.29  thf('177', plain,
% 2.04/2.29      (![X0 : $i]:
% 2.04/2.29         ((v2_struct_0 @ sk_A)
% 2.04/2.29          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 2.04/2.29          | (m1_subset_1 @ (sk_D_4 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.29          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 2.04/2.29      inference('demod', [status(thm)], ['17', '18', '19', '20'])).
% 2.04/2.29  thf('178', plain,
% 2.04/2.29      (((m1_subset_1 @ 
% 2.04/2.29         (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) @ 
% 2.04/2.29          sk_B @ sk_A) @ 
% 2.04/2.29         (u1_struct_0 @ sk_A))
% 2.04/2.29        | ((sk_B)
% 2.04/2.29            = (k16_lattice3 @ sk_A @ 
% 2.04/2.29               (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))
% 2.04/2.29        | (v2_struct_0 @ sk_A))),
% 2.04/2.29      inference('sup-', [status(thm)], ['176', '177'])).
% 2.04/2.29  thf('179', plain, (~ (v2_struct_0 @ sk_A)),
% 2.04/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.29  thf('180', plain,
% 2.04/2.29      ((((sk_B)
% 2.04/2.29          = (k16_lattice3 @ sk_A @ 
% 2.04/2.29             (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))
% 2.12/2.29        | (m1_subset_1 @ 
% 2.12/2.29           (sk_D_4 @ 
% 2.12/2.29            (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) @ sk_B @ 
% 2.12/2.29            sk_A) @ 
% 2.12/2.29           (u1_struct_0 @ sk_A)))),
% 2.12/2.29      inference('clc', [status(thm)], ['178', '179'])).
% 2.12/2.29  thf('181', plain,
% 2.12/2.29      ((r3_lattice3 @ sk_A @ sk_B @ 
% 2.12/2.29        (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))),
% 2.12/2.29      inference('clc', [status(thm)], ['174', '175'])).
% 2.12/2.29  thf('182', plain,
% 2.12/2.29      (![X0 : $i]:
% 2.12/2.29         ((v2_struct_0 @ sk_A)
% 2.12/2.29          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 2.12/2.29          | (r3_lattice3 @ sk_A @ (sk_D_4 @ X0 @ sk_B @ sk_A) @ X0)
% 2.12/2.29          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 2.12/2.29      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 2.12/2.29  thf('183', plain,
% 2.12/2.29      (((r3_lattice3 @ sk_A @ 
% 2.12/2.29         (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) @ 
% 2.12/2.29          sk_B @ sk_A) @ 
% 2.12/2.29         (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 2.12/2.29        | ((sk_B)
% 2.12/2.29            = (k16_lattice3 @ sk_A @ 
% 2.12/2.29               (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))
% 2.12/2.29        | (v2_struct_0 @ sk_A))),
% 2.12/2.29      inference('sup-', [status(thm)], ['181', '182'])).
% 2.12/2.29  thf('184', plain, (~ (v2_struct_0 @ sk_A)),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf('185', plain,
% 2.12/2.29      ((((sk_B)
% 2.12/2.29          = (k16_lattice3 @ sk_A @ 
% 2.12/2.29             (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))
% 2.12/2.29        | (r3_lattice3 @ sk_A @ 
% 2.12/2.29           (sk_D_4 @ 
% 2.12/2.29            (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) @ sk_B @ 
% 2.12/2.29            sk_A) @ 
% 2.12/2.29           (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 2.12/2.29      inference('clc', [status(thm)], ['183', '184'])).
% 2.12/2.29  thf('186', plain,
% 2.12/2.29      (![X0 : $i]:
% 2.12/2.29         ((v2_struct_0 @ sk_A)
% 2.12/2.29          | ~ (r3_lattice3 @ sk_A @ X0 @ 
% 2.12/2.29               (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 2.12/2.29          | (r3_lattices @ sk_A @ X0 @ 
% 2.12/2.29             (k16_lattice3 @ sk_A @ 
% 2.12/2.29              (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))
% 2.12/2.29          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 2.12/2.29      inference('demod', [status(thm)], ['147', '148', '149', '150', '151'])).
% 2.12/2.29  thf('187', plain,
% 2.12/2.29      ((((sk_B)
% 2.12/2.29          = (k16_lattice3 @ sk_A @ 
% 2.12/2.29             (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))
% 2.12/2.29        | ~ (m1_subset_1 @ 
% 2.12/2.29             (sk_D_4 @ 
% 2.12/2.29              (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) @ 
% 2.12/2.29              sk_B @ sk_A) @ 
% 2.12/2.29             (u1_struct_0 @ sk_A))
% 2.12/2.29        | (r3_lattices @ sk_A @ 
% 2.12/2.29           (sk_D_4 @ 
% 2.12/2.29            (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) @ sk_B @ 
% 2.12/2.29            sk_A) @ 
% 2.12/2.29           (k16_lattice3 @ sk_A @ 
% 2.12/2.29            (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))
% 2.12/2.29        | (v2_struct_0 @ sk_A))),
% 2.12/2.29      inference('sup-', [status(thm)], ['185', '186'])).
% 2.12/2.29  thf('188', plain,
% 2.12/2.29      ((((sk_B)
% 2.12/2.29          = (k16_lattice3 @ sk_A @ 
% 2.12/2.29             (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))
% 2.12/2.29        | (v2_struct_0 @ sk_A)
% 2.12/2.29        | (r3_lattices @ sk_A @ 
% 2.12/2.29           (sk_D_4 @ 
% 2.12/2.29            (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) @ sk_B @ 
% 2.12/2.29            sk_A) @ 
% 2.12/2.29           (k16_lattice3 @ sk_A @ 
% 2.12/2.29            (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))
% 2.12/2.29        | ((sk_B)
% 2.12/2.29            = (k16_lattice3 @ sk_A @ 
% 2.12/2.29               (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))))),
% 2.12/2.29      inference('sup-', [status(thm)], ['180', '187'])).
% 2.12/2.29  thf('189', plain,
% 2.12/2.29      (((r3_lattices @ sk_A @ 
% 2.12/2.29         (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) @ 
% 2.12/2.29          sk_B @ sk_A) @ 
% 2.12/2.29         (k16_lattice3 @ sk_A @ 
% 2.12/2.29          (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))
% 2.12/2.29        | (v2_struct_0 @ sk_A)
% 2.12/2.29        | ((sk_B)
% 2.12/2.29            = (k16_lattice3 @ sk_A @ 
% 2.12/2.29               (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))))),
% 2.12/2.29      inference('simplify', [status(thm)], ['188'])).
% 2.12/2.29  thf('190', plain, (~ (v2_struct_0 @ sk_A)),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf('191', plain,
% 2.12/2.29      ((((sk_B)
% 2.12/2.29          = (k16_lattice3 @ sk_A @ 
% 2.12/2.29             (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))
% 2.12/2.29        | (r3_lattices @ sk_A @ 
% 2.12/2.29           (sk_D_4 @ 
% 2.12/2.29            (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) @ sk_B @ 
% 2.12/2.29            sk_A) @ 
% 2.12/2.29           (k16_lattice3 @ sk_A @ 
% 2.12/2.29            (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))))),
% 2.12/2.29      inference('clc', [status(thm)], ['189', '190'])).
% 2.12/2.29  thf('192', plain,
% 2.12/2.29      (((r3_lattices @ sk_A @ 
% 2.12/2.29         (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) @ 
% 2.12/2.29          sk_B @ sk_A) @ 
% 2.12/2.29         (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 2.12/2.29        | (v2_struct_0 @ sk_A)
% 2.12/2.29        | ~ (v10_lattices @ sk_A)
% 2.12/2.29        | ~ (v4_lattice3 @ sk_A)
% 2.12/2.29        | ~ (l3_lattices @ sk_A)
% 2.12/2.29        | ((sk_B)
% 2.12/2.29            = (k16_lattice3 @ sk_A @ 
% 2.12/2.29               (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))))),
% 2.12/2.29      inference('sup+', [status(thm)], ['153', '191'])).
% 2.12/2.29  thf('193', plain,
% 2.12/2.29      (((k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) = (sk_B))),
% 2.12/2.29      inference('clc', [status(thm)], ['139', '140'])).
% 2.12/2.29  thf('194', plain, ((v10_lattices @ sk_A)),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf('195', plain, ((v4_lattice3 @ sk_A)),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf('196', plain, ((l3_lattices @ sk_A)),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf('197', plain,
% 2.12/2.29      (((r3_lattices @ sk_A @ 
% 2.12/2.29         (sk_D_4 @ (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) @ 
% 2.12/2.29          sk_B @ sk_A) @ 
% 2.12/2.29         sk_B)
% 2.12/2.29        | (v2_struct_0 @ sk_A)
% 2.12/2.29        | ((sk_B)
% 2.12/2.29            = (k16_lattice3 @ sk_A @ 
% 2.12/2.29               (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))))),
% 2.12/2.29      inference('demod', [status(thm)], ['192', '193', '194', '195', '196'])).
% 2.12/2.29  thf('198', plain, (~ (v2_struct_0 @ sk_A)),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf('199', plain,
% 2.12/2.29      ((((sk_B)
% 2.12/2.29          = (k16_lattice3 @ sk_A @ 
% 2.12/2.29             (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))
% 2.12/2.29        | (r3_lattices @ sk_A @ 
% 2.12/2.29           (sk_D_4 @ 
% 2.12/2.29            (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) @ sk_B @ 
% 2.12/2.29            sk_A) @ 
% 2.12/2.29           sk_B))),
% 2.12/2.29      inference('clc', [status(thm)], ['197', '198'])).
% 2.12/2.29  thf('200', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf('201', plain,
% 2.12/2.29      (![X18 : $i, X19 : $i, X22 : $i]:
% 2.12/2.29         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 2.12/2.29          | ~ (r3_lattice3 @ X19 @ X18 @ X22)
% 2.12/2.29          | ~ (r3_lattices @ X19 @ (sk_D_4 @ X22 @ X18 @ X19) @ X18)
% 2.12/2.29          | ((X18) = (k16_lattice3 @ X19 @ X22))
% 2.12/2.29          | ~ (l3_lattices @ X19)
% 2.12/2.29          | ~ (v4_lattice3 @ X19)
% 2.12/2.29          | ~ (v10_lattices @ X19)
% 2.12/2.29          | (v2_struct_0 @ X19))),
% 2.12/2.29      inference('cnf', [status(esa)], [t34_lattice3])).
% 2.12/2.29  thf('202', plain,
% 2.12/2.29      (![X0 : $i]:
% 2.12/2.29         ((v2_struct_0 @ sk_A)
% 2.12/2.29          | ~ (v10_lattices @ sk_A)
% 2.12/2.29          | ~ (v4_lattice3 @ sk_A)
% 2.12/2.29          | ~ (l3_lattices @ sk_A)
% 2.12/2.29          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 2.12/2.29          | ~ (r3_lattices @ sk_A @ (sk_D_4 @ X0 @ sk_B @ sk_A) @ sk_B)
% 2.12/2.29          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 2.12/2.29      inference('sup-', [status(thm)], ['200', '201'])).
% 2.12/2.29  thf('203', plain, ((v10_lattices @ sk_A)),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf('204', plain, ((v4_lattice3 @ sk_A)),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf('205', plain, ((l3_lattices @ sk_A)),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf('206', plain,
% 2.12/2.29      (![X0 : $i]:
% 2.12/2.29         ((v2_struct_0 @ sk_A)
% 2.12/2.29          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 2.12/2.29          | ~ (r3_lattices @ sk_A @ (sk_D_4 @ X0 @ sk_B @ sk_A) @ sk_B)
% 2.12/2.29          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 2.12/2.29      inference('demod', [status(thm)], ['202', '203', '204', '205'])).
% 2.12/2.29  thf('207', plain,
% 2.12/2.29      ((((sk_B)
% 2.12/2.29          = (k16_lattice3 @ sk_A @ 
% 2.12/2.29             (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))
% 2.12/2.29        | ~ (r3_lattice3 @ sk_A @ sk_B @ 
% 2.12/2.29             (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 2.12/2.29        | ((sk_B)
% 2.12/2.29            = (k16_lattice3 @ sk_A @ 
% 2.12/2.29               (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))
% 2.12/2.29        | (v2_struct_0 @ sk_A))),
% 2.12/2.29      inference('sup-', [status(thm)], ['199', '206'])).
% 2.12/2.29  thf('208', plain,
% 2.12/2.29      ((r3_lattice3 @ sk_A @ sk_B @ 
% 2.12/2.29        (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))),
% 2.12/2.29      inference('clc', [status(thm)], ['174', '175'])).
% 2.12/2.29  thf('209', plain,
% 2.12/2.29      ((((sk_B)
% 2.12/2.29          = (k16_lattice3 @ sk_A @ 
% 2.12/2.29             (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))
% 2.12/2.29        | ((sk_B)
% 2.12/2.29            = (k16_lattice3 @ sk_A @ 
% 2.12/2.29               (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))
% 2.12/2.29        | (v2_struct_0 @ sk_A))),
% 2.12/2.29      inference('demod', [status(thm)], ['207', '208'])).
% 2.12/2.29  thf('210', plain,
% 2.12/2.29      (((v2_struct_0 @ sk_A)
% 2.12/2.29        | ((sk_B)
% 2.12/2.29            = (k16_lattice3 @ sk_A @ 
% 2.12/2.29               (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))))),
% 2.12/2.29      inference('simplify', [status(thm)], ['209'])).
% 2.12/2.29  thf('211', plain, (~ (v2_struct_0 @ sk_A)),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf('212', plain,
% 2.12/2.29      (((sk_B)
% 2.12/2.29         = (k16_lattice3 @ sk_A @ 
% 2.12/2.29            (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 2.12/2.29      inference('clc', [status(thm)], ['210', '211'])).
% 2.12/2.29  thf('213', plain,
% 2.12/2.29      (![X0 : $i]:
% 2.12/2.29         ((v2_struct_0 @ sk_A)
% 2.12/2.29          | ~ (r3_lattice3 @ sk_A @ X0 @ 
% 2.12/2.29               (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 2.12/2.29          | (r3_lattices @ sk_A @ X0 @ sk_B)
% 2.12/2.29          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 2.12/2.29      inference('demod', [status(thm)], ['152', '212'])).
% 2.12/2.29  thf('214', plain,
% 2.12/2.29      ((~ (m1_subset_1 @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.12/2.29        | (r3_lattices @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ sk_B)
% 2.12/2.29        | (v2_struct_0 @ sk_A))),
% 2.12/2.29      inference('sup-', [status(thm)], ['78', '213'])).
% 2.12/2.29  thf('215', plain,
% 2.12/2.29      ((m1_subset_1 @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 2.12/2.29      inference('clc', [status(thm)], ['24', '25'])).
% 2.12/2.29  thf('216', plain,
% 2.12/2.29      (((r3_lattices @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ sk_B)
% 2.12/2.29        | (v2_struct_0 @ sk_A))),
% 2.12/2.29      inference('demod', [status(thm)], ['214', '215'])).
% 2.12/2.29  thf('217', plain, (~ (v2_struct_0 @ sk_A)),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf('218', plain,
% 2.12/2.29      ((r3_lattices @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 2.12/2.29      inference('clc', [status(thm)], ['216', '217'])).
% 2.12/2.29  thf('219', plain,
% 2.12/2.29      (![X0 : $i]:
% 2.12/2.29         ((v2_struct_0 @ sk_A)
% 2.12/2.29          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 2.12/2.29          | ~ (r3_lattices @ sk_A @ (sk_D_4 @ X0 @ sk_B @ sk_A) @ sk_B)
% 2.12/2.29          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 2.12/2.29      inference('demod', [status(thm)], ['202', '203', '204', '205'])).
% 2.12/2.29  thf('220', plain,
% 2.12/2.29      ((~ (r3_lattice3 @ sk_A @ sk_B @ sk_C)
% 2.12/2.29        | ((sk_B) = (k16_lattice3 @ sk_A @ sk_C))
% 2.12/2.29        | (v2_struct_0 @ sk_A))),
% 2.12/2.29      inference('sup-', [status(thm)], ['218', '219'])).
% 2.12/2.29  thf('221', plain, ((r3_lattice3 @ sk_A @ sk_B @ sk_C)),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf('222', plain,
% 2.12/2.29      ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C)) | (v2_struct_0 @ sk_A))),
% 2.12/2.29      inference('demod', [status(thm)], ['220', '221'])).
% 2.12/2.29  thf('223', plain, (((k16_lattice3 @ sk_A @ sk_C) != (sk_B))),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf('224', plain, ((v2_struct_0 @ sk_A)),
% 2.12/2.29      inference('simplify_reflect-', [status(thm)], ['222', '223'])).
% 2.12/2.29  thf('225', plain, ($false), inference('demod', [status(thm)], ['0', '224'])).
% 2.12/2.29  
% 2.12/2.29  % SZS output end Refutation
% 2.12/2.29  
% 2.12/2.29  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
