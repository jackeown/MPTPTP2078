%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2APJKxJfDJ

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:31 EST 2020

% Result     : Theorem 2.09s
% Output     : Refutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :  292 (3225 expanded)
%              Number of leaves         :   33 ( 881 expanded)
%              Depth                    :   53
%              Number of atoms          : 3689 (57703 expanded)
%              Number of equality atoms :   84 (1713 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r3_lattice3_type,type,(
    r3_lattice3: $i > $i > $i > $o )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(a_2_2_lattice3_type,type,(
    a_2_2_lattice3: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(r4_lattice3_type,type,(
    r4_lattice3: $i > $i > $i > $o )).

thf(sk_D_5_type,type,(
    sk_D_5: $i > $i > $i > $i )).

thf(a_2_1_lattice3_type,type,(
    a_2_1_lattice3: $i > $i > $i )).

thf(sk_D_4_type,type,(
    sk_D_4: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

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
    ! [X22: $i,X23: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ~ ( r3_lattice3 @ X23 @ X22 @ X26 )
      | ( r3_lattice3 @ X23 @ ( sk_D_5 @ X26 @ X22 @ X23 ) @ X26 )
      | ( X22
        = ( k16_lattice3 @ X23 @ X26 ) )
      | ~ ( l3_lattices @ X23 )
      | ~ ( v4_lattice3 @ X23 )
      | ~ ( v10_lattices @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( sk_B
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ( r3_lattice3 @ sk_A @ ( sk_D_5 @ X0 @ sk_B @ sk_A ) @ X0 )
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
      | ( r3_lattice3 @ sk_A @ ( sk_D_5 @ X0 @ sk_B @ sk_A ) @ X0 )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('9',plain,
    ( ( r3_lattice3 @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    ( k16_lattice3 @ sk_A @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r3_lattice3 @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r3_lattice3 @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ sk_C ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    r3_lattice3 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X22: $i,X23: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ~ ( r3_lattice3 @ X23 @ X22 @ X26 )
      | ( m1_subset_1 @ ( sk_D_5 @ X26 @ X22 @ X23 ) @ ( u1_struct_0 @ X23 ) )
      | ( X22
        = ( k16_lattice3 @ X23 @ X26 ) )
      | ~ ( l3_lattices @ X23 )
      | ~ ( v4_lattice3 @ X23 )
      | ~ ( v10_lattices @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( sk_B
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_D_5 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
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
      | ( m1_subset_1 @ ( sk_D_5 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18','19','20'])).

thf('22',plain,
    ( ( m1_subset_1 @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('23',plain,(
    ( k16_lattice3 @ sk_A @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( m1_subset_1 @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
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
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( l3_lattices @ X14 )
      | ( v2_struct_0 @ X14 )
      | ( r2_hidden @ X16 @ ( a_2_1_lattice3 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X14 ) )
      | ( X16 != X17 )
      | ~ ( r3_lattice3 @ X14 @ X17 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_lattice3])).

thf('28',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ~ ( r3_lattice3 @ X14 @ X17 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X14 ) )
      | ( r2_hidden @ X17 @ ( a_2_1_lattice3 @ X14 @ X15 ) )
      | ( v2_struct_0 @ X14 )
      | ~ ( l3_lattices @ X14 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattice3 @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ ( a_2_1_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    r2_hidden @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['13','33'])).

thf('35',plain,(
    m1_subset_1 @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('36',plain,(
    m1_subset_1 @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
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
      | ( r3_lattice3 @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ X0 )
      | ( r3_lattice3 @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ X0 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( l3_lattices @ X18 )
      | ~ ( v4_lattice3 @ X18 )
      | ~ ( v10_lattices @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( X20
        = ( sk_D_4 @ X19 @ X18 @ X20 ) )
      | ~ ( r2_hidden @ X20 @ ( a_2_2_lattice3 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_2_lattice3])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ( ( sk_D @ ( a_2_2_lattice3 @ X1 @ X0 ) @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ sk_A )
        = ( sk_D_4 @ X0 @ X1 @ ( sk_D @ ( a_2_2_lattice3 @ X1 @ X0 ) @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ X0 )
      | ( r3_lattice3 @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('46',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( l3_lattices @ X18 )
      | ~ ( v4_lattice3 @ X18 )
      | ~ ( v10_lattices @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( r4_lattice3 @ X18 @ ( sk_D_4 @ X19 @ X18 @ X20 ) @ X19 )
      | ~ ( r2_hidden @ X20 @ ( a_2_2_lattice3 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_2_lattice3])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ( r4_lattice3 @ X1 @ ( sk_D_4 @ X0 @ X1 @ ( sk_D @ ( a_2_2_lattice3 @ X1 @ X0 ) @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ X1 @ ( sk_D @ ( a_2_2_lattice3 @ X1 @ X0 ) @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ X0 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( r3_lattice3 @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( r3_lattice3 @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ ( a_2_2_lattice3 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( r4_lattice3 @ X1 @ ( sk_D @ ( a_2_2_lattice3 @ X1 @ X0 ) @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    m1_subset_1 @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
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
      | ( r3_lattice3 @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X0 @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_lattice3 @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ X0 ) ) ),
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
      ( ( r3_lattice3 @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ X1 @ ( sk_D @ X0 @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r4_lattice3 @ sk_A @ ( sk_D @ X0 @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r3_lattice3 @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ X1 @ ( sk_D @ X0 @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r4_lattice3 @ sk_A @ ( sk_D @ X0 @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ X2 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r1_lattices @ sk_A @ X1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ X0 ) @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ X0 ) ) ) ),
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
      | ( r3_lattice3 @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r1_lattices @ sk_A @ X1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ X0 ) @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['61','62','63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ X1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ X0 ) @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r3_lattice3 @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ( r1_lattices @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ X0 ) @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','66'])).

thf('68',plain,
    ( ( r1_lattices @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
    | ( r3_lattice3 @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','67'])).

thf('69',plain,(
    m1_subset_1 @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
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
      | ( r3_lattice3 @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ~ ( r1_lattices @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ ( sk_D @ X0 @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ~ ( r1_lattices @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ ( sk_D @ X0 @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ ( sk_D @ X0 @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ( r3_lattice3 @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_lattice3 @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['68','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    r3_lattice3 @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

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

thf('80',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X30 ) )
      | ( r3_lattices @ X30 @ X29 @ ( k16_lattice3 @ X30 @ X31 ) )
      | ~ ( r3_lattice3 @ X30 @ X29 @ X31 )
      | ~ ( l3_lattices @ X30 )
      | ~ ( v4_lattice3 @ X30 )
      | ~ ( v10_lattices @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t40_lattice3])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ( r3_lattices @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ ( k16_lattice3 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ( r3_lattices @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ ( k16_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ ( k16_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    r3_lattices @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['78','87'])).

thf(t37_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v4_lattice3 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( k15_lattice3 @ A @ B )
          = ( k16_lattice3 @ A @ ( a_2_2_lattice3 @ A @ B ) ) ) ) )).

thf('89',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k15_lattice3 @ X27 @ X28 )
        = ( k16_lattice3 @ X27 @ ( a_2_2_lattice3 @ X27 @ X28 ) ) )
      | ~ ( l3_lattices @ X27 )
      | ~ ( v4_lattice3 @ X27 )
      | ~ ( v10_lattices @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t37_lattice3])).

thf('90',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k15_lattice3 @ X27 @ X28 )
        = ( k16_lattice3 @ X27 @ ( a_2_2_lattice3 @ X27 @ X28 ) ) )
      | ~ ( l3_lattices @ X27 )
      | ~ ( v4_lattice3 @ X27 )
      | ~ ( v10_lattices @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t37_lattice3])).

thf('91',plain,(
    r3_lattice3 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ~ ( r3_lattice3 @ X14 @ X17 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X14 ) )
      | ( r2_hidden @ X17 @ ( a_2_1_lattice3 @ X14 @ X15 ) )
      | ( v2_struct_0 @ X14 )
      | ~ ( l3_lattices @ X14 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    r2_hidden @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['91','98'])).

thf('100',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ( r2_hidden @ ( sk_D_1 @ X9 @ X5 @ X6 ) @ X9 )
      | ( r4_lattice3 @ X6 @ X5 @ X9 )
      | ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( l3_lattices @ X14 )
      | ( v2_struct_0 @ X14 )
      | ( X16
        = ( sk_D_3 @ X15 @ X14 @ X16 ) )
      | ~ ( r2_hidden @ X16 @ ( a_2_1_lattice3 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_lattice3])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ X1 @ X0 ) )
      | ( ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A )
        = ( sk_D_3 @ X0 @ X1 @ ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('112',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( l3_lattices @ X14 )
      | ( v2_struct_0 @ X14 )
      | ( r3_lattice3 @ X14 @ ( sk_D_3 @ X15 @ X14 @ X16 ) @ X15 )
      | ~ ( r2_hidden @ X16 @ ( a_2_1_lattice3 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_lattice3])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ X1 @ X0 ) )
      | ( r3_lattice3 @ X1 @ ( sk_D_3 @ X0 @ X1 @ ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A ) ) @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ X1 @ ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A ) @ X0 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['110','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ X1 @ X0 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( r3_lattice3 @ X1 @ ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X9 @ X5 @ X6 ) @ ( u1_struct_0 @ X6 ) )
      | ( r4_lattice3 @ X6 @ X5 @ X9 )
      | ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r3_lattice3 @ X1 @ X0 @ X2 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r1_lattices @ X1 @ X0 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('124',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X1 )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X1 )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X2 ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ X0 ) @ sk_B @ sk_A ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['115','126'])).

thf('128',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ X0 ) @ sk_B @ sk_A ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ X0 ) @ sk_B @ sk_A ) @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ X0 ) @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['101','130'])).

thf('132',plain,
    ( ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_B @ sk_A ) @ sk_B )
    | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['100','131'])).

thf('133',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ~ ( r1_lattices @ X6 @ ( sk_D_1 @ X9 @ X5 @ X6 ) @ X5 )
      | ( r4_lattice3 @ X6 @ X5 @ X9 )
      | ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['132','139'])).

thf('141',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['140','141'])).

thf('143',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('144',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v10_lattices @ X10 )
      | ~ ( v4_lattice3 @ X10 )
      | ~ ( l3_lattices @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( r4_lattice3 @ X10 @ X11 @ X12 )
      | ( r4_lattice3 @ X10 @ ( sk_D_2 @ X11 @ X12 @ X10 ) @ X12 )
      | ( X11
        = ( k15_lattice3 @ X10 @ X12 ) )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('145',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( X11
        = ( k15_lattice3 @ X10 @ X12 ) )
      | ( r4_lattice3 @ X10 @ ( sk_D_2 @ X11 @ X12 @ X10 ) @ X12 )
      | ~ ( r4_lattice3 @ X10 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ~ ( v4_lattice3 @ X10 )
      | ~ ( v10_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r4_lattice3 @ sk_A @ ( sk_D_2 @ sk_B @ X0 @ sk_A ) @ X0 )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['143','145'])).

thf('147',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r4_lattice3 @ sk_A @ ( sk_D_2 @ sk_B @ X0 @ sk_A ) @ X0 )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['146','147','148','149'])).

thf('151',plain,
    ( ( sk_B
      = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
    | ( r4_lattice3 @ sk_A @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['142','150'])).

thf('152',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( r4_lattice3 @ sk_A @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
    | ( sk_B
      = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['151','152'])).

thf('154',plain,(
    r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['140','141'])).

thf('155',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v10_lattices @ X10 )
      | ~ ( v4_lattice3 @ X10 )
      | ~ ( l3_lattices @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( r4_lattice3 @ X10 @ X11 @ X12 )
      | ( m1_subset_1 @ ( sk_D_2 @ X11 @ X12 @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ( X11
        = ( k15_lattice3 @ X10 @ X12 ) )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('157',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( X11
        = ( k15_lattice3 @ X10 @ X12 ) )
      | ( m1_subset_1 @ ( sk_D_2 @ X11 @ X12 @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( r4_lattice3 @ X10 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ~ ( v4_lattice3 @ X10 )
      | ~ ( v10_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_B @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['155','157'])).

thf('159',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_B @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['158','159','160','161'])).

thf('163',plain,
    ( ( sk_B
      = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
    | ( m1_subset_1 @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['154','162'])).

thf('164',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( m1_subset_1 @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ~ ( r4_lattice3 @ X6 @ X5 @ X7 )
      | ~ ( r2_hidden @ X8 @ X7 )
      | ( r1_lattices @ X6 @ X8 @ X5 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ X0 @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r4_lattice3 @ sk_A @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ X0 @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r4_lattice3 @ sk_A @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) @ X1 ) ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
      | ( r1_lattices @ sk_A @ X0 @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['153','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ X0 @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,
    ( ( sk_B
      = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
    | ( r1_lattices @ sk_A @ sk_B @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['99','171'])).

thf('173',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( sk_B
      = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
    | ( r1_lattices @ sk_A @ sk_B @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('175',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( r1_lattices @ sk_A @ sk_B @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) )
    | ( sk_B
      = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v10_lattices @ X10 )
      | ~ ( v4_lattice3 @ X10 )
      | ~ ( l3_lattices @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( r4_lattice3 @ X10 @ X11 @ X12 )
      | ~ ( r1_lattices @ X10 @ X11 @ ( sk_D_2 @ X11 @ X12 @ X10 ) )
      | ( X11
        = ( k15_lattice3 @ X10 @ X12 ) )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('178',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( X11
        = ( k15_lattice3 @ X10 @ X12 ) )
      | ~ ( r1_lattices @ X10 @ X11 @ ( sk_D_2 @ X11 @ X12 @ X10 ) )
      | ~ ( r4_lattice3 @ X10 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ~ ( v4_lattice3 @ X10 )
      | ~ ( v10_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(simplify,[status(thm)],['177'])).

thf('179',plain,
    ( ( sk_B
      = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
    | ( sk_B
      = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['176','178'])).

thf('180',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['140','141'])).

thf('185',plain,
    ( ( sk_B
      = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['179','180','181','182','183','184'])).

thf('186',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['185'])).

thf('187',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,
    ( sk_B
    = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k15_lattice3 @ X27 @ X28 )
        = ( k16_lattice3 @ X27 @ ( a_2_2_lattice3 @ X27 @ X28 ) ) )
      | ~ ( l3_lattices @ X27 )
      | ~ ( v4_lattice3 @ X27 )
      | ~ ( v10_lattices @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t37_lattice3])).

thf('190',plain,(
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

thf('191',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v10_lattices @ X23 )
      | ~ ( v4_lattice3 @ X23 )
      | ~ ( l3_lattices @ X23 )
      | ( r3_lattice3 @ X23 @ ( k16_lattice3 @ X23 @ X24 ) @ X24 )
      | ~ ( m1_subset_1 @ ( k16_lattice3 @ X23 @ X24 ) @ ( u1_struct_0 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['190'])).

thf('192',plain,(
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
    inference('sup-',[status(thm)],['189','191'])).

thf('193',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ X1 @ ( k16_lattice3 @ X1 @ ( a_2_2_lattice3 @ X1 @ X0 ) ) @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_subset_1 @ ( k15_lattice3 @ X1 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['192'])).

thf('194',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( r3_lattice3 @ sk_A @ ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['188','193'])).

thf('195',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_lattice3 @ sk_A @ ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['194','195','196','197','198'])).

thf('200',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    r3_lattice3 @ sk_A @ ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['199','200'])).

thf('202',plain,
    ( ( r3_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup+',[status(thm)],['90','201'])).

thf('203',plain,
    ( sk_B
    = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['186','187'])).

thf('204',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ( r3_lattice3 @ sk_A @ sk_B @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['202','203','204','205','206'])).

thf('208',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    r3_lattice3 @ sk_A @ sk_B @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['207','208'])).

thf('210',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ( r3_lattice3 @ sk_A @ ( sk_D_5 @ X0 @ sk_B @ sk_A ) @ X0 )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('211',plain,
    ( ( r3_lattice3 @ sk_A @ ( sk_D_5 @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
    | ( sk_B
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['209','210'])).

thf('212',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,
    ( ( sk_B
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
    | ( r3_lattice3 @ sk_A @ ( sk_D_5 @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['211','212'])).

thf('214',plain,(
    r3_lattice3 @ sk_A @ sk_B @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['207','208'])).

thf('215',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_D_5 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18','19','20'])).

thf('216',plain,
    ( ( m1_subset_1 @ ( sk_D_5 @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('217',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,
    ( ( sk_B
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
    | ( m1_subset_1 @ ( sk_D_5 @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['216','217'])).

thf('219',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X30 ) )
      | ( r3_lattices @ X30 @ X29 @ ( k16_lattice3 @ X30 @ X31 ) )
      | ~ ( r3_lattice3 @ X30 @ X29 @ X31 )
      | ~ ( l3_lattices @ X30 )
      | ~ ( v4_lattice3 @ X30 )
      | ~ ( v10_lattices @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t40_lattice3])).

thf('220',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_5 @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ X0 )
      | ( r3_lattices @ sk_A @ ( sk_D_5 @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ ( k16_lattice3 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['218','219'])).

thf('221',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_5 @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ X0 )
      | ( r3_lattices @ sk_A @ ( sk_D_5 @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ ( k16_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['220','221','222','223'])).

thf('225',plain,
    ( ( sk_B
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
    | ( r3_lattices @ sk_A @ ( sk_D_5 @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['213','224'])).

thf('226',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_lattices @ sk_A @ ( sk_D_5 @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
    | ( sk_B
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ) ),
    inference(simplify,[status(thm)],['225'])).

thf('227',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,
    ( ( sk_B
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
    | ( r3_lattices @ sk_A @ ( sk_D_5 @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ) ),
    inference(clc,[status(thm)],['226','227'])).

thf('229',plain,
    ( ( r3_lattices @ sk_A @ ( sk_D_5 @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( sk_B
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup+',[status(thm)],['89','228'])).

thf('230',plain,
    ( sk_B
    = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['186','187'])).

thf('231',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,
    ( ( r3_lattices @ sk_A @ ( sk_D_5 @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['229','230','231','232','233'])).

thf('235',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,
    ( ( sk_B
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
    | ( r3_lattices @ sk_A @ ( sk_D_5 @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) @ sk_B @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['234','235'])).

thf('237',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    ! [X22: $i,X23: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ~ ( r3_lattice3 @ X23 @ X22 @ X26 )
      | ~ ( r3_lattices @ X23 @ ( sk_D_5 @ X26 @ X22 @ X23 ) @ X22 )
      | ( X22
        = ( k16_lattice3 @ X23 @ X26 ) )
      | ~ ( l3_lattices @ X23 )
      | ~ ( v4_lattice3 @ X23 )
      | ~ ( v10_lattices @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('239',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( sk_B
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattices @ sk_A @ ( sk_D_5 @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['237','238'])).

thf('240',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattices @ sk_A @ ( sk_D_5 @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['239','240','241','242'])).

thf('244',plain,
    ( ( sk_B
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
    | ~ ( r3_lattice3 @ sk_A @ sk_B @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
    | ( sk_B
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['236','243'])).

thf('245',plain,(
    r3_lattice3 @ sk_A @ sk_B @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['207','208'])).

thf('246',plain,
    ( ( sk_B
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
    | ( sk_B
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['244','245'])).

thf('247',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ) ),
    inference(simplify,[status(thm)],['246'])).

thf('248',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,
    ( sk_B
    = ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['247','248'])).

thf('250',plain,(
    r3_lattices @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['88','249'])).

thf('251',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattices @ sk_A @ ( sk_D_5 @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['239','240','241','242'])).

thf('252',plain,
    ( ~ ( r3_lattice3 @ sk_A @ sk_B @ sk_C )
    | ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['250','251'])).

thf('253',plain,(
    r3_lattice3 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,
    ( ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['252','253'])).

thf('255',plain,(
    ( k16_lattice3 @ sk_A @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['254','255'])).

thf('257',plain,(
    $false ),
    inference(demod,[status(thm)],['0','256'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2APJKxJfDJ
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:20:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 2.09/2.30  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.09/2.30  % Solved by: fo/fo7.sh
% 2.09/2.30  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.09/2.30  % done 1373 iterations in 1.841s
% 2.09/2.30  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.09/2.30  % SZS output start Refutation
% 2.09/2.30  thf(sk_C_type, type, sk_C: $i).
% 2.09/2.30  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 2.09/2.30  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 2.09/2.30  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 2.09/2.30  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.09/2.30  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i > $i).
% 2.09/2.30  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 2.09/2.30  thf(sk_A_type, type, sk_A: $i).
% 2.09/2.30  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.09/2.30  thf(r3_lattice3_type, type, r3_lattice3: $i > $i > $i > $o).
% 2.09/2.30  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 2.09/2.30  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 2.09/2.30  thf(a_2_2_lattice3_type, type, a_2_2_lattice3: $i > $i > $i).
% 2.09/2.30  thf(sk_B_type, type, sk_B: $i).
% 2.09/2.30  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 2.09/2.30  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 2.09/2.30  thf(r4_lattice3_type, type, r4_lattice3: $i > $i > $i > $o).
% 2.09/2.30  thf(sk_D_5_type, type, sk_D_5: $i > $i > $i > $i).
% 2.09/2.30  thf(a_2_1_lattice3_type, type, a_2_1_lattice3: $i > $i > $i).
% 2.09/2.30  thf(sk_D_4_type, type, sk_D_4: $i > $i > $i > $i).
% 2.09/2.30  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.09/2.30  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 2.09/2.30  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.09/2.30  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 2.09/2.30  thf(t42_lattice3, conjecture,
% 2.09/2.30    (![A:$i]:
% 2.09/2.30     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.09/2.30         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 2.09/2.30       ( ![B:$i]:
% 2.09/2.30         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.09/2.30           ( ![C:$i]:
% 2.09/2.30             ( ( ( r2_hidden @ B @ C ) & ( r3_lattice3 @ A @ B @ C ) ) =>
% 2.09/2.30               ( ( k16_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ))).
% 2.09/2.30  thf(zf_stmt_0, negated_conjecture,
% 2.09/2.30    (~( ![A:$i]:
% 2.09/2.30        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.09/2.30            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 2.09/2.30          ( ![B:$i]:
% 2.09/2.30            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.09/2.30              ( ![C:$i]:
% 2.09/2.30                ( ( ( r2_hidden @ B @ C ) & ( r3_lattice3 @ A @ B @ C ) ) =>
% 2.09/2.30                  ( ( k16_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ) )),
% 2.09/2.30    inference('cnf.neg', [status(esa)], [t42_lattice3])).
% 2.09/2.30  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 2.09/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.30  thf('1', plain, ((r3_lattice3 @ sk_A @ sk_B @ sk_C)),
% 2.09/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.30  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.09/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.30  thf(t34_lattice3, axiom,
% 2.09/2.30    (![A:$i]:
% 2.09/2.30     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.09/2.30         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 2.09/2.30       ( ![B:$i]:
% 2.09/2.30         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.09/2.30           ( ![C:$i]:
% 2.09/2.30             ( ( ( B ) = ( k16_lattice3 @ A @ C ) ) <=>
% 2.09/2.30               ( ( r3_lattice3 @ A @ B @ C ) & 
% 2.09/2.30                 ( ![D:$i]:
% 2.09/2.30                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 2.09/2.30                     ( ( r3_lattice3 @ A @ D @ C ) =>
% 2.09/2.30                       ( r3_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 2.09/2.30  thf('3', plain,
% 2.09/2.30      (![X22 : $i, X23 : $i, X26 : $i]:
% 2.09/2.30         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 2.09/2.30          | ~ (r3_lattice3 @ X23 @ X22 @ X26)
% 2.09/2.30          | (r3_lattice3 @ X23 @ (sk_D_5 @ X26 @ X22 @ X23) @ X26)
% 2.09/2.30          | ((X22) = (k16_lattice3 @ X23 @ X26))
% 2.09/2.30          | ~ (l3_lattices @ X23)
% 2.09/2.30          | ~ (v4_lattice3 @ X23)
% 2.09/2.30          | ~ (v10_lattices @ X23)
% 2.09/2.30          | (v2_struct_0 @ X23))),
% 2.09/2.30      inference('cnf', [status(esa)], [t34_lattice3])).
% 2.09/2.30  thf('4', plain,
% 2.09/2.30      (![X0 : $i]:
% 2.09/2.30         ((v2_struct_0 @ sk_A)
% 2.09/2.30          | ~ (v10_lattices @ sk_A)
% 2.09/2.30          | ~ (v4_lattice3 @ sk_A)
% 2.09/2.30          | ~ (l3_lattices @ sk_A)
% 2.09/2.30          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 2.09/2.30          | (r3_lattice3 @ sk_A @ (sk_D_5 @ X0 @ sk_B @ sk_A) @ X0)
% 2.09/2.30          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 2.09/2.30      inference('sup-', [status(thm)], ['2', '3'])).
% 2.09/2.30  thf('5', plain, ((v10_lattices @ sk_A)),
% 2.09/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.30  thf('6', plain, ((v4_lattice3 @ sk_A)),
% 2.09/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.30  thf('7', plain, ((l3_lattices @ sk_A)),
% 2.09/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.30  thf('8', plain,
% 2.09/2.30      (![X0 : $i]:
% 2.09/2.30         ((v2_struct_0 @ sk_A)
% 2.09/2.30          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 2.09/2.30          | (r3_lattice3 @ sk_A @ (sk_D_5 @ X0 @ sk_B @ sk_A) @ X0)
% 2.09/2.30          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 2.09/2.30      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 2.09/2.30  thf('9', plain,
% 2.09/2.30      (((r3_lattice3 @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 2.09/2.30        | ((sk_B) = (k16_lattice3 @ sk_A @ sk_C))
% 2.09/2.30        | (v2_struct_0 @ sk_A))),
% 2.09/2.30      inference('sup-', [status(thm)], ['1', '8'])).
% 2.09/2.30  thf('10', plain, (((k16_lattice3 @ sk_A @ sk_C) != (sk_B))),
% 2.09/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.30  thf('11', plain,
% 2.09/2.30      (((r3_lattice3 @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 2.09/2.30        | (v2_struct_0 @ sk_A))),
% 2.09/2.30      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 2.09/2.30  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 2.09/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.30  thf('13', plain,
% 2.09/2.30      ((r3_lattice3 @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ sk_C)),
% 2.09/2.30      inference('clc', [status(thm)], ['11', '12'])).
% 2.09/2.30  thf('14', plain, ((r3_lattice3 @ sk_A @ sk_B @ sk_C)),
% 2.09/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.30  thf('15', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.09/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.30  thf('16', plain,
% 2.09/2.30      (![X22 : $i, X23 : $i, X26 : $i]:
% 2.09/2.30         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 2.09/2.30          | ~ (r3_lattice3 @ X23 @ X22 @ X26)
% 2.09/2.30          | (m1_subset_1 @ (sk_D_5 @ X26 @ X22 @ X23) @ (u1_struct_0 @ X23))
% 2.09/2.30          | ((X22) = (k16_lattice3 @ X23 @ X26))
% 2.09/2.30          | ~ (l3_lattices @ X23)
% 2.09/2.30          | ~ (v4_lattice3 @ X23)
% 2.09/2.30          | ~ (v10_lattices @ X23)
% 2.09/2.30          | (v2_struct_0 @ X23))),
% 2.09/2.30      inference('cnf', [status(esa)], [t34_lattice3])).
% 2.09/2.30  thf('17', plain,
% 2.09/2.30      (![X0 : $i]:
% 2.09/2.30         ((v2_struct_0 @ sk_A)
% 2.09/2.30          | ~ (v10_lattices @ sk_A)
% 2.09/2.30          | ~ (v4_lattice3 @ sk_A)
% 2.09/2.30          | ~ (l3_lattices @ sk_A)
% 2.09/2.30          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 2.09/2.30          | (m1_subset_1 @ (sk_D_5 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.09/2.30          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 2.09/2.30      inference('sup-', [status(thm)], ['15', '16'])).
% 2.09/2.30  thf('18', plain, ((v10_lattices @ sk_A)),
% 2.09/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.30  thf('19', plain, ((v4_lattice3 @ sk_A)),
% 2.09/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.30  thf('20', plain, ((l3_lattices @ sk_A)),
% 2.09/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.30  thf('21', plain,
% 2.09/2.30      (![X0 : $i]:
% 2.09/2.30         ((v2_struct_0 @ sk_A)
% 2.09/2.30          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 2.09/2.30          | (m1_subset_1 @ (sk_D_5 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.09/2.30          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 2.09/2.30      inference('demod', [status(thm)], ['17', '18', '19', '20'])).
% 2.09/2.30  thf('22', plain,
% 2.09/2.30      (((m1_subset_1 @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.09/2.30        | ((sk_B) = (k16_lattice3 @ sk_A @ sk_C))
% 2.09/2.30        | (v2_struct_0 @ sk_A))),
% 2.09/2.30      inference('sup-', [status(thm)], ['14', '21'])).
% 2.09/2.30  thf('23', plain, (((k16_lattice3 @ sk_A @ sk_C) != (sk_B))),
% 2.09/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.30  thf('24', plain,
% 2.09/2.30      (((m1_subset_1 @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.09/2.30        | (v2_struct_0 @ sk_A))),
% 2.09/2.30      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 2.09/2.30  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 2.09/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.30  thf('26', plain,
% 2.09/2.30      ((m1_subset_1 @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 2.09/2.30      inference('clc', [status(thm)], ['24', '25'])).
% 2.09/2.30  thf(fraenkel_a_2_1_lattice3, axiom,
% 2.09/2.30    (![A:$i,B:$i,C:$i]:
% 2.09/2.30     ( ( ( ~( v2_struct_0 @ B ) ) & ( l3_lattices @ B ) ) =>
% 2.09/2.30       ( ( r2_hidden @ A @ ( a_2_1_lattice3 @ B @ C ) ) <=>
% 2.09/2.30         ( ?[D:$i]:
% 2.09/2.30           ( ( r3_lattice3 @ B @ D @ C ) & ( ( A ) = ( D ) ) & 
% 2.09/2.30             ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 2.09/2.30  thf('27', plain,
% 2.09/2.30      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 2.09/2.30         (~ (l3_lattices @ X14)
% 2.09/2.30          | (v2_struct_0 @ X14)
% 2.09/2.30          | (r2_hidden @ X16 @ (a_2_1_lattice3 @ X14 @ X15))
% 2.09/2.30          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X14))
% 2.09/2.30          | ((X16) != (X17))
% 2.09/2.30          | ~ (r3_lattice3 @ X14 @ X17 @ X15))),
% 2.09/2.30      inference('cnf', [status(esa)], [fraenkel_a_2_1_lattice3])).
% 2.09/2.30  thf('28', plain,
% 2.09/2.30      (![X14 : $i, X15 : $i, X17 : $i]:
% 2.09/2.30         (~ (r3_lattice3 @ X14 @ X17 @ X15)
% 2.09/2.30          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X14))
% 2.09/2.30          | (r2_hidden @ X17 @ (a_2_1_lattice3 @ X14 @ X15))
% 2.09/2.30          | (v2_struct_0 @ X14)
% 2.09/2.30          | ~ (l3_lattices @ X14))),
% 2.09/2.30      inference('simplify', [status(thm)], ['27'])).
% 2.09/2.30  thf('29', plain,
% 2.09/2.30      (![X0 : $i]:
% 2.09/2.30         (~ (l3_lattices @ sk_A)
% 2.09/2.30          | (v2_struct_0 @ sk_A)
% 2.09/2.30          | (r2_hidden @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ 
% 2.09/2.30             (a_2_1_lattice3 @ sk_A @ X0))
% 2.09/2.30          | ~ (r3_lattice3 @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ X0))),
% 2.09/2.30      inference('sup-', [status(thm)], ['26', '28'])).
% 2.09/2.30  thf('30', plain, ((l3_lattices @ sk_A)),
% 2.09/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.30  thf('31', plain,
% 2.09/2.30      (![X0 : $i]:
% 2.09/2.30         ((v2_struct_0 @ sk_A)
% 2.09/2.30          | (r2_hidden @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ 
% 2.09/2.30             (a_2_1_lattice3 @ sk_A @ X0))
% 2.09/2.30          | ~ (r3_lattice3 @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ X0))),
% 2.09/2.30      inference('demod', [status(thm)], ['29', '30'])).
% 2.09/2.30  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 2.09/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.30  thf('33', plain,
% 2.09/2.30      (![X0 : $i]:
% 2.09/2.30         (~ (r3_lattice3 @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ X0)
% 2.09/2.30          | (r2_hidden @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ 
% 2.09/2.30             (a_2_1_lattice3 @ sk_A @ X0)))),
% 2.09/2.30      inference('clc', [status(thm)], ['31', '32'])).
% 2.09/2.30  thf('34', plain,
% 2.09/2.30      ((r2_hidden @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ 
% 2.09/2.30        (a_2_1_lattice3 @ sk_A @ sk_C))),
% 2.09/2.30      inference('sup-', [status(thm)], ['13', '33'])).
% 2.09/2.30  thf('35', plain,
% 2.09/2.30      ((m1_subset_1 @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 2.09/2.30      inference('clc', [status(thm)], ['24', '25'])).
% 2.09/2.30  thf('36', plain,
% 2.09/2.30      ((m1_subset_1 @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 2.09/2.30      inference('clc', [status(thm)], ['24', '25'])).
% 2.09/2.30  thf(d16_lattice3, axiom,
% 2.09/2.30    (![A:$i]:
% 2.09/2.30     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 2.09/2.30       ( ![B:$i]:
% 2.09/2.30         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.09/2.30           ( ![C:$i]:
% 2.09/2.30             ( ( r3_lattice3 @ A @ B @ C ) <=>
% 2.09/2.30               ( ![D:$i]:
% 2.09/2.30                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 2.09/2.30                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 2.09/2.30  thf('37', plain,
% 2.09/2.30      (![X0 : $i, X1 : $i, X4 : $i]:
% 2.09/2.30         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 2.09/2.30          | (r2_hidden @ (sk_D @ X4 @ X0 @ X1) @ X4)
% 2.09/2.30          | (r3_lattice3 @ X1 @ X0 @ X4)
% 2.09/2.30          | ~ (l3_lattices @ X1)
% 2.09/2.30          | (v2_struct_0 @ X1))),
% 2.09/2.30      inference('cnf', [status(esa)], [d16_lattice3])).
% 2.09/2.30  thf('38', plain,
% 2.09/2.30      (![X0 : $i]:
% 2.09/2.30         ((v2_struct_0 @ sk_A)
% 2.09/2.30          | ~ (l3_lattices @ sk_A)
% 2.09/2.30          | (r3_lattice3 @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ X0)
% 2.09/2.30          | (r2_hidden @ (sk_D @ X0 @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ sk_A) @ 
% 2.09/2.30             X0))),
% 2.09/2.30      inference('sup-', [status(thm)], ['36', '37'])).
% 2.09/2.30  thf('39', plain, ((l3_lattices @ sk_A)),
% 2.09/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.30  thf('40', plain,
% 2.09/2.30      (![X0 : $i]:
% 2.09/2.30         ((v2_struct_0 @ sk_A)
% 2.09/2.30          | (r3_lattice3 @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ X0)
% 2.09/2.30          | (r2_hidden @ (sk_D @ X0 @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ sk_A) @ 
% 2.09/2.30             X0))),
% 2.09/2.30      inference('demod', [status(thm)], ['38', '39'])).
% 2.09/2.30  thf('41', plain, (~ (v2_struct_0 @ sk_A)),
% 2.09/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.30  thf('42', plain,
% 2.09/2.30      (![X0 : $i]:
% 2.09/2.30         ((r2_hidden @ (sk_D @ X0 @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ sk_A) @ X0)
% 2.09/2.30          | (r3_lattice3 @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ X0))),
% 2.09/2.30      inference('clc', [status(thm)], ['40', '41'])).
% 2.09/2.30  thf(fraenkel_a_2_2_lattice3, axiom,
% 2.09/2.30    (![A:$i,B:$i,C:$i]:
% 2.09/2.30     ( ( ( ~( v2_struct_0 @ B ) ) & ( v10_lattices @ B ) & 
% 2.09/2.30         ( v4_lattice3 @ B ) & ( l3_lattices @ B ) ) =>
% 2.09/2.30       ( ( r2_hidden @ A @ ( a_2_2_lattice3 @ B @ C ) ) <=>
% 2.09/2.30         ( ?[D:$i]:
% 2.09/2.30           ( ( r4_lattice3 @ B @ D @ C ) & ( ( A ) = ( D ) ) & 
% 2.09/2.30             ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 2.09/2.30  thf('43', plain,
% 2.09/2.30      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.09/2.30         (~ (l3_lattices @ X18)
% 2.09/2.30          | ~ (v4_lattice3 @ X18)
% 2.09/2.30          | ~ (v10_lattices @ X18)
% 2.09/2.30          | (v2_struct_0 @ X18)
% 2.09/2.30          | ((X20) = (sk_D_4 @ X19 @ X18 @ X20))
% 2.09/2.30          | ~ (r2_hidden @ X20 @ (a_2_2_lattice3 @ X18 @ X19)))),
% 2.09/2.30      inference('cnf', [status(esa)], [fraenkel_a_2_2_lattice3])).
% 2.09/2.30  thf('44', plain,
% 2.09/2.30      (![X0 : $i, X1 : $i]:
% 2.09/2.30         ((r3_lattice3 @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ 
% 2.09/2.30           (a_2_2_lattice3 @ X1 @ X0))
% 2.09/2.30          | ((sk_D @ (a_2_2_lattice3 @ X1 @ X0) @ 
% 2.09/2.30              (sk_D_5 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 2.09/2.30              = (sk_D_4 @ X0 @ X1 @ 
% 2.09/2.30                 (sk_D @ (a_2_2_lattice3 @ X1 @ X0) @ 
% 2.09/2.30                  (sk_D_5 @ sk_C @ sk_B @ sk_A) @ sk_A)))
% 2.09/2.30          | (v2_struct_0 @ X1)
% 2.09/2.30          | ~ (v10_lattices @ X1)
% 2.09/2.30          | ~ (v4_lattice3 @ X1)
% 2.09/2.30          | ~ (l3_lattices @ X1))),
% 2.09/2.30      inference('sup-', [status(thm)], ['42', '43'])).
% 2.09/2.30  thf('45', plain,
% 2.09/2.30      (![X0 : $i]:
% 2.09/2.30         ((r2_hidden @ (sk_D @ X0 @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ sk_A) @ X0)
% 2.09/2.30          | (r3_lattice3 @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ X0))),
% 2.09/2.30      inference('clc', [status(thm)], ['40', '41'])).
% 2.09/2.30  thf('46', plain,
% 2.09/2.30      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.09/2.30         (~ (l3_lattices @ X18)
% 2.09/2.30          | ~ (v4_lattice3 @ X18)
% 2.09/2.30          | ~ (v10_lattices @ X18)
% 2.09/2.30          | (v2_struct_0 @ X18)
% 2.09/2.30          | (r4_lattice3 @ X18 @ (sk_D_4 @ X19 @ X18 @ X20) @ X19)
% 2.09/2.30          | ~ (r2_hidden @ X20 @ (a_2_2_lattice3 @ X18 @ X19)))),
% 2.09/2.30      inference('cnf', [status(esa)], [fraenkel_a_2_2_lattice3])).
% 2.09/2.30  thf('47', plain,
% 2.09/2.30      (![X0 : $i, X1 : $i]:
% 2.09/2.30         ((r3_lattice3 @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ 
% 2.09/2.30           (a_2_2_lattice3 @ X1 @ X0))
% 2.09/2.30          | (r4_lattice3 @ X1 @ 
% 2.09/2.30             (sk_D_4 @ X0 @ X1 @ 
% 2.09/2.30              (sk_D @ (a_2_2_lattice3 @ X1 @ X0) @ 
% 2.09/2.30               (sk_D_5 @ sk_C @ sk_B @ sk_A) @ sk_A)) @ 
% 2.09/2.30             X0)
% 2.09/2.30          | (v2_struct_0 @ X1)
% 2.09/2.30          | ~ (v10_lattices @ X1)
% 2.09/2.30          | ~ (v4_lattice3 @ X1)
% 2.09/2.30          | ~ (l3_lattices @ X1))),
% 2.09/2.30      inference('sup-', [status(thm)], ['45', '46'])).
% 2.09/2.30  thf('48', plain,
% 2.09/2.30      (![X0 : $i, X1 : $i]:
% 2.09/2.30         ((r4_lattice3 @ X1 @ 
% 2.09/2.30           (sk_D @ (a_2_2_lattice3 @ X1 @ X0) @ 
% 2.09/2.30            (sk_D_5 @ sk_C @ sk_B @ sk_A) @ sk_A) @ 
% 2.09/2.30           X0)
% 2.09/2.30          | ~ (l3_lattices @ X1)
% 2.09/2.30          | ~ (v4_lattice3 @ X1)
% 2.09/2.30          | ~ (v10_lattices @ X1)
% 2.09/2.30          | (v2_struct_0 @ X1)
% 2.09/2.30          | (r3_lattice3 @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ 
% 2.09/2.30             (a_2_2_lattice3 @ X1 @ X0))
% 2.09/2.30          | ~ (l3_lattices @ X1)
% 2.09/2.30          | ~ (v4_lattice3 @ X1)
% 2.09/2.30          | ~ (v10_lattices @ X1)
% 2.09/2.30          | (v2_struct_0 @ X1)
% 2.09/2.30          | (r3_lattice3 @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ 
% 2.09/2.30             (a_2_2_lattice3 @ X1 @ X0)))),
% 2.09/2.30      inference('sup+', [status(thm)], ['44', '47'])).
% 2.09/2.30  thf('49', plain,
% 2.09/2.30      (![X0 : $i, X1 : $i]:
% 2.09/2.30         ((r3_lattice3 @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ 
% 2.09/2.30           (a_2_2_lattice3 @ X1 @ X0))
% 2.09/2.30          | (v2_struct_0 @ X1)
% 2.09/2.30          | ~ (v10_lattices @ X1)
% 2.09/2.30          | ~ (v4_lattice3 @ X1)
% 2.09/2.30          | ~ (l3_lattices @ X1)
% 2.09/2.30          | (r4_lattice3 @ X1 @ 
% 2.09/2.30             (sk_D @ (a_2_2_lattice3 @ X1 @ X0) @ 
% 2.09/2.30              (sk_D_5 @ sk_C @ sk_B @ sk_A) @ sk_A) @ 
% 2.09/2.30             X0))),
% 2.09/2.30      inference('simplify', [status(thm)], ['48'])).
% 2.09/2.30  thf('50', plain,
% 2.09/2.30      ((m1_subset_1 @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 2.09/2.30      inference('clc', [status(thm)], ['24', '25'])).
% 2.09/2.30  thf('51', plain,
% 2.09/2.30      (![X0 : $i, X1 : $i, X4 : $i]:
% 2.09/2.30         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 2.09/2.30          | (m1_subset_1 @ (sk_D @ X4 @ X0 @ X1) @ (u1_struct_0 @ X1))
% 2.09/2.30          | (r3_lattice3 @ X1 @ X0 @ X4)
% 2.09/2.30          | ~ (l3_lattices @ X1)
% 2.09/2.30          | (v2_struct_0 @ X1))),
% 2.09/2.30      inference('cnf', [status(esa)], [d16_lattice3])).
% 2.09/2.30  thf('52', plain,
% 2.09/2.30      (![X0 : $i]:
% 2.09/2.30         ((v2_struct_0 @ sk_A)
% 2.09/2.30          | ~ (l3_lattices @ sk_A)
% 2.09/2.30          | (r3_lattice3 @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ X0)
% 2.09/2.30          | (m1_subset_1 @ 
% 2.09/2.30             (sk_D @ X0 @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ sk_A) @ 
% 2.09/2.30             (u1_struct_0 @ sk_A)))),
% 2.09/2.30      inference('sup-', [status(thm)], ['50', '51'])).
% 2.09/2.30  thf('53', plain, ((l3_lattices @ sk_A)),
% 2.09/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.30  thf('54', plain,
% 2.09/2.30      (![X0 : $i]:
% 2.09/2.30         ((v2_struct_0 @ sk_A)
% 2.09/2.30          | (r3_lattice3 @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ X0)
% 2.09/2.30          | (m1_subset_1 @ 
% 2.09/2.30             (sk_D @ X0 @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ sk_A) @ 
% 2.09/2.30             (u1_struct_0 @ sk_A)))),
% 2.09/2.30      inference('demod', [status(thm)], ['52', '53'])).
% 2.09/2.30  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 2.09/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.30  thf('56', plain,
% 2.09/2.30      (![X0 : $i]:
% 2.09/2.30         ((m1_subset_1 @ (sk_D @ X0 @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ sk_A) @ 
% 2.09/2.30           (u1_struct_0 @ sk_A))
% 2.09/2.30          | (r3_lattice3 @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ X0))),
% 2.09/2.30      inference('clc', [status(thm)], ['54', '55'])).
% 2.09/2.30  thf(d17_lattice3, axiom,
% 2.09/2.30    (![A:$i]:
% 2.09/2.30     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 2.09/2.30       ( ![B:$i]:
% 2.09/2.30         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.09/2.30           ( ![C:$i]:
% 2.09/2.30             ( ( r4_lattice3 @ A @ B @ C ) <=>
% 2.09/2.30               ( ![D:$i]:
% 2.09/2.30                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 2.09/2.30                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ))).
% 2.09/2.30  thf('57', plain,
% 2.09/2.30      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 2.09/2.30         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 2.09/2.30          | ~ (r4_lattice3 @ X6 @ X5 @ X7)
% 2.09/2.30          | ~ (r2_hidden @ X8 @ X7)
% 2.09/2.30          | (r1_lattices @ X6 @ X8 @ X5)
% 2.09/2.30          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X6))
% 2.09/2.30          | ~ (l3_lattices @ X6)
% 2.09/2.30          | (v2_struct_0 @ X6))),
% 2.09/2.30      inference('cnf', [status(esa)], [d17_lattice3])).
% 2.09/2.30  thf('58', plain,
% 2.09/2.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.09/2.30         ((r3_lattice3 @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ X0)
% 2.09/2.30          | (v2_struct_0 @ sk_A)
% 2.09/2.30          | ~ (l3_lattices @ sk_A)
% 2.09/2.30          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.09/2.30          | (r1_lattices @ sk_A @ X1 @ 
% 2.09/2.30             (sk_D @ X0 @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ sk_A))
% 2.09/2.30          | ~ (r2_hidden @ X1 @ X2)
% 2.09/2.30          | ~ (r4_lattice3 @ sk_A @ 
% 2.09/2.30               (sk_D @ X0 @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ sk_A) @ X2))),
% 2.09/2.30      inference('sup-', [status(thm)], ['56', '57'])).
% 2.09/2.30  thf('59', plain, ((l3_lattices @ sk_A)),
% 2.09/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.30  thf('60', plain,
% 2.09/2.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.09/2.30         ((r3_lattice3 @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ X0)
% 2.09/2.30          | (v2_struct_0 @ sk_A)
% 2.09/2.30          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.09/2.30          | (r1_lattices @ sk_A @ X1 @ 
% 2.09/2.30             (sk_D @ X0 @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ sk_A))
% 2.09/2.30          | ~ (r2_hidden @ X1 @ X2)
% 2.09/2.30          | ~ (r4_lattice3 @ sk_A @ 
% 2.09/2.30               (sk_D @ X0 @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ sk_A) @ X2))),
% 2.09/2.30      inference('demod', [status(thm)], ['58', '59'])).
% 2.09/2.30  thf('61', plain,
% 2.09/2.30      (![X0 : $i, X1 : $i]:
% 2.09/2.30         (~ (l3_lattices @ sk_A)
% 2.09/2.30          | ~ (v4_lattice3 @ sk_A)
% 2.09/2.30          | ~ (v10_lattices @ sk_A)
% 2.09/2.30          | (v2_struct_0 @ sk_A)
% 2.09/2.30          | (r3_lattice3 @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ 
% 2.09/2.30             (a_2_2_lattice3 @ sk_A @ X0))
% 2.09/2.30          | ~ (r2_hidden @ X1 @ X0)
% 2.09/2.30          | (r1_lattices @ sk_A @ X1 @ 
% 2.09/2.30             (sk_D @ (a_2_2_lattice3 @ sk_A @ X0) @ 
% 2.09/2.30              (sk_D_5 @ sk_C @ sk_B @ sk_A) @ sk_A))
% 2.09/2.30          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.09/2.30          | (v2_struct_0 @ sk_A)
% 2.09/2.30          | (r3_lattice3 @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ 
% 2.09/2.30             (a_2_2_lattice3 @ sk_A @ X0)))),
% 2.09/2.30      inference('sup-', [status(thm)], ['49', '60'])).
% 2.09/2.30  thf('62', plain, ((l3_lattices @ sk_A)),
% 2.09/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.30  thf('63', plain, ((v4_lattice3 @ sk_A)),
% 2.09/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.30  thf('64', plain, ((v10_lattices @ sk_A)),
% 2.09/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.30  thf('65', plain,
% 2.09/2.30      (![X0 : $i, X1 : $i]:
% 2.09/2.30         ((v2_struct_0 @ sk_A)
% 2.09/2.30          | (r3_lattice3 @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ 
% 2.09/2.30             (a_2_2_lattice3 @ sk_A @ X0))
% 2.09/2.30          | ~ (r2_hidden @ X1 @ X0)
% 2.09/2.30          | (r1_lattices @ sk_A @ X1 @ 
% 2.09/2.30             (sk_D @ (a_2_2_lattice3 @ sk_A @ X0) @ 
% 2.09/2.30              (sk_D_5 @ sk_C @ sk_B @ sk_A) @ sk_A))
% 2.09/2.30          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.09/2.30          | (v2_struct_0 @ sk_A)
% 2.09/2.30          | (r3_lattice3 @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ 
% 2.09/2.30             (a_2_2_lattice3 @ sk_A @ X0)))),
% 2.09/2.30      inference('demod', [status(thm)], ['61', '62', '63', '64'])).
% 2.09/2.30  thf('66', plain,
% 2.09/2.30      (![X0 : $i, X1 : $i]:
% 2.09/2.30         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.09/2.30          | (r1_lattices @ sk_A @ X1 @ 
% 2.09/2.30             (sk_D @ (a_2_2_lattice3 @ sk_A @ X0) @ 
% 2.09/2.30              (sk_D_5 @ sk_C @ sk_B @ sk_A) @ sk_A))
% 2.09/2.30          | ~ (r2_hidden @ X1 @ X0)
% 2.09/2.30          | (r3_lattice3 @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ 
% 2.09/2.30             (a_2_2_lattice3 @ sk_A @ X0))
% 2.09/2.30          | (v2_struct_0 @ sk_A))),
% 2.09/2.30      inference('simplify', [status(thm)], ['65'])).
% 2.09/2.30  thf('67', plain,
% 2.09/2.30      (![X0 : $i]:
% 2.09/2.30         ((v2_struct_0 @ sk_A)
% 2.09/2.30          | (r3_lattice3 @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ 
% 2.09/2.30             (a_2_2_lattice3 @ sk_A @ X0))
% 2.09/2.30          | ~ (r2_hidden @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ X0)
% 2.09/2.30          | (r1_lattices @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ 
% 2.09/2.30             (sk_D @ (a_2_2_lattice3 @ sk_A @ X0) @ 
% 2.09/2.30              (sk_D_5 @ sk_C @ sk_B @ sk_A) @ sk_A)))),
% 2.09/2.30      inference('sup-', [status(thm)], ['35', '66'])).
% 2.09/2.30  thf('68', plain,
% 2.09/2.30      (((r1_lattices @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ 
% 2.09/2.30         (sk_D @ (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) @ 
% 2.09/2.30          (sk_D_5 @ sk_C @ sk_B @ sk_A) @ sk_A))
% 2.09/2.30        | (r3_lattice3 @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ 
% 2.09/2.30           (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 2.09/2.30        | (v2_struct_0 @ sk_A))),
% 2.09/2.30      inference('sup-', [status(thm)], ['34', '67'])).
% 2.09/2.30  thf('69', plain,
% 2.09/2.30      ((m1_subset_1 @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 2.09/2.30      inference('clc', [status(thm)], ['24', '25'])).
% 2.09/2.30  thf('70', plain,
% 2.09/2.30      (![X0 : $i, X1 : $i, X4 : $i]:
% 2.09/2.30         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 2.09/2.30          | ~ (r1_lattices @ X1 @ X0 @ (sk_D @ X4 @ X0 @ X1))
% 2.09/2.30          | (r3_lattice3 @ X1 @ X0 @ X4)
% 2.09/2.30          | ~ (l3_lattices @ X1)
% 2.09/2.30          | (v2_struct_0 @ X1))),
% 2.09/2.30      inference('cnf', [status(esa)], [d16_lattice3])).
% 2.09/2.30  thf('71', plain,
% 2.09/2.30      (![X0 : $i]:
% 2.09/2.31         ((v2_struct_0 @ sk_A)
% 2.09/2.31          | ~ (l3_lattices @ sk_A)
% 2.09/2.31          | (r3_lattice3 @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ X0)
% 2.09/2.31          | ~ (r1_lattices @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ 
% 2.09/2.31               (sk_D @ X0 @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ sk_A)))),
% 2.09/2.31      inference('sup-', [status(thm)], ['69', '70'])).
% 2.09/2.31  thf('72', plain, ((l3_lattices @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('73', plain,
% 2.09/2.31      (![X0 : $i]:
% 2.09/2.31         ((v2_struct_0 @ sk_A)
% 2.09/2.31          | (r3_lattice3 @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ X0)
% 2.09/2.31          | ~ (r1_lattices @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ 
% 2.09/2.31               (sk_D @ X0 @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ sk_A)))),
% 2.09/2.31      inference('demod', [status(thm)], ['71', '72'])).
% 2.09/2.31  thf('74', plain, (~ (v2_struct_0 @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('75', plain,
% 2.09/2.31      (![X0 : $i]:
% 2.09/2.31         (~ (r1_lattices @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ 
% 2.09/2.31             (sk_D @ X0 @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ sk_A))
% 2.09/2.31          | (r3_lattice3 @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ X0))),
% 2.09/2.31      inference('clc', [status(thm)], ['73', '74'])).
% 2.09/2.31  thf('76', plain,
% 2.09/2.31      (((v2_struct_0 @ sk_A)
% 2.09/2.31        | (r3_lattice3 @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ 
% 2.09/2.31           (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 2.09/2.31      inference('clc', [status(thm)], ['68', '75'])).
% 2.09/2.31  thf('77', plain, (~ (v2_struct_0 @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('78', plain,
% 2.09/2.31      ((r3_lattice3 @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ 
% 2.09/2.31        (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))),
% 2.09/2.31      inference('clc', [status(thm)], ['76', '77'])).
% 2.09/2.31  thf('79', plain,
% 2.09/2.31      ((m1_subset_1 @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 2.09/2.31      inference('clc', [status(thm)], ['24', '25'])).
% 2.09/2.31  thf(t40_lattice3, axiom,
% 2.09/2.31    (![A:$i]:
% 2.09/2.31     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.09/2.31         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 2.09/2.31       ( ![B:$i]:
% 2.09/2.31         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.09/2.31           ( ![C:$i]:
% 2.09/2.31             ( ( r3_lattice3 @ A @ B @ C ) =>
% 2.09/2.31               ( r3_lattices @ A @ B @ ( k16_lattice3 @ A @ C ) ) ) ) ) ) ))).
% 2.09/2.31  thf('80', plain,
% 2.09/2.31      (![X29 : $i, X30 : $i, X31 : $i]:
% 2.09/2.31         (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X30))
% 2.09/2.31          | (r3_lattices @ X30 @ X29 @ (k16_lattice3 @ X30 @ X31))
% 2.09/2.31          | ~ (r3_lattice3 @ X30 @ X29 @ X31)
% 2.09/2.31          | ~ (l3_lattices @ X30)
% 2.09/2.31          | ~ (v4_lattice3 @ X30)
% 2.09/2.31          | ~ (v10_lattices @ X30)
% 2.09/2.31          | (v2_struct_0 @ X30))),
% 2.09/2.31      inference('cnf', [status(esa)], [t40_lattice3])).
% 2.09/2.31  thf('81', plain,
% 2.09/2.31      (![X0 : $i]:
% 2.09/2.31         ((v2_struct_0 @ sk_A)
% 2.09/2.31          | ~ (v10_lattices @ sk_A)
% 2.09/2.31          | ~ (v4_lattice3 @ sk_A)
% 2.09/2.31          | ~ (l3_lattices @ sk_A)
% 2.09/2.31          | ~ (r3_lattice3 @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ X0)
% 2.09/2.31          | (r3_lattices @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ 
% 2.09/2.31             (k16_lattice3 @ sk_A @ X0)))),
% 2.09/2.31      inference('sup-', [status(thm)], ['79', '80'])).
% 2.09/2.31  thf('82', plain, ((v10_lattices @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('83', plain, ((v4_lattice3 @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('84', plain, ((l3_lattices @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('85', plain,
% 2.09/2.31      (![X0 : $i]:
% 2.09/2.31         ((v2_struct_0 @ sk_A)
% 2.09/2.31          | ~ (r3_lattice3 @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ X0)
% 2.09/2.31          | (r3_lattices @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ 
% 2.09/2.31             (k16_lattice3 @ sk_A @ X0)))),
% 2.09/2.31      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 2.09/2.31  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('87', plain,
% 2.09/2.31      (![X0 : $i]:
% 2.09/2.31         ((r3_lattices @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ 
% 2.09/2.31           (k16_lattice3 @ sk_A @ X0))
% 2.09/2.31          | ~ (r3_lattice3 @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ X0))),
% 2.09/2.31      inference('clc', [status(thm)], ['85', '86'])).
% 2.09/2.31  thf('88', plain,
% 2.09/2.31      ((r3_lattices @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ 
% 2.09/2.31        (k16_lattice3 @ sk_A @ 
% 2.09/2.31         (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 2.09/2.31      inference('sup-', [status(thm)], ['78', '87'])).
% 2.09/2.31  thf(t37_lattice3, axiom,
% 2.09/2.31    (![A:$i]:
% 2.09/2.31     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.09/2.31         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 2.09/2.31       ( ![B:$i]:
% 2.09/2.31         ( ( k15_lattice3 @ A @ B ) =
% 2.09/2.31           ( k16_lattice3 @ A @ ( a_2_2_lattice3 @ A @ B ) ) ) ) ))).
% 2.09/2.31  thf('89', plain,
% 2.09/2.31      (![X27 : $i, X28 : $i]:
% 2.09/2.31         (((k15_lattice3 @ X27 @ X28)
% 2.09/2.31            = (k16_lattice3 @ X27 @ (a_2_2_lattice3 @ X27 @ X28)))
% 2.09/2.31          | ~ (l3_lattices @ X27)
% 2.09/2.31          | ~ (v4_lattice3 @ X27)
% 2.09/2.31          | ~ (v10_lattices @ X27)
% 2.09/2.31          | (v2_struct_0 @ X27))),
% 2.09/2.31      inference('cnf', [status(esa)], [t37_lattice3])).
% 2.09/2.31  thf('90', plain,
% 2.09/2.31      (![X27 : $i, X28 : $i]:
% 2.09/2.31         (((k15_lattice3 @ X27 @ X28)
% 2.09/2.31            = (k16_lattice3 @ X27 @ (a_2_2_lattice3 @ X27 @ X28)))
% 2.09/2.31          | ~ (l3_lattices @ X27)
% 2.09/2.31          | ~ (v4_lattice3 @ X27)
% 2.09/2.31          | ~ (v10_lattices @ X27)
% 2.09/2.31          | (v2_struct_0 @ X27))),
% 2.09/2.31      inference('cnf', [status(esa)], [t37_lattice3])).
% 2.09/2.31  thf('91', plain, ((r3_lattice3 @ sk_A @ sk_B @ sk_C)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('92', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('93', plain,
% 2.09/2.31      (![X14 : $i, X15 : $i, X17 : $i]:
% 2.09/2.31         (~ (r3_lattice3 @ X14 @ X17 @ X15)
% 2.09/2.31          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X14))
% 2.09/2.31          | (r2_hidden @ X17 @ (a_2_1_lattice3 @ X14 @ X15))
% 2.09/2.31          | (v2_struct_0 @ X14)
% 2.09/2.31          | ~ (l3_lattices @ X14))),
% 2.09/2.31      inference('simplify', [status(thm)], ['27'])).
% 2.09/2.31  thf('94', plain,
% 2.09/2.31      (![X0 : $i]:
% 2.09/2.31         (~ (l3_lattices @ sk_A)
% 2.09/2.31          | (v2_struct_0 @ sk_A)
% 2.09/2.31          | (r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 2.09/2.31          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 2.09/2.31      inference('sup-', [status(thm)], ['92', '93'])).
% 2.09/2.31  thf('95', plain, ((l3_lattices @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('96', plain,
% 2.09/2.31      (![X0 : $i]:
% 2.09/2.31         ((v2_struct_0 @ sk_A)
% 2.09/2.31          | (r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 2.09/2.31          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 2.09/2.31      inference('demod', [status(thm)], ['94', '95'])).
% 2.09/2.31  thf('97', plain, (~ (v2_struct_0 @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('98', plain,
% 2.09/2.31      (![X0 : $i]:
% 2.09/2.31         (~ (r3_lattice3 @ sk_A @ sk_B @ X0)
% 2.09/2.31          | (r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0)))),
% 2.09/2.31      inference('clc', [status(thm)], ['96', '97'])).
% 2.09/2.31  thf('99', plain, ((r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))),
% 2.09/2.31      inference('sup-', [status(thm)], ['91', '98'])).
% 2.09/2.31  thf('100', plain, ((r2_hidden @ sk_B @ sk_C)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('101', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('102', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('103', plain,
% 2.09/2.31      (![X5 : $i, X6 : $i, X9 : $i]:
% 2.09/2.31         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 2.09/2.31          | (r2_hidden @ (sk_D_1 @ X9 @ X5 @ X6) @ X9)
% 2.09/2.31          | (r4_lattice3 @ X6 @ X5 @ X9)
% 2.09/2.31          | ~ (l3_lattices @ X6)
% 2.09/2.31          | (v2_struct_0 @ X6))),
% 2.09/2.31      inference('cnf', [status(esa)], [d17_lattice3])).
% 2.09/2.31  thf('104', plain,
% 2.09/2.31      (![X0 : $i]:
% 2.09/2.31         ((v2_struct_0 @ sk_A)
% 2.09/2.31          | ~ (l3_lattices @ sk_A)
% 2.09/2.31          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 2.09/2.31          | (r2_hidden @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0))),
% 2.09/2.31      inference('sup-', [status(thm)], ['102', '103'])).
% 2.09/2.31  thf('105', plain, ((l3_lattices @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('106', plain,
% 2.09/2.31      (![X0 : $i]:
% 2.09/2.31         ((v2_struct_0 @ sk_A)
% 2.09/2.31          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 2.09/2.31          | (r2_hidden @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0))),
% 2.09/2.31      inference('demod', [status(thm)], ['104', '105'])).
% 2.09/2.31  thf('107', plain, (~ (v2_struct_0 @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('108', plain,
% 2.09/2.31      (![X0 : $i]:
% 2.09/2.31         ((r2_hidden @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0)
% 2.09/2.31          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 2.09/2.31      inference('clc', [status(thm)], ['106', '107'])).
% 2.09/2.31  thf('109', plain,
% 2.09/2.31      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.09/2.31         (~ (l3_lattices @ X14)
% 2.09/2.31          | (v2_struct_0 @ X14)
% 2.09/2.31          | ((X16) = (sk_D_3 @ X15 @ X14 @ X16))
% 2.09/2.31          | ~ (r2_hidden @ X16 @ (a_2_1_lattice3 @ X14 @ X15)))),
% 2.09/2.31      inference('cnf', [status(esa)], [fraenkel_a_2_1_lattice3])).
% 2.09/2.31  thf('110', plain,
% 2.09/2.31      (![X0 : $i, X1 : $i]:
% 2.09/2.31         ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0))
% 2.09/2.31          | ((sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A)
% 2.09/2.31              = (sk_D_3 @ X0 @ X1 @ 
% 2.09/2.31                 (sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A)))
% 2.09/2.31          | (v2_struct_0 @ X1)
% 2.09/2.31          | ~ (l3_lattices @ X1))),
% 2.09/2.31      inference('sup-', [status(thm)], ['108', '109'])).
% 2.09/2.31  thf('111', plain,
% 2.09/2.31      (![X0 : $i]:
% 2.09/2.31         ((r2_hidden @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0)
% 2.09/2.31          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 2.09/2.31      inference('clc', [status(thm)], ['106', '107'])).
% 2.09/2.31  thf('112', plain,
% 2.09/2.31      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.09/2.31         (~ (l3_lattices @ X14)
% 2.09/2.31          | (v2_struct_0 @ X14)
% 2.09/2.31          | (r3_lattice3 @ X14 @ (sk_D_3 @ X15 @ X14 @ X16) @ X15)
% 2.09/2.31          | ~ (r2_hidden @ X16 @ (a_2_1_lattice3 @ X14 @ X15)))),
% 2.09/2.31      inference('cnf', [status(esa)], [fraenkel_a_2_1_lattice3])).
% 2.09/2.31  thf('113', plain,
% 2.09/2.31      (![X0 : $i, X1 : $i]:
% 2.09/2.31         ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0))
% 2.09/2.31          | (r3_lattice3 @ X1 @ 
% 2.09/2.31             (sk_D_3 @ X0 @ X1 @ 
% 2.09/2.31              (sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A)) @ 
% 2.09/2.31             X0)
% 2.09/2.31          | (v2_struct_0 @ X1)
% 2.09/2.31          | ~ (l3_lattices @ X1))),
% 2.09/2.31      inference('sup-', [status(thm)], ['111', '112'])).
% 2.09/2.31  thf('114', plain,
% 2.09/2.31      (![X0 : $i, X1 : $i]:
% 2.09/2.31         ((r3_lattice3 @ X1 @ 
% 2.09/2.31           (sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A) @ X0)
% 2.09/2.31          | ~ (l3_lattices @ X1)
% 2.09/2.31          | (v2_struct_0 @ X1)
% 2.09/2.31          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0))
% 2.09/2.31          | ~ (l3_lattices @ X1)
% 2.09/2.31          | (v2_struct_0 @ X1)
% 2.09/2.31          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0)))),
% 2.09/2.31      inference('sup+', [status(thm)], ['110', '113'])).
% 2.09/2.31  thf('115', plain,
% 2.09/2.31      (![X0 : $i, X1 : $i]:
% 2.09/2.31         ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0))
% 2.09/2.31          | (v2_struct_0 @ X1)
% 2.09/2.31          | ~ (l3_lattices @ X1)
% 2.09/2.31          | (r3_lattice3 @ X1 @ 
% 2.09/2.31             (sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A) @ X0))),
% 2.09/2.31      inference('simplify', [status(thm)], ['114'])).
% 2.09/2.31  thf('116', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('117', plain,
% 2.09/2.31      (![X5 : $i, X6 : $i, X9 : $i]:
% 2.09/2.31         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 2.09/2.31          | (m1_subset_1 @ (sk_D_1 @ X9 @ X5 @ X6) @ (u1_struct_0 @ X6))
% 2.09/2.31          | (r4_lattice3 @ X6 @ X5 @ X9)
% 2.09/2.31          | ~ (l3_lattices @ X6)
% 2.09/2.31          | (v2_struct_0 @ X6))),
% 2.09/2.31      inference('cnf', [status(esa)], [d17_lattice3])).
% 2.09/2.31  thf('118', plain,
% 2.09/2.31      (![X0 : $i]:
% 2.09/2.31         ((v2_struct_0 @ sk_A)
% 2.09/2.31          | ~ (l3_lattices @ sk_A)
% 2.09/2.31          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 2.09/2.31          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.09/2.31      inference('sup-', [status(thm)], ['116', '117'])).
% 2.09/2.31  thf('119', plain, ((l3_lattices @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('120', plain,
% 2.09/2.31      (![X0 : $i]:
% 2.09/2.31         ((v2_struct_0 @ sk_A)
% 2.09/2.31          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 2.09/2.31          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 2.09/2.31      inference('demod', [status(thm)], ['118', '119'])).
% 2.09/2.31  thf('121', plain, (~ (v2_struct_0 @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('122', plain,
% 2.09/2.31      (![X0 : $i]:
% 2.09/2.31         ((m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.09/2.31          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 2.09/2.31      inference('clc', [status(thm)], ['120', '121'])).
% 2.09/2.31  thf('123', plain,
% 2.09/2.31      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.09/2.31         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 2.09/2.31          | ~ (r3_lattice3 @ X1 @ X0 @ X2)
% 2.09/2.31          | ~ (r2_hidden @ X3 @ X2)
% 2.09/2.31          | (r1_lattices @ X1 @ X0 @ X3)
% 2.09/2.31          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 2.09/2.31          | ~ (l3_lattices @ X1)
% 2.09/2.31          | (v2_struct_0 @ X1))),
% 2.09/2.31      inference('cnf', [status(esa)], [d16_lattice3])).
% 2.09/2.31  thf('124', plain,
% 2.09/2.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.09/2.31         ((r4_lattice3 @ sk_A @ sk_B @ X0)
% 2.09/2.31          | (v2_struct_0 @ sk_A)
% 2.09/2.31          | ~ (l3_lattices @ sk_A)
% 2.09/2.31          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.09/2.31          | (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X1)
% 2.09/2.31          | ~ (r2_hidden @ X1 @ X2)
% 2.09/2.31          | ~ (r3_lattice3 @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X2))),
% 2.09/2.31      inference('sup-', [status(thm)], ['122', '123'])).
% 2.09/2.31  thf('125', plain, ((l3_lattices @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('126', plain,
% 2.09/2.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.09/2.31         ((r4_lattice3 @ sk_A @ sk_B @ X0)
% 2.09/2.31          | (v2_struct_0 @ sk_A)
% 2.09/2.31          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.09/2.31          | (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X1)
% 2.09/2.31          | ~ (r2_hidden @ X1 @ X2)
% 2.09/2.31          | ~ (r3_lattice3 @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X2))),
% 2.09/2.31      inference('demod', [status(thm)], ['124', '125'])).
% 2.09/2.31  thf('127', plain,
% 2.09/2.31      (![X0 : $i, X1 : $i]:
% 2.09/2.31         (~ (l3_lattices @ sk_A)
% 2.09/2.31          | (v2_struct_0 @ sk_A)
% 2.09/2.31          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 2.09/2.31          | ~ (r2_hidden @ X1 @ X0)
% 2.09/2.31          | (r1_lattices @ sk_A @ 
% 2.09/2.31             (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ X0) @ sk_B @ sk_A) @ X1)
% 2.09/2.31          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.09/2.31          | (v2_struct_0 @ sk_A)
% 2.09/2.31          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0)))),
% 2.09/2.31      inference('sup-', [status(thm)], ['115', '126'])).
% 2.09/2.31  thf('128', plain, ((l3_lattices @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('129', plain,
% 2.09/2.31      (![X0 : $i, X1 : $i]:
% 2.09/2.31         ((v2_struct_0 @ sk_A)
% 2.09/2.31          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 2.09/2.31          | ~ (r2_hidden @ X1 @ X0)
% 2.09/2.31          | (r1_lattices @ sk_A @ 
% 2.09/2.31             (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ X0) @ sk_B @ sk_A) @ X1)
% 2.09/2.31          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.09/2.31          | (v2_struct_0 @ sk_A)
% 2.09/2.31          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0)))),
% 2.09/2.31      inference('demod', [status(thm)], ['127', '128'])).
% 2.09/2.31  thf('130', plain,
% 2.09/2.31      (![X0 : $i, X1 : $i]:
% 2.09/2.31         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.09/2.31          | (r1_lattices @ sk_A @ 
% 2.09/2.31             (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ X0) @ sk_B @ sk_A) @ X1)
% 2.09/2.31          | ~ (r2_hidden @ X1 @ X0)
% 2.09/2.31          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 2.09/2.31          | (v2_struct_0 @ sk_A))),
% 2.09/2.31      inference('simplify', [status(thm)], ['129'])).
% 2.09/2.31  thf('131', plain,
% 2.09/2.31      (![X0 : $i]:
% 2.09/2.31         ((v2_struct_0 @ sk_A)
% 2.09/2.31          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 2.09/2.31          | ~ (r2_hidden @ sk_B @ X0)
% 2.09/2.31          | (r1_lattices @ sk_A @ 
% 2.09/2.31             (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ X0) @ sk_B @ sk_A) @ sk_B))),
% 2.09/2.31      inference('sup-', [status(thm)], ['101', '130'])).
% 2.09/2.31  thf('132', plain,
% 2.09/2.31      (((r1_lattices @ sk_A @ 
% 2.09/2.31         (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_B @ sk_A) @ sk_B)
% 2.09/2.31        | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))
% 2.09/2.31        | (v2_struct_0 @ sk_A))),
% 2.09/2.31      inference('sup-', [status(thm)], ['100', '131'])).
% 2.09/2.31  thf('133', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('134', plain,
% 2.09/2.31      (![X5 : $i, X6 : $i, X9 : $i]:
% 2.09/2.31         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 2.09/2.31          | ~ (r1_lattices @ X6 @ (sk_D_1 @ X9 @ X5 @ X6) @ X5)
% 2.09/2.31          | (r4_lattice3 @ X6 @ X5 @ X9)
% 2.09/2.31          | ~ (l3_lattices @ X6)
% 2.09/2.31          | (v2_struct_0 @ X6))),
% 2.09/2.31      inference('cnf', [status(esa)], [d17_lattice3])).
% 2.09/2.31  thf('135', plain,
% 2.09/2.31      (![X0 : $i]:
% 2.09/2.31         ((v2_struct_0 @ sk_A)
% 2.09/2.31          | ~ (l3_lattices @ sk_A)
% 2.09/2.31          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 2.09/2.31          | ~ (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_B))),
% 2.09/2.31      inference('sup-', [status(thm)], ['133', '134'])).
% 2.09/2.31  thf('136', plain, ((l3_lattices @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('137', plain,
% 2.09/2.31      (![X0 : $i]:
% 2.09/2.31         ((v2_struct_0 @ sk_A)
% 2.09/2.31          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 2.09/2.31          | ~ (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_B))),
% 2.09/2.31      inference('demod', [status(thm)], ['135', '136'])).
% 2.09/2.31  thf('138', plain, (~ (v2_struct_0 @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('139', plain,
% 2.09/2.31      (![X0 : $i]:
% 2.09/2.31         (~ (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_B)
% 2.09/2.31          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 2.09/2.31      inference('clc', [status(thm)], ['137', '138'])).
% 2.09/2.31  thf('140', plain,
% 2.09/2.31      (((v2_struct_0 @ sk_A)
% 2.09/2.31        | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C)))),
% 2.09/2.31      inference('clc', [status(thm)], ['132', '139'])).
% 2.09/2.31  thf('141', plain, (~ (v2_struct_0 @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('142', plain,
% 2.09/2.31      ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))),
% 2.09/2.31      inference('clc', [status(thm)], ['140', '141'])).
% 2.09/2.31  thf('143', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf(d21_lattice3, axiom,
% 2.09/2.31    (![A:$i]:
% 2.09/2.31     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 2.09/2.31       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.09/2.31           ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 2.09/2.31         ( ![B:$i,C:$i]:
% 2.09/2.31           ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.09/2.31             ( ( ( C ) = ( k15_lattice3 @ A @ B ) ) <=>
% 2.09/2.31               ( ( r4_lattice3 @ A @ C @ B ) & 
% 2.09/2.31                 ( ![D:$i]:
% 2.09/2.31                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 2.09/2.31                     ( ( r4_lattice3 @ A @ D @ B ) =>
% 2.09/2.31                       ( r1_lattices @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 2.09/2.31  thf('144', plain,
% 2.09/2.31      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.09/2.31         ((v2_struct_0 @ X10)
% 2.09/2.31          | ~ (v10_lattices @ X10)
% 2.09/2.31          | ~ (v4_lattice3 @ X10)
% 2.09/2.31          | ~ (l3_lattices @ X10)
% 2.09/2.31          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 2.09/2.31          | ~ (r4_lattice3 @ X10 @ X11 @ X12)
% 2.09/2.31          | (r4_lattice3 @ X10 @ (sk_D_2 @ X11 @ X12 @ X10) @ X12)
% 2.09/2.31          | ((X11) = (k15_lattice3 @ X10 @ X12))
% 2.09/2.31          | ~ (l3_lattices @ X10)
% 2.09/2.31          | (v2_struct_0 @ X10))),
% 2.09/2.31      inference('cnf', [status(esa)], [d21_lattice3])).
% 2.09/2.31  thf('145', plain,
% 2.09/2.31      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.09/2.31         (((X11) = (k15_lattice3 @ X10 @ X12))
% 2.09/2.31          | (r4_lattice3 @ X10 @ (sk_D_2 @ X11 @ X12 @ X10) @ X12)
% 2.09/2.31          | ~ (r4_lattice3 @ X10 @ X11 @ X12)
% 2.09/2.31          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 2.09/2.31          | ~ (l3_lattices @ X10)
% 2.09/2.31          | ~ (v4_lattice3 @ X10)
% 2.09/2.31          | ~ (v10_lattices @ X10)
% 2.09/2.31          | (v2_struct_0 @ X10))),
% 2.09/2.31      inference('simplify', [status(thm)], ['144'])).
% 2.09/2.31  thf('146', plain,
% 2.09/2.31      (![X0 : $i]:
% 2.09/2.31         ((v2_struct_0 @ sk_A)
% 2.09/2.31          | ~ (v10_lattices @ sk_A)
% 2.09/2.31          | ~ (v4_lattice3 @ sk_A)
% 2.09/2.31          | ~ (l3_lattices @ sk_A)
% 2.09/2.31          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0)
% 2.09/2.31          | (r4_lattice3 @ sk_A @ (sk_D_2 @ sk_B @ X0 @ sk_A) @ X0)
% 2.09/2.31          | ((sk_B) = (k15_lattice3 @ sk_A @ X0)))),
% 2.09/2.31      inference('sup-', [status(thm)], ['143', '145'])).
% 2.09/2.31  thf('147', plain, ((v10_lattices @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('148', plain, ((v4_lattice3 @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('149', plain, ((l3_lattices @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('150', plain,
% 2.09/2.31      (![X0 : $i]:
% 2.09/2.31         ((v2_struct_0 @ sk_A)
% 2.09/2.31          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0)
% 2.09/2.31          | (r4_lattice3 @ sk_A @ (sk_D_2 @ sk_B @ X0 @ sk_A) @ X0)
% 2.09/2.31          | ((sk_B) = (k15_lattice3 @ sk_A @ X0)))),
% 2.09/2.31      inference('demod', [status(thm)], ['146', '147', '148', '149'])).
% 2.09/2.31  thf('151', plain,
% 2.09/2.31      ((((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 2.09/2.31        | (r4_lattice3 @ sk_A @ 
% 2.09/2.31           (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A) @ 
% 2.09/2.31           (a_2_1_lattice3 @ sk_A @ sk_C))
% 2.09/2.31        | (v2_struct_0 @ sk_A))),
% 2.09/2.31      inference('sup-', [status(thm)], ['142', '150'])).
% 2.09/2.31  thf('152', plain, (~ (v2_struct_0 @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('153', plain,
% 2.09/2.31      (((r4_lattice3 @ sk_A @ 
% 2.09/2.31         (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A) @ 
% 2.09/2.31         (a_2_1_lattice3 @ sk_A @ sk_C))
% 2.09/2.31        | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 2.09/2.31      inference('clc', [status(thm)], ['151', '152'])).
% 2.09/2.31  thf('154', plain,
% 2.09/2.31      ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))),
% 2.09/2.31      inference('clc', [status(thm)], ['140', '141'])).
% 2.09/2.31  thf('155', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('156', plain,
% 2.09/2.31      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.09/2.31         ((v2_struct_0 @ X10)
% 2.09/2.31          | ~ (v10_lattices @ X10)
% 2.09/2.31          | ~ (v4_lattice3 @ X10)
% 2.09/2.31          | ~ (l3_lattices @ X10)
% 2.09/2.31          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 2.09/2.31          | ~ (r4_lattice3 @ X10 @ X11 @ X12)
% 2.09/2.31          | (m1_subset_1 @ (sk_D_2 @ X11 @ X12 @ X10) @ (u1_struct_0 @ X10))
% 2.09/2.31          | ((X11) = (k15_lattice3 @ X10 @ X12))
% 2.09/2.31          | ~ (l3_lattices @ X10)
% 2.09/2.31          | (v2_struct_0 @ X10))),
% 2.09/2.31      inference('cnf', [status(esa)], [d21_lattice3])).
% 2.09/2.31  thf('157', plain,
% 2.09/2.31      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.09/2.31         (((X11) = (k15_lattice3 @ X10 @ X12))
% 2.09/2.31          | (m1_subset_1 @ (sk_D_2 @ X11 @ X12 @ X10) @ (u1_struct_0 @ X10))
% 2.09/2.31          | ~ (r4_lattice3 @ X10 @ X11 @ X12)
% 2.09/2.31          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 2.09/2.31          | ~ (l3_lattices @ X10)
% 2.09/2.31          | ~ (v4_lattice3 @ X10)
% 2.09/2.31          | ~ (v10_lattices @ X10)
% 2.09/2.31          | (v2_struct_0 @ X10))),
% 2.09/2.31      inference('simplify', [status(thm)], ['156'])).
% 2.09/2.31  thf('158', plain,
% 2.09/2.31      (![X0 : $i]:
% 2.09/2.31         ((v2_struct_0 @ sk_A)
% 2.09/2.31          | ~ (v10_lattices @ sk_A)
% 2.09/2.31          | ~ (v4_lattice3 @ sk_A)
% 2.09/2.31          | ~ (l3_lattices @ sk_A)
% 2.09/2.31          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0)
% 2.09/2.31          | (m1_subset_1 @ (sk_D_2 @ sk_B @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.09/2.31          | ((sk_B) = (k15_lattice3 @ sk_A @ X0)))),
% 2.09/2.31      inference('sup-', [status(thm)], ['155', '157'])).
% 2.09/2.31  thf('159', plain, ((v10_lattices @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('160', plain, ((v4_lattice3 @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('161', plain, ((l3_lattices @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('162', plain,
% 2.09/2.31      (![X0 : $i]:
% 2.09/2.31         ((v2_struct_0 @ sk_A)
% 2.09/2.31          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0)
% 2.09/2.31          | (m1_subset_1 @ (sk_D_2 @ sk_B @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.09/2.31          | ((sk_B) = (k15_lattice3 @ sk_A @ X0)))),
% 2.09/2.31      inference('demod', [status(thm)], ['158', '159', '160', '161'])).
% 2.09/2.31  thf('163', plain,
% 2.09/2.31      ((((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 2.09/2.31        | (m1_subset_1 @ 
% 2.09/2.31           (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A) @ 
% 2.09/2.31           (u1_struct_0 @ sk_A))
% 2.09/2.31        | (v2_struct_0 @ sk_A))),
% 2.09/2.31      inference('sup-', [status(thm)], ['154', '162'])).
% 2.09/2.31  thf('164', plain, (~ (v2_struct_0 @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('165', plain,
% 2.09/2.31      (((m1_subset_1 @ 
% 2.09/2.31         (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A) @ 
% 2.09/2.31         (u1_struct_0 @ sk_A))
% 2.09/2.31        | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 2.09/2.31      inference('clc', [status(thm)], ['163', '164'])).
% 2.09/2.31  thf('166', plain,
% 2.09/2.31      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 2.09/2.31         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 2.09/2.31          | ~ (r4_lattice3 @ X6 @ X5 @ X7)
% 2.09/2.31          | ~ (r2_hidden @ X8 @ X7)
% 2.09/2.31          | (r1_lattices @ X6 @ X8 @ X5)
% 2.09/2.31          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X6))
% 2.09/2.31          | ~ (l3_lattices @ X6)
% 2.09/2.31          | (v2_struct_0 @ X6))),
% 2.09/2.31      inference('cnf', [status(esa)], [d17_lattice3])).
% 2.09/2.31  thf('167', plain,
% 2.09/2.31      (![X0 : $i, X1 : $i]:
% 2.09/2.31         (((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 2.09/2.31          | (v2_struct_0 @ sk_A)
% 2.09/2.31          | ~ (l3_lattices @ sk_A)
% 2.09/2.31          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.09/2.31          | (r1_lattices @ sk_A @ X0 @ 
% 2.09/2.31             (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A))
% 2.09/2.31          | ~ (r2_hidden @ X0 @ X1)
% 2.09/2.31          | ~ (r4_lattice3 @ sk_A @ 
% 2.09/2.31               (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A) @ X1))),
% 2.09/2.31      inference('sup-', [status(thm)], ['165', '166'])).
% 2.09/2.31  thf('168', plain, ((l3_lattices @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('169', plain,
% 2.09/2.31      (![X0 : $i, X1 : $i]:
% 2.09/2.31         (((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 2.09/2.31          | (v2_struct_0 @ sk_A)
% 2.09/2.31          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.09/2.31          | (r1_lattices @ sk_A @ X0 @ 
% 2.09/2.31             (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A))
% 2.09/2.31          | ~ (r2_hidden @ X0 @ X1)
% 2.09/2.31          | ~ (r4_lattice3 @ sk_A @ 
% 2.09/2.31               (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A) @ X1))),
% 2.09/2.31      inference('demod', [status(thm)], ['167', '168'])).
% 2.09/2.31  thf('170', plain,
% 2.09/2.31      (![X0 : $i]:
% 2.09/2.31         (((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 2.09/2.31          | ~ (r2_hidden @ X0 @ (a_2_1_lattice3 @ sk_A @ sk_C))
% 2.09/2.31          | (r1_lattices @ sk_A @ X0 @ 
% 2.09/2.31             (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A))
% 2.09/2.31          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.09/2.31          | (v2_struct_0 @ sk_A)
% 2.09/2.31          | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 2.09/2.31      inference('sup-', [status(thm)], ['153', '169'])).
% 2.09/2.31  thf('171', plain,
% 2.09/2.31      (![X0 : $i]:
% 2.09/2.31         ((v2_struct_0 @ sk_A)
% 2.09/2.31          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.09/2.31          | (r1_lattices @ sk_A @ X0 @ 
% 2.09/2.31             (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A))
% 2.09/2.31          | ~ (r2_hidden @ X0 @ (a_2_1_lattice3 @ sk_A @ sk_C))
% 2.09/2.31          | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 2.09/2.31      inference('simplify', [status(thm)], ['170'])).
% 2.09/2.31  thf('172', plain,
% 2.09/2.31      ((((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 2.09/2.31        | (r1_lattices @ sk_A @ sk_B @ 
% 2.09/2.31           (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A))
% 2.09/2.31        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 2.09/2.31        | (v2_struct_0 @ sk_A))),
% 2.09/2.31      inference('sup-', [status(thm)], ['99', '171'])).
% 2.09/2.31  thf('173', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('174', plain,
% 2.09/2.31      ((((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 2.09/2.31        | (r1_lattices @ sk_A @ sk_B @ 
% 2.09/2.31           (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A))
% 2.09/2.31        | (v2_struct_0 @ sk_A))),
% 2.09/2.31      inference('demod', [status(thm)], ['172', '173'])).
% 2.09/2.31  thf('175', plain, (~ (v2_struct_0 @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('176', plain,
% 2.09/2.31      (((r1_lattices @ sk_A @ sk_B @ 
% 2.09/2.31         (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A))
% 2.09/2.31        | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 2.09/2.31      inference('clc', [status(thm)], ['174', '175'])).
% 2.09/2.31  thf('177', plain,
% 2.09/2.31      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.09/2.31         ((v2_struct_0 @ X10)
% 2.09/2.31          | ~ (v10_lattices @ X10)
% 2.09/2.31          | ~ (v4_lattice3 @ X10)
% 2.09/2.31          | ~ (l3_lattices @ X10)
% 2.09/2.31          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 2.09/2.31          | ~ (r4_lattice3 @ X10 @ X11 @ X12)
% 2.09/2.31          | ~ (r1_lattices @ X10 @ X11 @ (sk_D_2 @ X11 @ X12 @ X10))
% 2.09/2.31          | ((X11) = (k15_lattice3 @ X10 @ X12))
% 2.09/2.31          | ~ (l3_lattices @ X10)
% 2.09/2.31          | (v2_struct_0 @ X10))),
% 2.09/2.31      inference('cnf', [status(esa)], [d21_lattice3])).
% 2.09/2.31  thf('178', plain,
% 2.09/2.31      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.09/2.31         (((X11) = (k15_lattice3 @ X10 @ X12))
% 2.09/2.31          | ~ (r1_lattices @ X10 @ X11 @ (sk_D_2 @ X11 @ X12 @ X10))
% 2.09/2.31          | ~ (r4_lattice3 @ X10 @ X11 @ X12)
% 2.09/2.31          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 2.09/2.31          | ~ (l3_lattices @ X10)
% 2.09/2.31          | ~ (v4_lattice3 @ X10)
% 2.09/2.31          | ~ (v10_lattices @ X10)
% 2.09/2.31          | (v2_struct_0 @ X10))),
% 2.09/2.31      inference('simplify', [status(thm)], ['177'])).
% 2.09/2.31  thf('179', plain,
% 2.09/2.31      ((((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 2.09/2.31        | (v2_struct_0 @ sk_A)
% 2.09/2.31        | ~ (v10_lattices @ sk_A)
% 2.09/2.31        | ~ (v4_lattice3 @ sk_A)
% 2.09/2.31        | ~ (l3_lattices @ sk_A)
% 2.09/2.31        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 2.09/2.31        | ~ (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))
% 2.09/2.31        | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 2.09/2.31      inference('sup-', [status(thm)], ['176', '178'])).
% 2.09/2.31  thf('180', plain, ((v10_lattices @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('181', plain, ((v4_lattice3 @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('182', plain, ((l3_lattices @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('183', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('184', plain,
% 2.09/2.31      ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))),
% 2.09/2.31      inference('clc', [status(thm)], ['140', '141'])).
% 2.09/2.31  thf('185', plain,
% 2.09/2.31      ((((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 2.09/2.31        | (v2_struct_0 @ sk_A)
% 2.09/2.31        | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 2.09/2.31      inference('demod', [status(thm)],
% 2.09/2.31                ['179', '180', '181', '182', '183', '184'])).
% 2.09/2.31  thf('186', plain,
% 2.09/2.31      (((v2_struct_0 @ sk_A)
% 2.09/2.31        | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 2.09/2.31      inference('simplify', [status(thm)], ['185'])).
% 2.09/2.31  thf('187', plain, (~ (v2_struct_0 @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('188', plain,
% 2.09/2.31      (((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))),
% 2.09/2.31      inference('clc', [status(thm)], ['186', '187'])).
% 2.09/2.31  thf('189', plain,
% 2.09/2.31      (![X27 : $i, X28 : $i]:
% 2.09/2.31         (((k15_lattice3 @ X27 @ X28)
% 2.09/2.31            = (k16_lattice3 @ X27 @ (a_2_2_lattice3 @ X27 @ X28)))
% 2.09/2.31          | ~ (l3_lattices @ X27)
% 2.09/2.31          | ~ (v4_lattice3 @ X27)
% 2.09/2.31          | ~ (v10_lattices @ X27)
% 2.09/2.31          | (v2_struct_0 @ X27))),
% 2.09/2.31      inference('cnf', [status(esa)], [t37_lattice3])).
% 2.09/2.31  thf('190', plain,
% 2.09/2.31      (![X22 : $i, X23 : $i, X24 : $i]:
% 2.09/2.31         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 2.09/2.31          | ((X22) != (k16_lattice3 @ X23 @ X24))
% 2.09/2.31          | (r3_lattice3 @ X23 @ X22 @ X24)
% 2.09/2.31          | ~ (l3_lattices @ X23)
% 2.09/2.31          | ~ (v4_lattice3 @ X23)
% 2.09/2.31          | ~ (v10_lattices @ X23)
% 2.09/2.31          | (v2_struct_0 @ X23))),
% 2.09/2.31      inference('cnf', [status(esa)], [t34_lattice3])).
% 2.09/2.31  thf('191', plain,
% 2.09/2.31      (![X23 : $i, X24 : $i]:
% 2.09/2.31         ((v2_struct_0 @ X23)
% 2.09/2.31          | ~ (v10_lattices @ X23)
% 2.09/2.31          | ~ (v4_lattice3 @ X23)
% 2.09/2.31          | ~ (l3_lattices @ X23)
% 2.09/2.31          | (r3_lattice3 @ X23 @ (k16_lattice3 @ X23 @ X24) @ X24)
% 2.09/2.31          | ~ (m1_subset_1 @ (k16_lattice3 @ X23 @ X24) @ (u1_struct_0 @ X23)))),
% 2.09/2.31      inference('simplify', [status(thm)], ['190'])).
% 2.09/2.31  thf('192', plain,
% 2.09/2.31      (![X0 : $i, X1 : $i]:
% 2.09/2.31         (~ (m1_subset_1 @ (k15_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1))
% 2.09/2.31          | (v2_struct_0 @ X1)
% 2.09/2.31          | ~ (v10_lattices @ X1)
% 2.09/2.31          | ~ (v4_lattice3 @ X1)
% 2.09/2.31          | ~ (l3_lattices @ X1)
% 2.09/2.31          | (r3_lattice3 @ X1 @ 
% 2.09/2.31             (k16_lattice3 @ X1 @ (a_2_2_lattice3 @ X1 @ X0)) @ 
% 2.09/2.31             (a_2_2_lattice3 @ X1 @ X0))
% 2.09/2.31          | ~ (l3_lattices @ X1)
% 2.09/2.31          | ~ (v4_lattice3 @ X1)
% 2.09/2.31          | ~ (v10_lattices @ X1)
% 2.09/2.31          | (v2_struct_0 @ X1))),
% 2.09/2.31      inference('sup-', [status(thm)], ['189', '191'])).
% 2.09/2.31  thf('193', plain,
% 2.09/2.31      (![X0 : $i, X1 : $i]:
% 2.09/2.31         ((r3_lattice3 @ X1 @ 
% 2.09/2.31           (k16_lattice3 @ X1 @ (a_2_2_lattice3 @ X1 @ X0)) @ 
% 2.09/2.31           (a_2_2_lattice3 @ X1 @ X0))
% 2.09/2.31          | ~ (l3_lattices @ X1)
% 2.09/2.31          | ~ (v4_lattice3 @ X1)
% 2.09/2.31          | ~ (v10_lattices @ X1)
% 2.09/2.31          | (v2_struct_0 @ X1)
% 2.09/2.31          | ~ (m1_subset_1 @ (k15_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1)))),
% 2.09/2.31      inference('simplify', [status(thm)], ['192'])).
% 2.09/2.31  thf('194', plain,
% 2.09/2.31      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 2.09/2.31        | (v2_struct_0 @ sk_A)
% 2.09/2.31        | ~ (v10_lattices @ sk_A)
% 2.09/2.31        | ~ (v4_lattice3 @ sk_A)
% 2.09/2.31        | ~ (l3_lattices @ sk_A)
% 2.09/2.31        | (r3_lattice3 @ sk_A @ 
% 2.09/2.31           (k16_lattice3 @ sk_A @ 
% 2.09/2.31            (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))) @ 
% 2.09/2.31           (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 2.09/2.31      inference('sup-', [status(thm)], ['188', '193'])).
% 2.09/2.31  thf('195', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('196', plain, ((v10_lattices @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('197', plain, ((v4_lattice3 @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('198', plain, ((l3_lattices @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('199', plain,
% 2.09/2.31      (((v2_struct_0 @ sk_A)
% 2.09/2.31        | (r3_lattice3 @ sk_A @ 
% 2.09/2.31           (k16_lattice3 @ sk_A @ 
% 2.09/2.31            (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))) @ 
% 2.09/2.31           (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 2.09/2.31      inference('demod', [status(thm)], ['194', '195', '196', '197', '198'])).
% 2.09/2.31  thf('200', plain, (~ (v2_struct_0 @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('201', plain,
% 2.09/2.31      ((r3_lattice3 @ sk_A @ 
% 2.09/2.31        (k16_lattice3 @ sk_A @ 
% 2.09/2.31         (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))) @ 
% 2.09/2.31        (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))),
% 2.09/2.31      inference('clc', [status(thm)], ['199', '200'])).
% 2.09/2.31  thf('202', plain,
% 2.09/2.31      (((r3_lattice3 @ sk_A @ 
% 2.09/2.31         (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) @ 
% 2.09/2.31         (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 2.09/2.31        | (v2_struct_0 @ sk_A)
% 2.09/2.31        | ~ (v10_lattices @ sk_A)
% 2.09/2.31        | ~ (v4_lattice3 @ sk_A)
% 2.09/2.31        | ~ (l3_lattices @ sk_A))),
% 2.09/2.31      inference('sup+', [status(thm)], ['90', '201'])).
% 2.09/2.31  thf('203', plain,
% 2.09/2.31      (((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))),
% 2.09/2.31      inference('clc', [status(thm)], ['186', '187'])).
% 2.09/2.31  thf('204', plain, ((v10_lattices @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('205', plain, ((v4_lattice3 @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('206', plain, ((l3_lattices @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('207', plain,
% 2.09/2.31      (((r3_lattice3 @ sk_A @ sk_B @ 
% 2.09/2.31         (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 2.09/2.31        | (v2_struct_0 @ sk_A))),
% 2.09/2.31      inference('demod', [status(thm)], ['202', '203', '204', '205', '206'])).
% 2.09/2.31  thf('208', plain, (~ (v2_struct_0 @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('209', plain,
% 2.09/2.31      ((r3_lattice3 @ sk_A @ sk_B @ 
% 2.09/2.31        (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))),
% 2.09/2.31      inference('clc', [status(thm)], ['207', '208'])).
% 2.09/2.31  thf('210', plain,
% 2.09/2.31      (![X0 : $i]:
% 2.09/2.31         ((v2_struct_0 @ sk_A)
% 2.09/2.31          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 2.09/2.31          | (r3_lattice3 @ sk_A @ (sk_D_5 @ X0 @ sk_B @ sk_A) @ X0)
% 2.09/2.31          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 2.09/2.31      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 2.09/2.31  thf('211', plain,
% 2.09/2.31      (((r3_lattice3 @ sk_A @ 
% 2.09/2.31         (sk_D_5 @ (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) @ 
% 2.09/2.31          sk_B @ sk_A) @ 
% 2.09/2.31         (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 2.09/2.31        | ((sk_B)
% 2.09/2.31            = (k16_lattice3 @ sk_A @ 
% 2.09/2.31               (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))
% 2.09/2.31        | (v2_struct_0 @ sk_A))),
% 2.09/2.31      inference('sup-', [status(thm)], ['209', '210'])).
% 2.09/2.31  thf('212', plain, (~ (v2_struct_0 @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('213', plain,
% 2.09/2.31      ((((sk_B)
% 2.09/2.31          = (k16_lattice3 @ sk_A @ 
% 2.09/2.31             (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))
% 2.09/2.31        | (r3_lattice3 @ sk_A @ 
% 2.09/2.31           (sk_D_5 @ 
% 2.09/2.31            (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) @ sk_B @ 
% 2.09/2.31            sk_A) @ 
% 2.09/2.31           (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 2.09/2.31      inference('clc', [status(thm)], ['211', '212'])).
% 2.09/2.31  thf('214', plain,
% 2.09/2.31      ((r3_lattice3 @ sk_A @ sk_B @ 
% 2.09/2.31        (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))),
% 2.09/2.31      inference('clc', [status(thm)], ['207', '208'])).
% 2.09/2.31  thf('215', plain,
% 2.09/2.31      (![X0 : $i]:
% 2.09/2.31         ((v2_struct_0 @ sk_A)
% 2.09/2.31          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 2.09/2.31          | (m1_subset_1 @ (sk_D_5 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.09/2.31          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 2.09/2.31      inference('demod', [status(thm)], ['17', '18', '19', '20'])).
% 2.09/2.31  thf('216', plain,
% 2.09/2.31      (((m1_subset_1 @ 
% 2.09/2.31         (sk_D_5 @ (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) @ 
% 2.09/2.31          sk_B @ sk_A) @ 
% 2.09/2.31         (u1_struct_0 @ sk_A))
% 2.09/2.31        | ((sk_B)
% 2.09/2.31            = (k16_lattice3 @ sk_A @ 
% 2.09/2.31               (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))
% 2.09/2.31        | (v2_struct_0 @ sk_A))),
% 2.09/2.31      inference('sup-', [status(thm)], ['214', '215'])).
% 2.09/2.31  thf('217', plain, (~ (v2_struct_0 @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('218', plain,
% 2.09/2.31      ((((sk_B)
% 2.09/2.31          = (k16_lattice3 @ sk_A @ 
% 2.09/2.31             (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))
% 2.09/2.31        | (m1_subset_1 @ 
% 2.09/2.31           (sk_D_5 @ 
% 2.09/2.31            (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) @ sk_B @ 
% 2.09/2.31            sk_A) @ 
% 2.09/2.31           (u1_struct_0 @ sk_A)))),
% 2.09/2.31      inference('clc', [status(thm)], ['216', '217'])).
% 2.09/2.31  thf('219', plain,
% 2.09/2.31      (![X29 : $i, X30 : $i, X31 : $i]:
% 2.09/2.31         (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X30))
% 2.09/2.31          | (r3_lattices @ X30 @ X29 @ (k16_lattice3 @ X30 @ X31))
% 2.09/2.31          | ~ (r3_lattice3 @ X30 @ X29 @ X31)
% 2.09/2.31          | ~ (l3_lattices @ X30)
% 2.09/2.31          | ~ (v4_lattice3 @ X30)
% 2.09/2.31          | ~ (v10_lattices @ X30)
% 2.09/2.31          | (v2_struct_0 @ X30))),
% 2.09/2.31      inference('cnf', [status(esa)], [t40_lattice3])).
% 2.09/2.31  thf('220', plain,
% 2.09/2.31      (![X0 : $i]:
% 2.09/2.31         (((sk_B)
% 2.09/2.31            = (k16_lattice3 @ sk_A @ 
% 2.09/2.31               (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))
% 2.09/2.31          | (v2_struct_0 @ sk_A)
% 2.09/2.31          | ~ (v10_lattices @ sk_A)
% 2.09/2.31          | ~ (v4_lattice3 @ sk_A)
% 2.09/2.31          | ~ (l3_lattices @ sk_A)
% 2.09/2.31          | ~ (r3_lattice3 @ sk_A @ 
% 2.09/2.31               (sk_D_5 @ 
% 2.09/2.31                (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) @ 
% 2.09/2.31                sk_B @ sk_A) @ 
% 2.09/2.31               X0)
% 2.09/2.31          | (r3_lattices @ sk_A @ 
% 2.09/2.31             (sk_D_5 @ 
% 2.09/2.31              (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) @ 
% 2.09/2.31              sk_B @ sk_A) @ 
% 2.09/2.31             (k16_lattice3 @ sk_A @ X0)))),
% 2.09/2.31      inference('sup-', [status(thm)], ['218', '219'])).
% 2.09/2.31  thf('221', plain, ((v10_lattices @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('222', plain, ((v4_lattice3 @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('223', plain, ((l3_lattices @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('224', plain,
% 2.09/2.31      (![X0 : $i]:
% 2.09/2.31         (((sk_B)
% 2.09/2.31            = (k16_lattice3 @ sk_A @ 
% 2.09/2.31               (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))
% 2.09/2.31          | (v2_struct_0 @ sk_A)
% 2.09/2.31          | ~ (r3_lattice3 @ sk_A @ 
% 2.09/2.31               (sk_D_5 @ 
% 2.09/2.31                (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) @ 
% 2.09/2.31                sk_B @ sk_A) @ 
% 2.09/2.31               X0)
% 2.09/2.31          | (r3_lattices @ sk_A @ 
% 2.09/2.31             (sk_D_5 @ 
% 2.09/2.31              (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) @ 
% 2.09/2.31              sk_B @ sk_A) @ 
% 2.09/2.31             (k16_lattice3 @ sk_A @ X0)))),
% 2.09/2.31      inference('demod', [status(thm)], ['220', '221', '222', '223'])).
% 2.09/2.31  thf('225', plain,
% 2.09/2.31      ((((sk_B)
% 2.09/2.31          = (k16_lattice3 @ sk_A @ 
% 2.09/2.31             (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))
% 2.09/2.31        | (r3_lattices @ sk_A @ 
% 2.09/2.31           (sk_D_5 @ 
% 2.09/2.31            (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) @ sk_B @ 
% 2.09/2.31            sk_A) @ 
% 2.09/2.31           (k16_lattice3 @ sk_A @ 
% 2.09/2.31            (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))
% 2.09/2.31        | (v2_struct_0 @ sk_A)
% 2.09/2.31        | ((sk_B)
% 2.09/2.31            = (k16_lattice3 @ sk_A @ 
% 2.09/2.31               (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))))),
% 2.09/2.31      inference('sup-', [status(thm)], ['213', '224'])).
% 2.09/2.31  thf('226', plain,
% 2.09/2.31      (((v2_struct_0 @ sk_A)
% 2.09/2.31        | (r3_lattices @ sk_A @ 
% 2.09/2.31           (sk_D_5 @ 
% 2.09/2.31            (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) @ sk_B @ 
% 2.09/2.31            sk_A) @ 
% 2.09/2.31           (k16_lattice3 @ sk_A @ 
% 2.09/2.31            (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))
% 2.09/2.31        | ((sk_B)
% 2.09/2.31            = (k16_lattice3 @ sk_A @ 
% 2.09/2.31               (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))))),
% 2.09/2.31      inference('simplify', [status(thm)], ['225'])).
% 2.09/2.31  thf('227', plain, (~ (v2_struct_0 @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('228', plain,
% 2.09/2.31      ((((sk_B)
% 2.09/2.31          = (k16_lattice3 @ sk_A @ 
% 2.09/2.31             (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))
% 2.09/2.31        | (r3_lattices @ sk_A @ 
% 2.09/2.31           (sk_D_5 @ 
% 2.09/2.31            (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) @ sk_B @ 
% 2.09/2.31            sk_A) @ 
% 2.09/2.31           (k16_lattice3 @ sk_A @ 
% 2.09/2.31            (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))))),
% 2.09/2.31      inference('clc', [status(thm)], ['226', '227'])).
% 2.09/2.31  thf('229', plain,
% 2.09/2.31      (((r3_lattices @ sk_A @ 
% 2.09/2.31         (sk_D_5 @ (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) @ 
% 2.09/2.31          sk_B @ sk_A) @ 
% 2.09/2.31         (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 2.09/2.31        | (v2_struct_0 @ sk_A)
% 2.09/2.31        | ~ (v10_lattices @ sk_A)
% 2.09/2.31        | ~ (v4_lattice3 @ sk_A)
% 2.09/2.31        | ~ (l3_lattices @ sk_A)
% 2.09/2.31        | ((sk_B)
% 2.09/2.31            = (k16_lattice3 @ sk_A @ 
% 2.09/2.31               (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))))),
% 2.09/2.31      inference('sup+', [status(thm)], ['89', '228'])).
% 2.09/2.31  thf('230', plain,
% 2.09/2.31      (((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))),
% 2.09/2.31      inference('clc', [status(thm)], ['186', '187'])).
% 2.09/2.31  thf('231', plain, ((v10_lattices @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('232', plain, ((v4_lattice3 @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('233', plain, ((l3_lattices @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('234', plain,
% 2.09/2.31      (((r3_lattices @ sk_A @ 
% 2.09/2.31         (sk_D_5 @ (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) @ 
% 2.09/2.31          sk_B @ sk_A) @ 
% 2.09/2.31         sk_B)
% 2.09/2.31        | (v2_struct_0 @ sk_A)
% 2.09/2.31        | ((sk_B)
% 2.09/2.31            = (k16_lattice3 @ sk_A @ 
% 2.09/2.31               (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))))),
% 2.09/2.31      inference('demod', [status(thm)], ['229', '230', '231', '232', '233'])).
% 2.09/2.31  thf('235', plain, (~ (v2_struct_0 @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('236', plain,
% 2.09/2.31      ((((sk_B)
% 2.09/2.31          = (k16_lattice3 @ sk_A @ 
% 2.09/2.31             (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))
% 2.09/2.31        | (r3_lattices @ sk_A @ 
% 2.09/2.31           (sk_D_5 @ 
% 2.09/2.31            (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) @ sk_B @ 
% 2.09/2.31            sk_A) @ 
% 2.09/2.31           sk_B))),
% 2.09/2.31      inference('clc', [status(thm)], ['234', '235'])).
% 2.09/2.31  thf('237', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('238', plain,
% 2.09/2.31      (![X22 : $i, X23 : $i, X26 : $i]:
% 2.09/2.31         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 2.09/2.31          | ~ (r3_lattice3 @ X23 @ X22 @ X26)
% 2.09/2.31          | ~ (r3_lattices @ X23 @ (sk_D_5 @ X26 @ X22 @ X23) @ X22)
% 2.09/2.31          | ((X22) = (k16_lattice3 @ X23 @ X26))
% 2.09/2.31          | ~ (l3_lattices @ X23)
% 2.09/2.31          | ~ (v4_lattice3 @ X23)
% 2.09/2.31          | ~ (v10_lattices @ X23)
% 2.09/2.31          | (v2_struct_0 @ X23))),
% 2.09/2.31      inference('cnf', [status(esa)], [t34_lattice3])).
% 2.09/2.31  thf('239', plain,
% 2.09/2.31      (![X0 : $i]:
% 2.09/2.31         ((v2_struct_0 @ sk_A)
% 2.09/2.31          | ~ (v10_lattices @ sk_A)
% 2.09/2.31          | ~ (v4_lattice3 @ sk_A)
% 2.09/2.31          | ~ (l3_lattices @ sk_A)
% 2.09/2.31          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 2.09/2.31          | ~ (r3_lattices @ sk_A @ (sk_D_5 @ X0 @ sk_B @ sk_A) @ sk_B)
% 2.09/2.31          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 2.09/2.31      inference('sup-', [status(thm)], ['237', '238'])).
% 2.09/2.31  thf('240', plain, ((v10_lattices @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('241', plain, ((v4_lattice3 @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('242', plain, ((l3_lattices @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('243', plain,
% 2.09/2.31      (![X0 : $i]:
% 2.09/2.31         ((v2_struct_0 @ sk_A)
% 2.09/2.31          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 2.09/2.31          | ~ (r3_lattices @ sk_A @ (sk_D_5 @ X0 @ sk_B @ sk_A) @ sk_B)
% 2.09/2.31          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 2.09/2.31      inference('demod', [status(thm)], ['239', '240', '241', '242'])).
% 2.09/2.31  thf('244', plain,
% 2.09/2.31      ((((sk_B)
% 2.09/2.31          = (k16_lattice3 @ sk_A @ 
% 2.09/2.31             (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))
% 2.09/2.31        | ~ (r3_lattice3 @ sk_A @ sk_B @ 
% 2.09/2.31             (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 2.09/2.31        | ((sk_B)
% 2.09/2.31            = (k16_lattice3 @ sk_A @ 
% 2.09/2.31               (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))
% 2.09/2.31        | (v2_struct_0 @ sk_A))),
% 2.09/2.31      inference('sup-', [status(thm)], ['236', '243'])).
% 2.09/2.31  thf('245', plain,
% 2.09/2.31      ((r3_lattice3 @ sk_A @ sk_B @ 
% 2.09/2.31        (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))),
% 2.09/2.31      inference('clc', [status(thm)], ['207', '208'])).
% 2.09/2.31  thf('246', plain,
% 2.09/2.31      ((((sk_B)
% 2.09/2.31          = (k16_lattice3 @ sk_A @ 
% 2.09/2.31             (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))
% 2.09/2.31        | ((sk_B)
% 2.09/2.31            = (k16_lattice3 @ sk_A @ 
% 2.09/2.31               (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))
% 2.09/2.31        | (v2_struct_0 @ sk_A))),
% 2.09/2.31      inference('demod', [status(thm)], ['244', '245'])).
% 2.09/2.31  thf('247', plain,
% 2.09/2.31      (((v2_struct_0 @ sk_A)
% 2.09/2.31        | ((sk_B)
% 2.09/2.31            = (k16_lattice3 @ sk_A @ 
% 2.09/2.31               (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))))),
% 2.09/2.31      inference('simplify', [status(thm)], ['246'])).
% 2.09/2.31  thf('248', plain, (~ (v2_struct_0 @ sk_A)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('249', plain,
% 2.09/2.31      (((sk_B)
% 2.09/2.31         = (k16_lattice3 @ sk_A @ 
% 2.09/2.31            (a_2_2_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 2.09/2.31      inference('clc', [status(thm)], ['247', '248'])).
% 2.09/2.31  thf('250', plain,
% 2.09/2.31      ((r3_lattices @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 2.09/2.31      inference('demod', [status(thm)], ['88', '249'])).
% 2.09/2.31  thf('251', plain,
% 2.09/2.31      (![X0 : $i]:
% 2.09/2.31         ((v2_struct_0 @ sk_A)
% 2.09/2.31          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 2.09/2.31          | ~ (r3_lattices @ sk_A @ (sk_D_5 @ X0 @ sk_B @ sk_A) @ sk_B)
% 2.09/2.31          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 2.09/2.31      inference('demod', [status(thm)], ['239', '240', '241', '242'])).
% 2.09/2.31  thf('252', plain,
% 2.09/2.31      ((~ (r3_lattice3 @ sk_A @ sk_B @ sk_C)
% 2.09/2.31        | ((sk_B) = (k16_lattice3 @ sk_A @ sk_C))
% 2.09/2.31        | (v2_struct_0 @ sk_A))),
% 2.09/2.31      inference('sup-', [status(thm)], ['250', '251'])).
% 2.09/2.31  thf('253', plain, ((r3_lattice3 @ sk_A @ sk_B @ sk_C)),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('254', plain,
% 2.09/2.31      ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C)) | (v2_struct_0 @ sk_A))),
% 2.09/2.31      inference('demod', [status(thm)], ['252', '253'])).
% 2.09/2.31  thf('255', plain, (((k16_lattice3 @ sk_A @ sk_C) != (sk_B))),
% 2.09/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.09/2.31  thf('256', plain, ((v2_struct_0 @ sk_A)),
% 2.09/2.31      inference('simplify_reflect-', [status(thm)], ['254', '255'])).
% 2.09/2.31  thf('257', plain, ($false), inference('demod', [status(thm)], ['0', '256'])).
% 2.09/2.31  
% 2.09/2.31  % SZS output end Refutation
% 2.09/2.31  
% 2.09/2.31  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
