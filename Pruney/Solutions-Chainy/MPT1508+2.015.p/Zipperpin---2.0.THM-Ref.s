%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8FvKMqgwOz

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:32 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 296 expanded)
%              Number of leaves         :   27 (  95 expanded)
%              Depth                    :   23
%              Number of atoms          : 1492 (4738 expanded)
%              Number of equality atoms :   30 ( 160 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(a_2_1_lattice3_type,type,(
    a_2_1_lattice3: $i > $i > $i )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r3_lattice3_type,type,(
    r3_lattice3: $i > $i > $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i > $i )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r4_lattice3_type,type,(
    r4_lattice3: $i > $i > $i > $o )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X14: $i,X15: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( r3_lattice3 @ X15 @ X14 @ X18 )
      | ( r3_lattice3 @ X15 @ ( sk_D_3 @ X18 @ X14 @ X15 ) @ X18 )
      | ( X14
        = ( k16_lattice3 @ X15 @ X18 ) )
      | ~ ( l3_lattices @ X15 )
      | ~ ( v4_lattice3 @ X15 )
      | ~ ( v10_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( sk_B
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ( r3_lattice3 @ sk_A @ ( sk_D_3 @ X0 @ sk_B @ sk_A ) @ X0 )
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
      | ( r3_lattice3 @ sk_A @ ( sk_D_3 @ X0 @ sk_B @ sk_A ) @ X0 )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('9',plain,
    ( ( r3_lattice3 @ sk_A @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    ( k16_lattice3 @ sk_A @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r3_lattice3 @ sk_A @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r3_lattice3 @ sk_A @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ sk_C ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    r3_lattice3 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X14: $i,X15: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( r3_lattice3 @ X15 @ X14 @ X18 )
      | ( m1_subset_1 @ ( sk_D_3 @ X18 @ X14 @ X15 ) @ ( u1_struct_0 @ X15 ) )
      | ( X14
        = ( k16_lattice3 @ X15 @ X18 ) )
      | ~ ( l3_lattices @ X15 )
      | ~ ( v4_lattice3 @ X15 )
      | ~ ( v10_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( sk_B
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_D_3 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
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
      | ( m1_subset_1 @ ( sk_D_3 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18','19','20'])).

thf('22',plain,
    ( ( m1_subset_1 @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('23',plain,(
    ( k16_lattice3 @ sk_A @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( m1_subset_1 @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
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
      | ( r2_hidden @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattice3 @ sk_A @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ ( a_2_1_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    r2_hidden @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['13','33'])).

thf('35',plain,(
    m1_subset_1 @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

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

thf('36',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ( r3_lattices @ X20 @ X19 @ ( k15_lattice3 @ X20 @ X21 ) )
      | ~ ( r2_hidden @ X19 @ X21 )
      | ~ ( l3_lattices @ X20 )
      | ~ ( v4_lattice3 @ X20 )
      | ~ ( v10_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t38_lattice3])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r2_hidden @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ( r3_lattices @ sk_A @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ( r3_lattices @ sk_A @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_A @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ ( k15_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    r3_lattices @ sk_A @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['34','43'])).

thf('45',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
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

thf('48',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ( r2_hidden @ ( sk_D_1 @ X9 @ X5 @ X6 ) @ X9 )
      | ( r4_lattice3 @ X6 @ X5 @ X9 )
      | ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( X12
        = ( sk_D_2 @ X11 @ X10 @ X12 ) )
      | ~ ( r2_hidden @ X12 @ ( a_2_1_lattice3 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_lattice3])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ X1 @ X0 ) )
      | ( ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A )
        = ( sk_D_2 @ X0 @ X1 @ ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('57',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( r3_lattice3 @ X10 @ ( sk_D_2 @ X11 @ X10 @ X12 ) @ X11 )
      | ~ ( r2_hidden @ X12 @ ( a_2_1_lattice3 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_lattice3])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ X1 @ X0 ) )
      | ( r3_lattice3 @ X1 @ ( sk_D_2 @ X0 @ X1 @ ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A ) ) @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ X1 @ ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A ) @ X0 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ X1 @ X0 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( r3_lattice3 @ X1 @ ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X9 @ X5 @ X6 ) @ ( u1_struct_0 @ X6 ) )
      | ( r4_lattice3 @ X6 @ X5 @ X9 )
      | ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['65','66'])).

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

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r3_lattice3 @ X1 @ X0 @ X2 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r1_lattices @ X1 @ X0 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X1 )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X1 )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X2 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ X0 ) @ sk_B @ sk_A ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','71'])).

thf('73',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ X0 ) @ sk_B @ sk_A ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ X0 ) @ sk_B @ sk_A ) @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ X0 ) @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','75'])).

thf('77',plain,
    ( ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_B @ sk_A ) @ sk_B )
    | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ~ ( r1_lattices @ X6 @ ( sk_D_1 @ X9 @ X5 @ X6 ) @ X5 )
      | ( r4_lattice3 @ X6 @ X5 @ X9 )
      | ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['77','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
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

thf('89',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( ( k15_lattice3 @ X23 @ X24 )
        = X22 )
      | ~ ( r4_lattice3 @ X23 @ X22 @ X24 )
      | ~ ( r2_hidden @ X22 @ X24 )
      | ~ ( l3_lattices @ X23 )
      | ~ ( v4_lattice3 @ X23 )
      | ~ ( v10_lattices @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t41_lattice3])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( ( k15_lattice3 @ sk_A @ X0 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( ( k15_lattice3 @ sk_A @ X0 )
        = sk_B ) ) ),
    inference(demod,[status(thm)],['90','91','92','93'])).

thf('95',plain,
    ( ( ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
      = sk_B )
    | ~ ( r2_hidden @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['87','94'])).

thf('96',plain,(
    r3_lattice3 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ~ ( r3_lattice3 @ X10 @ X13 @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X10 ) )
      | ( r2_hidden @ X13 @ ( a_2_1_lattice3 @ X10 @ X11 ) )
      | ( v2_struct_0 @ X10 )
      | ~ ( l3_lattices @ X10 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(clc,[status(thm)],['101','102'])).

thf('104',plain,(
    r2_hidden @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['96','103'])).

thf('105',plain,
    ( ( ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
      = sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['95','104'])).

thf('106',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
    = sk_B ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,(
    r3_lattices @ sk_A @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['44','107'])).

thf('109',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X14: $i,X15: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( r3_lattice3 @ X15 @ X14 @ X18 )
      | ~ ( r3_lattices @ X15 @ ( sk_D_3 @ X18 @ X14 @ X15 ) @ X14 )
      | ( X14
        = ( k16_lattice3 @ X15 @ X18 ) )
      | ~ ( l3_lattices @ X15 )
      | ~ ( v4_lattice3 @ X15 )
      | ~ ( v10_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( sk_B
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattices @ sk_A @ ( sk_D_3 @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattices @ sk_A @ ( sk_D_3 @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['111','112','113','114'])).

thf('116',plain,
    ( ~ ( r3_lattice3 @ sk_A @ sk_B @ sk_C )
    | ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['108','115'])).

thf('117',plain,(
    r3_lattice3 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ( k16_lattice3 @ sk_A @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['118','119'])).

thf('121',plain,(
    $false ),
    inference(demod,[status(thm)],['0','120'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8FvKMqgwOz
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:23:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.45/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.69  % Solved by: fo/fo7.sh
% 0.45/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.69  % done 174 iterations in 0.227s
% 0.45/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.69  % SZS output start Refutation
% 0.45/0.69  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.45/0.69  thf(a_2_1_lattice3_type, type, a_2_1_lattice3: $i > $i > $i).
% 0.45/0.69  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.45/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.69  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.69  thf(r3_lattice3_type, type, r3_lattice3: $i > $i > $i > $o).
% 0.45/0.69  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i > $i).
% 0.45/0.69  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 0.45/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.69  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.45/0.69  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.69  thf(r4_lattice3_type, type, r4_lattice3: $i > $i > $i > $o).
% 0.45/0.69  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 0.45/0.69  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 0.45/0.69  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.45/0.69  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 0.45/0.69  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 0.45/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.69  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.69  thf(t42_lattice3, conjecture,
% 0.45/0.69    (![A:$i]:
% 0.45/0.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.45/0.69         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.45/0.69       ( ![B:$i]:
% 0.45/0.69         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.69           ( ![C:$i]:
% 0.45/0.69             ( ( ( r2_hidden @ B @ C ) & ( r3_lattice3 @ A @ B @ C ) ) =>
% 0.45/0.69               ( ( k16_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ))).
% 0.45/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.69    (~( ![A:$i]:
% 0.45/0.69        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.45/0.69            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.45/0.69          ( ![B:$i]:
% 0.45/0.69            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.69              ( ![C:$i]:
% 0.45/0.69                ( ( ( r2_hidden @ B @ C ) & ( r3_lattice3 @ A @ B @ C ) ) =>
% 0.45/0.69                  ( ( k16_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ) )),
% 0.45/0.69    inference('cnf.neg', [status(esa)], [t42_lattice3])).
% 0.45/0.69  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('1', plain, ((r3_lattice3 @ sk_A @ sk_B @ sk_C)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf(t34_lattice3, axiom,
% 0.45/0.69    (![A:$i]:
% 0.45/0.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.45/0.69         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.45/0.69       ( ![B:$i]:
% 0.45/0.69         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.69           ( ![C:$i]:
% 0.45/0.69             ( ( ( B ) = ( k16_lattice3 @ A @ C ) ) <=>
% 0.45/0.69               ( ( r3_lattice3 @ A @ B @ C ) & 
% 0.45/0.69                 ( ![D:$i]:
% 0.45/0.69                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.69                     ( ( r3_lattice3 @ A @ D @ C ) =>
% 0.45/0.69                       ( r3_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.69  thf('3', plain,
% 0.45/0.69      (![X14 : $i, X15 : $i, X18 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.45/0.69          | ~ (r3_lattice3 @ X15 @ X14 @ X18)
% 0.45/0.69          | (r3_lattice3 @ X15 @ (sk_D_3 @ X18 @ X14 @ X15) @ X18)
% 0.45/0.69          | ((X14) = (k16_lattice3 @ X15 @ X18))
% 0.45/0.69          | ~ (l3_lattices @ X15)
% 0.45/0.69          | ~ (v4_lattice3 @ X15)
% 0.45/0.69          | ~ (v10_lattices @ X15)
% 0.45/0.69          | (v2_struct_0 @ X15))),
% 0.45/0.69      inference('cnf', [status(esa)], [t34_lattice3])).
% 0.45/0.69  thf('4', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((v2_struct_0 @ sk_A)
% 0.45/0.69          | ~ (v10_lattices @ sk_A)
% 0.45/0.69          | ~ (v4_lattice3 @ sk_A)
% 0.45/0.69          | ~ (l3_lattices @ sk_A)
% 0.45/0.69          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 0.45/0.69          | (r3_lattice3 @ sk_A @ (sk_D_3 @ X0 @ sk_B @ sk_A) @ X0)
% 0.45/0.69          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['2', '3'])).
% 0.45/0.69  thf('5', plain, ((v10_lattices @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('6', plain, ((v4_lattice3 @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('7', plain, ((l3_lattices @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('8', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((v2_struct_0 @ sk_A)
% 0.45/0.69          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 0.45/0.69          | (r3_lattice3 @ sk_A @ (sk_D_3 @ X0 @ sk_B @ sk_A) @ X0)
% 0.45/0.69          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.45/0.69      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.45/0.69  thf('9', plain,
% 0.45/0.69      (((r3_lattice3 @ sk_A @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.45/0.69        | ((sk_B) = (k16_lattice3 @ sk_A @ sk_C))
% 0.45/0.69        | (v2_struct_0 @ sk_A))),
% 0.45/0.69      inference('sup-', [status(thm)], ['1', '8'])).
% 0.45/0.69  thf('10', plain, (((k16_lattice3 @ sk_A @ sk_C) != (sk_B))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('11', plain,
% 0.45/0.69      (((r3_lattice3 @ sk_A @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.45/0.69        | (v2_struct_0 @ sk_A))),
% 0.45/0.69      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.45/0.69  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('13', plain,
% 0.45/0.69      ((r3_lattice3 @ sk_A @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ sk_C)),
% 0.45/0.69      inference('clc', [status(thm)], ['11', '12'])).
% 0.45/0.69  thf('14', plain, ((r3_lattice3 @ sk_A @ sk_B @ sk_C)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('15', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('16', plain,
% 0.45/0.69      (![X14 : $i, X15 : $i, X18 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.45/0.69          | ~ (r3_lattice3 @ X15 @ X14 @ X18)
% 0.45/0.69          | (m1_subset_1 @ (sk_D_3 @ X18 @ X14 @ X15) @ (u1_struct_0 @ X15))
% 0.45/0.69          | ((X14) = (k16_lattice3 @ X15 @ X18))
% 0.45/0.69          | ~ (l3_lattices @ X15)
% 0.45/0.69          | ~ (v4_lattice3 @ X15)
% 0.45/0.69          | ~ (v10_lattices @ X15)
% 0.45/0.69          | (v2_struct_0 @ X15))),
% 0.45/0.69      inference('cnf', [status(esa)], [t34_lattice3])).
% 0.45/0.69  thf('17', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((v2_struct_0 @ sk_A)
% 0.45/0.69          | ~ (v10_lattices @ sk_A)
% 0.45/0.69          | ~ (v4_lattice3 @ sk_A)
% 0.45/0.69          | ~ (l3_lattices @ sk_A)
% 0.45/0.69          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 0.45/0.69          | (m1_subset_1 @ (sk_D_3 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.45/0.69          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['15', '16'])).
% 0.45/0.69  thf('18', plain, ((v10_lattices @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('19', plain, ((v4_lattice3 @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('20', plain, ((l3_lattices @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('21', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((v2_struct_0 @ sk_A)
% 0.45/0.69          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 0.45/0.69          | (m1_subset_1 @ (sk_D_3 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.45/0.69          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.45/0.69      inference('demod', [status(thm)], ['17', '18', '19', '20'])).
% 0.45/0.69  thf('22', plain,
% 0.45/0.69      (((m1_subset_1 @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.45/0.69        | ((sk_B) = (k16_lattice3 @ sk_A @ sk_C))
% 0.45/0.69        | (v2_struct_0 @ sk_A))),
% 0.45/0.69      inference('sup-', [status(thm)], ['14', '21'])).
% 0.45/0.69  thf('23', plain, (((k16_lattice3 @ sk_A @ sk_C) != (sk_B))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('24', plain,
% 0.45/0.69      (((m1_subset_1 @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.45/0.69        | (v2_struct_0 @ sk_A))),
% 0.45/0.69      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.45/0.69  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('26', plain,
% 0.45/0.69      ((m1_subset_1 @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.45/0.69      inference('clc', [status(thm)], ['24', '25'])).
% 0.45/0.69  thf(fraenkel_a_2_1_lattice3, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ( ( ~( v2_struct_0 @ B ) ) & ( l3_lattices @ B ) ) =>
% 0.45/0.69       ( ( r2_hidden @ A @ ( a_2_1_lattice3 @ B @ C ) ) <=>
% 0.45/0.69         ( ?[D:$i]:
% 0.45/0.69           ( ( r3_lattice3 @ B @ D @ C ) & ( ( A ) = ( D ) ) & 
% 0.45/0.69             ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.45/0.69  thf('27', plain,
% 0.45/0.69      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.45/0.69         (~ (l3_lattices @ X10)
% 0.45/0.69          | (v2_struct_0 @ X10)
% 0.45/0.69          | (r2_hidden @ X12 @ (a_2_1_lattice3 @ X10 @ X11))
% 0.45/0.69          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X10))
% 0.45/0.69          | ((X12) != (X13))
% 0.45/0.69          | ~ (r3_lattice3 @ X10 @ X13 @ X11))),
% 0.45/0.69      inference('cnf', [status(esa)], [fraenkel_a_2_1_lattice3])).
% 0.45/0.69  thf('28', plain,
% 0.45/0.69      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.45/0.69         (~ (r3_lattice3 @ X10 @ X13 @ X11)
% 0.45/0.69          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X10))
% 0.45/0.69          | (r2_hidden @ X13 @ (a_2_1_lattice3 @ X10 @ X11))
% 0.45/0.69          | (v2_struct_0 @ X10)
% 0.45/0.69          | ~ (l3_lattices @ X10))),
% 0.45/0.69      inference('simplify', [status(thm)], ['27'])).
% 0.45/0.69  thf('29', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (~ (l3_lattices @ sk_A)
% 0.45/0.69          | (v2_struct_0 @ sk_A)
% 0.45/0.69          | (r2_hidden @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.69             (a_2_1_lattice3 @ sk_A @ X0))
% 0.45/0.69          | ~ (r3_lattice3 @ sk_A @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ X0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['26', '28'])).
% 0.45/0.69  thf('30', plain, ((l3_lattices @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('31', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((v2_struct_0 @ sk_A)
% 0.45/0.69          | (r2_hidden @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.69             (a_2_1_lattice3 @ sk_A @ X0))
% 0.45/0.69          | ~ (r3_lattice3 @ sk_A @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ X0))),
% 0.45/0.69      inference('demod', [status(thm)], ['29', '30'])).
% 0.45/0.69  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('33', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (~ (r3_lattice3 @ sk_A @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ X0)
% 0.45/0.69          | (r2_hidden @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.69             (a_2_1_lattice3 @ sk_A @ X0)))),
% 0.45/0.69      inference('clc', [status(thm)], ['31', '32'])).
% 0.45/0.69  thf('34', plain,
% 0.45/0.69      ((r2_hidden @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.69        (a_2_1_lattice3 @ sk_A @ sk_C))),
% 0.45/0.69      inference('sup-', [status(thm)], ['13', '33'])).
% 0.45/0.69  thf('35', plain,
% 0.45/0.69      ((m1_subset_1 @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.45/0.69      inference('clc', [status(thm)], ['24', '25'])).
% 0.45/0.69  thf(t38_lattice3, axiom,
% 0.45/0.69    (![A:$i]:
% 0.45/0.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.45/0.69         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.45/0.69       ( ![B:$i]:
% 0.45/0.69         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.69           ( ![C:$i]:
% 0.45/0.69             ( ( r2_hidden @ B @ C ) =>
% 0.45/0.69               ( ( r3_lattices @ A @ B @ ( k15_lattice3 @ A @ C ) ) & 
% 0.45/0.69                 ( r3_lattices @ A @ ( k16_lattice3 @ A @ C ) @ B ) ) ) ) ) ) ))).
% 0.45/0.69  thf('36', plain,
% 0.45/0.69      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 0.45/0.69          | (r3_lattices @ X20 @ X19 @ (k15_lattice3 @ X20 @ X21))
% 0.45/0.69          | ~ (r2_hidden @ X19 @ X21)
% 0.45/0.69          | ~ (l3_lattices @ X20)
% 0.45/0.69          | ~ (v4_lattice3 @ X20)
% 0.45/0.69          | ~ (v10_lattices @ X20)
% 0.45/0.69          | (v2_struct_0 @ X20))),
% 0.45/0.69      inference('cnf', [status(esa)], [t38_lattice3])).
% 0.45/0.69  thf('37', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((v2_struct_0 @ sk_A)
% 0.45/0.69          | ~ (v10_lattices @ sk_A)
% 0.45/0.69          | ~ (v4_lattice3 @ sk_A)
% 0.45/0.69          | ~ (l3_lattices @ sk_A)
% 0.45/0.69          | ~ (r2_hidden @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ X0)
% 0.45/0.69          | (r3_lattices @ sk_A @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.69             (k15_lattice3 @ sk_A @ X0)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['35', '36'])).
% 0.45/0.69  thf('38', plain, ((v10_lattices @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('39', plain, ((v4_lattice3 @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('40', plain, ((l3_lattices @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('41', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((v2_struct_0 @ sk_A)
% 0.45/0.69          | ~ (r2_hidden @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ X0)
% 0.45/0.69          | (r3_lattices @ sk_A @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.69             (k15_lattice3 @ sk_A @ X0)))),
% 0.45/0.69      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 0.45/0.69  thf('42', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('43', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((r3_lattices @ sk_A @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.69           (k15_lattice3 @ sk_A @ X0))
% 0.45/0.69          | ~ (r2_hidden @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ X0))),
% 0.45/0.69      inference('clc', [status(thm)], ['41', '42'])).
% 0.45/0.69  thf('44', plain,
% 0.45/0.69      ((r3_lattices @ sk_A @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.69        (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['34', '43'])).
% 0.45/0.69  thf('45', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('46', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('47', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf(d17_lattice3, axiom,
% 0.45/0.69    (![A:$i]:
% 0.45/0.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.45/0.69       ( ![B:$i]:
% 0.45/0.69         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.69           ( ![C:$i]:
% 0.45/0.69             ( ( r4_lattice3 @ A @ B @ C ) <=>
% 0.45/0.69               ( ![D:$i]:
% 0.45/0.69                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.69                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ))).
% 0.45/0.69  thf('48', plain,
% 0.45/0.69      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 0.45/0.69          | (r2_hidden @ (sk_D_1 @ X9 @ X5 @ X6) @ X9)
% 0.45/0.69          | (r4_lattice3 @ X6 @ X5 @ X9)
% 0.45/0.69          | ~ (l3_lattices @ X6)
% 0.45/0.69          | (v2_struct_0 @ X6))),
% 0.45/0.69      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.45/0.69  thf('49', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((v2_struct_0 @ sk_A)
% 0.45/0.69          | ~ (l3_lattices @ sk_A)
% 0.45/0.69          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.45/0.69          | (r2_hidden @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['47', '48'])).
% 0.45/0.69  thf('50', plain, ((l3_lattices @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('51', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((v2_struct_0 @ sk_A)
% 0.45/0.69          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.45/0.69          | (r2_hidden @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0))),
% 0.45/0.69      inference('demod', [status(thm)], ['49', '50'])).
% 0.45/0.69  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('53', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((r2_hidden @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0)
% 0.45/0.69          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 0.45/0.69      inference('clc', [status(thm)], ['51', '52'])).
% 0.45/0.69  thf('54', plain,
% 0.45/0.69      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.45/0.69         (~ (l3_lattices @ X10)
% 0.45/0.69          | (v2_struct_0 @ X10)
% 0.45/0.69          | ((X12) = (sk_D_2 @ X11 @ X10 @ X12))
% 0.45/0.69          | ~ (r2_hidden @ X12 @ (a_2_1_lattice3 @ X10 @ X11)))),
% 0.45/0.69      inference('cnf', [status(esa)], [fraenkel_a_2_1_lattice3])).
% 0.45/0.69  thf('55', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0))
% 0.45/0.69          | ((sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A)
% 0.45/0.69              = (sk_D_2 @ X0 @ X1 @ 
% 0.45/0.69                 (sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A)))
% 0.45/0.69          | (v2_struct_0 @ X1)
% 0.45/0.69          | ~ (l3_lattices @ X1))),
% 0.45/0.69      inference('sup-', [status(thm)], ['53', '54'])).
% 0.45/0.69  thf('56', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((r2_hidden @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0)
% 0.45/0.69          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 0.45/0.69      inference('clc', [status(thm)], ['51', '52'])).
% 0.45/0.69  thf('57', plain,
% 0.45/0.69      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.45/0.69         (~ (l3_lattices @ X10)
% 0.45/0.69          | (v2_struct_0 @ X10)
% 0.45/0.69          | (r3_lattice3 @ X10 @ (sk_D_2 @ X11 @ X10 @ X12) @ X11)
% 0.45/0.69          | ~ (r2_hidden @ X12 @ (a_2_1_lattice3 @ X10 @ X11)))),
% 0.45/0.69      inference('cnf', [status(esa)], [fraenkel_a_2_1_lattice3])).
% 0.45/0.69  thf('58', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0))
% 0.45/0.69          | (r3_lattice3 @ X1 @ 
% 0.45/0.69             (sk_D_2 @ X0 @ X1 @ 
% 0.45/0.69              (sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A)) @ 
% 0.45/0.69             X0)
% 0.45/0.69          | (v2_struct_0 @ X1)
% 0.45/0.69          | ~ (l3_lattices @ X1))),
% 0.45/0.69      inference('sup-', [status(thm)], ['56', '57'])).
% 0.45/0.69  thf('59', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((r3_lattice3 @ X1 @ 
% 0.45/0.69           (sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A) @ X0)
% 0.45/0.69          | ~ (l3_lattices @ X1)
% 0.45/0.69          | (v2_struct_0 @ X1)
% 0.45/0.69          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0))
% 0.45/0.69          | ~ (l3_lattices @ X1)
% 0.45/0.69          | (v2_struct_0 @ X1)
% 0.45/0.69          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0)))),
% 0.45/0.69      inference('sup+', [status(thm)], ['55', '58'])).
% 0.45/0.69  thf('60', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0))
% 0.45/0.69          | (v2_struct_0 @ X1)
% 0.45/0.69          | ~ (l3_lattices @ X1)
% 0.45/0.69          | (r3_lattice3 @ X1 @ 
% 0.45/0.69             (sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A) @ X0))),
% 0.45/0.69      inference('simplify', [status(thm)], ['59'])).
% 0.45/0.69  thf('61', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('62', plain,
% 0.45/0.69      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 0.45/0.69          | (m1_subset_1 @ (sk_D_1 @ X9 @ X5 @ X6) @ (u1_struct_0 @ X6))
% 0.45/0.69          | (r4_lattice3 @ X6 @ X5 @ X9)
% 0.45/0.69          | ~ (l3_lattices @ X6)
% 0.45/0.69          | (v2_struct_0 @ X6))),
% 0.45/0.69      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.45/0.69  thf('63', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((v2_struct_0 @ sk_A)
% 0.45/0.69          | ~ (l3_lattices @ sk_A)
% 0.45/0.69          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.45/0.69          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['61', '62'])).
% 0.45/0.69  thf('64', plain, ((l3_lattices @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('65', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((v2_struct_0 @ sk_A)
% 0.45/0.69          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.45/0.69          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.45/0.69      inference('demod', [status(thm)], ['63', '64'])).
% 0.45/0.69  thf('66', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('67', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.45/0.69          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 0.45/0.69      inference('clc', [status(thm)], ['65', '66'])).
% 0.45/0.69  thf(d16_lattice3, axiom,
% 0.45/0.69    (![A:$i]:
% 0.45/0.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.45/0.69       ( ![B:$i]:
% 0.45/0.69         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.69           ( ![C:$i]:
% 0.45/0.69             ( ( r3_lattice3 @ A @ B @ C ) <=>
% 0.45/0.69               ( ![D:$i]:
% 0.45/0.69                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.69                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 0.45/0.69  thf('68', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.45/0.69          | ~ (r3_lattice3 @ X1 @ X0 @ X2)
% 0.45/0.69          | ~ (r2_hidden @ X3 @ X2)
% 0.45/0.69          | (r1_lattices @ X1 @ X0 @ X3)
% 0.45/0.69          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.45/0.69          | ~ (l3_lattices @ X1)
% 0.45/0.69          | (v2_struct_0 @ X1))),
% 0.45/0.69      inference('cnf', [status(esa)], [d16_lattice3])).
% 0.45/0.69  thf('69', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         ((r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.45/0.69          | (v2_struct_0 @ sk_A)
% 0.45/0.69          | ~ (l3_lattices @ sk_A)
% 0.45/0.69          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.45/0.69          | (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X1)
% 0.45/0.69          | ~ (r2_hidden @ X1 @ X2)
% 0.45/0.69          | ~ (r3_lattice3 @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X2))),
% 0.45/0.69      inference('sup-', [status(thm)], ['67', '68'])).
% 0.45/0.69  thf('70', plain, ((l3_lattices @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('71', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         ((r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.45/0.69          | (v2_struct_0 @ sk_A)
% 0.45/0.69          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.45/0.69          | (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X1)
% 0.45/0.69          | ~ (r2_hidden @ X1 @ X2)
% 0.45/0.69          | ~ (r3_lattice3 @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X2))),
% 0.45/0.69      inference('demod', [status(thm)], ['69', '70'])).
% 0.45/0.69  thf('72', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         (~ (l3_lattices @ sk_A)
% 0.45/0.69          | (v2_struct_0 @ sk_A)
% 0.45/0.69          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 0.45/0.69          | ~ (r2_hidden @ X1 @ X0)
% 0.45/0.69          | (r1_lattices @ sk_A @ 
% 0.45/0.69             (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ X0) @ sk_B @ sk_A) @ X1)
% 0.45/0.69          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.45/0.69          | (v2_struct_0 @ sk_A)
% 0.45/0.69          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['60', '71'])).
% 0.45/0.69  thf('73', plain, ((l3_lattices @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('74', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((v2_struct_0 @ sk_A)
% 0.45/0.69          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 0.45/0.69          | ~ (r2_hidden @ X1 @ X0)
% 0.45/0.69          | (r1_lattices @ sk_A @ 
% 0.45/0.69             (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ X0) @ sk_B @ sk_A) @ X1)
% 0.45/0.69          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.45/0.69          | (v2_struct_0 @ sk_A)
% 0.45/0.69          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0)))),
% 0.45/0.69      inference('demod', [status(thm)], ['72', '73'])).
% 0.45/0.69  thf('75', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.45/0.69          | (r1_lattices @ sk_A @ 
% 0.45/0.69             (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ X0) @ sk_B @ sk_A) @ X1)
% 0.45/0.69          | ~ (r2_hidden @ X1 @ X0)
% 0.45/0.69          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 0.45/0.69          | (v2_struct_0 @ sk_A))),
% 0.45/0.69      inference('simplify', [status(thm)], ['74'])).
% 0.45/0.69  thf('76', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((v2_struct_0 @ sk_A)
% 0.45/0.69          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 0.45/0.69          | ~ (r2_hidden @ sk_B @ X0)
% 0.45/0.69          | (r1_lattices @ sk_A @ 
% 0.45/0.69             (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ X0) @ sk_B @ sk_A) @ sk_B))),
% 0.45/0.69      inference('sup-', [status(thm)], ['46', '75'])).
% 0.45/0.69  thf('77', plain,
% 0.45/0.69      (((r1_lattices @ sk_A @ 
% 0.45/0.69         (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_B @ sk_A) @ sk_B)
% 0.45/0.69        | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))
% 0.45/0.69        | (v2_struct_0 @ sk_A))),
% 0.45/0.69      inference('sup-', [status(thm)], ['45', '76'])).
% 0.45/0.69  thf('78', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('79', plain,
% 0.45/0.69      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 0.45/0.69          | ~ (r1_lattices @ X6 @ (sk_D_1 @ X9 @ X5 @ X6) @ X5)
% 0.45/0.69          | (r4_lattice3 @ X6 @ X5 @ X9)
% 0.45/0.69          | ~ (l3_lattices @ X6)
% 0.45/0.69          | (v2_struct_0 @ X6))),
% 0.45/0.69      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.45/0.69  thf('80', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((v2_struct_0 @ sk_A)
% 0.45/0.69          | ~ (l3_lattices @ sk_A)
% 0.45/0.69          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.45/0.69          | ~ (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_B))),
% 0.45/0.69      inference('sup-', [status(thm)], ['78', '79'])).
% 0.45/0.69  thf('81', plain, ((l3_lattices @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('82', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((v2_struct_0 @ sk_A)
% 0.45/0.69          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.45/0.69          | ~ (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_B))),
% 0.45/0.69      inference('demod', [status(thm)], ['80', '81'])).
% 0.45/0.69  thf('83', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('84', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (~ (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_B)
% 0.45/0.69          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 0.45/0.69      inference('clc', [status(thm)], ['82', '83'])).
% 0.45/0.69  thf('85', plain,
% 0.45/0.69      (((v2_struct_0 @ sk_A)
% 0.45/0.69        | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C)))),
% 0.45/0.69      inference('clc', [status(thm)], ['77', '84'])).
% 0.45/0.69  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('87', plain,
% 0.45/0.69      ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))),
% 0.45/0.69      inference('clc', [status(thm)], ['85', '86'])).
% 0.45/0.69  thf('88', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf(t41_lattice3, axiom,
% 0.45/0.69    (![A:$i]:
% 0.45/0.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.45/0.69         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.45/0.69       ( ![B:$i]:
% 0.45/0.69         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.69           ( ![C:$i]:
% 0.45/0.69             ( ( ( r2_hidden @ B @ C ) & ( r4_lattice3 @ A @ B @ C ) ) =>
% 0.45/0.69               ( ( k15_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ))).
% 0.45/0.69  thf('89', plain,
% 0.45/0.69      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 0.45/0.69          | ((k15_lattice3 @ X23 @ X24) = (X22))
% 0.45/0.69          | ~ (r4_lattice3 @ X23 @ X22 @ X24)
% 0.45/0.69          | ~ (r2_hidden @ X22 @ X24)
% 0.45/0.69          | ~ (l3_lattices @ X23)
% 0.45/0.69          | ~ (v4_lattice3 @ X23)
% 0.45/0.69          | ~ (v10_lattices @ X23)
% 0.45/0.69          | (v2_struct_0 @ X23))),
% 0.45/0.69      inference('cnf', [status(esa)], [t41_lattice3])).
% 0.45/0.69  thf('90', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((v2_struct_0 @ sk_A)
% 0.45/0.69          | ~ (v10_lattices @ sk_A)
% 0.45/0.69          | ~ (v4_lattice3 @ sk_A)
% 0.45/0.69          | ~ (l3_lattices @ sk_A)
% 0.45/0.69          | ~ (r2_hidden @ sk_B @ X0)
% 0.45/0.69          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.45/0.69          | ((k15_lattice3 @ sk_A @ X0) = (sk_B)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['88', '89'])).
% 0.45/0.69  thf('91', plain, ((v10_lattices @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('92', plain, ((v4_lattice3 @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('93', plain, ((l3_lattices @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('94', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((v2_struct_0 @ sk_A)
% 0.45/0.69          | ~ (r2_hidden @ sk_B @ X0)
% 0.45/0.69          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.45/0.69          | ((k15_lattice3 @ sk_A @ X0) = (sk_B)))),
% 0.45/0.69      inference('demod', [status(thm)], ['90', '91', '92', '93'])).
% 0.45/0.69  thf('95', plain,
% 0.45/0.69      ((((k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) = (sk_B))
% 0.45/0.69        | ~ (r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))
% 0.45/0.69        | (v2_struct_0 @ sk_A))),
% 0.45/0.69      inference('sup-', [status(thm)], ['87', '94'])).
% 0.45/0.69  thf('96', plain, ((r3_lattice3 @ sk_A @ sk_B @ sk_C)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('97', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('98', plain,
% 0.45/0.69      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.45/0.69         (~ (r3_lattice3 @ X10 @ X13 @ X11)
% 0.45/0.69          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X10))
% 0.45/0.69          | (r2_hidden @ X13 @ (a_2_1_lattice3 @ X10 @ X11))
% 0.45/0.69          | (v2_struct_0 @ X10)
% 0.45/0.69          | ~ (l3_lattices @ X10))),
% 0.45/0.69      inference('simplify', [status(thm)], ['27'])).
% 0.45/0.69  thf('99', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (~ (l3_lattices @ sk_A)
% 0.45/0.69          | (v2_struct_0 @ sk_A)
% 0.45/0.69          | (r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 0.45/0.69          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['97', '98'])).
% 0.45/0.69  thf('100', plain, ((l3_lattices @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('101', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((v2_struct_0 @ sk_A)
% 0.45/0.69          | (r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 0.45/0.69          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.45/0.69      inference('demod', [status(thm)], ['99', '100'])).
% 0.45/0.69  thf('102', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('103', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (~ (r3_lattice3 @ sk_A @ sk_B @ X0)
% 0.45/0.69          | (r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0)))),
% 0.45/0.69      inference('clc', [status(thm)], ['101', '102'])).
% 0.45/0.69  thf('104', plain, ((r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))),
% 0.45/0.69      inference('sup-', [status(thm)], ['96', '103'])).
% 0.45/0.69  thf('105', plain,
% 0.45/0.69      ((((k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) = (sk_B))
% 0.45/0.69        | (v2_struct_0 @ sk_A))),
% 0.45/0.69      inference('demod', [status(thm)], ['95', '104'])).
% 0.45/0.69  thf('106', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('107', plain,
% 0.45/0.69      (((k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) = (sk_B))),
% 0.45/0.69      inference('clc', [status(thm)], ['105', '106'])).
% 0.45/0.69  thf('108', plain,
% 0.45/0.69      ((r3_lattices @ sk_A @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.45/0.69      inference('demod', [status(thm)], ['44', '107'])).
% 0.45/0.69  thf('109', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('110', plain,
% 0.45/0.69      (![X14 : $i, X15 : $i, X18 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.45/0.69          | ~ (r3_lattice3 @ X15 @ X14 @ X18)
% 0.45/0.69          | ~ (r3_lattices @ X15 @ (sk_D_3 @ X18 @ X14 @ X15) @ X14)
% 0.45/0.69          | ((X14) = (k16_lattice3 @ X15 @ X18))
% 0.45/0.69          | ~ (l3_lattices @ X15)
% 0.45/0.69          | ~ (v4_lattice3 @ X15)
% 0.45/0.69          | ~ (v10_lattices @ X15)
% 0.45/0.69          | (v2_struct_0 @ X15))),
% 0.45/0.69      inference('cnf', [status(esa)], [t34_lattice3])).
% 0.45/0.69  thf('111', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((v2_struct_0 @ sk_A)
% 0.45/0.69          | ~ (v10_lattices @ sk_A)
% 0.45/0.69          | ~ (v4_lattice3 @ sk_A)
% 0.45/0.69          | ~ (l3_lattices @ sk_A)
% 0.45/0.69          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 0.45/0.69          | ~ (r3_lattices @ sk_A @ (sk_D_3 @ X0 @ sk_B @ sk_A) @ sk_B)
% 0.45/0.69          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['109', '110'])).
% 0.45/0.69  thf('112', plain, ((v10_lattices @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('113', plain, ((v4_lattice3 @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('114', plain, ((l3_lattices @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('115', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((v2_struct_0 @ sk_A)
% 0.45/0.69          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 0.45/0.69          | ~ (r3_lattices @ sk_A @ (sk_D_3 @ X0 @ sk_B @ sk_A) @ sk_B)
% 0.45/0.69          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.45/0.69      inference('demod', [status(thm)], ['111', '112', '113', '114'])).
% 0.45/0.69  thf('116', plain,
% 0.45/0.69      ((~ (r3_lattice3 @ sk_A @ sk_B @ sk_C)
% 0.45/0.69        | ((sk_B) = (k16_lattice3 @ sk_A @ sk_C))
% 0.45/0.69        | (v2_struct_0 @ sk_A))),
% 0.45/0.69      inference('sup-', [status(thm)], ['108', '115'])).
% 0.45/0.69  thf('117', plain, ((r3_lattice3 @ sk_A @ sk_B @ sk_C)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('118', plain,
% 0.45/0.69      ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C)) | (v2_struct_0 @ sk_A))),
% 0.45/0.69      inference('demod', [status(thm)], ['116', '117'])).
% 0.45/0.69  thf('119', plain, (((k16_lattice3 @ sk_A @ sk_C) != (sk_B))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('120', plain, ((v2_struct_0 @ sk_A)),
% 0.45/0.69      inference('simplify_reflect-', [status(thm)], ['118', '119'])).
% 0.45/0.69  thf('121', plain, ($false), inference('demod', [status(thm)], ['0', '120'])).
% 0.45/0.69  
% 0.45/0.69  % SZS output end Refutation
% 0.45/0.69  
% 0.53/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
