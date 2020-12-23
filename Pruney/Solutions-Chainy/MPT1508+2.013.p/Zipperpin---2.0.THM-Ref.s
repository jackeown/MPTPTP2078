%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cMkezTCJnP

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:32 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 314 expanded)
%              Number of leaves         :   27 ( 101 expanded)
%              Depth                    :   23
%              Number of atoms          : 1560 (5110 expanded)
%              Number of equality atoms :   30 ( 172 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i > $i )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r3_lattice3_type,type,(
    r3_lattice3: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(a_2_9_lattice3_type,type,(
    a_2_9_lattice3: $i > $i > $i )).

thf(r4_lattice3_type,type,(
    r4_lattice3: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

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
    ! [X16: $i,X17: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ~ ( r3_lattice3 @ X17 @ X16 @ X20 )
      | ( r3_lattice3 @ X17 @ ( sk_D_3 @ X20 @ X16 @ X17 ) @ X20 )
      | ( X16
        = ( k16_lattice3 @ X17 @ X20 ) )
      | ~ ( l3_lattices @ X17 )
      | ~ ( v4_lattice3 @ X17 )
      | ~ ( v10_lattices @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
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
    ! [X16: $i,X17: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ~ ( r3_lattice3 @ X17 @ X16 @ X20 )
      | ( m1_subset_1 @ ( sk_D_3 @ X20 @ X16 @ X17 ) @ ( u1_struct_0 @ X17 ) )
      | ( X16
        = ( k16_lattice3 @ X17 @ X20 ) )
      | ~ ( l3_lattices @ X17 )
      | ~ ( v4_lattice3 @ X17 )
      | ~ ( v10_lattices @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
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

thf(fraenkel_a_2_9_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( v10_lattices @ B )
        & ( v4_lattice3 @ B )
        & ( l3_lattices @ B ) )
     => ( ( r2_hidden @ A @ ( a_2_9_lattice3 @ B @ C ) )
      <=> ? [D: $i] :
            ( ( r3_lattice3 @ B @ D @ C )
            & ( A = D )
            & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('27',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( l3_lattices @ X12 )
      | ~ ( v4_lattice3 @ X12 )
      | ~ ( v10_lattices @ X12 )
      | ( v2_struct_0 @ X12 )
      | ( r2_hidden @ X14 @ ( a_2_9_lattice3 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X12 ) )
      | ( X14 != X15 )
      | ~ ( r3_lattice3 @ X12 @ X15 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_9_lattice3])).

thf('28',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ~ ( r3_lattice3 @ X12 @ X15 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X12 ) )
      | ( r2_hidden @ X15 @ ( a_2_9_lattice3 @ X12 @ X13 ) )
      | ( v2_struct_0 @ X12 )
      | ~ ( v10_lattices @ X12 )
      | ~ ( v4_lattice3 @ X12 )
      | ~ ( l3_lattices @ X12 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ ( a_2_9_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ ( a_2_9_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattice3 @ sk_A @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ ( a_2_9_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    r2_hidden @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ ( a_2_9_lattice3 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['13','35'])).

thf('37',plain,(
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

thf('38',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ( r3_lattices @ X22 @ X21 @ ( k15_lattice3 @ X22 @ X23 ) )
      | ~ ( r2_hidden @ X21 @ X23 )
      | ~ ( l3_lattices @ X22 )
      | ~ ( v4_lattice3 @ X22 )
      | ~ ( v10_lattices @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t38_lattice3])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r2_hidden @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ( r3_lattices @ sk_A @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ( r3_lattices @ sk_A @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_A @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ ( k15_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    r3_lattices @ sk_A @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ ( k15_lattice3 @ sk_A @ ( a_2_9_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['36','45'])).

thf('47',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
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

thf('50',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ( r2_hidden @ ( sk_D_1 @ X9 @ X5 @ X6 ) @ X9 )
      | ( r4_lattice3 @ X6 @ X5 @ X9 )
      | ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( l3_lattices @ X12 )
      | ~ ( v4_lattice3 @ X12 )
      | ~ ( v10_lattices @ X12 )
      | ( v2_struct_0 @ X12 )
      | ( X14
        = ( sk_D_2 @ X13 @ X12 @ X14 ) )
      | ~ ( r2_hidden @ X14 @ ( a_2_9_lattice3 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_9_lattice3])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_9_lattice3 @ X1 @ X0 ) )
      | ( ( sk_D_1 @ ( a_2_9_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A )
        = ( sk_D_2 @ X0 @ X1 @ ( sk_D_1 @ ( a_2_9_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('59',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( l3_lattices @ X12 )
      | ~ ( v4_lattice3 @ X12 )
      | ~ ( v10_lattices @ X12 )
      | ( v2_struct_0 @ X12 )
      | ( r3_lattice3 @ X12 @ ( sk_D_2 @ X13 @ X12 @ X14 ) @ X13 )
      | ~ ( r2_hidden @ X14 @ ( a_2_9_lattice3 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_9_lattice3])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_9_lattice3 @ X1 @ X0 ) )
      | ( r3_lattice3 @ X1 @ ( sk_D_2 @ X0 @ X1 @ ( sk_D_1 @ ( a_2_9_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A ) ) @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ X1 @ ( sk_D_1 @ ( a_2_9_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A ) @ X0 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_9_lattice3 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_9_lattice3 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_9_lattice3 @ X1 @ X0 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( r3_lattice3 @ X1 @ ( sk_D_1 @ ( a_2_9_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X9 @ X5 @ X6 ) @ ( u1_struct_0 @ X6 ) )
      | ( r4_lattice3 @ X6 @ X5 @ X9 )
      | ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['67','68'])).

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

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r3_lattice3 @ X1 @ X0 @ X2 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r1_lattices @ X1 @ X0 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X1 )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X1 )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X2 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_9_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_9_lattice3 @ sk_A @ X0 ) @ sk_B @ sk_A ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_9_lattice3 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','73'])).

thf('75',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_9_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_9_lattice3 @ sk_A @ X0 ) @ sk_B @ sk_A ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_9_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['74','75','76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_9_lattice3 @ sk_A @ X0 ) @ sk_B @ sk_A ) @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_9_lattice3 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_9_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_9_lattice3 @ sk_A @ X0 ) @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','79'])).

thf('81',plain,
    ( ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_9_lattice3 @ sk_A @ sk_C ) @ sk_B @ sk_A ) @ sk_B )
    | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_9_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ~ ( r1_lattices @ X6 @ ( sk_D_1 @ X9 @ X5 @ X6 ) @ X5 )
      | ( r4_lattice3 @ X6 @ X5 @ X9 )
      | ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_9_lattice3 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['81','88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    r4_lattice3 @ sk_A @ sk_B @ ( a_2_9_lattice3 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,(
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

thf('93',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) )
      | ( ( k15_lattice3 @ X25 @ X26 )
        = X24 )
      | ~ ( r4_lattice3 @ X25 @ X24 @ X26 )
      | ~ ( r2_hidden @ X24 @ X26 )
      | ~ ( l3_lattices @ X25 )
      | ~ ( v4_lattice3 @ X25 )
      | ~ ( v10_lattices @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t41_lattice3])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( ( k15_lattice3 @ sk_A @ X0 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( ( k15_lattice3 @ sk_A @ X0 )
        = sk_B ) ) ),
    inference(demod,[status(thm)],['94','95','96','97'])).

thf('99',plain,
    ( ( ( k15_lattice3 @ sk_A @ ( a_2_9_lattice3 @ sk_A @ sk_C ) )
      = sk_B )
    | ~ ( r2_hidden @ sk_B @ ( a_2_9_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['91','98'])).

thf('100',plain,(
    r3_lattice3 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ~ ( r3_lattice3 @ X12 @ X15 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X12 ) )
      | ( r2_hidden @ X15 @ ( a_2_9_lattice3 @ X12 @ X13 ) )
      | ( v2_struct_0 @ X12 )
      | ~ ( v10_lattices @ X12 )
      | ~ ( v4_lattice3 @ X12 )
      | ~ ( l3_lattices @ X12 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_B @ ( a_2_9_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_B @ ( a_2_9_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['103','104','105','106'])).

thf('108',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ ( a_2_9_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,(
    r2_hidden @ sk_B @ ( a_2_9_lattice3 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['100','109'])).

thf('111',plain,
    ( ( ( k15_lattice3 @ sk_A @ ( a_2_9_lattice3 @ sk_A @ sk_C ) )
      = sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['99','110'])).

thf('112',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( k15_lattice3 @ sk_A @ ( a_2_9_lattice3 @ sk_A @ sk_C ) )
    = sk_B ),
    inference(clc,[status(thm)],['111','112'])).

thf('114',plain,(
    r3_lattices @ sk_A @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['46','113'])).

thf('115',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X16: $i,X17: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ~ ( r3_lattice3 @ X17 @ X16 @ X20 )
      | ~ ( r3_lattices @ X17 @ ( sk_D_3 @ X20 @ X16 @ X17 ) @ X16 )
      | ( X16
        = ( k16_lattice3 @ X17 @ X20 ) )
      | ~ ( l3_lattices @ X17 )
      | ~ ( v4_lattice3 @ X17 )
      | ~ ( v10_lattices @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( sk_B
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattices @ sk_A @ ( sk_D_3 @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattices @ sk_A @ ( sk_D_3 @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['117','118','119','120'])).

thf('122',plain,
    ( ~ ( r3_lattice3 @ sk_A @ sk_B @ sk_C )
    | ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['114','121'])).

thf('123',plain,(
    r3_lattice3 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ( k16_lattice3 @ sk_A @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['124','125'])).

thf('127',plain,(
    $false ),
    inference(demod,[status(thm)],['0','126'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cMkezTCJnP
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:19:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.90/1.15  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.90/1.15  % Solved by: fo/fo7.sh
% 0.90/1.15  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.15  % done 464 iterations in 0.669s
% 0.90/1.15  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.90/1.15  % SZS output start Refutation
% 0.90/1.15  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.90/1.15  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 0.90/1.15  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.90/1.15  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i > $i).
% 0.90/1.15  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 0.90/1.15  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.90/1.15  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.15  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.90/1.15  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.90/1.15  thf(r3_lattice3_type, type, r3_lattice3: $i > $i > $i > $o).
% 0.90/1.15  thf(sk_C_type, type, sk_C: $i).
% 0.90/1.15  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 0.90/1.15  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 0.90/1.15  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.15  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.90/1.15  thf(a_2_9_lattice3_type, type, a_2_9_lattice3: $i > $i > $i).
% 0.90/1.15  thf(r4_lattice3_type, type, r4_lattice3: $i > $i > $i > $o).
% 0.90/1.15  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.15  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 0.90/1.15  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.90/1.15  thf(t42_lattice3, conjecture,
% 0.90/1.15    (![A:$i]:
% 0.90/1.15     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.90/1.15         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.90/1.15       ( ![B:$i]:
% 0.90/1.15         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.90/1.15           ( ![C:$i]:
% 0.90/1.15             ( ( ( r2_hidden @ B @ C ) & ( r3_lattice3 @ A @ B @ C ) ) =>
% 0.90/1.15               ( ( k16_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ))).
% 0.90/1.15  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.15    (~( ![A:$i]:
% 0.90/1.15        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.90/1.15            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.90/1.15          ( ![B:$i]:
% 0.90/1.15            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.90/1.15              ( ![C:$i]:
% 0.90/1.15                ( ( ( r2_hidden @ B @ C ) & ( r3_lattice3 @ A @ B @ C ) ) =>
% 0.90/1.16                  ( ( k16_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ) )),
% 0.90/1.16    inference('cnf.neg', [status(esa)], [t42_lattice3])).
% 0.90/1.16  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('1', plain, ((r3_lattice3 @ sk_A @ sk_B @ sk_C)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf(t34_lattice3, axiom,
% 0.90/1.16    (![A:$i]:
% 0.90/1.16     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.90/1.16         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.90/1.16       ( ![B:$i]:
% 0.90/1.16         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.90/1.16           ( ![C:$i]:
% 0.90/1.16             ( ( ( B ) = ( k16_lattice3 @ A @ C ) ) <=>
% 0.90/1.16               ( ( r3_lattice3 @ A @ B @ C ) & 
% 0.90/1.16                 ( ![D:$i]:
% 0.90/1.16                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.90/1.16                     ( ( r3_lattice3 @ A @ D @ C ) =>
% 0.90/1.16                       ( r3_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.90/1.16  thf('3', plain,
% 0.90/1.16      (![X16 : $i, X17 : $i, X20 : $i]:
% 0.90/1.16         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.90/1.16          | ~ (r3_lattice3 @ X17 @ X16 @ X20)
% 0.90/1.16          | (r3_lattice3 @ X17 @ (sk_D_3 @ X20 @ X16 @ X17) @ X20)
% 0.90/1.16          | ((X16) = (k16_lattice3 @ X17 @ X20))
% 0.90/1.16          | ~ (l3_lattices @ X17)
% 0.90/1.16          | ~ (v4_lattice3 @ X17)
% 0.90/1.16          | ~ (v10_lattices @ X17)
% 0.90/1.16          | (v2_struct_0 @ X17))),
% 0.90/1.16      inference('cnf', [status(esa)], [t34_lattice3])).
% 0.90/1.16  thf('4', plain,
% 0.90/1.16      (![X0 : $i]:
% 0.90/1.16         ((v2_struct_0 @ sk_A)
% 0.90/1.16          | ~ (v10_lattices @ sk_A)
% 0.90/1.16          | ~ (v4_lattice3 @ sk_A)
% 0.90/1.16          | ~ (l3_lattices @ sk_A)
% 0.90/1.16          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 0.90/1.16          | (r3_lattice3 @ sk_A @ (sk_D_3 @ X0 @ sk_B @ sk_A) @ X0)
% 0.90/1.16          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.90/1.16      inference('sup-', [status(thm)], ['2', '3'])).
% 0.90/1.16  thf('5', plain, ((v10_lattices @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('6', plain, ((v4_lattice3 @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('7', plain, ((l3_lattices @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('8', plain,
% 0.90/1.16      (![X0 : $i]:
% 0.90/1.16         ((v2_struct_0 @ sk_A)
% 0.90/1.16          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 0.90/1.16          | (r3_lattice3 @ sk_A @ (sk_D_3 @ X0 @ sk_B @ sk_A) @ X0)
% 0.90/1.16          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.90/1.16      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.90/1.16  thf('9', plain,
% 0.90/1.16      (((r3_lattice3 @ sk_A @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.90/1.16        | ((sk_B) = (k16_lattice3 @ sk_A @ sk_C))
% 0.90/1.16        | (v2_struct_0 @ sk_A))),
% 0.90/1.16      inference('sup-', [status(thm)], ['1', '8'])).
% 0.90/1.16  thf('10', plain, (((k16_lattice3 @ sk_A @ sk_C) != (sk_B))),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('11', plain,
% 0.90/1.16      (((r3_lattice3 @ sk_A @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.90/1.16        | (v2_struct_0 @ sk_A))),
% 0.90/1.16      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.90/1.16  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('13', plain,
% 0.90/1.16      ((r3_lattice3 @ sk_A @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ sk_C)),
% 0.90/1.16      inference('clc', [status(thm)], ['11', '12'])).
% 0.90/1.16  thf('14', plain, ((r3_lattice3 @ sk_A @ sk_B @ sk_C)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('15', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('16', plain,
% 0.90/1.16      (![X16 : $i, X17 : $i, X20 : $i]:
% 0.90/1.16         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.90/1.16          | ~ (r3_lattice3 @ X17 @ X16 @ X20)
% 0.90/1.16          | (m1_subset_1 @ (sk_D_3 @ X20 @ X16 @ X17) @ (u1_struct_0 @ X17))
% 0.90/1.16          | ((X16) = (k16_lattice3 @ X17 @ X20))
% 0.90/1.16          | ~ (l3_lattices @ X17)
% 0.90/1.16          | ~ (v4_lattice3 @ X17)
% 0.90/1.16          | ~ (v10_lattices @ X17)
% 0.90/1.16          | (v2_struct_0 @ X17))),
% 0.90/1.16      inference('cnf', [status(esa)], [t34_lattice3])).
% 0.90/1.16  thf('17', plain,
% 0.90/1.16      (![X0 : $i]:
% 0.90/1.16         ((v2_struct_0 @ sk_A)
% 0.90/1.16          | ~ (v10_lattices @ sk_A)
% 0.90/1.16          | ~ (v4_lattice3 @ sk_A)
% 0.90/1.16          | ~ (l3_lattices @ sk_A)
% 0.90/1.16          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 0.90/1.16          | (m1_subset_1 @ (sk_D_3 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.90/1.16          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.90/1.16      inference('sup-', [status(thm)], ['15', '16'])).
% 0.90/1.16  thf('18', plain, ((v10_lattices @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('19', plain, ((v4_lattice3 @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('20', plain, ((l3_lattices @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('21', plain,
% 0.90/1.16      (![X0 : $i]:
% 0.90/1.16         ((v2_struct_0 @ sk_A)
% 0.90/1.16          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 0.90/1.16          | (m1_subset_1 @ (sk_D_3 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.90/1.16          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.90/1.16      inference('demod', [status(thm)], ['17', '18', '19', '20'])).
% 0.90/1.16  thf('22', plain,
% 0.90/1.16      (((m1_subset_1 @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.90/1.16        | ((sk_B) = (k16_lattice3 @ sk_A @ sk_C))
% 0.90/1.16        | (v2_struct_0 @ sk_A))),
% 0.90/1.16      inference('sup-', [status(thm)], ['14', '21'])).
% 0.90/1.16  thf('23', plain, (((k16_lattice3 @ sk_A @ sk_C) != (sk_B))),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('24', plain,
% 0.90/1.16      (((m1_subset_1 @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.90/1.16        | (v2_struct_0 @ sk_A))),
% 0.90/1.16      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.90/1.16  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('26', plain,
% 0.90/1.16      ((m1_subset_1 @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.90/1.16      inference('clc', [status(thm)], ['24', '25'])).
% 0.90/1.16  thf(fraenkel_a_2_9_lattice3, axiom,
% 0.90/1.16    (![A:$i,B:$i,C:$i]:
% 0.90/1.16     ( ( ( ~( v2_struct_0 @ B ) ) & ( v10_lattices @ B ) & 
% 0.90/1.16         ( v4_lattice3 @ B ) & ( l3_lattices @ B ) ) =>
% 0.90/1.16       ( ( r2_hidden @ A @ ( a_2_9_lattice3 @ B @ C ) ) <=>
% 0.90/1.16         ( ?[D:$i]:
% 0.90/1.16           ( ( r3_lattice3 @ B @ D @ C ) & ( ( A ) = ( D ) ) & 
% 0.90/1.16             ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.90/1.16  thf('27', plain,
% 0.90/1.16      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.90/1.16         (~ (l3_lattices @ X12)
% 0.90/1.16          | ~ (v4_lattice3 @ X12)
% 0.90/1.16          | ~ (v10_lattices @ X12)
% 0.90/1.16          | (v2_struct_0 @ X12)
% 0.90/1.16          | (r2_hidden @ X14 @ (a_2_9_lattice3 @ X12 @ X13))
% 0.90/1.16          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X12))
% 0.90/1.16          | ((X14) != (X15))
% 0.90/1.16          | ~ (r3_lattice3 @ X12 @ X15 @ X13))),
% 0.90/1.16      inference('cnf', [status(esa)], [fraenkel_a_2_9_lattice3])).
% 0.90/1.16  thf('28', plain,
% 0.90/1.16      (![X12 : $i, X13 : $i, X15 : $i]:
% 0.90/1.16         (~ (r3_lattice3 @ X12 @ X15 @ X13)
% 0.90/1.16          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X12))
% 0.90/1.16          | (r2_hidden @ X15 @ (a_2_9_lattice3 @ X12 @ X13))
% 0.90/1.16          | (v2_struct_0 @ X12)
% 0.90/1.16          | ~ (v10_lattices @ X12)
% 0.90/1.16          | ~ (v4_lattice3 @ X12)
% 0.90/1.16          | ~ (l3_lattices @ X12))),
% 0.90/1.16      inference('simplify', [status(thm)], ['27'])).
% 0.90/1.16  thf('29', plain,
% 0.90/1.16      (![X0 : $i]:
% 0.90/1.16         (~ (l3_lattices @ sk_A)
% 0.90/1.16          | ~ (v4_lattice3 @ sk_A)
% 0.90/1.16          | ~ (v10_lattices @ sk_A)
% 0.90/1.16          | (v2_struct_0 @ sk_A)
% 0.90/1.16          | (r2_hidden @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ 
% 0.90/1.16             (a_2_9_lattice3 @ sk_A @ X0))
% 0.90/1.16          | ~ (r3_lattice3 @ sk_A @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ X0))),
% 0.90/1.16      inference('sup-', [status(thm)], ['26', '28'])).
% 0.90/1.16  thf('30', plain, ((l3_lattices @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('31', plain, ((v4_lattice3 @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('32', plain, ((v10_lattices @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('33', plain,
% 0.90/1.16      (![X0 : $i]:
% 0.90/1.16         ((v2_struct_0 @ sk_A)
% 0.90/1.16          | (r2_hidden @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ 
% 0.90/1.16             (a_2_9_lattice3 @ sk_A @ X0))
% 0.90/1.16          | ~ (r3_lattice3 @ sk_A @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ X0))),
% 0.90/1.16      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.90/1.16  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('35', plain,
% 0.90/1.16      (![X0 : $i]:
% 0.90/1.16         (~ (r3_lattice3 @ sk_A @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ X0)
% 0.90/1.16          | (r2_hidden @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ 
% 0.90/1.16             (a_2_9_lattice3 @ sk_A @ X0)))),
% 0.90/1.16      inference('clc', [status(thm)], ['33', '34'])).
% 0.90/1.16  thf('36', plain,
% 0.90/1.16      ((r2_hidden @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ 
% 0.90/1.16        (a_2_9_lattice3 @ sk_A @ sk_C))),
% 0.90/1.16      inference('sup-', [status(thm)], ['13', '35'])).
% 0.90/1.16  thf('37', plain,
% 0.90/1.16      ((m1_subset_1 @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.90/1.16      inference('clc', [status(thm)], ['24', '25'])).
% 0.90/1.16  thf(t38_lattice3, axiom,
% 0.90/1.16    (![A:$i]:
% 0.90/1.16     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.90/1.16         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.90/1.16       ( ![B:$i]:
% 0.90/1.16         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.90/1.16           ( ![C:$i]:
% 0.90/1.16             ( ( r2_hidden @ B @ C ) =>
% 0.90/1.16               ( ( r3_lattices @ A @ B @ ( k15_lattice3 @ A @ C ) ) & 
% 0.90/1.16                 ( r3_lattices @ A @ ( k16_lattice3 @ A @ C ) @ B ) ) ) ) ) ) ))).
% 0.90/1.16  thf('38', plain,
% 0.90/1.16      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.90/1.16         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 0.90/1.16          | (r3_lattices @ X22 @ X21 @ (k15_lattice3 @ X22 @ X23))
% 0.90/1.16          | ~ (r2_hidden @ X21 @ X23)
% 0.90/1.16          | ~ (l3_lattices @ X22)
% 0.90/1.16          | ~ (v4_lattice3 @ X22)
% 0.90/1.16          | ~ (v10_lattices @ X22)
% 0.90/1.16          | (v2_struct_0 @ X22))),
% 0.90/1.16      inference('cnf', [status(esa)], [t38_lattice3])).
% 0.90/1.16  thf('39', plain,
% 0.90/1.16      (![X0 : $i]:
% 0.90/1.16         ((v2_struct_0 @ sk_A)
% 0.90/1.16          | ~ (v10_lattices @ sk_A)
% 0.90/1.16          | ~ (v4_lattice3 @ sk_A)
% 0.90/1.16          | ~ (l3_lattices @ sk_A)
% 0.90/1.16          | ~ (r2_hidden @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ X0)
% 0.90/1.16          | (r3_lattices @ sk_A @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ 
% 0.90/1.16             (k15_lattice3 @ sk_A @ X0)))),
% 0.90/1.16      inference('sup-', [status(thm)], ['37', '38'])).
% 0.90/1.16  thf('40', plain, ((v10_lattices @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('41', plain, ((v4_lattice3 @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('42', plain, ((l3_lattices @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('43', plain,
% 0.90/1.16      (![X0 : $i]:
% 0.90/1.16         ((v2_struct_0 @ sk_A)
% 0.90/1.16          | ~ (r2_hidden @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ X0)
% 0.90/1.16          | (r3_lattices @ sk_A @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ 
% 0.90/1.16             (k15_lattice3 @ sk_A @ X0)))),
% 0.90/1.16      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 0.90/1.16  thf('44', plain, (~ (v2_struct_0 @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('45', plain,
% 0.90/1.16      (![X0 : $i]:
% 0.90/1.16         ((r3_lattices @ sk_A @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ 
% 0.90/1.16           (k15_lattice3 @ sk_A @ X0))
% 0.90/1.16          | ~ (r2_hidden @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ X0))),
% 0.90/1.16      inference('clc', [status(thm)], ['43', '44'])).
% 0.90/1.16  thf('46', plain,
% 0.90/1.16      ((r3_lattices @ sk_A @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ 
% 0.90/1.16        (k15_lattice3 @ sk_A @ (a_2_9_lattice3 @ sk_A @ sk_C)))),
% 0.90/1.16      inference('sup-', [status(thm)], ['36', '45'])).
% 0.90/1.16  thf('47', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('48', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('49', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf(d17_lattice3, axiom,
% 0.90/1.16    (![A:$i]:
% 0.90/1.16     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.90/1.16       ( ![B:$i]:
% 0.90/1.16         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.90/1.16           ( ![C:$i]:
% 0.90/1.16             ( ( r4_lattice3 @ A @ B @ C ) <=>
% 0.90/1.16               ( ![D:$i]:
% 0.90/1.16                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.90/1.16                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ))).
% 0.90/1.16  thf('50', plain,
% 0.90/1.16      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.90/1.16         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 0.90/1.16          | (r2_hidden @ (sk_D_1 @ X9 @ X5 @ X6) @ X9)
% 0.90/1.16          | (r4_lattice3 @ X6 @ X5 @ X9)
% 0.90/1.16          | ~ (l3_lattices @ X6)
% 0.90/1.16          | (v2_struct_0 @ X6))),
% 0.90/1.16      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.90/1.16  thf('51', plain,
% 0.90/1.16      (![X0 : $i]:
% 0.90/1.16         ((v2_struct_0 @ sk_A)
% 0.90/1.16          | ~ (l3_lattices @ sk_A)
% 0.90/1.16          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.90/1.16          | (r2_hidden @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0))),
% 0.90/1.16      inference('sup-', [status(thm)], ['49', '50'])).
% 0.90/1.16  thf('52', plain, ((l3_lattices @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('53', plain,
% 0.90/1.16      (![X0 : $i]:
% 0.90/1.16         ((v2_struct_0 @ sk_A)
% 0.90/1.16          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.90/1.16          | (r2_hidden @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0))),
% 0.90/1.16      inference('demod', [status(thm)], ['51', '52'])).
% 0.90/1.16  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('55', plain,
% 0.90/1.16      (![X0 : $i]:
% 0.90/1.16         ((r2_hidden @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0)
% 0.90/1.16          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 0.90/1.16      inference('clc', [status(thm)], ['53', '54'])).
% 0.90/1.16  thf('56', plain,
% 0.90/1.16      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.90/1.16         (~ (l3_lattices @ X12)
% 0.90/1.16          | ~ (v4_lattice3 @ X12)
% 0.90/1.16          | ~ (v10_lattices @ X12)
% 0.90/1.16          | (v2_struct_0 @ X12)
% 0.90/1.16          | ((X14) = (sk_D_2 @ X13 @ X12 @ X14))
% 0.90/1.16          | ~ (r2_hidden @ X14 @ (a_2_9_lattice3 @ X12 @ X13)))),
% 0.90/1.16      inference('cnf', [status(esa)], [fraenkel_a_2_9_lattice3])).
% 0.90/1.16  thf('57', plain,
% 0.90/1.16      (![X0 : $i, X1 : $i]:
% 0.90/1.16         ((r4_lattice3 @ sk_A @ sk_B @ (a_2_9_lattice3 @ X1 @ X0))
% 0.90/1.16          | ((sk_D_1 @ (a_2_9_lattice3 @ X1 @ X0) @ sk_B @ sk_A)
% 0.90/1.16              = (sk_D_2 @ X0 @ X1 @ 
% 0.90/1.16                 (sk_D_1 @ (a_2_9_lattice3 @ X1 @ X0) @ sk_B @ sk_A)))
% 0.90/1.16          | (v2_struct_0 @ X1)
% 0.90/1.16          | ~ (v10_lattices @ X1)
% 0.90/1.16          | ~ (v4_lattice3 @ X1)
% 0.90/1.16          | ~ (l3_lattices @ X1))),
% 0.90/1.16      inference('sup-', [status(thm)], ['55', '56'])).
% 0.90/1.16  thf('58', plain,
% 0.90/1.16      (![X0 : $i]:
% 0.90/1.16         ((r2_hidden @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0)
% 0.90/1.16          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 0.90/1.16      inference('clc', [status(thm)], ['53', '54'])).
% 0.90/1.16  thf('59', plain,
% 0.90/1.16      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.90/1.16         (~ (l3_lattices @ X12)
% 0.90/1.16          | ~ (v4_lattice3 @ X12)
% 0.90/1.16          | ~ (v10_lattices @ X12)
% 0.90/1.16          | (v2_struct_0 @ X12)
% 0.90/1.16          | (r3_lattice3 @ X12 @ (sk_D_2 @ X13 @ X12 @ X14) @ X13)
% 0.90/1.16          | ~ (r2_hidden @ X14 @ (a_2_9_lattice3 @ X12 @ X13)))),
% 0.90/1.16      inference('cnf', [status(esa)], [fraenkel_a_2_9_lattice3])).
% 0.90/1.16  thf('60', plain,
% 0.90/1.16      (![X0 : $i, X1 : $i]:
% 0.90/1.16         ((r4_lattice3 @ sk_A @ sk_B @ (a_2_9_lattice3 @ X1 @ X0))
% 0.90/1.16          | (r3_lattice3 @ X1 @ 
% 0.90/1.16             (sk_D_2 @ X0 @ X1 @ 
% 0.90/1.16              (sk_D_1 @ (a_2_9_lattice3 @ X1 @ X0) @ sk_B @ sk_A)) @ 
% 0.90/1.16             X0)
% 0.90/1.16          | (v2_struct_0 @ X1)
% 0.90/1.16          | ~ (v10_lattices @ X1)
% 0.90/1.16          | ~ (v4_lattice3 @ X1)
% 0.90/1.16          | ~ (l3_lattices @ X1))),
% 0.90/1.16      inference('sup-', [status(thm)], ['58', '59'])).
% 0.90/1.16  thf('61', plain,
% 0.90/1.16      (![X0 : $i, X1 : $i]:
% 0.90/1.16         ((r3_lattice3 @ X1 @ 
% 0.90/1.16           (sk_D_1 @ (a_2_9_lattice3 @ X1 @ X0) @ sk_B @ sk_A) @ X0)
% 0.90/1.16          | ~ (l3_lattices @ X1)
% 0.90/1.16          | ~ (v4_lattice3 @ X1)
% 0.90/1.16          | ~ (v10_lattices @ X1)
% 0.90/1.16          | (v2_struct_0 @ X1)
% 0.90/1.16          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_9_lattice3 @ X1 @ X0))
% 0.90/1.16          | ~ (l3_lattices @ X1)
% 0.90/1.16          | ~ (v4_lattice3 @ X1)
% 0.90/1.16          | ~ (v10_lattices @ X1)
% 0.90/1.16          | (v2_struct_0 @ X1)
% 0.90/1.16          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_9_lattice3 @ X1 @ X0)))),
% 0.90/1.16      inference('sup+', [status(thm)], ['57', '60'])).
% 0.90/1.16  thf('62', plain,
% 0.90/1.16      (![X0 : $i, X1 : $i]:
% 0.90/1.16         ((r4_lattice3 @ sk_A @ sk_B @ (a_2_9_lattice3 @ X1 @ X0))
% 0.90/1.16          | (v2_struct_0 @ X1)
% 0.90/1.16          | ~ (v10_lattices @ X1)
% 0.90/1.16          | ~ (v4_lattice3 @ X1)
% 0.90/1.16          | ~ (l3_lattices @ X1)
% 0.90/1.16          | (r3_lattice3 @ X1 @ 
% 0.90/1.16             (sk_D_1 @ (a_2_9_lattice3 @ X1 @ X0) @ sk_B @ sk_A) @ X0))),
% 0.90/1.16      inference('simplify', [status(thm)], ['61'])).
% 0.90/1.16  thf('63', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('64', plain,
% 0.90/1.16      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.90/1.16         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 0.90/1.16          | (m1_subset_1 @ (sk_D_1 @ X9 @ X5 @ X6) @ (u1_struct_0 @ X6))
% 0.90/1.16          | (r4_lattice3 @ X6 @ X5 @ X9)
% 0.90/1.16          | ~ (l3_lattices @ X6)
% 0.90/1.16          | (v2_struct_0 @ X6))),
% 0.90/1.16      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.90/1.16  thf('65', plain,
% 0.90/1.16      (![X0 : $i]:
% 0.90/1.16         ((v2_struct_0 @ sk_A)
% 0.90/1.16          | ~ (l3_lattices @ sk_A)
% 0.90/1.16          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.90/1.16          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.90/1.16      inference('sup-', [status(thm)], ['63', '64'])).
% 0.90/1.16  thf('66', plain, ((l3_lattices @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('67', plain,
% 0.90/1.16      (![X0 : $i]:
% 0.90/1.16         ((v2_struct_0 @ sk_A)
% 0.90/1.16          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.90/1.16          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.90/1.16      inference('demod', [status(thm)], ['65', '66'])).
% 0.90/1.16  thf('68', plain, (~ (v2_struct_0 @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('69', plain,
% 0.90/1.16      (![X0 : $i]:
% 0.90/1.16         ((m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.90/1.16          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 0.90/1.16      inference('clc', [status(thm)], ['67', '68'])).
% 0.90/1.16  thf(d16_lattice3, axiom,
% 0.90/1.16    (![A:$i]:
% 0.90/1.16     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.90/1.16       ( ![B:$i]:
% 0.90/1.16         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.90/1.16           ( ![C:$i]:
% 0.90/1.16             ( ( r3_lattice3 @ A @ B @ C ) <=>
% 0.90/1.16               ( ![D:$i]:
% 0.90/1.16                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.90/1.16                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 0.90/1.16  thf('70', plain,
% 0.90/1.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.90/1.16         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.90/1.16          | ~ (r3_lattice3 @ X1 @ X0 @ X2)
% 0.90/1.16          | ~ (r2_hidden @ X3 @ X2)
% 0.90/1.16          | (r1_lattices @ X1 @ X0 @ X3)
% 0.90/1.16          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.90/1.16          | ~ (l3_lattices @ X1)
% 0.90/1.16          | (v2_struct_0 @ X1))),
% 0.90/1.16      inference('cnf', [status(esa)], [d16_lattice3])).
% 0.90/1.16  thf('71', plain,
% 0.90/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.16         ((r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.90/1.16          | (v2_struct_0 @ sk_A)
% 0.90/1.16          | ~ (l3_lattices @ sk_A)
% 0.90/1.16          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.90/1.16          | (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X1)
% 0.90/1.16          | ~ (r2_hidden @ X1 @ X2)
% 0.90/1.16          | ~ (r3_lattice3 @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X2))),
% 0.90/1.16      inference('sup-', [status(thm)], ['69', '70'])).
% 0.90/1.16  thf('72', plain, ((l3_lattices @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('73', plain,
% 0.90/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.16         ((r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.90/1.16          | (v2_struct_0 @ sk_A)
% 0.90/1.16          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.90/1.16          | (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X1)
% 0.90/1.16          | ~ (r2_hidden @ X1 @ X2)
% 0.90/1.16          | ~ (r3_lattice3 @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X2))),
% 0.90/1.16      inference('demod', [status(thm)], ['71', '72'])).
% 0.90/1.16  thf('74', plain,
% 0.90/1.16      (![X0 : $i, X1 : $i]:
% 0.90/1.16         (~ (l3_lattices @ sk_A)
% 0.90/1.16          | ~ (v4_lattice3 @ sk_A)
% 0.90/1.16          | ~ (v10_lattices @ sk_A)
% 0.90/1.16          | (v2_struct_0 @ sk_A)
% 0.90/1.16          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_9_lattice3 @ sk_A @ X0))
% 0.90/1.16          | ~ (r2_hidden @ X1 @ X0)
% 0.90/1.16          | (r1_lattices @ sk_A @ 
% 0.90/1.16             (sk_D_1 @ (a_2_9_lattice3 @ sk_A @ X0) @ sk_B @ sk_A) @ X1)
% 0.90/1.16          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.90/1.16          | (v2_struct_0 @ sk_A)
% 0.90/1.16          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_9_lattice3 @ sk_A @ X0)))),
% 0.90/1.16      inference('sup-', [status(thm)], ['62', '73'])).
% 0.90/1.16  thf('75', plain, ((l3_lattices @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('76', plain, ((v4_lattice3 @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('77', plain, ((v10_lattices @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('78', plain,
% 0.90/1.16      (![X0 : $i, X1 : $i]:
% 0.90/1.16         ((v2_struct_0 @ sk_A)
% 0.90/1.16          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_9_lattice3 @ sk_A @ X0))
% 0.90/1.16          | ~ (r2_hidden @ X1 @ X0)
% 0.90/1.16          | (r1_lattices @ sk_A @ 
% 0.90/1.16             (sk_D_1 @ (a_2_9_lattice3 @ sk_A @ X0) @ sk_B @ sk_A) @ X1)
% 0.90/1.16          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.90/1.16          | (v2_struct_0 @ sk_A)
% 0.90/1.16          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_9_lattice3 @ sk_A @ X0)))),
% 0.90/1.16      inference('demod', [status(thm)], ['74', '75', '76', '77'])).
% 0.90/1.16  thf('79', plain,
% 0.90/1.16      (![X0 : $i, X1 : $i]:
% 0.90/1.16         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.90/1.16          | (r1_lattices @ sk_A @ 
% 0.90/1.16             (sk_D_1 @ (a_2_9_lattice3 @ sk_A @ X0) @ sk_B @ sk_A) @ X1)
% 0.90/1.16          | ~ (r2_hidden @ X1 @ X0)
% 0.90/1.16          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_9_lattice3 @ sk_A @ X0))
% 0.90/1.16          | (v2_struct_0 @ sk_A))),
% 0.90/1.16      inference('simplify', [status(thm)], ['78'])).
% 0.90/1.16  thf('80', plain,
% 0.90/1.16      (![X0 : $i]:
% 0.90/1.16         ((v2_struct_0 @ sk_A)
% 0.90/1.16          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_9_lattice3 @ sk_A @ X0))
% 0.90/1.16          | ~ (r2_hidden @ sk_B @ X0)
% 0.90/1.16          | (r1_lattices @ sk_A @ 
% 0.90/1.16             (sk_D_1 @ (a_2_9_lattice3 @ sk_A @ X0) @ sk_B @ sk_A) @ sk_B))),
% 0.90/1.16      inference('sup-', [status(thm)], ['48', '79'])).
% 0.90/1.16  thf('81', plain,
% 0.90/1.16      (((r1_lattices @ sk_A @ 
% 0.90/1.16         (sk_D_1 @ (a_2_9_lattice3 @ sk_A @ sk_C) @ sk_B @ sk_A) @ sk_B)
% 0.90/1.16        | (r4_lattice3 @ sk_A @ sk_B @ (a_2_9_lattice3 @ sk_A @ sk_C))
% 0.90/1.16        | (v2_struct_0 @ sk_A))),
% 0.90/1.16      inference('sup-', [status(thm)], ['47', '80'])).
% 0.90/1.16  thf('82', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('83', plain,
% 0.90/1.16      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.90/1.16         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 0.90/1.16          | ~ (r1_lattices @ X6 @ (sk_D_1 @ X9 @ X5 @ X6) @ X5)
% 0.90/1.16          | (r4_lattice3 @ X6 @ X5 @ X9)
% 0.90/1.16          | ~ (l3_lattices @ X6)
% 0.90/1.16          | (v2_struct_0 @ X6))),
% 0.90/1.16      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.90/1.16  thf('84', plain,
% 0.90/1.16      (![X0 : $i]:
% 0.90/1.16         ((v2_struct_0 @ sk_A)
% 0.90/1.16          | ~ (l3_lattices @ sk_A)
% 0.90/1.16          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.90/1.16          | ~ (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_B))),
% 0.90/1.16      inference('sup-', [status(thm)], ['82', '83'])).
% 0.90/1.16  thf('85', plain, ((l3_lattices @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('86', plain,
% 0.90/1.16      (![X0 : $i]:
% 0.90/1.16         ((v2_struct_0 @ sk_A)
% 0.90/1.16          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.90/1.16          | ~ (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_B))),
% 0.90/1.16      inference('demod', [status(thm)], ['84', '85'])).
% 0.90/1.16  thf('87', plain, (~ (v2_struct_0 @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('88', plain,
% 0.90/1.16      (![X0 : $i]:
% 0.90/1.16         (~ (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_B)
% 0.90/1.16          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 0.90/1.16      inference('clc', [status(thm)], ['86', '87'])).
% 0.90/1.16  thf('89', plain,
% 0.90/1.16      (((v2_struct_0 @ sk_A)
% 0.90/1.16        | (r4_lattice3 @ sk_A @ sk_B @ (a_2_9_lattice3 @ sk_A @ sk_C)))),
% 0.90/1.16      inference('clc', [status(thm)], ['81', '88'])).
% 0.90/1.16  thf('90', plain, (~ (v2_struct_0 @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('91', plain,
% 0.90/1.16      ((r4_lattice3 @ sk_A @ sk_B @ (a_2_9_lattice3 @ sk_A @ sk_C))),
% 0.90/1.16      inference('clc', [status(thm)], ['89', '90'])).
% 0.90/1.16  thf('92', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf(t41_lattice3, axiom,
% 0.90/1.16    (![A:$i]:
% 0.90/1.16     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.90/1.16         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.90/1.16       ( ![B:$i]:
% 0.90/1.16         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.90/1.16           ( ![C:$i]:
% 0.90/1.16             ( ( ( r2_hidden @ B @ C ) & ( r4_lattice3 @ A @ B @ C ) ) =>
% 0.90/1.16               ( ( k15_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ))).
% 0.90/1.16  thf('93', plain,
% 0.90/1.16      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.90/1.16         (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X25))
% 0.90/1.16          | ((k15_lattice3 @ X25 @ X26) = (X24))
% 0.90/1.16          | ~ (r4_lattice3 @ X25 @ X24 @ X26)
% 0.90/1.16          | ~ (r2_hidden @ X24 @ X26)
% 0.90/1.16          | ~ (l3_lattices @ X25)
% 0.90/1.16          | ~ (v4_lattice3 @ X25)
% 0.90/1.16          | ~ (v10_lattices @ X25)
% 0.90/1.16          | (v2_struct_0 @ X25))),
% 0.90/1.16      inference('cnf', [status(esa)], [t41_lattice3])).
% 0.90/1.16  thf('94', plain,
% 0.90/1.16      (![X0 : $i]:
% 0.90/1.16         ((v2_struct_0 @ sk_A)
% 0.90/1.16          | ~ (v10_lattices @ sk_A)
% 0.90/1.16          | ~ (v4_lattice3 @ sk_A)
% 0.90/1.16          | ~ (l3_lattices @ sk_A)
% 0.90/1.16          | ~ (r2_hidden @ sk_B @ X0)
% 0.90/1.16          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.90/1.16          | ((k15_lattice3 @ sk_A @ X0) = (sk_B)))),
% 0.90/1.16      inference('sup-', [status(thm)], ['92', '93'])).
% 0.90/1.16  thf('95', plain, ((v10_lattices @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('96', plain, ((v4_lattice3 @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('97', plain, ((l3_lattices @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('98', plain,
% 0.90/1.16      (![X0 : $i]:
% 0.90/1.16         ((v2_struct_0 @ sk_A)
% 0.90/1.16          | ~ (r2_hidden @ sk_B @ X0)
% 0.90/1.16          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.90/1.16          | ((k15_lattice3 @ sk_A @ X0) = (sk_B)))),
% 0.90/1.16      inference('demod', [status(thm)], ['94', '95', '96', '97'])).
% 0.90/1.16  thf('99', plain,
% 0.90/1.16      ((((k15_lattice3 @ sk_A @ (a_2_9_lattice3 @ sk_A @ sk_C)) = (sk_B))
% 0.90/1.16        | ~ (r2_hidden @ sk_B @ (a_2_9_lattice3 @ sk_A @ sk_C))
% 0.90/1.16        | (v2_struct_0 @ sk_A))),
% 0.90/1.16      inference('sup-', [status(thm)], ['91', '98'])).
% 0.90/1.16  thf('100', plain, ((r3_lattice3 @ sk_A @ sk_B @ sk_C)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('101', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('102', plain,
% 0.90/1.16      (![X12 : $i, X13 : $i, X15 : $i]:
% 0.90/1.16         (~ (r3_lattice3 @ X12 @ X15 @ X13)
% 0.90/1.16          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X12))
% 0.90/1.16          | (r2_hidden @ X15 @ (a_2_9_lattice3 @ X12 @ X13))
% 0.90/1.16          | (v2_struct_0 @ X12)
% 0.90/1.16          | ~ (v10_lattices @ X12)
% 0.90/1.16          | ~ (v4_lattice3 @ X12)
% 0.90/1.16          | ~ (l3_lattices @ X12))),
% 0.90/1.16      inference('simplify', [status(thm)], ['27'])).
% 0.90/1.16  thf('103', plain,
% 0.90/1.16      (![X0 : $i]:
% 0.90/1.16         (~ (l3_lattices @ sk_A)
% 0.90/1.16          | ~ (v4_lattice3 @ sk_A)
% 0.90/1.16          | ~ (v10_lattices @ sk_A)
% 0.90/1.16          | (v2_struct_0 @ sk_A)
% 0.90/1.16          | (r2_hidden @ sk_B @ (a_2_9_lattice3 @ sk_A @ X0))
% 0.90/1.16          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.90/1.16      inference('sup-', [status(thm)], ['101', '102'])).
% 0.90/1.16  thf('104', plain, ((l3_lattices @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('105', plain, ((v4_lattice3 @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('106', plain, ((v10_lattices @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('107', plain,
% 0.90/1.16      (![X0 : $i]:
% 0.90/1.16         ((v2_struct_0 @ sk_A)
% 0.90/1.16          | (r2_hidden @ sk_B @ (a_2_9_lattice3 @ sk_A @ X0))
% 0.90/1.16          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.90/1.16      inference('demod', [status(thm)], ['103', '104', '105', '106'])).
% 0.90/1.16  thf('108', plain, (~ (v2_struct_0 @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('109', plain,
% 0.90/1.16      (![X0 : $i]:
% 0.90/1.16         (~ (r3_lattice3 @ sk_A @ sk_B @ X0)
% 0.90/1.16          | (r2_hidden @ sk_B @ (a_2_9_lattice3 @ sk_A @ X0)))),
% 0.90/1.16      inference('clc', [status(thm)], ['107', '108'])).
% 0.90/1.16  thf('110', plain, ((r2_hidden @ sk_B @ (a_2_9_lattice3 @ sk_A @ sk_C))),
% 0.90/1.16      inference('sup-', [status(thm)], ['100', '109'])).
% 0.90/1.16  thf('111', plain,
% 0.90/1.16      ((((k15_lattice3 @ sk_A @ (a_2_9_lattice3 @ sk_A @ sk_C)) = (sk_B))
% 0.90/1.16        | (v2_struct_0 @ sk_A))),
% 0.90/1.16      inference('demod', [status(thm)], ['99', '110'])).
% 0.90/1.16  thf('112', plain, (~ (v2_struct_0 @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('113', plain,
% 0.90/1.16      (((k15_lattice3 @ sk_A @ (a_2_9_lattice3 @ sk_A @ sk_C)) = (sk_B))),
% 0.90/1.16      inference('clc', [status(thm)], ['111', '112'])).
% 0.90/1.16  thf('114', plain,
% 0.90/1.16      ((r3_lattices @ sk_A @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.90/1.16      inference('demod', [status(thm)], ['46', '113'])).
% 0.90/1.16  thf('115', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('116', plain,
% 0.90/1.16      (![X16 : $i, X17 : $i, X20 : $i]:
% 0.90/1.16         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.90/1.16          | ~ (r3_lattice3 @ X17 @ X16 @ X20)
% 0.90/1.16          | ~ (r3_lattices @ X17 @ (sk_D_3 @ X20 @ X16 @ X17) @ X16)
% 0.90/1.16          | ((X16) = (k16_lattice3 @ X17 @ X20))
% 0.90/1.16          | ~ (l3_lattices @ X17)
% 0.90/1.16          | ~ (v4_lattice3 @ X17)
% 0.90/1.16          | ~ (v10_lattices @ X17)
% 0.90/1.16          | (v2_struct_0 @ X17))),
% 0.90/1.16      inference('cnf', [status(esa)], [t34_lattice3])).
% 0.90/1.16  thf('117', plain,
% 0.90/1.16      (![X0 : $i]:
% 0.90/1.16         ((v2_struct_0 @ sk_A)
% 0.90/1.16          | ~ (v10_lattices @ sk_A)
% 0.90/1.16          | ~ (v4_lattice3 @ sk_A)
% 0.90/1.16          | ~ (l3_lattices @ sk_A)
% 0.90/1.16          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 0.90/1.16          | ~ (r3_lattices @ sk_A @ (sk_D_3 @ X0 @ sk_B @ sk_A) @ sk_B)
% 0.90/1.16          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.90/1.16      inference('sup-', [status(thm)], ['115', '116'])).
% 0.90/1.16  thf('118', plain, ((v10_lattices @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('119', plain, ((v4_lattice3 @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('120', plain, ((l3_lattices @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('121', plain,
% 0.90/1.16      (![X0 : $i]:
% 0.90/1.16         ((v2_struct_0 @ sk_A)
% 0.90/1.16          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 0.90/1.16          | ~ (r3_lattices @ sk_A @ (sk_D_3 @ X0 @ sk_B @ sk_A) @ sk_B)
% 0.90/1.16          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.90/1.16      inference('demod', [status(thm)], ['117', '118', '119', '120'])).
% 0.90/1.16  thf('122', plain,
% 0.90/1.16      ((~ (r3_lattice3 @ sk_A @ sk_B @ sk_C)
% 0.90/1.16        | ((sk_B) = (k16_lattice3 @ sk_A @ sk_C))
% 0.90/1.16        | (v2_struct_0 @ sk_A))),
% 0.90/1.16      inference('sup-', [status(thm)], ['114', '121'])).
% 0.90/1.16  thf('123', plain, ((r3_lattice3 @ sk_A @ sk_B @ sk_C)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('124', plain,
% 0.90/1.16      ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C)) | (v2_struct_0 @ sk_A))),
% 0.90/1.16      inference('demod', [status(thm)], ['122', '123'])).
% 0.90/1.16  thf('125', plain, (((k16_lattice3 @ sk_A @ sk_C) != (sk_B))),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('126', plain, ((v2_struct_0 @ sk_A)),
% 0.90/1.16      inference('simplify_reflect-', [status(thm)], ['124', '125'])).
% 0.90/1.16  thf('127', plain, ($false), inference('demod', [status(thm)], ['0', '126'])).
% 0.90/1.16  
% 0.90/1.16  % SZS output end Refutation
% 0.90/1.16  
% 0.90/1.16  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
