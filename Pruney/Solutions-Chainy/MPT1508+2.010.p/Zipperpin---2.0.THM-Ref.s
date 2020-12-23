%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eXliiNOrj2

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:32 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :  186 ( 539 expanded)
%              Number of leaves         :   28 ( 160 expanded)
%              Depth                    :   33
%              Number of atoms          : 2071 (9200 expanded)
%              Number of equality atoms :   52 ( 286 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r3_lattice3_type,type,(
    r3_lattice3: $i > $i > $i > $o )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i > $i )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(r4_lattice3_type,type,(
    r4_lattice3: $i > $i > $i > $o )).

thf(a_2_1_lattice3_type,type,(
    a_2_1_lattice3: $i > $i > $i )).

thf(sk_D_5_type,type,(
    sk_D_5: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X28 ) )
      | ( r3_lattices @ X28 @ X27 @ ( k15_lattice3 @ X28 @ X29 ) )
      | ~ ( r2_hidden @ X27 @ X29 )
      | ~ ( l3_lattices @ X28 )
      | ~ ( v4_lattice3 @ X28 )
      | ~ ( v10_lattices @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t38_lattice3])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r2_hidden @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ( r3_lattices @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
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
      | ~ ( r2_hidden @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ( r3_lattices @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ ( k15_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    r3_lattices @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['34','43'])).

thf('45',plain,(
    r3_lattice3 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ~ ( r3_lattice3 @ X14 @ X17 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X14 ) )
      | ( r2_hidden @ X17 @ ( a_2_1_lattice3 @ X14 @ X15 ) )
      | ( v2_struct_0 @ X14 )
      | ~ ( l3_lattices @ X14 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    r2_hidden @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['45','52'])).

thf('54',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
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

thf('57',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ( r2_hidden @ ( sk_D_1 @ X9 @ X5 @ X6 ) @ X9 )
      | ( r4_lattice3 @ X6 @ X5 @ X9 )
      | ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( l3_lattices @ X14 )
      | ( v2_struct_0 @ X14 )
      | ( X16
        = ( sk_D_3 @ X15 @ X14 @ X16 ) )
      | ~ ( r2_hidden @ X16 @ ( a_2_1_lattice3 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_lattice3])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ X1 @ X0 ) )
      | ( ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A )
        = ( sk_D_3 @ X0 @ X1 @ ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('66',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( l3_lattices @ X14 )
      | ( v2_struct_0 @ X14 )
      | ( r3_lattice3 @ X14 @ ( sk_D_3 @ X15 @ X14 @ X16 ) @ X15 )
      | ~ ( r2_hidden @ X16 @ ( a_2_1_lattice3 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_lattice3])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ X1 @ X0 ) )
      | ( r3_lattice3 @ X1 @ ( sk_D_3 @ X0 @ X1 @ ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A ) ) @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ X1 @ ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A ) @ X0 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ X1 @ X0 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( r3_lattice3 @ X1 @ ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X9 @ X5 @ X6 ) @ ( u1_struct_0 @ X6 ) )
      | ( r4_lattice3 @ X6 @ X5 @ X9 )
      | ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['74','75'])).

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

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r3_lattice3 @ X1 @ X0 @ X2 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r1_lattices @ X1 @ X0 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X1 )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X1 )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X2 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ X0 ) @ sk_B @ sk_A ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['69','80'])).

thf('82',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ X0 ) @ sk_B @ sk_A ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ X0 ) @ sk_B @ sk_A ) @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ X0 ) @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','84'])).

thf('86',plain,
    ( ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_B @ sk_A ) @ sk_B )
    | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['54','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ~ ( r1_lattices @ X6 @ ( sk_D_1 @ X9 @ X5 @ X6 ) @ X5 )
      | ( r4_lattice3 @ X6 @ X5 @ X9 )
      | ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['86','93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
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

thf('98',plain,(
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

thf('99',plain,(
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
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r4_lattice3 @ sk_A @ ( sk_D_2 @ sk_B @ X0 @ sk_A ) @ X0 )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['97','99'])).

thf('101',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r4_lattice3 @ sk_A @ ( sk_D_2 @ sk_B @ X0 @ sk_A ) @ X0 )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['100','101','102','103'])).

thf('105',plain,
    ( ( sk_B
      = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
    | ( r4_lattice3 @ sk_A @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['96','104'])).

thf('106',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( r4_lattice3 @ sk_A @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
    | ( sk_B
      = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,(
    r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('109',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
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

thf('111',plain,(
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
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_B @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['109','111'])).

thf('113',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_B @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['112','113','114','115'])).

thf('117',plain,
    ( ( sk_B
      = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
    | ( m1_subset_1 @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['108','116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( m1_subset_1 @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ~ ( r4_lattice3 @ X6 @ X5 @ X7 )
      | ~ ( r2_hidden @ X8 @ X7 )
      | ( r1_lattices @ X6 @ X8 @ X5 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ X0 @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r4_lattice3 @ sk_A @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ X0 @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r4_lattice3 @ sk_A @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) @ X1 ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
      | ( r1_lattices @ sk_A @ X0 @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['107','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ X0 @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,
    ( ( sk_B
      = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
    | ( r1_lattices @ sk_A @ sk_B @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','125'])).

thf('127',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( sk_B
      = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
    | ( r1_lattices @ sk_A @ sk_B @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( r1_lattices @ sk_A @ sk_B @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) )
    | ( sk_B
      = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['128','129'])).

thf('131',plain,(
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

thf('132',plain,(
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
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,
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
    inference('sup-',[status(thm)],['130','132'])).

thf('134',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('139',plain,
    ( ( sk_B
      = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['133','134','135','136','137','138'])).

thf('140',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( sk_B
    = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['140','141'])).

thf('143',plain,(
    r3_lattices @ sk_A @ ( sk_D_5 @ sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['44','142'])).

thf('144',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
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

thf('146',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( sk_B
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattices @ sk_A @ ( sk_D_5 @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

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
      | ( sk_B
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattices @ sk_A @ ( sk_D_5 @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['146','147','148','149'])).

thf('151',plain,
    ( ~ ( r3_lattice3 @ sk_A @ sk_B @ sk_C )
    | ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['143','150'])).

thf('152',plain,(
    r3_lattice3 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    ( k16_lattice3 @ sk_A @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['153','154'])).

thf('156',plain,(
    $false ),
    inference(demod,[status(thm)],['0','155'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eXliiNOrj2
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:52:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.68/0.86  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.68/0.86  % Solved by: fo/fo7.sh
% 0.68/0.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.86  % done 361 iterations in 0.407s
% 0.68/0.86  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.68/0.86  % SZS output start Refutation
% 0.68/0.86  thf(sk_C_type, type, sk_C: $i).
% 0.68/0.86  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.68/0.86  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.68/0.86  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 0.68/0.86  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.68/0.86  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.86  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.68/0.86  thf(r3_lattice3_type, type, r3_lattice3: $i > $i > $i > $o).
% 0.68/0.86  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 0.68/0.86  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i > $i).
% 0.68/0.86  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.68/0.86  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 0.68/0.86  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 0.68/0.86  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.68/0.86  thf(r4_lattice3_type, type, r4_lattice3: $i > $i > $i > $o).
% 0.68/0.86  thf(a_2_1_lattice3_type, type, a_2_1_lattice3: $i > $i > $i).
% 0.68/0.86  thf(sk_D_5_type, type, sk_D_5: $i > $i > $i > $i).
% 0.68/0.86  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.68/0.86  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.86  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.68/0.86  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 0.68/0.86  thf(t42_lattice3, conjecture,
% 0.68/0.86    (![A:$i]:
% 0.68/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.68/0.86         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.68/0.86       ( ![B:$i]:
% 0.68/0.86         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.86           ( ![C:$i]:
% 0.68/0.86             ( ( ( r2_hidden @ B @ C ) & ( r3_lattice3 @ A @ B @ C ) ) =>
% 0.68/0.86               ( ( k16_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ))).
% 0.68/0.86  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.86    (~( ![A:$i]:
% 0.68/0.86        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.68/0.86            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.68/0.86          ( ![B:$i]:
% 0.68/0.86            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.86              ( ![C:$i]:
% 0.68/0.86                ( ( ( r2_hidden @ B @ C ) & ( r3_lattice3 @ A @ B @ C ) ) =>
% 0.68/0.86                  ( ( k16_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ) )),
% 0.68/0.86    inference('cnf.neg', [status(esa)], [t42_lattice3])).
% 0.68/0.86  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('1', plain, ((r3_lattice3 @ sk_A @ sk_B @ sk_C)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf(t34_lattice3, axiom,
% 0.68/0.86    (![A:$i]:
% 0.68/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.68/0.86         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.68/0.86       ( ![B:$i]:
% 0.68/0.86         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.86           ( ![C:$i]:
% 0.68/0.86             ( ( ( B ) = ( k16_lattice3 @ A @ C ) ) <=>
% 0.68/0.86               ( ( r3_lattice3 @ A @ B @ C ) & 
% 0.68/0.86                 ( ![D:$i]:
% 0.68/0.86                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.86                     ( ( r3_lattice3 @ A @ D @ C ) =>
% 0.68/0.86                       ( r3_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.68/0.86  thf('3', plain,
% 0.68/0.86      (![X22 : $i, X23 : $i, X26 : $i]:
% 0.68/0.86         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 0.68/0.86          | ~ (r3_lattice3 @ X23 @ X22 @ X26)
% 0.68/0.86          | (r3_lattice3 @ X23 @ (sk_D_5 @ X26 @ X22 @ X23) @ X26)
% 0.68/0.86          | ((X22) = (k16_lattice3 @ X23 @ X26))
% 0.68/0.86          | ~ (l3_lattices @ X23)
% 0.68/0.86          | ~ (v4_lattice3 @ X23)
% 0.68/0.86          | ~ (v10_lattices @ X23)
% 0.68/0.86          | (v2_struct_0 @ X23))),
% 0.68/0.86      inference('cnf', [status(esa)], [t34_lattice3])).
% 0.68/0.86  thf('4', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         ((v2_struct_0 @ sk_A)
% 0.68/0.86          | ~ (v10_lattices @ sk_A)
% 0.68/0.86          | ~ (v4_lattice3 @ sk_A)
% 0.68/0.86          | ~ (l3_lattices @ sk_A)
% 0.68/0.86          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 0.68/0.86          | (r3_lattice3 @ sk_A @ (sk_D_5 @ X0 @ sk_B @ sk_A) @ X0)
% 0.68/0.86          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.68/0.86      inference('sup-', [status(thm)], ['2', '3'])).
% 0.68/0.86  thf('5', plain, ((v10_lattices @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('6', plain, ((v4_lattice3 @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('7', plain, ((l3_lattices @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('8', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         ((v2_struct_0 @ sk_A)
% 0.68/0.86          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 0.68/0.86          | (r3_lattice3 @ sk_A @ (sk_D_5 @ X0 @ sk_B @ sk_A) @ X0)
% 0.68/0.86          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.68/0.86      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.68/0.86  thf('9', plain,
% 0.68/0.86      (((r3_lattice3 @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.68/0.86        | ((sk_B) = (k16_lattice3 @ sk_A @ sk_C))
% 0.68/0.86        | (v2_struct_0 @ sk_A))),
% 0.68/0.86      inference('sup-', [status(thm)], ['1', '8'])).
% 0.68/0.86  thf('10', plain, (((k16_lattice3 @ sk_A @ sk_C) != (sk_B))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('11', plain,
% 0.68/0.86      (((r3_lattice3 @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.68/0.86        | (v2_struct_0 @ sk_A))),
% 0.68/0.86      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.68/0.86  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('13', plain,
% 0.68/0.86      ((r3_lattice3 @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ sk_C)),
% 0.68/0.86      inference('clc', [status(thm)], ['11', '12'])).
% 0.68/0.86  thf('14', plain, ((r3_lattice3 @ sk_A @ sk_B @ sk_C)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('15', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('16', plain,
% 0.68/0.86      (![X22 : $i, X23 : $i, X26 : $i]:
% 0.68/0.86         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 0.68/0.86          | ~ (r3_lattice3 @ X23 @ X22 @ X26)
% 0.68/0.86          | (m1_subset_1 @ (sk_D_5 @ X26 @ X22 @ X23) @ (u1_struct_0 @ X23))
% 0.68/0.86          | ((X22) = (k16_lattice3 @ X23 @ X26))
% 0.68/0.86          | ~ (l3_lattices @ X23)
% 0.68/0.86          | ~ (v4_lattice3 @ X23)
% 0.68/0.86          | ~ (v10_lattices @ X23)
% 0.68/0.86          | (v2_struct_0 @ X23))),
% 0.68/0.86      inference('cnf', [status(esa)], [t34_lattice3])).
% 0.68/0.86  thf('17', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         ((v2_struct_0 @ sk_A)
% 0.68/0.86          | ~ (v10_lattices @ sk_A)
% 0.68/0.86          | ~ (v4_lattice3 @ sk_A)
% 0.68/0.86          | ~ (l3_lattices @ sk_A)
% 0.68/0.86          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 0.68/0.86          | (m1_subset_1 @ (sk_D_5 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.68/0.86          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.68/0.86      inference('sup-', [status(thm)], ['15', '16'])).
% 0.68/0.86  thf('18', plain, ((v10_lattices @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('19', plain, ((v4_lattice3 @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('20', plain, ((l3_lattices @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('21', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         ((v2_struct_0 @ sk_A)
% 0.68/0.86          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 0.68/0.86          | (m1_subset_1 @ (sk_D_5 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.68/0.86          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.68/0.86      inference('demod', [status(thm)], ['17', '18', '19', '20'])).
% 0.68/0.86  thf('22', plain,
% 0.68/0.86      (((m1_subset_1 @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.68/0.86        | ((sk_B) = (k16_lattice3 @ sk_A @ sk_C))
% 0.68/0.86        | (v2_struct_0 @ sk_A))),
% 0.68/0.86      inference('sup-', [status(thm)], ['14', '21'])).
% 0.68/0.86  thf('23', plain, (((k16_lattice3 @ sk_A @ sk_C) != (sk_B))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('24', plain,
% 0.68/0.86      (((m1_subset_1 @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.68/0.86        | (v2_struct_0 @ sk_A))),
% 0.68/0.86      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.68/0.86  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('26', plain,
% 0.68/0.86      ((m1_subset_1 @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.68/0.86      inference('clc', [status(thm)], ['24', '25'])).
% 0.68/0.86  thf(fraenkel_a_2_1_lattice3, axiom,
% 0.68/0.86    (![A:$i,B:$i,C:$i]:
% 0.68/0.86     ( ( ( ~( v2_struct_0 @ B ) ) & ( l3_lattices @ B ) ) =>
% 0.68/0.86       ( ( r2_hidden @ A @ ( a_2_1_lattice3 @ B @ C ) ) <=>
% 0.68/0.86         ( ?[D:$i]:
% 0.68/0.86           ( ( r3_lattice3 @ B @ D @ C ) & ( ( A ) = ( D ) ) & 
% 0.68/0.86             ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.68/0.86  thf('27', plain,
% 0.68/0.86      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.68/0.86         (~ (l3_lattices @ X14)
% 0.68/0.86          | (v2_struct_0 @ X14)
% 0.68/0.86          | (r2_hidden @ X16 @ (a_2_1_lattice3 @ X14 @ X15))
% 0.68/0.86          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X14))
% 0.68/0.86          | ((X16) != (X17))
% 0.68/0.86          | ~ (r3_lattice3 @ X14 @ X17 @ X15))),
% 0.68/0.86      inference('cnf', [status(esa)], [fraenkel_a_2_1_lattice3])).
% 0.68/0.86  thf('28', plain,
% 0.68/0.86      (![X14 : $i, X15 : $i, X17 : $i]:
% 0.68/0.86         (~ (r3_lattice3 @ X14 @ X17 @ X15)
% 0.68/0.86          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X14))
% 0.68/0.86          | (r2_hidden @ X17 @ (a_2_1_lattice3 @ X14 @ X15))
% 0.68/0.86          | (v2_struct_0 @ X14)
% 0.68/0.86          | ~ (l3_lattices @ X14))),
% 0.68/0.86      inference('simplify', [status(thm)], ['27'])).
% 0.68/0.86  thf('29', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         (~ (l3_lattices @ sk_A)
% 0.68/0.86          | (v2_struct_0 @ sk_A)
% 0.68/0.86          | (r2_hidden @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ 
% 0.68/0.86             (a_2_1_lattice3 @ sk_A @ X0))
% 0.68/0.86          | ~ (r3_lattice3 @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ X0))),
% 0.68/0.86      inference('sup-', [status(thm)], ['26', '28'])).
% 0.68/0.86  thf('30', plain, ((l3_lattices @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('31', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         ((v2_struct_0 @ sk_A)
% 0.68/0.86          | (r2_hidden @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ 
% 0.68/0.86             (a_2_1_lattice3 @ sk_A @ X0))
% 0.68/0.86          | ~ (r3_lattice3 @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ X0))),
% 0.68/0.86      inference('demod', [status(thm)], ['29', '30'])).
% 0.68/0.86  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('33', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         (~ (r3_lattice3 @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ X0)
% 0.68/0.86          | (r2_hidden @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ 
% 0.68/0.86             (a_2_1_lattice3 @ sk_A @ X0)))),
% 0.68/0.86      inference('clc', [status(thm)], ['31', '32'])).
% 0.68/0.86  thf('34', plain,
% 0.68/0.86      ((r2_hidden @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ 
% 0.68/0.86        (a_2_1_lattice3 @ sk_A @ sk_C))),
% 0.68/0.86      inference('sup-', [status(thm)], ['13', '33'])).
% 0.68/0.86  thf('35', plain,
% 0.68/0.86      ((m1_subset_1 @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.68/0.86      inference('clc', [status(thm)], ['24', '25'])).
% 0.68/0.86  thf(t38_lattice3, axiom,
% 0.68/0.86    (![A:$i]:
% 0.68/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.68/0.86         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.68/0.86       ( ![B:$i]:
% 0.68/0.86         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.86           ( ![C:$i]:
% 0.68/0.86             ( ( r2_hidden @ B @ C ) =>
% 0.68/0.86               ( ( r3_lattices @ A @ B @ ( k15_lattice3 @ A @ C ) ) & 
% 0.68/0.86                 ( r3_lattices @ A @ ( k16_lattice3 @ A @ C ) @ B ) ) ) ) ) ) ))).
% 0.68/0.86  thf('36', plain,
% 0.68/0.86      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.68/0.86         (~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X28))
% 0.68/0.86          | (r3_lattices @ X28 @ X27 @ (k15_lattice3 @ X28 @ X29))
% 0.68/0.86          | ~ (r2_hidden @ X27 @ X29)
% 0.68/0.86          | ~ (l3_lattices @ X28)
% 0.68/0.86          | ~ (v4_lattice3 @ X28)
% 0.68/0.86          | ~ (v10_lattices @ X28)
% 0.68/0.86          | (v2_struct_0 @ X28))),
% 0.68/0.86      inference('cnf', [status(esa)], [t38_lattice3])).
% 0.68/0.86  thf('37', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         ((v2_struct_0 @ sk_A)
% 0.68/0.86          | ~ (v10_lattices @ sk_A)
% 0.68/0.86          | ~ (v4_lattice3 @ sk_A)
% 0.68/0.86          | ~ (l3_lattices @ sk_A)
% 0.68/0.86          | ~ (r2_hidden @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ X0)
% 0.68/0.86          | (r3_lattices @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ 
% 0.68/0.86             (k15_lattice3 @ sk_A @ X0)))),
% 0.68/0.86      inference('sup-', [status(thm)], ['35', '36'])).
% 0.68/0.86  thf('38', plain, ((v10_lattices @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('39', plain, ((v4_lattice3 @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('40', plain, ((l3_lattices @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('41', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         ((v2_struct_0 @ sk_A)
% 0.68/0.86          | ~ (r2_hidden @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ X0)
% 0.68/0.86          | (r3_lattices @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ 
% 0.68/0.86             (k15_lattice3 @ sk_A @ X0)))),
% 0.68/0.86      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 0.68/0.86  thf('42', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('43', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         ((r3_lattices @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ 
% 0.68/0.86           (k15_lattice3 @ sk_A @ X0))
% 0.68/0.86          | ~ (r2_hidden @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ X0))),
% 0.68/0.86      inference('clc', [status(thm)], ['41', '42'])).
% 0.68/0.86  thf('44', plain,
% 0.68/0.86      ((r3_lattices @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ 
% 0.68/0.86        (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))),
% 0.68/0.86      inference('sup-', [status(thm)], ['34', '43'])).
% 0.68/0.86  thf('45', plain, ((r3_lattice3 @ sk_A @ sk_B @ sk_C)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('46', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('47', plain,
% 0.68/0.86      (![X14 : $i, X15 : $i, X17 : $i]:
% 0.68/0.86         (~ (r3_lattice3 @ X14 @ X17 @ X15)
% 0.68/0.86          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X14))
% 0.68/0.86          | (r2_hidden @ X17 @ (a_2_1_lattice3 @ X14 @ X15))
% 0.68/0.86          | (v2_struct_0 @ X14)
% 0.68/0.86          | ~ (l3_lattices @ X14))),
% 0.68/0.86      inference('simplify', [status(thm)], ['27'])).
% 0.68/0.86  thf('48', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         (~ (l3_lattices @ sk_A)
% 0.68/0.86          | (v2_struct_0 @ sk_A)
% 0.68/0.86          | (r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 0.68/0.86          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.68/0.86      inference('sup-', [status(thm)], ['46', '47'])).
% 0.68/0.86  thf('49', plain, ((l3_lattices @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('50', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         ((v2_struct_0 @ sk_A)
% 0.68/0.86          | (r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 0.68/0.86          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.68/0.86      inference('demod', [status(thm)], ['48', '49'])).
% 0.68/0.86  thf('51', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('52', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         (~ (r3_lattice3 @ sk_A @ sk_B @ X0)
% 0.68/0.86          | (r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0)))),
% 0.68/0.86      inference('clc', [status(thm)], ['50', '51'])).
% 0.68/0.86  thf('53', plain, ((r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))),
% 0.68/0.86      inference('sup-', [status(thm)], ['45', '52'])).
% 0.68/0.86  thf('54', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('55', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('56', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf(d17_lattice3, axiom,
% 0.68/0.86    (![A:$i]:
% 0.68/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.68/0.86       ( ![B:$i]:
% 0.68/0.86         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.86           ( ![C:$i]:
% 0.68/0.86             ( ( r4_lattice3 @ A @ B @ C ) <=>
% 0.68/0.86               ( ![D:$i]:
% 0.68/0.86                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.86                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ))).
% 0.68/0.86  thf('57', plain,
% 0.68/0.86      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.68/0.86         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 0.68/0.86          | (r2_hidden @ (sk_D_1 @ X9 @ X5 @ X6) @ X9)
% 0.68/0.86          | (r4_lattice3 @ X6 @ X5 @ X9)
% 0.68/0.86          | ~ (l3_lattices @ X6)
% 0.68/0.86          | (v2_struct_0 @ X6))),
% 0.68/0.86      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.68/0.86  thf('58', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         ((v2_struct_0 @ sk_A)
% 0.68/0.86          | ~ (l3_lattices @ sk_A)
% 0.68/0.86          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.68/0.86          | (r2_hidden @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0))),
% 0.68/0.86      inference('sup-', [status(thm)], ['56', '57'])).
% 0.68/0.86  thf('59', plain, ((l3_lattices @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('60', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         ((v2_struct_0 @ sk_A)
% 0.68/0.86          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.68/0.86          | (r2_hidden @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0))),
% 0.68/0.86      inference('demod', [status(thm)], ['58', '59'])).
% 0.68/0.86  thf('61', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('62', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         ((r2_hidden @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0)
% 0.68/0.86          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 0.68/0.86      inference('clc', [status(thm)], ['60', '61'])).
% 0.68/0.86  thf('63', plain,
% 0.68/0.86      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.68/0.86         (~ (l3_lattices @ X14)
% 0.68/0.86          | (v2_struct_0 @ X14)
% 0.68/0.86          | ((X16) = (sk_D_3 @ X15 @ X14 @ X16))
% 0.68/0.86          | ~ (r2_hidden @ X16 @ (a_2_1_lattice3 @ X14 @ X15)))),
% 0.68/0.86      inference('cnf', [status(esa)], [fraenkel_a_2_1_lattice3])).
% 0.68/0.86  thf('64', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]:
% 0.68/0.86         ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0))
% 0.68/0.86          | ((sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A)
% 0.68/0.86              = (sk_D_3 @ X0 @ X1 @ 
% 0.68/0.86                 (sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A)))
% 0.68/0.86          | (v2_struct_0 @ X1)
% 0.68/0.86          | ~ (l3_lattices @ X1))),
% 0.68/0.86      inference('sup-', [status(thm)], ['62', '63'])).
% 0.68/0.86  thf('65', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         ((r2_hidden @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0)
% 0.68/0.86          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 0.68/0.86      inference('clc', [status(thm)], ['60', '61'])).
% 0.68/0.86  thf('66', plain,
% 0.68/0.86      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.68/0.86         (~ (l3_lattices @ X14)
% 0.68/0.86          | (v2_struct_0 @ X14)
% 0.68/0.86          | (r3_lattice3 @ X14 @ (sk_D_3 @ X15 @ X14 @ X16) @ X15)
% 0.68/0.86          | ~ (r2_hidden @ X16 @ (a_2_1_lattice3 @ X14 @ X15)))),
% 0.68/0.86      inference('cnf', [status(esa)], [fraenkel_a_2_1_lattice3])).
% 0.68/0.86  thf('67', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]:
% 0.68/0.86         ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0))
% 0.68/0.86          | (r3_lattice3 @ X1 @ 
% 0.68/0.86             (sk_D_3 @ X0 @ X1 @ 
% 0.68/0.86              (sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A)) @ 
% 0.68/0.86             X0)
% 0.68/0.86          | (v2_struct_0 @ X1)
% 0.68/0.86          | ~ (l3_lattices @ X1))),
% 0.68/0.86      inference('sup-', [status(thm)], ['65', '66'])).
% 0.68/0.86  thf('68', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]:
% 0.68/0.86         ((r3_lattice3 @ X1 @ 
% 0.68/0.86           (sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A) @ X0)
% 0.68/0.86          | ~ (l3_lattices @ X1)
% 0.68/0.86          | (v2_struct_0 @ X1)
% 0.68/0.86          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0))
% 0.68/0.86          | ~ (l3_lattices @ X1)
% 0.68/0.86          | (v2_struct_0 @ X1)
% 0.68/0.86          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0)))),
% 0.68/0.86      inference('sup+', [status(thm)], ['64', '67'])).
% 0.68/0.86  thf('69', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]:
% 0.68/0.86         ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0))
% 0.68/0.86          | (v2_struct_0 @ X1)
% 0.68/0.86          | ~ (l3_lattices @ X1)
% 0.68/0.86          | (r3_lattice3 @ X1 @ 
% 0.68/0.86             (sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A) @ X0))),
% 0.68/0.86      inference('simplify', [status(thm)], ['68'])).
% 0.68/0.86  thf('70', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('71', plain,
% 0.68/0.86      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.68/0.86         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 0.68/0.86          | (m1_subset_1 @ (sk_D_1 @ X9 @ X5 @ X6) @ (u1_struct_0 @ X6))
% 0.68/0.86          | (r4_lattice3 @ X6 @ X5 @ X9)
% 0.68/0.86          | ~ (l3_lattices @ X6)
% 0.68/0.86          | (v2_struct_0 @ X6))),
% 0.68/0.86      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.68/0.86  thf('72', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         ((v2_struct_0 @ sk_A)
% 0.68/0.86          | ~ (l3_lattices @ sk_A)
% 0.68/0.86          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.68/0.86          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.68/0.86      inference('sup-', [status(thm)], ['70', '71'])).
% 0.68/0.86  thf('73', plain, ((l3_lattices @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('74', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         ((v2_struct_0 @ sk_A)
% 0.68/0.86          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.68/0.86          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.68/0.86      inference('demod', [status(thm)], ['72', '73'])).
% 0.68/0.86  thf('75', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('76', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         ((m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.68/0.86          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 0.68/0.86      inference('clc', [status(thm)], ['74', '75'])).
% 0.68/0.86  thf(d16_lattice3, axiom,
% 0.68/0.86    (![A:$i]:
% 0.68/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.68/0.86       ( ![B:$i]:
% 0.68/0.86         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.86           ( ![C:$i]:
% 0.68/0.86             ( ( r3_lattice3 @ A @ B @ C ) <=>
% 0.68/0.86               ( ![D:$i]:
% 0.68/0.86                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.86                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 0.68/0.86  thf('77', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.86         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.68/0.86          | ~ (r3_lattice3 @ X1 @ X0 @ X2)
% 0.68/0.86          | ~ (r2_hidden @ X3 @ X2)
% 0.68/0.86          | (r1_lattices @ X1 @ X0 @ X3)
% 0.68/0.86          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.68/0.86          | ~ (l3_lattices @ X1)
% 0.68/0.86          | (v2_struct_0 @ X1))),
% 0.68/0.86      inference('cnf', [status(esa)], [d16_lattice3])).
% 0.68/0.86  thf('78', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.86         ((r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.68/0.86          | (v2_struct_0 @ sk_A)
% 0.68/0.86          | ~ (l3_lattices @ sk_A)
% 0.68/0.86          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.68/0.86          | (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X1)
% 0.68/0.86          | ~ (r2_hidden @ X1 @ X2)
% 0.68/0.86          | ~ (r3_lattice3 @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X2))),
% 0.68/0.86      inference('sup-', [status(thm)], ['76', '77'])).
% 0.68/0.86  thf('79', plain, ((l3_lattices @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('80', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.86         ((r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.68/0.86          | (v2_struct_0 @ sk_A)
% 0.68/0.86          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.68/0.86          | (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X1)
% 0.68/0.86          | ~ (r2_hidden @ X1 @ X2)
% 0.68/0.86          | ~ (r3_lattice3 @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X2))),
% 0.68/0.86      inference('demod', [status(thm)], ['78', '79'])).
% 0.68/0.86  thf('81', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]:
% 0.68/0.86         (~ (l3_lattices @ sk_A)
% 0.68/0.86          | (v2_struct_0 @ sk_A)
% 0.68/0.86          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 0.68/0.86          | ~ (r2_hidden @ X1 @ X0)
% 0.68/0.86          | (r1_lattices @ sk_A @ 
% 0.68/0.86             (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ X0) @ sk_B @ sk_A) @ X1)
% 0.68/0.86          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.68/0.87          | (v2_struct_0 @ sk_A)
% 0.68/0.87          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['69', '80'])).
% 0.68/0.87  thf('82', plain, ((l3_lattices @ sk_A)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('83', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]:
% 0.68/0.87         ((v2_struct_0 @ sk_A)
% 0.68/0.87          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 0.68/0.87          | ~ (r2_hidden @ X1 @ X0)
% 0.68/0.87          | (r1_lattices @ sk_A @ 
% 0.68/0.87             (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ X0) @ sk_B @ sk_A) @ X1)
% 0.68/0.87          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.68/0.87          | (v2_struct_0 @ sk_A)
% 0.68/0.87          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0)))),
% 0.68/0.87      inference('demod', [status(thm)], ['81', '82'])).
% 0.68/0.87  thf('84', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]:
% 0.68/0.87         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.68/0.87          | (r1_lattices @ sk_A @ 
% 0.68/0.87             (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ X0) @ sk_B @ sk_A) @ X1)
% 0.68/0.87          | ~ (r2_hidden @ X1 @ X0)
% 0.68/0.87          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 0.68/0.87          | (v2_struct_0 @ sk_A))),
% 0.68/0.87      inference('simplify', [status(thm)], ['83'])).
% 0.68/0.87  thf('85', plain,
% 0.68/0.87      (![X0 : $i]:
% 0.68/0.87         ((v2_struct_0 @ sk_A)
% 0.68/0.87          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 0.68/0.87          | ~ (r2_hidden @ sk_B @ X0)
% 0.68/0.87          | (r1_lattices @ sk_A @ 
% 0.68/0.87             (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ X0) @ sk_B @ sk_A) @ sk_B))),
% 0.68/0.87      inference('sup-', [status(thm)], ['55', '84'])).
% 0.68/0.87  thf('86', plain,
% 0.68/0.87      (((r1_lattices @ sk_A @ 
% 0.68/0.87         (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_B @ sk_A) @ sk_B)
% 0.68/0.87        | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))
% 0.68/0.87        | (v2_struct_0 @ sk_A))),
% 0.68/0.87      inference('sup-', [status(thm)], ['54', '85'])).
% 0.68/0.87  thf('87', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('88', plain,
% 0.68/0.87      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.68/0.87         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 0.68/0.87          | ~ (r1_lattices @ X6 @ (sk_D_1 @ X9 @ X5 @ X6) @ X5)
% 0.68/0.87          | (r4_lattice3 @ X6 @ X5 @ X9)
% 0.68/0.87          | ~ (l3_lattices @ X6)
% 0.68/0.87          | (v2_struct_0 @ X6))),
% 0.68/0.87      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.68/0.87  thf('89', plain,
% 0.68/0.87      (![X0 : $i]:
% 0.68/0.87         ((v2_struct_0 @ sk_A)
% 0.68/0.87          | ~ (l3_lattices @ sk_A)
% 0.68/0.87          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.68/0.87          | ~ (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_B))),
% 0.68/0.87      inference('sup-', [status(thm)], ['87', '88'])).
% 0.68/0.87  thf('90', plain, ((l3_lattices @ sk_A)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('91', plain,
% 0.68/0.87      (![X0 : $i]:
% 0.68/0.87         ((v2_struct_0 @ sk_A)
% 0.68/0.87          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.68/0.87          | ~ (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_B))),
% 0.68/0.87      inference('demod', [status(thm)], ['89', '90'])).
% 0.68/0.87  thf('92', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('93', plain,
% 0.68/0.87      (![X0 : $i]:
% 0.68/0.87         (~ (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_B)
% 0.68/0.87          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 0.68/0.87      inference('clc', [status(thm)], ['91', '92'])).
% 0.68/0.87  thf('94', plain,
% 0.68/0.87      (((v2_struct_0 @ sk_A)
% 0.68/0.87        | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C)))),
% 0.68/0.87      inference('clc', [status(thm)], ['86', '93'])).
% 0.68/0.87  thf('95', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('96', plain,
% 0.68/0.87      ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))),
% 0.68/0.87      inference('clc', [status(thm)], ['94', '95'])).
% 0.68/0.87  thf('97', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf(d21_lattice3, axiom,
% 0.68/0.87    (![A:$i]:
% 0.68/0.87     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.68/0.87       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.68/0.87           ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.68/0.87         ( ![B:$i,C:$i]:
% 0.68/0.87           ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.87             ( ( ( C ) = ( k15_lattice3 @ A @ B ) ) <=>
% 0.68/0.87               ( ( r4_lattice3 @ A @ C @ B ) & 
% 0.68/0.87                 ( ![D:$i]:
% 0.68/0.87                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.87                     ( ( r4_lattice3 @ A @ D @ B ) =>
% 0.68/0.87                       ( r1_lattices @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.68/0.87  thf('98', plain,
% 0.68/0.87      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.68/0.87         ((v2_struct_0 @ X10)
% 0.68/0.87          | ~ (v10_lattices @ X10)
% 0.68/0.87          | ~ (v4_lattice3 @ X10)
% 0.68/0.87          | ~ (l3_lattices @ X10)
% 0.68/0.87          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.68/0.87          | ~ (r4_lattice3 @ X10 @ X11 @ X12)
% 0.68/0.87          | (r4_lattice3 @ X10 @ (sk_D_2 @ X11 @ X12 @ X10) @ X12)
% 0.68/0.87          | ((X11) = (k15_lattice3 @ X10 @ X12))
% 0.68/0.87          | ~ (l3_lattices @ X10)
% 0.68/0.87          | (v2_struct_0 @ X10))),
% 0.68/0.87      inference('cnf', [status(esa)], [d21_lattice3])).
% 0.68/0.87  thf('99', plain,
% 0.68/0.87      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.68/0.87         (((X11) = (k15_lattice3 @ X10 @ X12))
% 0.68/0.87          | (r4_lattice3 @ X10 @ (sk_D_2 @ X11 @ X12 @ X10) @ X12)
% 0.68/0.87          | ~ (r4_lattice3 @ X10 @ X11 @ X12)
% 0.68/0.87          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.68/0.87          | ~ (l3_lattices @ X10)
% 0.68/0.87          | ~ (v4_lattice3 @ X10)
% 0.68/0.87          | ~ (v10_lattices @ X10)
% 0.68/0.87          | (v2_struct_0 @ X10))),
% 0.68/0.87      inference('simplify', [status(thm)], ['98'])).
% 0.68/0.87  thf('100', plain,
% 0.68/0.87      (![X0 : $i]:
% 0.68/0.87         ((v2_struct_0 @ sk_A)
% 0.68/0.87          | ~ (v10_lattices @ sk_A)
% 0.68/0.87          | ~ (v4_lattice3 @ sk_A)
% 0.68/0.87          | ~ (l3_lattices @ sk_A)
% 0.68/0.87          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.68/0.87          | (r4_lattice3 @ sk_A @ (sk_D_2 @ sk_B @ X0 @ sk_A) @ X0)
% 0.68/0.87          | ((sk_B) = (k15_lattice3 @ sk_A @ X0)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['97', '99'])).
% 0.68/0.87  thf('101', plain, ((v10_lattices @ sk_A)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('102', plain, ((v4_lattice3 @ sk_A)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('103', plain, ((l3_lattices @ sk_A)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('104', plain,
% 0.68/0.87      (![X0 : $i]:
% 0.68/0.87         ((v2_struct_0 @ sk_A)
% 0.68/0.87          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.68/0.87          | (r4_lattice3 @ sk_A @ (sk_D_2 @ sk_B @ X0 @ sk_A) @ X0)
% 0.68/0.87          | ((sk_B) = (k15_lattice3 @ sk_A @ X0)))),
% 0.68/0.87      inference('demod', [status(thm)], ['100', '101', '102', '103'])).
% 0.68/0.87  thf('105', plain,
% 0.68/0.87      ((((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 0.68/0.87        | (r4_lattice3 @ sk_A @ 
% 0.68/0.87           (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A) @ 
% 0.68/0.87           (a_2_1_lattice3 @ sk_A @ sk_C))
% 0.68/0.87        | (v2_struct_0 @ sk_A))),
% 0.68/0.87      inference('sup-', [status(thm)], ['96', '104'])).
% 0.68/0.87  thf('106', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('107', plain,
% 0.68/0.87      (((r4_lattice3 @ sk_A @ 
% 0.68/0.87         (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A) @ 
% 0.68/0.87         (a_2_1_lattice3 @ sk_A @ sk_C))
% 0.68/0.87        | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 0.68/0.87      inference('clc', [status(thm)], ['105', '106'])).
% 0.68/0.87  thf('108', plain,
% 0.68/0.87      ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))),
% 0.68/0.87      inference('clc', [status(thm)], ['94', '95'])).
% 0.68/0.87  thf('109', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('110', plain,
% 0.68/0.87      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.68/0.87         ((v2_struct_0 @ X10)
% 0.68/0.87          | ~ (v10_lattices @ X10)
% 0.68/0.87          | ~ (v4_lattice3 @ X10)
% 0.68/0.87          | ~ (l3_lattices @ X10)
% 0.68/0.87          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.68/0.87          | ~ (r4_lattice3 @ X10 @ X11 @ X12)
% 0.68/0.87          | (m1_subset_1 @ (sk_D_2 @ X11 @ X12 @ X10) @ (u1_struct_0 @ X10))
% 0.68/0.87          | ((X11) = (k15_lattice3 @ X10 @ X12))
% 0.68/0.87          | ~ (l3_lattices @ X10)
% 0.68/0.87          | (v2_struct_0 @ X10))),
% 0.68/0.87      inference('cnf', [status(esa)], [d21_lattice3])).
% 0.68/0.87  thf('111', plain,
% 0.68/0.87      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.68/0.87         (((X11) = (k15_lattice3 @ X10 @ X12))
% 0.68/0.87          | (m1_subset_1 @ (sk_D_2 @ X11 @ X12 @ X10) @ (u1_struct_0 @ X10))
% 0.68/0.87          | ~ (r4_lattice3 @ X10 @ X11 @ X12)
% 0.68/0.87          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.68/0.87          | ~ (l3_lattices @ X10)
% 0.68/0.87          | ~ (v4_lattice3 @ X10)
% 0.68/0.87          | ~ (v10_lattices @ X10)
% 0.68/0.87          | (v2_struct_0 @ X10))),
% 0.68/0.87      inference('simplify', [status(thm)], ['110'])).
% 0.68/0.87  thf('112', plain,
% 0.68/0.87      (![X0 : $i]:
% 0.68/0.87         ((v2_struct_0 @ sk_A)
% 0.68/0.87          | ~ (v10_lattices @ sk_A)
% 0.68/0.87          | ~ (v4_lattice3 @ sk_A)
% 0.68/0.87          | ~ (l3_lattices @ sk_A)
% 0.68/0.87          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.68/0.87          | (m1_subset_1 @ (sk_D_2 @ sk_B @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.68/0.87          | ((sk_B) = (k15_lattice3 @ sk_A @ X0)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['109', '111'])).
% 0.68/0.87  thf('113', plain, ((v10_lattices @ sk_A)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('114', plain, ((v4_lattice3 @ sk_A)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('115', plain, ((l3_lattices @ sk_A)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('116', plain,
% 0.68/0.87      (![X0 : $i]:
% 0.68/0.87         ((v2_struct_0 @ sk_A)
% 0.68/0.87          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.68/0.87          | (m1_subset_1 @ (sk_D_2 @ sk_B @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.68/0.87          | ((sk_B) = (k15_lattice3 @ sk_A @ X0)))),
% 0.68/0.87      inference('demod', [status(thm)], ['112', '113', '114', '115'])).
% 0.68/0.87  thf('117', plain,
% 0.68/0.87      ((((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 0.68/0.87        | (m1_subset_1 @ 
% 0.68/0.87           (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A) @ 
% 0.68/0.87           (u1_struct_0 @ sk_A))
% 0.68/0.87        | (v2_struct_0 @ sk_A))),
% 0.68/0.87      inference('sup-', [status(thm)], ['108', '116'])).
% 0.68/0.87  thf('118', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('119', plain,
% 0.68/0.87      (((m1_subset_1 @ 
% 0.68/0.87         (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A) @ 
% 0.68/0.87         (u1_struct_0 @ sk_A))
% 0.68/0.87        | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 0.68/0.87      inference('clc', [status(thm)], ['117', '118'])).
% 0.68/0.87  thf('120', plain,
% 0.68/0.87      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.68/0.87         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 0.68/0.87          | ~ (r4_lattice3 @ X6 @ X5 @ X7)
% 0.68/0.87          | ~ (r2_hidden @ X8 @ X7)
% 0.68/0.87          | (r1_lattices @ X6 @ X8 @ X5)
% 0.68/0.87          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X6))
% 0.68/0.87          | ~ (l3_lattices @ X6)
% 0.68/0.87          | (v2_struct_0 @ X6))),
% 0.68/0.87      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.68/0.87  thf('121', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]:
% 0.68/0.87         (((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 0.68/0.87          | (v2_struct_0 @ sk_A)
% 0.68/0.87          | ~ (l3_lattices @ sk_A)
% 0.68/0.87          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.68/0.87          | (r1_lattices @ sk_A @ X0 @ 
% 0.68/0.87             (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A))
% 0.68/0.87          | ~ (r2_hidden @ X0 @ X1)
% 0.68/0.87          | ~ (r4_lattice3 @ sk_A @ 
% 0.68/0.87               (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A) @ X1))),
% 0.68/0.87      inference('sup-', [status(thm)], ['119', '120'])).
% 0.68/0.87  thf('122', plain, ((l3_lattices @ sk_A)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('123', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]:
% 0.68/0.87         (((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 0.68/0.87          | (v2_struct_0 @ sk_A)
% 0.68/0.87          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.68/0.87          | (r1_lattices @ sk_A @ X0 @ 
% 0.68/0.87             (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A))
% 0.68/0.87          | ~ (r2_hidden @ X0 @ X1)
% 0.68/0.87          | ~ (r4_lattice3 @ sk_A @ 
% 0.68/0.87               (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A) @ X1))),
% 0.68/0.87      inference('demod', [status(thm)], ['121', '122'])).
% 0.68/0.87  thf('124', plain,
% 0.68/0.87      (![X0 : $i]:
% 0.68/0.87         (((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 0.68/0.87          | ~ (r2_hidden @ X0 @ (a_2_1_lattice3 @ sk_A @ sk_C))
% 0.68/0.87          | (r1_lattices @ sk_A @ X0 @ 
% 0.68/0.87             (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A))
% 0.68/0.87          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.68/0.87          | (v2_struct_0 @ sk_A)
% 0.68/0.87          | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 0.68/0.87      inference('sup-', [status(thm)], ['107', '123'])).
% 0.68/0.87  thf('125', plain,
% 0.68/0.87      (![X0 : $i]:
% 0.68/0.87         ((v2_struct_0 @ sk_A)
% 0.68/0.87          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.68/0.87          | (r1_lattices @ sk_A @ X0 @ 
% 0.68/0.87             (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A))
% 0.68/0.87          | ~ (r2_hidden @ X0 @ (a_2_1_lattice3 @ sk_A @ sk_C))
% 0.68/0.87          | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 0.68/0.87      inference('simplify', [status(thm)], ['124'])).
% 0.68/0.87  thf('126', plain,
% 0.68/0.87      ((((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 0.68/0.87        | (r1_lattices @ sk_A @ sk_B @ 
% 0.68/0.87           (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A))
% 0.68/0.87        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.68/0.87        | (v2_struct_0 @ sk_A))),
% 0.68/0.87      inference('sup-', [status(thm)], ['53', '125'])).
% 0.68/0.87  thf('127', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('128', plain,
% 0.68/0.87      ((((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 0.68/0.87        | (r1_lattices @ sk_A @ sk_B @ 
% 0.68/0.87           (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A))
% 0.68/0.87        | (v2_struct_0 @ sk_A))),
% 0.68/0.87      inference('demod', [status(thm)], ['126', '127'])).
% 0.68/0.87  thf('129', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('130', plain,
% 0.68/0.87      (((r1_lattices @ sk_A @ sk_B @ 
% 0.68/0.87         (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A))
% 0.68/0.87        | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 0.68/0.87      inference('clc', [status(thm)], ['128', '129'])).
% 0.68/0.87  thf('131', plain,
% 0.68/0.87      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.68/0.87         ((v2_struct_0 @ X10)
% 0.68/0.87          | ~ (v10_lattices @ X10)
% 0.68/0.87          | ~ (v4_lattice3 @ X10)
% 0.68/0.87          | ~ (l3_lattices @ X10)
% 0.68/0.87          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.68/0.87          | ~ (r4_lattice3 @ X10 @ X11 @ X12)
% 0.68/0.87          | ~ (r1_lattices @ X10 @ X11 @ (sk_D_2 @ X11 @ X12 @ X10))
% 0.68/0.87          | ((X11) = (k15_lattice3 @ X10 @ X12))
% 0.68/0.87          | ~ (l3_lattices @ X10)
% 0.68/0.87          | (v2_struct_0 @ X10))),
% 0.68/0.87      inference('cnf', [status(esa)], [d21_lattice3])).
% 0.68/0.87  thf('132', plain,
% 0.68/0.87      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.68/0.87         (((X11) = (k15_lattice3 @ X10 @ X12))
% 0.68/0.87          | ~ (r1_lattices @ X10 @ X11 @ (sk_D_2 @ X11 @ X12 @ X10))
% 0.68/0.87          | ~ (r4_lattice3 @ X10 @ X11 @ X12)
% 0.68/0.87          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.68/0.87          | ~ (l3_lattices @ X10)
% 0.68/0.87          | ~ (v4_lattice3 @ X10)
% 0.68/0.87          | ~ (v10_lattices @ X10)
% 0.68/0.87          | (v2_struct_0 @ X10))),
% 0.68/0.87      inference('simplify', [status(thm)], ['131'])).
% 0.68/0.87  thf('133', plain,
% 0.68/0.87      ((((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 0.68/0.87        | (v2_struct_0 @ sk_A)
% 0.68/0.87        | ~ (v10_lattices @ sk_A)
% 0.68/0.87        | ~ (v4_lattice3 @ sk_A)
% 0.68/0.87        | ~ (l3_lattices @ sk_A)
% 0.68/0.87        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.68/0.87        | ~ (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))
% 0.68/0.87        | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 0.68/0.87      inference('sup-', [status(thm)], ['130', '132'])).
% 0.68/0.87  thf('134', plain, ((v10_lattices @ sk_A)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('135', plain, ((v4_lattice3 @ sk_A)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('136', plain, ((l3_lattices @ sk_A)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('137', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('138', plain,
% 0.68/0.87      ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))),
% 0.68/0.87      inference('clc', [status(thm)], ['94', '95'])).
% 0.68/0.87  thf('139', plain,
% 0.68/0.87      ((((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 0.68/0.87        | (v2_struct_0 @ sk_A)
% 0.68/0.87        | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 0.68/0.87      inference('demod', [status(thm)],
% 0.68/0.87                ['133', '134', '135', '136', '137', '138'])).
% 0.68/0.87  thf('140', plain,
% 0.68/0.87      (((v2_struct_0 @ sk_A)
% 0.68/0.87        | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 0.68/0.87      inference('simplify', [status(thm)], ['139'])).
% 0.68/0.87  thf('141', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('142', plain,
% 0.68/0.87      (((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))),
% 0.68/0.87      inference('clc', [status(thm)], ['140', '141'])).
% 0.68/0.87  thf('143', plain,
% 0.68/0.87      ((r3_lattices @ sk_A @ (sk_D_5 @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.68/0.87      inference('demod', [status(thm)], ['44', '142'])).
% 0.68/0.87  thf('144', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('145', plain,
% 0.68/0.87      (![X22 : $i, X23 : $i, X26 : $i]:
% 0.68/0.87         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 0.68/0.87          | ~ (r3_lattice3 @ X23 @ X22 @ X26)
% 0.68/0.87          | ~ (r3_lattices @ X23 @ (sk_D_5 @ X26 @ X22 @ X23) @ X22)
% 0.68/0.87          | ((X22) = (k16_lattice3 @ X23 @ X26))
% 0.68/0.87          | ~ (l3_lattices @ X23)
% 0.68/0.87          | ~ (v4_lattice3 @ X23)
% 0.68/0.87          | ~ (v10_lattices @ X23)
% 0.68/0.87          | (v2_struct_0 @ X23))),
% 0.68/0.87      inference('cnf', [status(esa)], [t34_lattice3])).
% 0.68/0.87  thf('146', plain,
% 0.68/0.87      (![X0 : $i]:
% 0.68/0.87         ((v2_struct_0 @ sk_A)
% 0.68/0.87          | ~ (v10_lattices @ sk_A)
% 0.68/0.87          | ~ (v4_lattice3 @ sk_A)
% 0.68/0.87          | ~ (l3_lattices @ sk_A)
% 0.68/0.87          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 0.68/0.87          | ~ (r3_lattices @ sk_A @ (sk_D_5 @ X0 @ sk_B @ sk_A) @ sk_B)
% 0.68/0.87          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.68/0.87      inference('sup-', [status(thm)], ['144', '145'])).
% 0.68/0.87  thf('147', plain, ((v10_lattices @ sk_A)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('148', plain, ((v4_lattice3 @ sk_A)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('149', plain, ((l3_lattices @ sk_A)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('150', plain,
% 0.68/0.87      (![X0 : $i]:
% 0.68/0.87         ((v2_struct_0 @ sk_A)
% 0.68/0.87          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 0.68/0.87          | ~ (r3_lattices @ sk_A @ (sk_D_5 @ X0 @ sk_B @ sk_A) @ sk_B)
% 0.68/0.87          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.68/0.87      inference('demod', [status(thm)], ['146', '147', '148', '149'])).
% 0.68/0.87  thf('151', plain,
% 0.68/0.87      ((~ (r3_lattice3 @ sk_A @ sk_B @ sk_C)
% 0.68/0.87        | ((sk_B) = (k16_lattice3 @ sk_A @ sk_C))
% 0.68/0.87        | (v2_struct_0 @ sk_A))),
% 0.68/0.87      inference('sup-', [status(thm)], ['143', '150'])).
% 0.68/0.87  thf('152', plain, ((r3_lattice3 @ sk_A @ sk_B @ sk_C)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('153', plain,
% 0.68/0.87      ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C)) | (v2_struct_0 @ sk_A))),
% 0.68/0.87      inference('demod', [status(thm)], ['151', '152'])).
% 0.68/0.87  thf('154', plain, (((k16_lattice3 @ sk_A @ sk_C) != (sk_B))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('155', plain, ((v2_struct_0 @ sk_A)),
% 0.68/0.87      inference('simplify_reflect-', [status(thm)], ['153', '154'])).
% 0.68/0.87  thf('156', plain, ($false), inference('demod', [status(thm)], ['0', '155'])).
% 0.68/0.87  
% 0.68/0.87  % SZS output end Refutation
% 0.68/0.87  
% 0.68/0.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
