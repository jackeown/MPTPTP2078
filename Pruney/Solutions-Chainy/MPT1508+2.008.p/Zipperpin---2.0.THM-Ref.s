%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.URdtZZSlyN

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:31 EST 2020

% Result     : Theorem 1.12s
% Output     : Refutation 1.12s
% Verified   : 
% Statistics : Number of formulae       :  186 ( 539 expanded)
%              Number of leaves         :   28 ( 160 expanded)
%              Depth                    :   33
%              Number of atoms          : 2071 (9200 expanded)
%              Number of equality atoms :   52 ( 286 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_4_type,type,(
    sk_D_4: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r3_lattice3_type,type,(
    r3_lattice3: $i > $i > $i > $o )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i > $i )).

thf(a_2_1_lattice3_type,type,(
    a_2_1_lattice3: $i > $i > $i )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(r4_lattice3_type,type,(
    r4_lattice3: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

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
    ! [X20: $i,X21: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( r3_lattice3 @ X21 @ X20 @ X24 )
      | ( r3_lattice3 @ X21 @ ( sk_D_4 @ X24 @ X20 @ X21 ) @ X24 )
      | ( X20
        = ( k16_lattice3 @ X21 @ X24 ) )
      | ~ ( l3_lattices @ X21 )
      | ~ ( v4_lattice3 @ X21 )
      | ~ ( v10_lattices @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
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
    ! [X20: $i,X21: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( r3_lattice3 @ X21 @ X20 @ X24 )
      | ( m1_subset_1 @ ( sk_D_4 @ X24 @ X20 @ X21 ) @ ( u1_struct_0 @ X21 ) )
      | ( X20
        = ( k16_lattice3 @ X21 @ X24 ) )
      | ~ ( l3_lattices @ X21 )
      | ~ ( v4_lattice3 @ X21 )
      | ~ ( v10_lattices @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( l3_lattices @ X16 )
      | ( v2_struct_0 @ X16 )
      | ( r2_hidden @ X18 @ ( a_2_1_lattice3 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X16 ) )
      | ( X18 != X19 )
      | ~ ( r3_lattice3 @ X16 @ X19 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_lattice3])).

thf('28',plain,(
    ! [X16: $i,X17: $i,X19: $i] :
      ( ~ ( r3_lattice3 @ X16 @ X19 @ X17 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X16 ) )
      | ( r2_hidden @ X19 @ ( a_2_1_lattice3 @ X16 @ X17 ) )
      | ( v2_struct_0 @ X16 )
      | ~ ( l3_lattices @ X16 ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X26 ) )
      | ( r3_lattices @ X26 @ X25 @ ( k15_lattice3 @ X26 @ X27 ) )
      | ~ ( r2_hidden @ X25 @ X27 )
      | ~ ( l3_lattices @ X26 )
      | ~ ( v4_lattice3 @ X26 )
      | ~ ( v10_lattices @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t38_lattice3])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r2_hidden @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ( r3_lattices @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
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
      | ~ ( r2_hidden @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ( r3_lattices @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ ( k15_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    r3_lattices @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['34','43'])).

thf('45',plain,(
    r3_lattice3 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X16: $i,X17: $i,X19: $i] :
      ( ~ ( r3_lattice3 @ X16 @ X19 @ X17 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X16 ) )
      | ( r2_hidden @ X19 @ ( a_2_1_lattice3 @ X16 @ X17 ) )
      | ( v2_struct_0 @ X16 )
      | ~ ( l3_lattices @ X16 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( l3_lattices @ X16 )
      | ( v2_struct_0 @ X16 )
      | ( X18
        = ( sk_D_3 @ X17 @ X16 @ X18 ) )
      | ~ ( r2_hidden @ X18 @ ( a_2_1_lattice3 @ X16 @ X17 ) ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( l3_lattices @ X16 )
      | ( v2_struct_0 @ X16 )
      | ( r3_lattice3 @ X16 @ ( sk_D_3 @ X17 @ X16 @ X18 ) @ X17 )
      | ~ ( r2_hidden @ X18 @ ( a_2_1_lattice3 @ X16 @ X17 ) ) ) ),
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
    r3_lattices @ sk_A @ ( sk_D_4 @ sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['44','142'])).

thf('144',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    ! [X20: $i,X21: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( r3_lattice3 @ X21 @ X20 @ X24 )
      | ~ ( r3_lattices @ X21 @ ( sk_D_4 @ X24 @ X20 @ X21 ) @ X20 )
      | ( X20
        = ( k16_lattice3 @ X21 @ X24 ) )
      | ~ ( l3_lattices @ X21 )
      | ~ ( v4_lattice3 @ X21 )
      | ~ ( v10_lattices @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( sk_B
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattices @ sk_A @ ( sk_D_4 @ X0 @ sk_B @ sk_A ) @ sk_B )
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
      | ~ ( r3_lattices @ sk_A @ ( sk_D_4 @ X0 @ sk_B @ sk_A ) @ sk_B )
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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.URdtZZSlyN
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:18:25 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.12/1.35  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.12/1.35  % Solved by: fo/fo7.sh
% 1.12/1.35  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.12/1.35  % done 610 iterations in 0.854s
% 1.12/1.35  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.12/1.35  % SZS output start Refutation
% 1.12/1.35  thf(sk_B_type, type, sk_B: $i).
% 1.12/1.35  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 1.12/1.35  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 1.12/1.35  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 1.12/1.35  thf(sk_C_type, type, sk_C: $i).
% 1.12/1.35  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.12/1.35  thf(sk_A_type, type, sk_A: $i).
% 1.12/1.35  thf(sk_D_4_type, type, sk_D_4: $i > $i > $i > $i).
% 1.12/1.35  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.12/1.35  thf(r3_lattice3_type, type, r3_lattice3: $i > $i > $i > $o).
% 1.12/1.35  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 1.12/1.35  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 1.12/1.35  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 1.12/1.35  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i > $i).
% 1.12/1.35  thf(a_2_1_lattice3_type, type, a_2_1_lattice3: $i > $i > $i).
% 1.12/1.35  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 1.12/1.35  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 1.12/1.35  thf(r4_lattice3_type, type, r4_lattice3: $i > $i > $i > $o).
% 1.12/1.35  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 1.12/1.35  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.12/1.35  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.12/1.35  thf(t42_lattice3, conjecture,
% 1.12/1.35    (![A:$i]:
% 1.12/1.35     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 1.12/1.35         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 1.12/1.35       ( ![B:$i]:
% 1.12/1.35         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.12/1.35           ( ![C:$i]:
% 1.12/1.35             ( ( ( r2_hidden @ B @ C ) & ( r3_lattice3 @ A @ B @ C ) ) =>
% 1.12/1.35               ( ( k16_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ))).
% 1.12/1.35  thf(zf_stmt_0, negated_conjecture,
% 1.12/1.35    (~( ![A:$i]:
% 1.12/1.35        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 1.12/1.35            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 1.12/1.35          ( ![B:$i]:
% 1.12/1.35            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.12/1.35              ( ![C:$i]:
% 1.12/1.35                ( ( ( r2_hidden @ B @ C ) & ( r3_lattice3 @ A @ B @ C ) ) =>
% 1.12/1.35                  ( ( k16_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ) )),
% 1.12/1.35    inference('cnf.neg', [status(esa)], [t42_lattice3])).
% 1.12/1.35  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('1', plain, ((r3_lattice3 @ sk_A @ sk_B @ sk_C)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf(t34_lattice3, axiom,
% 1.12/1.35    (![A:$i]:
% 1.12/1.35     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 1.12/1.35         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 1.12/1.35       ( ![B:$i]:
% 1.12/1.35         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.12/1.35           ( ![C:$i]:
% 1.12/1.35             ( ( ( B ) = ( k16_lattice3 @ A @ C ) ) <=>
% 1.12/1.35               ( ( r3_lattice3 @ A @ B @ C ) & 
% 1.12/1.35                 ( ![D:$i]:
% 1.12/1.35                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 1.12/1.35                     ( ( r3_lattice3 @ A @ D @ C ) =>
% 1.12/1.35                       ( r3_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 1.12/1.35  thf('3', plain,
% 1.12/1.35      (![X20 : $i, X21 : $i, X24 : $i]:
% 1.12/1.35         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 1.12/1.35          | ~ (r3_lattice3 @ X21 @ X20 @ X24)
% 1.12/1.35          | (r3_lattice3 @ X21 @ (sk_D_4 @ X24 @ X20 @ X21) @ X24)
% 1.12/1.35          | ((X20) = (k16_lattice3 @ X21 @ X24))
% 1.12/1.35          | ~ (l3_lattices @ X21)
% 1.12/1.35          | ~ (v4_lattice3 @ X21)
% 1.12/1.35          | ~ (v10_lattices @ X21)
% 1.12/1.35          | (v2_struct_0 @ X21))),
% 1.12/1.35      inference('cnf', [status(esa)], [t34_lattice3])).
% 1.12/1.35  thf('4', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         ((v2_struct_0 @ sk_A)
% 1.12/1.35          | ~ (v10_lattices @ sk_A)
% 1.12/1.35          | ~ (v4_lattice3 @ sk_A)
% 1.12/1.35          | ~ (l3_lattices @ sk_A)
% 1.12/1.35          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 1.12/1.35          | (r3_lattice3 @ sk_A @ (sk_D_4 @ X0 @ sk_B @ sk_A) @ X0)
% 1.12/1.35          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 1.12/1.35      inference('sup-', [status(thm)], ['2', '3'])).
% 1.12/1.35  thf('5', plain, ((v10_lattices @ sk_A)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('6', plain, ((v4_lattice3 @ sk_A)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('7', plain, ((l3_lattices @ sk_A)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('8', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         ((v2_struct_0 @ sk_A)
% 1.12/1.35          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 1.12/1.35          | (r3_lattice3 @ sk_A @ (sk_D_4 @ X0 @ sk_B @ sk_A) @ X0)
% 1.12/1.35          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 1.12/1.35      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 1.12/1.35  thf('9', plain,
% 1.12/1.35      (((r3_lattice3 @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 1.12/1.35        | ((sk_B) = (k16_lattice3 @ sk_A @ sk_C))
% 1.12/1.35        | (v2_struct_0 @ sk_A))),
% 1.12/1.35      inference('sup-', [status(thm)], ['1', '8'])).
% 1.12/1.35  thf('10', plain, (((k16_lattice3 @ sk_A @ sk_C) != (sk_B))),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('11', plain,
% 1.12/1.35      (((r3_lattice3 @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 1.12/1.35        | (v2_struct_0 @ sk_A))),
% 1.12/1.35      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 1.12/1.35  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('13', plain,
% 1.12/1.35      ((r3_lattice3 @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ sk_C)),
% 1.12/1.35      inference('clc', [status(thm)], ['11', '12'])).
% 1.12/1.35  thf('14', plain, ((r3_lattice3 @ sk_A @ sk_B @ sk_C)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('15', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('16', plain,
% 1.12/1.35      (![X20 : $i, X21 : $i, X24 : $i]:
% 1.12/1.35         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 1.12/1.35          | ~ (r3_lattice3 @ X21 @ X20 @ X24)
% 1.12/1.35          | (m1_subset_1 @ (sk_D_4 @ X24 @ X20 @ X21) @ (u1_struct_0 @ X21))
% 1.12/1.35          | ((X20) = (k16_lattice3 @ X21 @ X24))
% 1.12/1.35          | ~ (l3_lattices @ X21)
% 1.12/1.35          | ~ (v4_lattice3 @ X21)
% 1.12/1.35          | ~ (v10_lattices @ X21)
% 1.12/1.35          | (v2_struct_0 @ X21))),
% 1.12/1.35      inference('cnf', [status(esa)], [t34_lattice3])).
% 1.12/1.35  thf('17', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         ((v2_struct_0 @ sk_A)
% 1.12/1.35          | ~ (v10_lattices @ sk_A)
% 1.12/1.35          | ~ (v4_lattice3 @ sk_A)
% 1.12/1.35          | ~ (l3_lattices @ sk_A)
% 1.12/1.35          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 1.12/1.35          | (m1_subset_1 @ (sk_D_4 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 1.12/1.35          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 1.12/1.35      inference('sup-', [status(thm)], ['15', '16'])).
% 1.12/1.35  thf('18', plain, ((v10_lattices @ sk_A)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('19', plain, ((v4_lattice3 @ sk_A)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('20', plain, ((l3_lattices @ sk_A)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('21', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         ((v2_struct_0 @ sk_A)
% 1.12/1.35          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 1.12/1.35          | (m1_subset_1 @ (sk_D_4 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 1.12/1.35          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 1.12/1.35      inference('demod', [status(thm)], ['17', '18', '19', '20'])).
% 1.12/1.35  thf('22', plain,
% 1.12/1.35      (((m1_subset_1 @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 1.12/1.35        | ((sk_B) = (k16_lattice3 @ sk_A @ sk_C))
% 1.12/1.35        | (v2_struct_0 @ sk_A))),
% 1.12/1.35      inference('sup-', [status(thm)], ['14', '21'])).
% 1.12/1.35  thf('23', plain, (((k16_lattice3 @ sk_A @ sk_C) != (sk_B))),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('24', plain,
% 1.12/1.35      (((m1_subset_1 @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 1.12/1.35        | (v2_struct_0 @ sk_A))),
% 1.12/1.35      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 1.12/1.35  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('26', plain,
% 1.12/1.35      ((m1_subset_1 @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 1.12/1.35      inference('clc', [status(thm)], ['24', '25'])).
% 1.12/1.35  thf(fraenkel_a_2_1_lattice3, axiom,
% 1.12/1.35    (![A:$i,B:$i,C:$i]:
% 1.12/1.35     ( ( ( ~( v2_struct_0 @ B ) ) & ( l3_lattices @ B ) ) =>
% 1.12/1.35       ( ( r2_hidden @ A @ ( a_2_1_lattice3 @ B @ C ) ) <=>
% 1.12/1.35         ( ?[D:$i]:
% 1.12/1.35           ( ( r3_lattice3 @ B @ D @ C ) & ( ( A ) = ( D ) ) & 
% 1.12/1.35             ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 1.12/1.35  thf('27', plain,
% 1.12/1.35      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 1.12/1.35         (~ (l3_lattices @ X16)
% 1.12/1.35          | (v2_struct_0 @ X16)
% 1.12/1.35          | (r2_hidden @ X18 @ (a_2_1_lattice3 @ X16 @ X17))
% 1.12/1.35          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X16))
% 1.12/1.35          | ((X18) != (X19))
% 1.12/1.35          | ~ (r3_lattice3 @ X16 @ X19 @ X17))),
% 1.12/1.35      inference('cnf', [status(esa)], [fraenkel_a_2_1_lattice3])).
% 1.12/1.35  thf('28', plain,
% 1.12/1.35      (![X16 : $i, X17 : $i, X19 : $i]:
% 1.12/1.35         (~ (r3_lattice3 @ X16 @ X19 @ X17)
% 1.12/1.35          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X16))
% 1.12/1.35          | (r2_hidden @ X19 @ (a_2_1_lattice3 @ X16 @ X17))
% 1.12/1.35          | (v2_struct_0 @ X16)
% 1.12/1.35          | ~ (l3_lattices @ X16))),
% 1.12/1.35      inference('simplify', [status(thm)], ['27'])).
% 1.12/1.35  thf('29', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         (~ (l3_lattices @ sk_A)
% 1.12/1.35          | (v2_struct_0 @ sk_A)
% 1.12/1.35          | (r2_hidden @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ 
% 1.12/1.35             (a_2_1_lattice3 @ sk_A @ X0))
% 1.12/1.35          | ~ (r3_lattice3 @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ X0))),
% 1.12/1.35      inference('sup-', [status(thm)], ['26', '28'])).
% 1.12/1.35  thf('30', plain, ((l3_lattices @ sk_A)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('31', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         ((v2_struct_0 @ sk_A)
% 1.12/1.35          | (r2_hidden @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ 
% 1.12/1.35             (a_2_1_lattice3 @ sk_A @ X0))
% 1.12/1.35          | ~ (r3_lattice3 @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ X0))),
% 1.12/1.35      inference('demod', [status(thm)], ['29', '30'])).
% 1.12/1.35  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('33', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         (~ (r3_lattice3 @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ X0)
% 1.12/1.35          | (r2_hidden @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ 
% 1.12/1.35             (a_2_1_lattice3 @ sk_A @ X0)))),
% 1.12/1.35      inference('clc', [status(thm)], ['31', '32'])).
% 1.12/1.35  thf('34', plain,
% 1.12/1.35      ((r2_hidden @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ 
% 1.12/1.35        (a_2_1_lattice3 @ sk_A @ sk_C))),
% 1.12/1.35      inference('sup-', [status(thm)], ['13', '33'])).
% 1.12/1.35  thf('35', plain,
% 1.12/1.35      ((m1_subset_1 @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 1.12/1.35      inference('clc', [status(thm)], ['24', '25'])).
% 1.12/1.35  thf(t38_lattice3, axiom,
% 1.12/1.35    (![A:$i]:
% 1.12/1.35     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 1.12/1.35         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 1.12/1.35       ( ![B:$i]:
% 1.12/1.35         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.12/1.35           ( ![C:$i]:
% 1.12/1.35             ( ( r2_hidden @ B @ C ) =>
% 1.12/1.35               ( ( r3_lattices @ A @ B @ ( k15_lattice3 @ A @ C ) ) & 
% 1.12/1.35                 ( r3_lattices @ A @ ( k16_lattice3 @ A @ C ) @ B ) ) ) ) ) ) ))).
% 1.12/1.35  thf('36', plain,
% 1.12/1.35      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.12/1.35         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X26))
% 1.12/1.35          | (r3_lattices @ X26 @ X25 @ (k15_lattice3 @ X26 @ X27))
% 1.12/1.35          | ~ (r2_hidden @ X25 @ X27)
% 1.12/1.35          | ~ (l3_lattices @ X26)
% 1.12/1.35          | ~ (v4_lattice3 @ X26)
% 1.12/1.35          | ~ (v10_lattices @ X26)
% 1.12/1.35          | (v2_struct_0 @ X26))),
% 1.12/1.35      inference('cnf', [status(esa)], [t38_lattice3])).
% 1.12/1.35  thf('37', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         ((v2_struct_0 @ sk_A)
% 1.12/1.35          | ~ (v10_lattices @ sk_A)
% 1.12/1.35          | ~ (v4_lattice3 @ sk_A)
% 1.12/1.35          | ~ (l3_lattices @ sk_A)
% 1.12/1.35          | ~ (r2_hidden @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ X0)
% 1.12/1.35          | (r3_lattices @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ 
% 1.12/1.35             (k15_lattice3 @ sk_A @ X0)))),
% 1.12/1.35      inference('sup-', [status(thm)], ['35', '36'])).
% 1.12/1.35  thf('38', plain, ((v10_lattices @ sk_A)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('39', plain, ((v4_lattice3 @ sk_A)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('40', plain, ((l3_lattices @ sk_A)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('41', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         ((v2_struct_0 @ sk_A)
% 1.12/1.35          | ~ (r2_hidden @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ X0)
% 1.12/1.35          | (r3_lattices @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ 
% 1.12/1.35             (k15_lattice3 @ sk_A @ X0)))),
% 1.12/1.35      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 1.12/1.35  thf('42', plain, (~ (v2_struct_0 @ sk_A)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('43', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         ((r3_lattices @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ 
% 1.12/1.35           (k15_lattice3 @ sk_A @ X0))
% 1.12/1.35          | ~ (r2_hidden @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ X0))),
% 1.12/1.35      inference('clc', [status(thm)], ['41', '42'])).
% 1.12/1.35  thf('44', plain,
% 1.12/1.35      ((r3_lattices @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ 
% 1.12/1.35        (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))),
% 1.12/1.35      inference('sup-', [status(thm)], ['34', '43'])).
% 1.12/1.35  thf('45', plain, ((r3_lattice3 @ sk_A @ sk_B @ sk_C)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('46', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('47', plain,
% 1.12/1.35      (![X16 : $i, X17 : $i, X19 : $i]:
% 1.12/1.35         (~ (r3_lattice3 @ X16 @ X19 @ X17)
% 1.12/1.35          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X16))
% 1.12/1.35          | (r2_hidden @ X19 @ (a_2_1_lattice3 @ X16 @ X17))
% 1.12/1.35          | (v2_struct_0 @ X16)
% 1.12/1.35          | ~ (l3_lattices @ X16))),
% 1.12/1.35      inference('simplify', [status(thm)], ['27'])).
% 1.12/1.35  thf('48', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         (~ (l3_lattices @ sk_A)
% 1.12/1.35          | (v2_struct_0 @ sk_A)
% 1.12/1.35          | (r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 1.12/1.35          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 1.12/1.35      inference('sup-', [status(thm)], ['46', '47'])).
% 1.12/1.35  thf('49', plain, ((l3_lattices @ sk_A)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('50', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         ((v2_struct_0 @ sk_A)
% 1.12/1.35          | (r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 1.12/1.35          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 1.12/1.35      inference('demod', [status(thm)], ['48', '49'])).
% 1.12/1.35  thf('51', plain, (~ (v2_struct_0 @ sk_A)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('52', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         (~ (r3_lattice3 @ sk_A @ sk_B @ X0)
% 1.12/1.35          | (r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0)))),
% 1.12/1.35      inference('clc', [status(thm)], ['50', '51'])).
% 1.12/1.35  thf('53', plain, ((r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))),
% 1.12/1.35      inference('sup-', [status(thm)], ['45', '52'])).
% 1.12/1.35  thf('54', plain, ((r2_hidden @ sk_B @ sk_C)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('55', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('56', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf(d17_lattice3, axiom,
% 1.12/1.35    (![A:$i]:
% 1.12/1.35     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 1.12/1.35       ( ![B:$i]:
% 1.12/1.35         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.12/1.35           ( ![C:$i]:
% 1.12/1.35             ( ( r4_lattice3 @ A @ B @ C ) <=>
% 1.12/1.35               ( ![D:$i]:
% 1.12/1.35                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 1.12/1.35                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ))).
% 1.12/1.35  thf('57', plain,
% 1.12/1.35      (![X5 : $i, X6 : $i, X9 : $i]:
% 1.12/1.35         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 1.12/1.35          | (r2_hidden @ (sk_D_1 @ X9 @ X5 @ X6) @ X9)
% 1.12/1.35          | (r4_lattice3 @ X6 @ X5 @ X9)
% 1.12/1.35          | ~ (l3_lattices @ X6)
% 1.12/1.35          | (v2_struct_0 @ X6))),
% 1.12/1.35      inference('cnf', [status(esa)], [d17_lattice3])).
% 1.12/1.35  thf('58', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         ((v2_struct_0 @ sk_A)
% 1.12/1.35          | ~ (l3_lattices @ sk_A)
% 1.12/1.35          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 1.12/1.35          | (r2_hidden @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0))),
% 1.12/1.35      inference('sup-', [status(thm)], ['56', '57'])).
% 1.12/1.35  thf('59', plain, ((l3_lattices @ sk_A)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('60', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         ((v2_struct_0 @ sk_A)
% 1.12/1.35          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 1.12/1.35          | (r2_hidden @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0))),
% 1.12/1.35      inference('demod', [status(thm)], ['58', '59'])).
% 1.12/1.35  thf('61', plain, (~ (v2_struct_0 @ sk_A)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('62', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         ((r2_hidden @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0)
% 1.12/1.35          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 1.12/1.35      inference('clc', [status(thm)], ['60', '61'])).
% 1.12/1.35  thf('63', plain,
% 1.12/1.35      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.12/1.35         (~ (l3_lattices @ X16)
% 1.12/1.35          | (v2_struct_0 @ X16)
% 1.12/1.35          | ((X18) = (sk_D_3 @ X17 @ X16 @ X18))
% 1.12/1.35          | ~ (r2_hidden @ X18 @ (a_2_1_lattice3 @ X16 @ X17)))),
% 1.12/1.35      inference('cnf', [status(esa)], [fraenkel_a_2_1_lattice3])).
% 1.12/1.35  thf('64', plain,
% 1.12/1.35      (![X0 : $i, X1 : $i]:
% 1.12/1.35         ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0))
% 1.12/1.35          | ((sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A)
% 1.12/1.35              = (sk_D_3 @ X0 @ X1 @ 
% 1.12/1.35                 (sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A)))
% 1.12/1.35          | (v2_struct_0 @ X1)
% 1.12/1.35          | ~ (l3_lattices @ X1))),
% 1.12/1.35      inference('sup-', [status(thm)], ['62', '63'])).
% 1.12/1.35  thf('65', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         ((r2_hidden @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0)
% 1.12/1.35          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 1.12/1.35      inference('clc', [status(thm)], ['60', '61'])).
% 1.12/1.35  thf('66', plain,
% 1.12/1.35      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.12/1.35         (~ (l3_lattices @ X16)
% 1.12/1.35          | (v2_struct_0 @ X16)
% 1.12/1.35          | (r3_lattice3 @ X16 @ (sk_D_3 @ X17 @ X16 @ X18) @ X17)
% 1.12/1.35          | ~ (r2_hidden @ X18 @ (a_2_1_lattice3 @ X16 @ X17)))),
% 1.12/1.35      inference('cnf', [status(esa)], [fraenkel_a_2_1_lattice3])).
% 1.12/1.35  thf('67', plain,
% 1.12/1.35      (![X0 : $i, X1 : $i]:
% 1.12/1.35         ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0))
% 1.12/1.35          | (r3_lattice3 @ X1 @ 
% 1.12/1.35             (sk_D_3 @ X0 @ X1 @ 
% 1.12/1.35              (sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A)) @ 
% 1.12/1.35             X0)
% 1.12/1.35          | (v2_struct_0 @ X1)
% 1.12/1.35          | ~ (l3_lattices @ X1))),
% 1.12/1.35      inference('sup-', [status(thm)], ['65', '66'])).
% 1.12/1.35  thf('68', plain,
% 1.12/1.35      (![X0 : $i, X1 : $i]:
% 1.12/1.35         ((r3_lattice3 @ X1 @ 
% 1.12/1.35           (sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A) @ X0)
% 1.12/1.35          | ~ (l3_lattices @ X1)
% 1.12/1.35          | (v2_struct_0 @ X1)
% 1.12/1.35          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0))
% 1.12/1.35          | ~ (l3_lattices @ X1)
% 1.12/1.35          | (v2_struct_0 @ X1)
% 1.12/1.35          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0)))),
% 1.12/1.35      inference('sup+', [status(thm)], ['64', '67'])).
% 1.12/1.35  thf('69', plain,
% 1.12/1.35      (![X0 : $i, X1 : $i]:
% 1.12/1.35         ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0))
% 1.12/1.35          | (v2_struct_0 @ X1)
% 1.12/1.35          | ~ (l3_lattices @ X1)
% 1.12/1.35          | (r3_lattice3 @ X1 @ 
% 1.12/1.35             (sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A) @ X0))),
% 1.12/1.35      inference('simplify', [status(thm)], ['68'])).
% 1.12/1.35  thf('70', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('71', plain,
% 1.12/1.35      (![X5 : $i, X6 : $i, X9 : $i]:
% 1.12/1.35         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 1.12/1.35          | (m1_subset_1 @ (sk_D_1 @ X9 @ X5 @ X6) @ (u1_struct_0 @ X6))
% 1.12/1.35          | (r4_lattice3 @ X6 @ X5 @ X9)
% 1.12/1.35          | ~ (l3_lattices @ X6)
% 1.12/1.35          | (v2_struct_0 @ X6))),
% 1.12/1.35      inference('cnf', [status(esa)], [d17_lattice3])).
% 1.12/1.35  thf('72', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         ((v2_struct_0 @ sk_A)
% 1.12/1.35          | ~ (l3_lattices @ sk_A)
% 1.12/1.35          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 1.12/1.35          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 1.12/1.35      inference('sup-', [status(thm)], ['70', '71'])).
% 1.12/1.35  thf('73', plain, ((l3_lattices @ sk_A)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('74', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         ((v2_struct_0 @ sk_A)
% 1.12/1.35          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 1.12/1.35          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 1.12/1.35      inference('demod', [status(thm)], ['72', '73'])).
% 1.12/1.35  thf('75', plain, (~ (v2_struct_0 @ sk_A)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('76', plain,
% 1.12/1.35      (![X0 : $i]:
% 1.12/1.35         ((m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 1.12/1.35          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 1.12/1.35      inference('clc', [status(thm)], ['74', '75'])).
% 1.12/1.35  thf(d16_lattice3, axiom,
% 1.12/1.35    (![A:$i]:
% 1.12/1.35     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 1.12/1.35       ( ![B:$i]:
% 1.12/1.35         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.12/1.35           ( ![C:$i]:
% 1.12/1.35             ( ( r3_lattice3 @ A @ B @ C ) <=>
% 1.12/1.35               ( ![D:$i]:
% 1.12/1.35                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 1.12/1.35                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 1.12/1.35  thf('77', plain,
% 1.12/1.35      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.12/1.35         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 1.12/1.35          | ~ (r3_lattice3 @ X1 @ X0 @ X2)
% 1.12/1.35          | ~ (r2_hidden @ X3 @ X2)
% 1.12/1.35          | (r1_lattices @ X1 @ X0 @ X3)
% 1.12/1.35          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 1.12/1.35          | ~ (l3_lattices @ X1)
% 1.12/1.35          | (v2_struct_0 @ X1))),
% 1.12/1.35      inference('cnf', [status(esa)], [d16_lattice3])).
% 1.12/1.35  thf('78', plain,
% 1.12/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.12/1.35         ((r4_lattice3 @ sk_A @ sk_B @ X0)
% 1.12/1.35          | (v2_struct_0 @ sk_A)
% 1.12/1.35          | ~ (l3_lattices @ sk_A)
% 1.12/1.35          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 1.12/1.35          | (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X1)
% 1.12/1.35          | ~ (r2_hidden @ X1 @ X2)
% 1.12/1.35          | ~ (r3_lattice3 @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X2))),
% 1.12/1.35      inference('sup-', [status(thm)], ['76', '77'])).
% 1.12/1.35  thf('79', plain, ((l3_lattices @ sk_A)),
% 1.12/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.35  thf('80', plain,
% 1.12/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.12/1.35         ((r4_lattice3 @ sk_A @ sk_B @ X0)
% 1.12/1.35          | (v2_struct_0 @ sk_A)
% 1.12/1.35          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 1.12/1.35          | (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X1)
% 1.12/1.35          | ~ (r2_hidden @ X1 @ X2)
% 1.12/1.35          | ~ (r3_lattice3 @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X2))),
% 1.12/1.35      inference('demod', [status(thm)], ['78', '79'])).
% 1.12/1.35  thf('81', plain,
% 1.12/1.35      (![X0 : $i, X1 : $i]:
% 1.12/1.35         (~ (l3_lattices @ sk_A)
% 1.12/1.35          | (v2_struct_0 @ sk_A)
% 1.12/1.35          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 1.12/1.35          | ~ (r2_hidden @ X1 @ X0)
% 1.12/1.35          | (r1_lattices @ sk_A @ 
% 1.12/1.35             (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ X0) @ sk_B @ sk_A) @ X1)
% 1.12/1.35          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 1.12/1.36          | (v2_struct_0 @ sk_A)
% 1.12/1.36          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0)))),
% 1.12/1.36      inference('sup-', [status(thm)], ['69', '80'])).
% 1.12/1.36  thf('82', plain, ((l3_lattices @ sk_A)),
% 1.12/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.36  thf('83', plain,
% 1.12/1.36      (![X0 : $i, X1 : $i]:
% 1.12/1.36         ((v2_struct_0 @ sk_A)
% 1.12/1.36          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 1.12/1.36          | ~ (r2_hidden @ X1 @ X0)
% 1.12/1.36          | (r1_lattices @ sk_A @ 
% 1.12/1.36             (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ X0) @ sk_B @ sk_A) @ X1)
% 1.12/1.36          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 1.12/1.36          | (v2_struct_0 @ sk_A)
% 1.12/1.36          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0)))),
% 1.12/1.36      inference('demod', [status(thm)], ['81', '82'])).
% 1.12/1.36  thf('84', plain,
% 1.12/1.36      (![X0 : $i, X1 : $i]:
% 1.12/1.36         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 1.12/1.36          | (r1_lattices @ sk_A @ 
% 1.12/1.36             (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ X0) @ sk_B @ sk_A) @ X1)
% 1.12/1.36          | ~ (r2_hidden @ X1 @ X0)
% 1.12/1.36          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 1.12/1.36          | (v2_struct_0 @ sk_A))),
% 1.12/1.36      inference('simplify', [status(thm)], ['83'])).
% 1.12/1.36  thf('85', plain,
% 1.12/1.36      (![X0 : $i]:
% 1.12/1.36         ((v2_struct_0 @ sk_A)
% 1.12/1.36          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 1.12/1.36          | ~ (r2_hidden @ sk_B @ X0)
% 1.12/1.36          | (r1_lattices @ sk_A @ 
% 1.12/1.36             (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ X0) @ sk_B @ sk_A) @ sk_B))),
% 1.12/1.36      inference('sup-', [status(thm)], ['55', '84'])).
% 1.12/1.36  thf('86', plain,
% 1.12/1.36      (((r1_lattices @ sk_A @ 
% 1.12/1.36         (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_B @ sk_A) @ sk_B)
% 1.12/1.36        | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))
% 1.12/1.36        | (v2_struct_0 @ sk_A))),
% 1.12/1.36      inference('sup-', [status(thm)], ['54', '85'])).
% 1.12/1.36  thf('87', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.12/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.36  thf('88', plain,
% 1.12/1.36      (![X5 : $i, X6 : $i, X9 : $i]:
% 1.12/1.36         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 1.12/1.36          | ~ (r1_lattices @ X6 @ (sk_D_1 @ X9 @ X5 @ X6) @ X5)
% 1.12/1.36          | (r4_lattice3 @ X6 @ X5 @ X9)
% 1.12/1.36          | ~ (l3_lattices @ X6)
% 1.12/1.36          | (v2_struct_0 @ X6))),
% 1.12/1.36      inference('cnf', [status(esa)], [d17_lattice3])).
% 1.12/1.36  thf('89', plain,
% 1.12/1.36      (![X0 : $i]:
% 1.12/1.36         ((v2_struct_0 @ sk_A)
% 1.12/1.36          | ~ (l3_lattices @ sk_A)
% 1.12/1.36          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 1.12/1.36          | ~ (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_B))),
% 1.12/1.36      inference('sup-', [status(thm)], ['87', '88'])).
% 1.12/1.36  thf('90', plain, ((l3_lattices @ sk_A)),
% 1.12/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.36  thf('91', plain,
% 1.12/1.36      (![X0 : $i]:
% 1.12/1.36         ((v2_struct_0 @ sk_A)
% 1.12/1.36          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 1.12/1.36          | ~ (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_B))),
% 1.12/1.36      inference('demod', [status(thm)], ['89', '90'])).
% 1.12/1.36  thf('92', plain, (~ (v2_struct_0 @ sk_A)),
% 1.12/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.36  thf('93', plain,
% 1.12/1.36      (![X0 : $i]:
% 1.12/1.36         (~ (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_B)
% 1.12/1.36          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 1.12/1.36      inference('clc', [status(thm)], ['91', '92'])).
% 1.12/1.36  thf('94', plain,
% 1.12/1.36      (((v2_struct_0 @ sk_A)
% 1.12/1.36        | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C)))),
% 1.12/1.36      inference('clc', [status(thm)], ['86', '93'])).
% 1.12/1.36  thf('95', plain, (~ (v2_struct_0 @ sk_A)),
% 1.12/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.36  thf('96', plain,
% 1.12/1.36      ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))),
% 1.12/1.36      inference('clc', [status(thm)], ['94', '95'])).
% 1.12/1.36  thf('97', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.12/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.36  thf(d21_lattice3, axiom,
% 1.12/1.36    (![A:$i]:
% 1.12/1.36     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 1.12/1.36       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 1.12/1.36           ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 1.12/1.36         ( ![B:$i,C:$i]:
% 1.12/1.36           ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.12/1.36             ( ( ( C ) = ( k15_lattice3 @ A @ B ) ) <=>
% 1.12/1.36               ( ( r4_lattice3 @ A @ C @ B ) & 
% 1.12/1.36                 ( ![D:$i]:
% 1.12/1.36                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 1.12/1.36                     ( ( r4_lattice3 @ A @ D @ B ) =>
% 1.12/1.36                       ( r1_lattices @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 1.12/1.36  thf('98', plain,
% 1.12/1.36      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.12/1.36         ((v2_struct_0 @ X10)
% 1.12/1.36          | ~ (v10_lattices @ X10)
% 1.12/1.36          | ~ (v4_lattice3 @ X10)
% 1.12/1.36          | ~ (l3_lattices @ X10)
% 1.12/1.36          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 1.12/1.36          | ~ (r4_lattice3 @ X10 @ X11 @ X12)
% 1.12/1.36          | (r4_lattice3 @ X10 @ (sk_D_2 @ X11 @ X12 @ X10) @ X12)
% 1.12/1.36          | ((X11) = (k15_lattice3 @ X10 @ X12))
% 1.12/1.36          | ~ (l3_lattices @ X10)
% 1.12/1.36          | (v2_struct_0 @ X10))),
% 1.12/1.36      inference('cnf', [status(esa)], [d21_lattice3])).
% 1.12/1.36  thf('99', plain,
% 1.12/1.36      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.12/1.36         (((X11) = (k15_lattice3 @ X10 @ X12))
% 1.12/1.36          | (r4_lattice3 @ X10 @ (sk_D_2 @ X11 @ X12 @ X10) @ X12)
% 1.12/1.36          | ~ (r4_lattice3 @ X10 @ X11 @ X12)
% 1.12/1.36          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 1.12/1.36          | ~ (l3_lattices @ X10)
% 1.12/1.36          | ~ (v4_lattice3 @ X10)
% 1.12/1.36          | ~ (v10_lattices @ X10)
% 1.12/1.36          | (v2_struct_0 @ X10))),
% 1.12/1.36      inference('simplify', [status(thm)], ['98'])).
% 1.12/1.36  thf('100', plain,
% 1.12/1.36      (![X0 : $i]:
% 1.12/1.36         ((v2_struct_0 @ sk_A)
% 1.12/1.36          | ~ (v10_lattices @ sk_A)
% 1.12/1.36          | ~ (v4_lattice3 @ sk_A)
% 1.12/1.36          | ~ (l3_lattices @ sk_A)
% 1.12/1.36          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0)
% 1.12/1.36          | (r4_lattice3 @ sk_A @ (sk_D_2 @ sk_B @ X0 @ sk_A) @ X0)
% 1.12/1.36          | ((sk_B) = (k15_lattice3 @ sk_A @ X0)))),
% 1.12/1.36      inference('sup-', [status(thm)], ['97', '99'])).
% 1.12/1.36  thf('101', plain, ((v10_lattices @ sk_A)),
% 1.12/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.36  thf('102', plain, ((v4_lattice3 @ sk_A)),
% 1.12/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.36  thf('103', plain, ((l3_lattices @ sk_A)),
% 1.12/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.36  thf('104', plain,
% 1.12/1.36      (![X0 : $i]:
% 1.12/1.36         ((v2_struct_0 @ sk_A)
% 1.12/1.36          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0)
% 1.12/1.36          | (r4_lattice3 @ sk_A @ (sk_D_2 @ sk_B @ X0 @ sk_A) @ X0)
% 1.12/1.36          | ((sk_B) = (k15_lattice3 @ sk_A @ X0)))),
% 1.12/1.36      inference('demod', [status(thm)], ['100', '101', '102', '103'])).
% 1.12/1.36  thf('105', plain,
% 1.12/1.36      ((((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 1.12/1.36        | (r4_lattice3 @ sk_A @ 
% 1.12/1.36           (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A) @ 
% 1.12/1.36           (a_2_1_lattice3 @ sk_A @ sk_C))
% 1.12/1.36        | (v2_struct_0 @ sk_A))),
% 1.12/1.36      inference('sup-', [status(thm)], ['96', '104'])).
% 1.12/1.36  thf('106', plain, (~ (v2_struct_0 @ sk_A)),
% 1.12/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.36  thf('107', plain,
% 1.12/1.36      (((r4_lattice3 @ sk_A @ 
% 1.12/1.36         (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A) @ 
% 1.12/1.36         (a_2_1_lattice3 @ sk_A @ sk_C))
% 1.12/1.36        | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 1.12/1.36      inference('clc', [status(thm)], ['105', '106'])).
% 1.12/1.36  thf('108', plain,
% 1.12/1.36      ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))),
% 1.12/1.36      inference('clc', [status(thm)], ['94', '95'])).
% 1.12/1.36  thf('109', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.12/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.36  thf('110', plain,
% 1.12/1.36      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.12/1.36         ((v2_struct_0 @ X10)
% 1.12/1.36          | ~ (v10_lattices @ X10)
% 1.12/1.36          | ~ (v4_lattice3 @ X10)
% 1.12/1.36          | ~ (l3_lattices @ X10)
% 1.12/1.36          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 1.12/1.36          | ~ (r4_lattice3 @ X10 @ X11 @ X12)
% 1.12/1.36          | (m1_subset_1 @ (sk_D_2 @ X11 @ X12 @ X10) @ (u1_struct_0 @ X10))
% 1.12/1.36          | ((X11) = (k15_lattice3 @ X10 @ X12))
% 1.12/1.36          | ~ (l3_lattices @ X10)
% 1.12/1.36          | (v2_struct_0 @ X10))),
% 1.12/1.36      inference('cnf', [status(esa)], [d21_lattice3])).
% 1.12/1.36  thf('111', plain,
% 1.12/1.36      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.12/1.36         (((X11) = (k15_lattice3 @ X10 @ X12))
% 1.12/1.36          | (m1_subset_1 @ (sk_D_2 @ X11 @ X12 @ X10) @ (u1_struct_0 @ X10))
% 1.12/1.36          | ~ (r4_lattice3 @ X10 @ X11 @ X12)
% 1.12/1.36          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 1.12/1.36          | ~ (l3_lattices @ X10)
% 1.12/1.36          | ~ (v4_lattice3 @ X10)
% 1.12/1.36          | ~ (v10_lattices @ X10)
% 1.12/1.36          | (v2_struct_0 @ X10))),
% 1.12/1.36      inference('simplify', [status(thm)], ['110'])).
% 1.12/1.36  thf('112', plain,
% 1.12/1.36      (![X0 : $i]:
% 1.12/1.36         ((v2_struct_0 @ sk_A)
% 1.12/1.36          | ~ (v10_lattices @ sk_A)
% 1.12/1.36          | ~ (v4_lattice3 @ sk_A)
% 1.12/1.36          | ~ (l3_lattices @ sk_A)
% 1.12/1.36          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0)
% 1.12/1.36          | (m1_subset_1 @ (sk_D_2 @ sk_B @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 1.12/1.36          | ((sk_B) = (k15_lattice3 @ sk_A @ X0)))),
% 1.12/1.36      inference('sup-', [status(thm)], ['109', '111'])).
% 1.12/1.36  thf('113', plain, ((v10_lattices @ sk_A)),
% 1.12/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.36  thf('114', plain, ((v4_lattice3 @ sk_A)),
% 1.12/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.36  thf('115', plain, ((l3_lattices @ sk_A)),
% 1.12/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.36  thf('116', plain,
% 1.12/1.36      (![X0 : $i]:
% 1.12/1.36         ((v2_struct_0 @ sk_A)
% 1.12/1.36          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0)
% 1.12/1.36          | (m1_subset_1 @ (sk_D_2 @ sk_B @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 1.12/1.36          | ((sk_B) = (k15_lattice3 @ sk_A @ X0)))),
% 1.12/1.36      inference('demod', [status(thm)], ['112', '113', '114', '115'])).
% 1.12/1.36  thf('117', plain,
% 1.12/1.36      ((((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 1.12/1.36        | (m1_subset_1 @ 
% 1.12/1.36           (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A) @ 
% 1.12/1.36           (u1_struct_0 @ sk_A))
% 1.12/1.36        | (v2_struct_0 @ sk_A))),
% 1.12/1.36      inference('sup-', [status(thm)], ['108', '116'])).
% 1.12/1.36  thf('118', plain, (~ (v2_struct_0 @ sk_A)),
% 1.12/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.36  thf('119', plain,
% 1.12/1.36      (((m1_subset_1 @ 
% 1.12/1.36         (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A) @ 
% 1.12/1.36         (u1_struct_0 @ sk_A))
% 1.12/1.36        | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 1.12/1.36      inference('clc', [status(thm)], ['117', '118'])).
% 1.12/1.36  thf('120', plain,
% 1.12/1.36      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.12/1.36         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 1.12/1.36          | ~ (r4_lattice3 @ X6 @ X5 @ X7)
% 1.12/1.36          | ~ (r2_hidden @ X8 @ X7)
% 1.12/1.36          | (r1_lattices @ X6 @ X8 @ X5)
% 1.12/1.36          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X6))
% 1.12/1.36          | ~ (l3_lattices @ X6)
% 1.12/1.36          | (v2_struct_0 @ X6))),
% 1.12/1.36      inference('cnf', [status(esa)], [d17_lattice3])).
% 1.12/1.36  thf('121', plain,
% 1.12/1.36      (![X0 : $i, X1 : $i]:
% 1.12/1.36         (((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 1.12/1.36          | (v2_struct_0 @ sk_A)
% 1.12/1.36          | ~ (l3_lattices @ sk_A)
% 1.12/1.36          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.12/1.36          | (r1_lattices @ sk_A @ X0 @ 
% 1.12/1.36             (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A))
% 1.12/1.36          | ~ (r2_hidden @ X0 @ X1)
% 1.12/1.36          | ~ (r4_lattice3 @ sk_A @ 
% 1.12/1.36               (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A) @ X1))),
% 1.12/1.36      inference('sup-', [status(thm)], ['119', '120'])).
% 1.12/1.36  thf('122', plain, ((l3_lattices @ sk_A)),
% 1.12/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.36  thf('123', plain,
% 1.12/1.36      (![X0 : $i, X1 : $i]:
% 1.12/1.36         (((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 1.12/1.36          | (v2_struct_0 @ sk_A)
% 1.12/1.36          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.12/1.36          | (r1_lattices @ sk_A @ X0 @ 
% 1.12/1.36             (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A))
% 1.12/1.36          | ~ (r2_hidden @ X0 @ X1)
% 1.12/1.36          | ~ (r4_lattice3 @ sk_A @ 
% 1.12/1.36               (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A) @ X1))),
% 1.12/1.36      inference('demod', [status(thm)], ['121', '122'])).
% 1.12/1.36  thf('124', plain,
% 1.12/1.36      (![X0 : $i]:
% 1.12/1.36         (((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 1.12/1.36          | ~ (r2_hidden @ X0 @ (a_2_1_lattice3 @ sk_A @ sk_C))
% 1.12/1.36          | (r1_lattices @ sk_A @ X0 @ 
% 1.12/1.36             (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A))
% 1.12/1.36          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.12/1.36          | (v2_struct_0 @ sk_A)
% 1.12/1.36          | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 1.12/1.36      inference('sup-', [status(thm)], ['107', '123'])).
% 1.12/1.36  thf('125', plain,
% 1.12/1.36      (![X0 : $i]:
% 1.12/1.36         ((v2_struct_0 @ sk_A)
% 1.12/1.36          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.12/1.36          | (r1_lattices @ sk_A @ X0 @ 
% 1.12/1.36             (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A))
% 1.12/1.36          | ~ (r2_hidden @ X0 @ (a_2_1_lattice3 @ sk_A @ sk_C))
% 1.12/1.36          | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 1.12/1.36      inference('simplify', [status(thm)], ['124'])).
% 1.12/1.36  thf('126', plain,
% 1.12/1.36      ((((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 1.12/1.36        | (r1_lattices @ sk_A @ sk_B @ 
% 1.12/1.36           (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A))
% 1.12/1.36        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 1.12/1.36        | (v2_struct_0 @ sk_A))),
% 1.12/1.36      inference('sup-', [status(thm)], ['53', '125'])).
% 1.12/1.36  thf('127', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.12/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.36  thf('128', plain,
% 1.12/1.36      ((((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 1.12/1.36        | (r1_lattices @ sk_A @ sk_B @ 
% 1.12/1.36           (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A))
% 1.12/1.36        | (v2_struct_0 @ sk_A))),
% 1.12/1.36      inference('demod', [status(thm)], ['126', '127'])).
% 1.12/1.36  thf('129', plain, (~ (v2_struct_0 @ sk_A)),
% 1.12/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.36  thf('130', plain,
% 1.12/1.36      (((r1_lattices @ sk_A @ sk_B @ 
% 1.12/1.36         (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A))
% 1.12/1.36        | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 1.12/1.36      inference('clc', [status(thm)], ['128', '129'])).
% 1.12/1.36  thf('131', plain,
% 1.12/1.36      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.12/1.36         ((v2_struct_0 @ X10)
% 1.12/1.36          | ~ (v10_lattices @ X10)
% 1.12/1.36          | ~ (v4_lattice3 @ X10)
% 1.12/1.36          | ~ (l3_lattices @ X10)
% 1.12/1.36          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 1.12/1.36          | ~ (r4_lattice3 @ X10 @ X11 @ X12)
% 1.12/1.36          | ~ (r1_lattices @ X10 @ X11 @ (sk_D_2 @ X11 @ X12 @ X10))
% 1.12/1.36          | ((X11) = (k15_lattice3 @ X10 @ X12))
% 1.12/1.36          | ~ (l3_lattices @ X10)
% 1.12/1.36          | (v2_struct_0 @ X10))),
% 1.12/1.36      inference('cnf', [status(esa)], [d21_lattice3])).
% 1.12/1.36  thf('132', plain,
% 1.12/1.36      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.12/1.36         (((X11) = (k15_lattice3 @ X10 @ X12))
% 1.12/1.36          | ~ (r1_lattices @ X10 @ X11 @ (sk_D_2 @ X11 @ X12 @ X10))
% 1.12/1.36          | ~ (r4_lattice3 @ X10 @ X11 @ X12)
% 1.12/1.36          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 1.12/1.36          | ~ (l3_lattices @ X10)
% 1.12/1.36          | ~ (v4_lattice3 @ X10)
% 1.12/1.36          | ~ (v10_lattices @ X10)
% 1.12/1.36          | (v2_struct_0 @ X10))),
% 1.12/1.36      inference('simplify', [status(thm)], ['131'])).
% 1.12/1.36  thf('133', plain,
% 1.12/1.36      ((((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 1.12/1.36        | (v2_struct_0 @ sk_A)
% 1.12/1.36        | ~ (v10_lattices @ sk_A)
% 1.12/1.36        | ~ (v4_lattice3 @ sk_A)
% 1.12/1.36        | ~ (l3_lattices @ sk_A)
% 1.12/1.36        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 1.12/1.36        | ~ (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))
% 1.12/1.36        | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 1.12/1.36      inference('sup-', [status(thm)], ['130', '132'])).
% 1.12/1.36  thf('134', plain, ((v10_lattices @ sk_A)),
% 1.12/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.36  thf('135', plain, ((v4_lattice3 @ sk_A)),
% 1.12/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.36  thf('136', plain, ((l3_lattices @ sk_A)),
% 1.12/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.36  thf('137', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.12/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.36  thf('138', plain,
% 1.12/1.36      ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))),
% 1.12/1.36      inference('clc', [status(thm)], ['94', '95'])).
% 1.12/1.36  thf('139', plain,
% 1.12/1.36      ((((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 1.12/1.36        | (v2_struct_0 @ sk_A)
% 1.12/1.36        | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 1.12/1.36      inference('demod', [status(thm)],
% 1.12/1.36                ['133', '134', '135', '136', '137', '138'])).
% 1.12/1.36  thf('140', plain,
% 1.12/1.36      (((v2_struct_0 @ sk_A)
% 1.12/1.36        | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 1.12/1.36      inference('simplify', [status(thm)], ['139'])).
% 1.12/1.36  thf('141', plain, (~ (v2_struct_0 @ sk_A)),
% 1.12/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.36  thf('142', plain,
% 1.12/1.36      (((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))),
% 1.12/1.36      inference('clc', [status(thm)], ['140', '141'])).
% 1.12/1.36  thf('143', plain,
% 1.12/1.36      ((r3_lattices @ sk_A @ (sk_D_4 @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 1.12/1.36      inference('demod', [status(thm)], ['44', '142'])).
% 1.12/1.36  thf('144', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.12/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.36  thf('145', plain,
% 1.12/1.36      (![X20 : $i, X21 : $i, X24 : $i]:
% 1.12/1.36         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 1.12/1.36          | ~ (r3_lattice3 @ X21 @ X20 @ X24)
% 1.12/1.36          | ~ (r3_lattices @ X21 @ (sk_D_4 @ X24 @ X20 @ X21) @ X20)
% 1.12/1.36          | ((X20) = (k16_lattice3 @ X21 @ X24))
% 1.12/1.36          | ~ (l3_lattices @ X21)
% 1.12/1.36          | ~ (v4_lattice3 @ X21)
% 1.12/1.36          | ~ (v10_lattices @ X21)
% 1.12/1.36          | (v2_struct_0 @ X21))),
% 1.12/1.36      inference('cnf', [status(esa)], [t34_lattice3])).
% 1.12/1.36  thf('146', plain,
% 1.12/1.36      (![X0 : $i]:
% 1.12/1.36         ((v2_struct_0 @ sk_A)
% 1.12/1.36          | ~ (v10_lattices @ sk_A)
% 1.12/1.36          | ~ (v4_lattice3 @ sk_A)
% 1.12/1.36          | ~ (l3_lattices @ sk_A)
% 1.12/1.36          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 1.12/1.36          | ~ (r3_lattices @ sk_A @ (sk_D_4 @ X0 @ sk_B @ sk_A) @ sk_B)
% 1.12/1.36          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 1.12/1.36      inference('sup-', [status(thm)], ['144', '145'])).
% 1.12/1.36  thf('147', plain, ((v10_lattices @ sk_A)),
% 1.12/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.36  thf('148', plain, ((v4_lattice3 @ sk_A)),
% 1.12/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.36  thf('149', plain, ((l3_lattices @ sk_A)),
% 1.12/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.36  thf('150', plain,
% 1.12/1.36      (![X0 : $i]:
% 1.12/1.36         ((v2_struct_0 @ sk_A)
% 1.12/1.36          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 1.12/1.36          | ~ (r3_lattices @ sk_A @ (sk_D_4 @ X0 @ sk_B @ sk_A) @ sk_B)
% 1.12/1.36          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 1.12/1.36      inference('demod', [status(thm)], ['146', '147', '148', '149'])).
% 1.12/1.36  thf('151', plain,
% 1.12/1.36      ((~ (r3_lattice3 @ sk_A @ sk_B @ sk_C)
% 1.12/1.36        | ((sk_B) = (k16_lattice3 @ sk_A @ sk_C))
% 1.12/1.36        | (v2_struct_0 @ sk_A))),
% 1.12/1.36      inference('sup-', [status(thm)], ['143', '150'])).
% 1.12/1.36  thf('152', plain, ((r3_lattice3 @ sk_A @ sk_B @ sk_C)),
% 1.12/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.36  thf('153', plain,
% 1.12/1.36      ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C)) | (v2_struct_0 @ sk_A))),
% 1.12/1.36      inference('demod', [status(thm)], ['151', '152'])).
% 1.12/1.36  thf('154', plain, (((k16_lattice3 @ sk_A @ sk_C) != (sk_B))),
% 1.12/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.36  thf('155', plain, ((v2_struct_0 @ sk_A)),
% 1.12/1.36      inference('simplify_reflect-', [status(thm)], ['153', '154'])).
% 1.12/1.36  thf('156', plain, ($false), inference('demod', [status(thm)], ['0', '155'])).
% 1.12/1.36  
% 1.12/1.36  % SZS output end Refutation
% 1.12/1.36  
% 1.12/1.36  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
