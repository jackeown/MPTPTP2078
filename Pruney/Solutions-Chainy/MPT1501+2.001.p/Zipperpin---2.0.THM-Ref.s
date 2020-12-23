%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jekBkEvauJ

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:26 EST 2020

% Result     : Theorem 4.48s
% Output     : Refutation 4.48s
% Verified   : 
% Statistics : Number of formulae       :  350 (1225 expanded)
%              Number of leaves         :   36 ( 348 expanded)
%              Depth                    :   36
%              Number of atoms          : 5002 (26204 expanded)
%              Number of equality atoms :  133 ( 717 expanded)
%              Maximal formula depth    :   21 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(a_2_1_lattice3_type,type,(
    a_2_1_lattice3: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r3_lattice3_type,type,(
    r3_lattice3: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i > $i )).

thf(r4_lattice3_type,type,(
    r4_lattice3: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_D_4_type,type,(
    sk_D_4: $i )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t34_lattice3,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
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
                       => ( r3_lattices @ A @ D @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_lattice3])).

thf('0',plain,(
    ! [X24: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_lattices @ sk_A @ X24 @ sk_B )
      | ~ ( r3_lattice3 @ sk_A @ X24 @ sk_C )
      | ( sk_B
        = ( k16_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_A ) )
        | ( r3_lattices @ sk_A @ X24 @ sk_B )
        | ~ ( r3_lattice3 @ sk_A @ X24 @ sk_C ) )
    | ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r3_lattice3 @ sk_A @ sk_D_4 @ sk_C )
    | ~ ( r3_lattice3 @ sk_A @ sk_B @ sk_C )
    | ( sk_B
     != ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r3_lattice3 @ sk_A @ sk_D_4 @ sk_C )
    | ~ ( r3_lattice3 @ sk_A @ sk_B @ sk_C )
    | ( sk_B
     != ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( m1_subset_1 @ sk_D_4 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r3_lattice3 @ sk_A @ sk_B @ sk_C )
    | ( sk_B
     != ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_subset_1 @ sk_D_4 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r3_lattice3 @ sk_A @ sk_B @ sk_C )
    | ( sk_B
     != ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ~ ( r3_lattices @ sk_A @ sk_D_4 @ sk_B )
    | ~ ( r3_lattice3 @ sk_A @ sk_B @ sk_C )
    | ( sk_B
     != ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ~ ( r3_lattice3 @ sk_A @ sk_B @ sk_C )
    | ~ ( r3_lattices @ sk_A @ sk_D_4 @ sk_B )
    | ( sk_B
     != ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( r3_lattice3 @ sk_A @ sk_D_4 @ sk_C )
   <= ( r3_lattice3 @ sk_A @ sk_D_4 @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('9',plain,
    ( ( m1_subset_1 @ sk_D_4 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_4 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf(fraenkel_a_2_1_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( l3_lattices @ B ) )
     => ( ( r2_hidden @ A @ ( a_2_1_lattice3 @ B @ C ) )
      <=> ? [D: $i] :
            ( ( r3_lattice3 @ B @ D @ C )
            & ( A = D )
            & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('10',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( r2_hidden @ X22 @ ( a_2_1_lattice3 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X20 ) )
      | ( X22 != X23 )
      | ~ ( r3_lattice3 @ X20 @ X23 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_lattice3])).

thf('11',plain,(
    ! [X20: $i,X21: $i,X23: $i] :
      ( ~ ( r3_lattice3 @ X20 @ X23 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X20 ) )
      | ( r2_hidden @ X23 @ ( a_2_1_lattice3 @ X20 @ X21 ) )
      | ( v2_struct_0 @ X20 )
      | ~ ( l3_lattices @ X20 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ! [X0: $i] :
        ( ~ ( l3_lattices @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( r2_hidden @ sk_D_4 @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
        | ~ ( r3_lattice3 @ sk_A @ sk_D_4 @ X0 ) )
   <= ( m1_subset_1 @ sk_D_4 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_hidden @ sk_D_4 @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
        | ~ ( r3_lattice3 @ sk_A @ sk_D_4 @ X0 ) )
   <= ( m1_subset_1 @ sk_D_4 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ! [X0: $i] :
        ( ~ ( r3_lattice3 @ sk_A @ sk_D_4 @ X0 )
        | ( r2_hidden @ sk_D_4 @ ( a_2_1_lattice3 @ sk_A @ X0 ) ) )
   <= ( m1_subset_1 @ sk_D_4 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r2_hidden @ sk_D_4 @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
   <= ( ( r3_lattice3 @ sk_A @ sk_D_4 @ sk_C )
      & ( m1_subset_1 @ sk_D_4 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','16'])).

thf(d22_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( k16_lattice3 @ A @ B )
          = ( k15_lattice3 @ A @ ( a_2_1_lattice3 @ A @ B ) ) ) ) )).

thf('18',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k16_lattice3 @ X18 @ X19 )
        = ( k15_lattice3 @ X18 @ ( a_2_1_lattice3 @ X18 @ X19 ) ) )
      | ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d22_lattice3])).

thf('19',plain,
    ( ( r3_lattice3 @ sk_A @ sk_B @ sk_C )
    | ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) )
   <= ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k16_lattice3 @ X18 @ X19 )
        = ( k15_lattice3 @ X18 @ ( a_2_1_lattice3 @ X18 @ X19 ) ) )
      | ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d22_lattice3])).

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

thf('22',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( v10_lattices @ X14 )
      | ~ ( v4_lattice3 @ X14 )
      | ~ ( l3_lattices @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( X15
       != ( k15_lattice3 @ X14 @ X16 ) )
      | ( r4_lattice3 @ X14 @ X15 @ X16 )
      | ~ ( l3_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('23',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r4_lattice3 @ X14 @ ( k15_lattice3 @ X14 @ X16 ) @ X16 )
      | ~ ( m1_subset_1 @ ( k15_lattice3 @ X14 @ X16 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( l3_lattices @ X14 )
      | ~ ( v4_lattice3 @ X14 )
      | ~ ( v10_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( k16_lattice3 @ X1 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( r4_lattice3 @ X1 @ ( k15_lattice3 @ X1 @ ( a_2_1_lattice3 @ X1 @ X0 ) ) @ ( a_2_1_lattice3 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ X1 @ ( k15_lattice3 @ X1 @ ( a_2_1_lattice3 @ X1 @ X0 ) ) @ ( a_2_1_lattice3 @ X1 @ X0 ) )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_subset_1 @ ( k16_lattice3 @ X1 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
   <= ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
   <= ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['26','27','28','29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
   <= ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( r4_lattice3 @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C ) @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A ) )
   <= ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['18','33'])).

thf('35',plain,
    ( ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) )
   <= ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['19'])).

thf('36',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
   <= ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( m1_subset_1 @ sk_D_4 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_4 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('41',plain,(
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

thf('42',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( r4_lattice3 @ X10 @ X9 @ X11 )
      | ~ ( r2_hidden @ X12 @ X11 )
      | ( r1_lattices @ X10 @ X12 @ X9 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ X1 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ~ ( r4_lattice3 @ sk_A @ sk_B @ X0 )
        | ~ ( r2_hidden @ sk_D_4 @ X0 )
        | ( r1_lattices @ sk_A @ sk_D_4 @ sk_B )
        | ( v2_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_4 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r1_lattices @ sk_A @ sk_D_4 @ sk_B )
      | ~ ( r2_hidden @ sk_D_4 @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
   <= ( ( sk_B
        = ( k16_lattice3 @ sk_A @ sk_C ) )
      & ( m1_subset_1 @ sk_D_4 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ~ ( r2_hidden @ sk_D_4 @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
      | ( r1_lattices @ sk_A @ sk_D_4 @ sk_B ) )
   <= ( ( sk_B
        = ( k16_lattice3 @ sk_A @ sk_C ) )
      & ( m1_subset_1 @ sk_D_4 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( r1_lattices @ sk_A @ sk_D_4 @ sk_B )
   <= ( ( sk_B
        = ( k16_lattice3 @ sk_A @ sk_C ) )
      & ( r3_lattice3 @ sk_A @ sk_D_4 @ sk_C )
      & ( m1_subset_1 @ sk_D_4 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','49'])).

thf('51',plain,
    ( ( m1_subset_1 @ sk_D_4 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_4 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

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

thf('52',plain,(
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

thf('53',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_lattices @ sk_A @ sk_D_4 @ X0 )
        | ( r3_lattices @ sk_A @ sk_D_4 @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v6_lattices @ sk_A )
        | ~ ( v8_lattices @ sk_A )
        | ~ ( v9_lattices @ sk_A )
        | ~ ( l3_lattices @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_4 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

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

thf('54',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_lattices @ sk_A @ sk_D_4 @ X0 )
        | ( r3_lattices @ sk_A @ sk_D_4 @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_4 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','59','65','71','72'])).

thf('74',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r3_lattices @ sk_A @ sk_D_4 @ sk_B ) )
   <= ( ( sk_B
        = ( k16_lattice3 @ sk_A @ sk_C ) )
      & ( r3_lattice3 @ sk_A @ sk_D_4 @ sk_C )
      & ( m1_subset_1 @ sk_D_4 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['50','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r3_lattices @ sk_A @ sk_D_4 @ sk_B ) )
   <= ( ( sk_B
        = ( k16_lattice3 @ sk_A @ sk_C ) )
      & ( r3_lattice3 @ sk_A @ sk_D_4 @ sk_C )
      & ( m1_subset_1 @ sk_D_4 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( r3_lattices @ sk_A @ sk_D_4 @ sk_B )
   <= ( ( sk_B
        = ( k16_lattice3 @ sk_A @ sk_C ) )
      & ( r3_lattice3 @ sk_A @ sk_D_4 @ sk_C )
      & ( m1_subset_1 @ sk_D_4 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,
    ( ~ ( r3_lattices @ sk_A @ sk_D_4 @ sk_B )
   <= ~ ( r3_lattices @ sk_A @ sk_D_4 @ sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('80',plain,
    ( ( r3_lattices @ sk_A @ sk_D_4 @ sk_B )
    | ~ ( r3_lattice3 @ sk_A @ sk_D_4 @ sk_C )
    | ( sk_B
     != ( k16_lattice3 @ sk_A @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_D_4 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('82',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( m1_subset_1 @ ( sk_D @ X8 @ X4 @ X5 ) @ ( u1_struct_0 @ X5 ) )
      | ( r3_lattice3 @ X5 @ X4 @ X8 )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X4 @ X5 ) @ X8 )
      | ( r3_lattice3 @ X5 @ X4 @ X8 )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('97',plain,(
    ! [X9: $i,X10: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ( r2_hidden @ ( sk_D_1 @ X13 @ X9 @ X10 ) @ X13 )
      | ( r4_lattice3 @ X10 @ X9 @ X13 )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A ) @ X1 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( X22
        = ( sk_D_3 @ X21 @ X20 @ X22 ) )
      | ~ ( r2_hidden @ X22 @ ( a_2_1_lattice3 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_lattice3])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r4_lattice3 @ sk_A @ ( sk_D @ X2 @ sk_B @ sk_A ) @ ( a_2_1_lattice3 @ X1 @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ sk_B @ X2 )
      | ( ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ ( sk_D @ X2 @ sk_B @ sk_A ) @ sk_A )
        = ( sk_D_3 @ X0 @ X1 @ ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ ( sk_D @ X2 @ sk_B @ sk_A ) @ sk_A ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A ) @ X1 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('104',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( r3_lattice3 @ X20 @ ( sk_D_3 @ X21 @ X20 @ X22 ) @ X21 )
      | ~ ( r2_hidden @ X22 @ ( a_2_1_lattice3 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_lattice3])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r4_lattice3 @ sk_A @ ( sk_D @ X2 @ sk_B @ sk_A ) @ ( a_2_1_lattice3 @ X1 @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ sk_B @ X2 )
      | ( r3_lattice3 @ X1 @ ( sk_D_3 @ X0 @ X1 @ ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ ( sk_D @ X2 @ sk_B @ sk_A ) @ sk_A ) ) @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r3_lattice3 @ X2 @ ( sk_D_1 @ ( a_2_1_lattice3 @ X2 @ X1 ) @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A ) @ X1 )
      | ~ ( l3_lattices @ X2 )
      | ( v2_struct_0 @ X2 )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( a_2_1_lattice3 @ X2 @ X1 ) )
      | ~ ( l3_lattices @ X2 )
      | ( v2_struct_0 @ X2 )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( a_2_1_lattice3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['102','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r4_lattice3 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( a_2_1_lattice3 @ X2 @ X1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ X2 )
      | ~ ( l3_lattices @ X2 )
      | ( r3_lattice3 @ X2 @ ( sk_D_1 @ ( a_2_1_lattice3 @ X2 @ X1 ) @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('109',plain,(
    ! [X9: $i,X10: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X13 @ X9 @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ( r4_lattice3 @ X10 @ X9 @ X13 )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X1 )
      | ( m1_subset_1 @ ( sk_D_1 @ X1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X1 )
      | ( m1_subset_1 @ ( sk_D_1 @ X1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r3_lattice3 @ X5 @ X4 @ X6 )
      | ~ ( r2_hidden @ X7 @ X6 )
      | ( r1_lattices @ X5 @ X4 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r4_lattice3 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ X1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A ) @ X2 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_1 @ X1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r4_lattice3 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ X1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A ) @ X2 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_1 @ X1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A ) @ X3 ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r3_lattice3 @ sk_A @ ( sk_D_1 @ X1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A ) @ X3 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ X1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l3_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ sk_B @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( sk_D @ X1 @ sk_B @ sk_A ) @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ( r4_lattice3 @ sk_A @ ( sk_D @ X1 @ sk_B @ sk_A ) @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ X0 ) @ ( sk_D @ X1 @ sk_B @ sk_A ) @ sk_A ) @ X2 )
      | ~ ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['107','117'])).

thf('119',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ sk_B @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( sk_D @ X1 @ sk_B @ sk_A ) @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ( r4_lattice3 @ sk_A @ ( sk_D @ X1 @ sk_B @ sk_A ) @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ X0 ) @ ( sk_D @ X1 @ sk_B @ sk_A ) @ sk_A ) @ X2 )
      | ~ ( r2_hidden @ X2 @ X0 ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ X0 ) @ ( sk_D @ X1 @ sk_B @ sk_A ) @ sk_A ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) )
      | ( r4_lattice3 @ sk_A @ ( sk_D @ X1 @ sk_B @ sk_A ) @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ( r3_lattice3 @ sk_A @ sk_B @ X1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ sk_B @ X1 )
      | ( r4_lattice3 @ sk_A @ ( sk_D @ X1 @ sk_B @ sk_A ) @ ( a_2_1_lattice3 @ sk_A @ X2 ) )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ X2 ) @ ( sk_D @ X1 @ sk_B @ sk_A ) @ sk_A ) @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['95','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ X0 ) @ ( sk_D @ X1 @ sk_B @ sk_A ) @ sk_A ) @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( r4_lattice3 @ sk_A @ ( sk_D @ X1 @ sk_B @ sk_A ) @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ( r3_lattice3 @ sk_A @ sk_B @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ sk_B @ X1 )
      | ( r4_lattice3 @ sk_A @ ( sk_D @ X1 @ sk_B @ sk_A ) @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ X0 ) @ ( sk_D @ X1 @ sk_B @ sk_A ) @ sk_A ) @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('126',plain,(
    ! [X9: $i,X10: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( r1_lattices @ X10 @ ( sk_D_1 @ X13 @ X9 @ X10 ) @ X9 )
      | ( r4_lattice3 @ X10 @ X9 @ X13 )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X1 )
      | ~ ( r1_lattices @ sk_A @ ( sk_D_1 @ X1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A ) @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X1 )
      | ~ ( r1_lattices @ sk_A @ ( sk_D_1 @ X1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A ) @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r4_lattice3 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['124','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r4_lattice3 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( a_2_1_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) )
   <= ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['19'])).

thf('135',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k16_lattice3 @ X18 @ X19 )
        = ( k15_lattice3 @ X18 @ ( a_2_1_lattice3 @ X18 @ X19 ) ) )
      | ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d22_lattice3])).

thf('136',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( v10_lattices @ X14 )
      | ~ ( v4_lattice3 @ X14 )
      | ~ ( l3_lattices @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( X15
       != ( k15_lattice3 @ X14 @ X16 ) )
      | ~ ( r4_lattice3 @ X14 @ X17 @ X16 )
      | ( r1_lattices @ X14 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l3_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('137',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X14 ) )
      | ( r1_lattices @ X14 @ ( k15_lattice3 @ X14 @ X16 ) @ X17 )
      | ~ ( r4_lattice3 @ X14 @ X17 @ X16 )
      | ~ ( m1_subset_1 @ ( k15_lattice3 @ X14 @ X16 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( l3_lattices @ X14 )
      | ~ ( v4_lattice3 @ X14 )
      | ~ ( v10_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( k16_lattice3 @ X1 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( r4_lattice3 @ X1 @ X2 @ ( a_2_1_lattice3 @ X1 @ X0 ) )
      | ( r1_lattices @ X1 @ ( k15_lattice3 @ X1 @ ( a_2_1_lattice3 @ X1 @ X0 ) ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['135','137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r1_lattices @ X1 @ ( k15_lattice3 @ X1 @ ( a_2_1_lattice3 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r4_lattice3 @ X1 @ X2 @ ( a_2_1_lattice3 @ X1 @ X0 ) )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_subset_1 @ ( k16_lattice3 @ X1 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( l3_lattices @ sk_A )
        | ~ ( v10_lattices @ sk_A )
        | ~ ( v4_lattice3 @ sk_A )
        | ~ ( r4_lattice3 @ sk_A @ X0 @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
        | ( r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['134','139'])).

thf('141',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( r4_lattice3 @ sk_A @ X0 @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
        | ( r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['140','141','142','143','144'])).

thf('146',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k16_lattice3 @ X18 @ X19 )
        = ( k15_lattice3 @ X18 @ ( a_2_1_lattice3 @ X18 @ X19 ) ) )
      | ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d22_lattice3])).

thf('147',plain,
    ( ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
   <= ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('148',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( v10_lattices @ X14 )
      | ~ ( v4_lattice3 @ X14 )
      | ~ ( l3_lattices @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ~ ( r4_lattice3 @ X14 @ X15 @ X16 )
      | ( m1_subset_1 @ ( sk_D_2 @ X15 @ X16 @ X14 ) @ ( u1_struct_0 @ X14 ) )
      | ( X15
        = ( k15_lattice3 @ X14 @ X16 ) )
      | ~ ( l3_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('150',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X15
        = ( k15_lattice3 @ X14 @ X16 ) )
      | ( m1_subset_1 @ ( sk_D_2 @ X15 @ X16 @ X14 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( r4_lattice3 @ X14 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l3_lattices @ X14 )
      | ~ ( v4_lattice3 @ X14 )
      | ~ ( v10_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_B @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['148','150'])).

thf('152',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_B @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['151','152','153','154'])).

thf('156',plain,
    ( ( ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['147','155'])).

thf('157',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( ( m1_subset_1 @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
   <= ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('159',plain,
    ( ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
   <= ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('160',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( v10_lattices @ X14 )
      | ~ ( v4_lattice3 @ X14 )
      | ~ ( l3_lattices @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ~ ( r4_lattice3 @ X14 @ X15 @ X16 )
      | ( r4_lattice3 @ X14 @ ( sk_D_2 @ X15 @ X16 @ X14 ) @ X16 )
      | ( X15
        = ( k15_lattice3 @ X14 @ X16 ) )
      | ~ ( l3_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('162',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X15
        = ( k15_lattice3 @ X14 @ X16 ) )
      | ( r4_lattice3 @ X14 @ ( sk_D_2 @ X15 @ X16 @ X14 ) @ X16 )
      | ~ ( r4_lattice3 @ X14 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l3_lattices @ X14 )
      | ~ ( v4_lattice3 @ X14 )
      | ~ ( v10_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r4_lattice3 @ sk_A @ ( sk_D_2 @ sk_B @ X0 @ sk_A ) @ X0 )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['160','162'])).

thf('164',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r4_lattice3 @ sk_A @ ( sk_D_2 @ sk_B @ X0 @ sk_A ) @ X0 )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['163','164','165','166'])).

thf('168',plain,
    ( ( ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
      | ( r4_lattice3 @ sk_A @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['159','167'])).

thf('169',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( ( r4_lattice3 @ sk_A @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
   <= ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['168','169'])).

thf('171',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( r4_lattice3 @ sk_A @ X0 @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
        | ( r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['140','141','142','143','144'])).

thf('172',plain,
    ( ( ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
      | ~ ( m1_subset_1 @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,
    ( ( ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
   <= ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['158','172'])).

thf('174',plain,
    ( ( ( r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
   <= ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
      | ( r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) ) )
   <= ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['174','175'])).

thf('177',plain,
    ( ( ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C ) @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
   <= ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['146','176'])).

thf('178',plain,
    ( ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) )
   <= ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['19'])).

thf('179',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,
    ( ( ( r1_lattices @ sk_A @ sk_B @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
   <= ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['177','178','179'])).

thf('181',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ( ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
      | ( r1_lattices @ sk_A @ sk_B @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) ) )
   <= ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( v10_lattices @ X14 )
      | ~ ( v4_lattice3 @ X14 )
      | ~ ( l3_lattices @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ~ ( r4_lattice3 @ X14 @ X15 @ X16 )
      | ~ ( r1_lattices @ X14 @ X15 @ ( sk_D_2 @ X15 @ X16 @ X14 ) )
      | ( X15
        = ( k15_lattice3 @ X14 @ X16 ) )
      | ~ ( l3_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('184',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X15
        = ( k15_lattice3 @ X14 @ X16 ) )
      | ~ ( r1_lattices @ X14 @ X15 @ ( sk_D_2 @ X15 @ X16 @ X14 ) )
      | ~ ( r4_lattice3 @ X14 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l3_lattices @ X14 )
      | ~ ( v4_lattice3 @ X14 )
      | ~ ( v10_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(simplify,[status(thm)],['183'])).

thf('185',plain,
    ( ( ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
   <= ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['182','184'])).

thf('186',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
   <= ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('191',plain,
    ( ( ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
   <= ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['185','186','187','188','189','190'])).

thf('192',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
   <= ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(simplify,[status(thm)],['191'])).

thf('193',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ( sk_B
      = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
   <= ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['192','193'])).

thf('195',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( r4_lattice3 @ sk_A @ X0 @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
        | ( r1_lattices @ sk_A @ sk_B @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['145','194'])).

thf('196',plain,
    ( ( ( r3_lattice3 @ sk_A @ sk_B @ sk_C )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['133','195'])).

thf('197',plain,
    ( ( ( r3_lattice3 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( r1_lattices @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r3_lattice3 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['87','196'])).

thf('198',plain,
    ( ( ( r1_lattices @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(simplify,[status(thm)],['197'])).

thf('199',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r1_lattices @ X5 @ X4 @ ( sk_D @ X8 @ X4 @ X5 ) )
      | ( r3_lattice3 @ X5 @ X4 @ X8 )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('201',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_lattices @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_lattices @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('204',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['203','204'])).

thf('206',plain,
    ( ( ( r3_lattice3 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['198','205'])).

thf('207',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,
    ( ( r3_lattice3 @ sk_A @ sk_B @ sk_C )
   <= ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['206','207'])).

thf('209',plain,
    ( ~ ( r3_lattice3 @ sk_A @ sk_B @ sk_C )
   <= ~ ( r3_lattice3 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('210',plain,
    ( ( r3_lattice3 @ sk_A @ sk_B @ sk_C )
    | ( sk_B
     != ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['208','209'])).

thf('211',plain,
    ( ( r3_lattice3 @ sk_A @ sk_B @ sk_C )
    | ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['19'])).

thf('212',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k16_lattice3 @ X18 @ X19 )
        = ( k15_lattice3 @ X18 @ ( a_2_1_lattice3 @ X18 @ X19 ) ) )
      | ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d22_lattice3])).

thf('213',plain,
    ( ( r3_lattice3 @ sk_A @ sk_B @ sk_C )
   <= ( r3_lattice3 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['19'])).

thf('214',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    ! [X20: $i,X21: $i,X23: $i] :
      ( ~ ( r3_lattice3 @ X20 @ X23 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X20 ) )
      | ( r2_hidden @ X23 @ ( a_2_1_lattice3 @ X20 @ X21 ) )
      | ( v2_struct_0 @ X20 )
      | ~ ( l3_lattices @ X20 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('216',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('217',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['216','217'])).

thf('219',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(clc,[status(thm)],['218','219'])).

thf('221',plain,
    ( ( r2_hidden @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
   <= ( r3_lattice3 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['213','220'])).

thf('222',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,(
    ! [X9: $i,X10: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ( r2_hidden @ ( sk_D_1 @ X13 @ X9 @ X10 ) @ X13 )
      | ( r4_lattice3 @ X10 @ X9 @ X13 )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('224',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['222','223'])).

thf('225',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['224','225'])).

thf('227',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['226','227'])).

thf('229',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( X22
        = ( sk_D_3 @ X21 @ X20 @ X22 ) )
      | ~ ( r2_hidden @ X22 @ ( a_2_1_lattice3 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_lattice3])).

thf('230',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ X1 @ X0 ) )
      | ( ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A )
        = ( sk_D_3 @ X0 @ X1 @ ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['228','229'])).

thf('231',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['226','227'])).

thf('232',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( r3_lattice3 @ X20 @ ( sk_D_3 @ X21 @ X20 @ X22 ) @ X21 )
      | ~ ( r2_hidden @ X22 @ ( a_2_1_lattice3 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_lattice3])).

thf('233',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ X1 @ X0 ) )
      | ( r3_lattice3 @ X1 @ ( sk_D_3 @ X0 @ X1 @ ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A ) ) @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['231','232'])).

thf('234',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ X1 @ ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A ) @ X0 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['230','233'])).

thf('235',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ X1 @ X0 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( r3_lattice3 @ X1 @ ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['234'])).

thf('236',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,(
    ! [X9: $i,X10: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X13 @ X9 @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ( r4_lattice3 @ X10 @ X9 @ X13 )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('238',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['236','237'])).

thf('239',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['238','239'])).

thf('241',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['240','241'])).

thf('243',plain,
    ( ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_A ) )
        | ( r3_lattices @ sk_A @ X24 @ sk_B )
        | ~ ( r3_lattice3 @ sk_A @ X24 @ sk_C ) )
   <= ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_A ) )
        | ( r3_lattices @ sk_A @ X24 @ sk_B )
        | ~ ( r3_lattice3 @ sk_A @ X24 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('244',plain,
    ( ! [X0: $i] :
        ( ( r4_lattice3 @ sk_A @ sk_B @ X0 )
        | ~ ( r3_lattice3 @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_C )
        | ( r3_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_B ) )
   <= ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_A ) )
        | ( r3_lattices @ sk_A @ X24 @ sk_B )
        | ~ ( r3_lattice3 @ sk_A @ X24 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['242','243'])).

thf('245',plain,
    ( ( ~ ( l3_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
      | ( r3_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_B @ sk_A ) @ sk_B )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
   <= ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_A ) )
        | ( r3_lattices @ sk_A @ X24 @ sk_B )
        | ~ ( r3_lattice3 @ sk_A @ X24 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['235','244'])).

thf('246',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
      | ( r3_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_B @ sk_A ) @ sk_B )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
   <= ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_A ) )
        | ( r3_lattices @ sk_A @ X24 @ sk_B )
        | ~ ( r3_lattice3 @ sk_A @ X24 @ sk_C ) ) ),
    inference(demod,[status(thm)],['245','246'])).

thf('248',plain,
    ( ( ( r3_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_B @ sk_A ) @ sk_B )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_A ) )
        | ( r3_lattices @ sk_A @ X24 @ sk_B )
        | ~ ( r3_lattice3 @ sk_A @ X24 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['247'])).

thf('249',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('250',plain,
    ( ( ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
      | ( r3_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_B @ sk_A ) @ sk_B ) )
   <= ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_A ) )
        | ( r3_lattices @ sk_A @ X24 @ sk_B )
        | ~ ( r3_lattice3 @ sk_A @ X24 @ sk_C ) ) ),
    inference(clc,[status(thm)],['248','249'])).

thf('251',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['240','241'])).

thf('252',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l3_lattices @ X2 )
      | ~ ( v9_lattices @ X2 )
      | ~ ( v8_lattices @ X2 )
      | ~ ( v6_lattices @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( r1_lattices @ X2 @ X1 @ X3 )
      | ~ ( r3_lattices @ X2 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('253',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ~ ( r3_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X1 )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['251','252'])).

thf('254',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('255',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('256',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('257',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('258',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ~ ( r3_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X1 )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['253','254','255','256','257'])).

thf('259',plain,
    ( ( ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_B @ sk_A ) @ sk_B )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
   <= ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_A ) )
        | ( r3_lattices @ sk_A @ X24 @ sk_B )
        | ~ ( r3_lattice3 @ sk_A @ X24 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['250','258'])).

thf('260',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,
    ( ( ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_B @ sk_A ) @ sk_B )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
   <= ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_A ) )
        | ( r3_lattices @ sk_A @ X24 @ sk_B )
        | ~ ( r3_lattice3 @ sk_A @ X24 @ sk_C ) ) ),
    inference(demod,[status(thm)],['259','260'])).

thf('262',plain,
    ( ( ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
   <= ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_A ) )
        | ( r3_lattices @ sk_A @ X24 @ sk_B )
        | ~ ( r3_lattice3 @ sk_A @ X24 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['261'])).

thf('263',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,(
    ! [X9: $i,X10: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( r1_lattices @ X10 @ ( sk_D_1 @ X13 @ X9 @ X10 ) @ X9 )
      | ( r4_lattice3 @ X10 @ X9 @ X13 )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('265',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['263','264'])).

thf('266',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['265','266'])).

thf('268',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('269',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['267','268'])).

thf('270',plain,
    ( ( ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_A ) )
        | ( r3_lattices @ sk_A @ X24 @ sk_B )
        | ~ ( r3_lattice3 @ sk_A @ X24 @ sk_C ) ) ),
    inference(clc,[status(thm)],['262','269'])).

thf('271',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('272',plain,
    ( ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
   <= ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_A ) )
        | ( r3_lattices @ sk_A @ X24 @ sk_B )
        | ~ ( r3_lattice3 @ sk_A @ X24 @ sk_C ) ) ),
    inference(clc,[status(thm)],['270','271'])).

thf('273',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r4_lattice3 @ sk_A @ ( sk_D_2 @ sk_B @ X0 @ sk_A ) @ X0 )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['163','164','165','166'])).

thf('274',plain,
    ( ( ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
      | ( r4_lattice3 @ sk_A @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_A ) )
        | ( r3_lattices @ sk_A @ X24 @ sk_B )
        | ~ ( r3_lattice3 @ sk_A @ X24 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['272','273'])).

thf('275',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,
    ( ( ( r4_lattice3 @ sk_A @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
   <= ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_A ) )
        | ( r3_lattices @ sk_A @ X24 @ sk_B )
        | ~ ( r3_lattice3 @ sk_A @ X24 @ sk_C ) ) ),
    inference(clc,[status(thm)],['274','275'])).

thf('277',plain,
    ( ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
   <= ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_A ) )
        | ( r3_lattices @ sk_A @ X24 @ sk_B )
        | ~ ( r3_lattice3 @ sk_A @ X24 @ sk_C ) ) ),
    inference(clc,[status(thm)],['270','271'])).

thf('278',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_B @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['151','152','153','154'])).

thf('279',plain,
    ( ( ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_A ) )
        | ( r3_lattices @ sk_A @ X24 @ sk_B )
        | ~ ( r3_lattice3 @ sk_A @ X24 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['277','278'])).

thf('280',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,
    ( ( ( m1_subset_1 @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
   <= ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_A ) )
        | ( r3_lattices @ sk_A @ X24 @ sk_B )
        | ~ ( r3_lattice3 @ sk_A @ X24 @ sk_C ) ) ),
    inference(clc,[status(thm)],['279','280'])).

thf('282',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( r4_lattice3 @ X10 @ X9 @ X11 )
      | ~ ( r2_hidden @ X12 @ X11 )
      | ( r1_lattices @ X10 @ X12 @ X9 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('283',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( sk_B
          = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( l3_lattices @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_lattices @ sk_A @ X0 @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ X1 )
        | ~ ( r4_lattice3 @ sk_A @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) @ X1 ) )
   <= ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_A ) )
        | ( r3_lattices @ sk_A @ X24 @ sk_B )
        | ~ ( r3_lattice3 @ sk_A @ X24 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['281','282'])).

thf('284',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('285',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( sk_B
          = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_lattices @ sk_A @ X0 @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ X1 )
        | ~ ( r4_lattice3 @ sk_A @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) @ X1 ) )
   <= ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_A ) )
        | ( r3_lattices @ sk_A @ X24 @ sk_B )
        | ~ ( r3_lattice3 @ sk_A @ X24 @ sk_C ) ) ),
    inference(demod,[status(thm)],['283','284'])).

thf('286',plain,
    ( ! [X0: $i] :
        ( ( sk_B
          = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
        | ~ ( r2_hidden @ X0 @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
        | ( r1_lattices @ sk_A @ X0 @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( sk_B
          = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
   <= ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_A ) )
        | ( r3_lattices @ sk_A @ X24 @ sk_B )
        | ~ ( r3_lattice3 @ sk_A @ X24 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['276','285'])).

thf('287',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_lattices @ sk_A @ X0 @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
        | ( sk_B
          = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
   <= ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_A ) )
        | ( r3_lattices @ sk_A @ X24 @ sk_B )
        | ~ ( r3_lattice3 @ sk_A @ X24 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['286'])).

thf('288',plain,
    ( ( ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
      | ( r1_lattices @ sk_A @ sk_B @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r3_lattice3 @ sk_A @ sk_B @ sk_C )
      & ! [X24: $i] :
          ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_A ) )
          | ( r3_lattices @ sk_A @ X24 @ sk_B )
          | ~ ( r3_lattice3 @ sk_A @ X24 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['221','287'])).

thf('289',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('290',plain,
    ( ( ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
      | ( r1_lattices @ sk_A @ sk_B @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r3_lattice3 @ sk_A @ sk_B @ sk_C )
      & ! [X24: $i] :
          ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_A ) )
          | ( r3_lattices @ sk_A @ X24 @ sk_B )
          | ~ ( r3_lattice3 @ sk_A @ X24 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['288','289'])).

thf('291',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('292',plain,
    ( ( ( r1_lattices @ sk_A @ sk_B @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
   <= ( ( r3_lattice3 @ sk_A @ sk_B @ sk_C )
      & ! [X24: $i] :
          ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_A ) )
          | ( r3_lattices @ sk_A @ X24 @ sk_B )
          | ~ ( r3_lattice3 @ sk_A @ X24 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['290','291'])).

thf('293',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X15
        = ( k15_lattice3 @ X14 @ X16 ) )
      | ~ ( r1_lattices @ X14 @ X15 @ ( sk_D_2 @ X15 @ X16 @ X14 ) )
      | ~ ( r4_lattice3 @ X14 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l3_lattices @ X14 )
      | ~ ( v4_lattice3 @ X14 )
      | ~ ( v10_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(simplify,[status(thm)],['183'])).

thf('294',plain,
    ( ( ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
   <= ( ( r3_lattice3 @ sk_A @ sk_B @ sk_C )
      & ! [X24: $i] :
          ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_A ) )
          | ( r3_lattices @ sk_A @ X24 @ sk_B )
          | ~ ( r3_lattice3 @ sk_A @ X24 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['292','293'])).

thf('295',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('296',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('297',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('298',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('299',plain,
    ( ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
   <= ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_A ) )
        | ( r3_lattices @ sk_A @ X24 @ sk_B )
        | ~ ( r3_lattice3 @ sk_A @ X24 @ sk_C ) ) ),
    inference(clc,[status(thm)],['270','271'])).

thf('300',plain,
    ( ( ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
   <= ( ( r3_lattice3 @ sk_A @ sk_B @ sk_C )
      & ! [X24: $i] :
          ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_A ) )
          | ( r3_lattices @ sk_A @ X24 @ sk_B )
          | ~ ( r3_lattice3 @ sk_A @ X24 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['294','295','296','297','298','299'])).

thf('301',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) )
   <= ( ( r3_lattice3 @ sk_A @ sk_B @ sk_C )
      & ! [X24: $i] :
          ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_A ) )
          | ( r3_lattices @ sk_A @ X24 @ sk_B )
          | ~ ( r3_lattice3 @ sk_A @ X24 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['300'])).

thf('302',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('303',plain,
    ( ( sk_B
      = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
   <= ( ( r3_lattice3 @ sk_A @ sk_B @ sk_C )
      & ! [X24: $i] :
          ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_A ) )
          | ( r3_lattices @ sk_A @ X24 @ sk_B )
          | ~ ( r3_lattice3 @ sk_A @ X24 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['301','302'])).

thf('304',plain,
    ( ( ( sk_B
        = ( k16_lattice3 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A ) )
   <= ( ( r3_lattice3 @ sk_A @ sk_B @ sk_C )
      & ! [X24: $i] :
          ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_A ) )
          | ( r3_lattices @ sk_A @ X24 @ sk_B )
          | ~ ( r3_lattice3 @ sk_A @ X24 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['212','303'])).

thf('305',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('306',plain,
    ( ( ( sk_B
        = ( k16_lattice3 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r3_lattice3 @ sk_A @ sk_B @ sk_C )
      & ! [X24: $i] :
          ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_A ) )
          | ( r3_lattices @ sk_A @ X24 @ sk_B )
          | ~ ( r3_lattice3 @ sk_A @ X24 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['304','305'])).

thf('307',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('308',plain,
    ( ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) )
   <= ( ( r3_lattice3 @ sk_A @ sk_B @ sk_C )
      & ! [X24: $i] :
          ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_A ) )
          | ( r3_lattices @ sk_A @ X24 @ sk_B )
          | ~ ( r3_lattice3 @ sk_A @ X24 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['306','307'])).

thf('309',plain,
    ( ( sk_B
     != ( k16_lattice3 @ sk_A @ sk_C ) )
   <= ( sk_B
     != ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf('310',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B
       != ( k16_lattice3 @ sk_A @ sk_C ) )
      & ( r3_lattice3 @ sk_A @ sk_B @ sk_C )
      & ! [X24: $i] :
          ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_A ) )
          | ( r3_lattices @ sk_A @ X24 @ sk_B )
          | ~ ( r3_lattice3 @ sk_A @ X24 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['308','309'])).

thf('311',plain,
    ( ~ ( r3_lattice3 @ sk_A @ sk_B @ sk_C )
    | ~ ! [X24: $i] :
          ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ sk_A ) )
          | ( r3_lattices @ sk_A @ X24 @ sk_B )
          | ~ ( r3_lattice3 @ sk_A @ X24 @ sk_C ) )
    | ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(simplify,[status(thm)],['310'])).

thf('312',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','80','210','211','311'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jekBkEvauJ
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:27:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.48/4.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.48/4.68  % Solved by: fo/fo7.sh
% 4.48/4.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.48/4.68  % done 3844 iterations in 4.199s
% 4.48/4.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.48/4.68  % SZS output start Refutation
% 4.48/4.68  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 4.48/4.68  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 4.48/4.68  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 4.48/4.68  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 4.48/4.68  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 4.48/4.68  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 4.48/4.68  thf(sk_C_type, type, sk_C: $i).
% 4.48/4.68  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 4.48/4.68  thf(a_2_1_lattice3_type, type, a_2_1_lattice3: $i > $i > $i).
% 4.48/4.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.48/4.68  thf(r3_lattice3_type, type, r3_lattice3: $i > $i > $i > $o).
% 4.48/4.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.48/4.68  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i > $i).
% 4.48/4.68  thf(r4_lattice3_type, type, r4_lattice3: $i > $i > $i > $o).
% 4.48/4.68  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 4.48/4.68  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 4.48/4.68  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 4.48/4.68  thf(sk_A_type, type, sk_A: $i).
% 4.48/4.68  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 4.48/4.68  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 4.48/4.68  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 4.48/4.68  thf(sk_B_type, type, sk_B: $i).
% 4.48/4.68  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 4.48/4.68  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 4.48/4.68  thf(sk_D_4_type, type, sk_D_4: $i).
% 4.48/4.68  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 4.48/4.68  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 4.48/4.68  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 4.48/4.68  thf(t34_lattice3, conjecture,
% 4.48/4.68    (![A:$i]:
% 4.48/4.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 4.48/4.68         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 4.48/4.68       ( ![B:$i]:
% 4.48/4.68         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 4.48/4.68           ( ![C:$i]:
% 4.48/4.68             ( ( ( B ) = ( k16_lattice3 @ A @ C ) ) <=>
% 4.48/4.68               ( ( r3_lattice3 @ A @ B @ C ) & 
% 4.48/4.68                 ( ![D:$i]:
% 4.48/4.68                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 4.48/4.68                     ( ( r3_lattice3 @ A @ D @ C ) =>
% 4.48/4.68                       ( r3_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 4.48/4.68  thf(zf_stmt_0, negated_conjecture,
% 4.48/4.68    (~( ![A:$i]:
% 4.48/4.68        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 4.48/4.68            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 4.48/4.68          ( ![B:$i]:
% 4.48/4.68            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 4.48/4.68              ( ![C:$i]:
% 4.48/4.68                ( ( ( B ) = ( k16_lattice3 @ A @ C ) ) <=>
% 4.48/4.68                  ( ( r3_lattice3 @ A @ B @ C ) & 
% 4.48/4.68                    ( ![D:$i]:
% 4.48/4.68                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 4.48/4.68                        ( ( r3_lattice3 @ A @ D @ C ) =>
% 4.48/4.68                          ( r3_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ) ) )),
% 4.48/4.68    inference('cnf.neg', [status(esa)], [t34_lattice3])).
% 4.48/4.68  thf('0', plain,
% 4.48/4.68      (![X24 : $i]:
% 4.48/4.68         (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_A))
% 4.48/4.68          | (r3_lattices @ sk_A @ X24 @ sk_B)
% 4.48/4.68          | ~ (r3_lattice3 @ sk_A @ X24 @ sk_C)
% 4.48/4.68          | ((sk_B) = (k16_lattice3 @ sk_A @ sk_C)))),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('1', plain,
% 4.48/4.68      ((![X24 : $i]:
% 4.48/4.68          (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_A))
% 4.48/4.68           | (r3_lattices @ sk_A @ X24 @ sk_B)
% 4.48/4.68           | ~ (r3_lattice3 @ sk_A @ X24 @ sk_C))) | 
% 4.48/4.68       (((sk_B) = (k16_lattice3 @ sk_A @ sk_C)))),
% 4.48/4.68      inference('split', [status(esa)], ['0'])).
% 4.48/4.68  thf('2', plain,
% 4.48/4.68      (((r3_lattice3 @ sk_A @ sk_D_4 @ sk_C)
% 4.48/4.68        | ~ (r3_lattice3 @ sk_A @ sk_B @ sk_C)
% 4.48/4.68        | ((sk_B) != (k16_lattice3 @ sk_A @ sk_C)))),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('3', plain,
% 4.48/4.68      (((r3_lattice3 @ sk_A @ sk_D_4 @ sk_C)) | 
% 4.48/4.68       ~ ((r3_lattice3 @ sk_A @ sk_B @ sk_C)) | 
% 4.48/4.68       ~ (((sk_B) = (k16_lattice3 @ sk_A @ sk_C)))),
% 4.48/4.68      inference('split', [status(esa)], ['2'])).
% 4.48/4.68  thf('4', plain,
% 4.48/4.68      (((m1_subset_1 @ sk_D_4 @ (u1_struct_0 @ sk_A))
% 4.48/4.68        | ~ (r3_lattice3 @ sk_A @ sk_B @ sk_C)
% 4.48/4.68        | ((sk_B) != (k16_lattice3 @ sk_A @ sk_C)))),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('5', plain,
% 4.48/4.68      (((m1_subset_1 @ sk_D_4 @ (u1_struct_0 @ sk_A))) | 
% 4.48/4.68       ~ ((r3_lattice3 @ sk_A @ sk_B @ sk_C)) | 
% 4.48/4.68       ~ (((sk_B) = (k16_lattice3 @ sk_A @ sk_C)))),
% 4.48/4.68      inference('split', [status(esa)], ['4'])).
% 4.48/4.68  thf('6', plain,
% 4.48/4.68      ((~ (r3_lattices @ sk_A @ sk_D_4 @ sk_B)
% 4.48/4.68        | ~ (r3_lattice3 @ sk_A @ sk_B @ sk_C)
% 4.48/4.68        | ((sk_B) != (k16_lattice3 @ sk_A @ sk_C)))),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('7', plain,
% 4.48/4.68      (~ ((r3_lattice3 @ sk_A @ sk_B @ sk_C)) | 
% 4.48/4.68       ~ ((r3_lattices @ sk_A @ sk_D_4 @ sk_B)) | 
% 4.48/4.68       ~ (((sk_B) = (k16_lattice3 @ sk_A @ sk_C)))),
% 4.48/4.68      inference('split', [status(esa)], ['6'])).
% 4.48/4.68  thf('8', plain,
% 4.48/4.68      (((r3_lattice3 @ sk_A @ sk_D_4 @ sk_C))
% 4.48/4.68         <= (((r3_lattice3 @ sk_A @ sk_D_4 @ sk_C)))),
% 4.48/4.68      inference('split', [status(esa)], ['2'])).
% 4.48/4.68  thf('9', plain,
% 4.48/4.68      (((m1_subset_1 @ sk_D_4 @ (u1_struct_0 @ sk_A)))
% 4.48/4.68         <= (((m1_subset_1 @ sk_D_4 @ (u1_struct_0 @ sk_A))))),
% 4.48/4.68      inference('split', [status(esa)], ['4'])).
% 4.48/4.68  thf(fraenkel_a_2_1_lattice3, axiom,
% 4.48/4.68    (![A:$i,B:$i,C:$i]:
% 4.48/4.68     ( ( ( ~( v2_struct_0 @ B ) ) & ( l3_lattices @ B ) ) =>
% 4.48/4.68       ( ( r2_hidden @ A @ ( a_2_1_lattice3 @ B @ C ) ) <=>
% 4.48/4.68         ( ?[D:$i]:
% 4.48/4.68           ( ( r3_lattice3 @ B @ D @ C ) & ( ( A ) = ( D ) ) & 
% 4.48/4.68             ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 4.48/4.68  thf('10', plain,
% 4.48/4.68      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 4.48/4.68         (~ (l3_lattices @ X20)
% 4.48/4.68          | (v2_struct_0 @ X20)
% 4.48/4.68          | (r2_hidden @ X22 @ (a_2_1_lattice3 @ X20 @ X21))
% 4.48/4.68          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X20))
% 4.48/4.68          | ((X22) != (X23))
% 4.48/4.68          | ~ (r3_lattice3 @ X20 @ X23 @ X21))),
% 4.48/4.68      inference('cnf', [status(esa)], [fraenkel_a_2_1_lattice3])).
% 4.48/4.68  thf('11', plain,
% 4.48/4.68      (![X20 : $i, X21 : $i, X23 : $i]:
% 4.48/4.68         (~ (r3_lattice3 @ X20 @ X23 @ X21)
% 4.48/4.68          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X20))
% 4.48/4.68          | (r2_hidden @ X23 @ (a_2_1_lattice3 @ X20 @ X21))
% 4.48/4.68          | (v2_struct_0 @ X20)
% 4.48/4.68          | ~ (l3_lattices @ X20))),
% 4.48/4.68      inference('simplify', [status(thm)], ['10'])).
% 4.48/4.68  thf('12', plain,
% 4.48/4.68      ((![X0 : $i]:
% 4.48/4.68          (~ (l3_lattices @ sk_A)
% 4.48/4.68           | (v2_struct_0 @ sk_A)
% 4.48/4.68           | (r2_hidden @ sk_D_4 @ (a_2_1_lattice3 @ sk_A @ X0))
% 4.48/4.68           | ~ (r3_lattice3 @ sk_A @ sk_D_4 @ X0)))
% 4.48/4.68         <= (((m1_subset_1 @ sk_D_4 @ (u1_struct_0 @ sk_A))))),
% 4.48/4.68      inference('sup-', [status(thm)], ['9', '11'])).
% 4.48/4.68  thf('13', plain, ((l3_lattices @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('14', plain,
% 4.48/4.68      ((![X0 : $i]:
% 4.48/4.68          ((v2_struct_0 @ sk_A)
% 4.48/4.68           | (r2_hidden @ sk_D_4 @ (a_2_1_lattice3 @ sk_A @ X0))
% 4.48/4.68           | ~ (r3_lattice3 @ sk_A @ sk_D_4 @ X0)))
% 4.48/4.68         <= (((m1_subset_1 @ sk_D_4 @ (u1_struct_0 @ sk_A))))),
% 4.48/4.68      inference('demod', [status(thm)], ['12', '13'])).
% 4.48/4.68  thf('15', plain, (~ (v2_struct_0 @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('16', plain,
% 4.48/4.68      ((![X0 : $i]:
% 4.48/4.68          (~ (r3_lattice3 @ sk_A @ sk_D_4 @ X0)
% 4.48/4.68           | (r2_hidden @ sk_D_4 @ (a_2_1_lattice3 @ sk_A @ X0))))
% 4.48/4.68         <= (((m1_subset_1 @ sk_D_4 @ (u1_struct_0 @ sk_A))))),
% 4.48/4.68      inference('clc', [status(thm)], ['14', '15'])).
% 4.48/4.68  thf('17', plain,
% 4.48/4.68      (((r2_hidden @ sk_D_4 @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 4.48/4.68         <= (((r3_lattice3 @ sk_A @ sk_D_4 @ sk_C)) & 
% 4.48/4.68             ((m1_subset_1 @ sk_D_4 @ (u1_struct_0 @ sk_A))))),
% 4.48/4.68      inference('sup-', [status(thm)], ['8', '16'])).
% 4.48/4.68  thf(d22_lattice3, axiom,
% 4.48/4.68    (![A:$i]:
% 4.48/4.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 4.48/4.68       ( ![B:$i]:
% 4.48/4.68         ( ( k16_lattice3 @ A @ B ) =
% 4.48/4.68           ( k15_lattice3 @ A @ ( a_2_1_lattice3 @ A @ B ) ) ) ) ))).
% 4.48/4.68  thf('18', plain,
% 4.48/4.68      (![X18 : $i, X19 : $i]:
% 4.48/4.68         (((k16_lattice3 @ X18 @ X19)
% 4.48/4.68            = (k15_lattice3 @ X18 @ (a_2_1_lattice3 @ X18 @ X19)))
% 4.48/4.68          | ~ (l3_lattices @ X18)
% 4.48/4.68          | (v2_struct_0 @ X18))),
% 4.48/4.68      inference('cnf', [status(esa)], [d22_lattice3])).
% 4.48/4.68  thf('19', plain,
% 4.48/4.68      (((r3_lattice3 @ sk_A @ sk_B @ sk_C)
% 4.48/4.68        | ((sk_B) = (k16_lattice3 @ sk_A @ sk_C)))),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('20', plain,
% 4.48/4.68      ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C)))
% 4.48/4.68         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))))),
% 4.48/4.68      inference('split', [status(esa)], ['19'])).
% 4.48/4.68  thf('21', plain,
% 4.48/4.68      (![X18 : $i, X19 : $i]:
% 4.48/4.68         (((k16_lattice3 @ X18 @ X19)
% 4.48/4.68            = (k15_lattice3 @ X18 @ (a_2_1_lattice3 @ X18 @ X19)))
% 4.48/4.68          | ~ (l3_lattices @ X18)
% 4.48/4.68          | (v2_struct_0 @ X18))),
% 4.48/4.68      inference('cnf', [status(esa)], [d22_lattice3])).
% 4.48/4.68  thf(d21_lattice3, axiom,
% 4.48/4.68    (![A:$i]:
% 4.48/4.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 4.48/4.68       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 4.48/4.68           ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 4.48/4.68         ( ![B:$i,C:$i]:
% 4.48/4.68           ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 4.48/4.68             ( ( ( C ) = ( k15_lattice3 @ A @ B ) ) <=>
% 4.48/4.68               ( ( r4_lattice3 @ A @ C @ B ) & 
% 4.48/4.68                 ( ![D:$i]:
% 4.48/4.68                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 4.48/4.68                     ( ( r4_lattice3 @ A @ D @ B ) =>
% 4.48/4.68                       ( r1_lattices @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 4.48/4.68  thf('22', plain,
% 4.48/4.68      (![X14 : $i, X15 : $i, X16 : $i]:
% 4.48/4.68         ((v2_struct_0 @ X14)
% 4.48/4.68          | ~ (v10_lattices @ X14)
% 4.48/4.68          | ~ (v4_lattice3 @ X14)
% 4.48/4.68          | ~ (l3_lattices @ X14)
% 4.48/4.68          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 4.48/4.68          | ((X15) != (k15_lattice3 @ X14 @ X16))
% 4.48/4.68          | (r4_lattice3 @ X14 @ X15 @ X16)
% 4.48/4.68          | ~ (l3_lattices @ X14)
% 4.48/4.68          | (v2_struct_0 @ X14))),
% 4.48/4.68      inference('cnf', [status(esa)], [d21_lattice3])).
% 4.48/4.68  thf('23', plain,
% 4.48/4.68      (![X14 : $i, X16 : $i]:
% 4.48/4.68         ((r4_lattice3 @ X14 @ (k15_lattice3 @ X14 @ X16) @ X16)
% 4.48/4.68          | ~ (m1_subset_1 @ (k15_lattice3 @ X14 @ X16) @ (u1_struct_0 @ X14))
% 4.48/4.68          | ~ (l3_lattices @ X14)
% 4.48/4.68          | ~ (v4_lattice3 @ X14)
% 4.48/4.68          | ~ (v10_lattices @ X14)
% 4.48/4.68          | (v2_struct_0 @ X14))),
% 4.48/4.68      inference('simplify', [status(thm)], ['22'])).
% 4.48/4.68  thf('24', plain,
% 4.48/4.68      (![X0 : $i, X1 : $i]:
% 4.48/4.68         (~ (m1_subset_1 @ (k16_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1))
% 4.48/4.68          | (v2_struct_0 @ X1)
% 4.48/4.68          | ~ (l3_lattices @ X1)
% 4.48/4.68          | (v2_struct_0 @ X1)
% 4.48/4.68          | ~ (v10_lattices @ X1)
% 4.48/4.68          | ~ (v4_lattice3 @ X1)
% 4.48/4.68          | ~ (l3_lattices @ X1)
% 4.48/4.68          | (r4_lattice3 @ X1 @ 
% 4.48/4.68             (k15_lattice3 @ X1 @ (a_2_1_lattice3 @ X1 @ X0)) @ 
% 4.48/4.68             (a_2_1_lattice3 @ X1 @ X0)))),
% 4.48/4.68      inference('sup-', [status(thm)], ['21', '23'])).
% 4.48/4.68  thf('25', plain,
% 4.48/4.68      (![X0 : $i, X1 : $i]:
% 4.48/4.68         ((r4_lattice3 @ X1 @ 
% 4.48/4.68           (k15_lattice3 @ X1 @ (a_2_1_lattice3 @ X1 @ X0)) @ 
% 4.48/4.68           (a_2_1_lattice3 @ X1 @ X0))
% 4.48/4.68          | ~ (v4_lattice3 @ X1)
% 4.48/4.68          | ~ (v10_lattices @ X1)
% 4.48/4.68          | ~ (l3_lattices @ X1)
% 4.48/4.68          | (v2_struct_0 @ X1)
% 4.48/4.68          | ~ (m1_subset_1 @ (k16_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1)))),
% 4.48/4.68      inference('simplify', [status(thm)], ['24'])).
% 4.48/4.68  thf('26', plain,
% 4.48/4.68      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 4.48/4.68         | (v2_struct_0 @ sk_A)
% 4.48/4.68         | ~ (l3_lattices @ sk_A)
% 4.48/4.68         | ~ (v10_lattices @ sk_A)
% 4.48/4.68         | ~ (v4_lattice3 @ sk_A)
% 4.48/4.68         | (r4_lattice3 @ sk_A @ 
% 4.48/4.68            (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) @ 
% 4.48/4.68            (a_2_1_lattice3 @ sk_A @ sk_C))))
% 4.48/4.68         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))))),
% 4.48/4.68      inference('sup-', [status(thm)], ['20', '25'])).
% 4.48/4.68  thf('27', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('28', plain, ((l3_lattices @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('29', plain, ((v10_lattices @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('30', plain, ((v4_lattice3 @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('31', plain,
% 4.48/4.68      ((((v2_struct_0 @ sk_A)
% 4.48/4.68         | (r4_lattice3 @ sk_A @ 
% 4.48/4.68            (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) @ 
% 4.48/4.68            (a_2_1_lattice3 @ sk_A @ sk_C))))
% 4.48/4.68         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))))),
% 4.48/4.68      inference('demod', [status(thm)], ['26', '27', '28', '29', '30'])).
% 4.48/4.68  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('33', plain,
% 4.48/4.68      (((r4_lattice3 @ sk_A @ 
% 4.48/4.68         (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) @ 
% 4.48/4.68         (a_2_1_lattice3 @ sk_A @ sk_C)))
% 4.48/4.68         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))))),
% 4.48/4.68      inference('clc', [status(thm)], ['31', '32'])).
% 4.48/4.68  thf('34', plain,
% 4.48/4.68      ((((r4_lattice3 @ sk_A @ (k16_lattice3 @ sk_A @ sk_C) @ 
% 4.48/4.68          (a_2_1_lattice3 @ sk_A @ sk_C))
% 4.48/4.68         | (v2_struct_0 @ sk_A)
% 4.48/4.68         | ~ (l3_lattices @ sk_A)))
% 4.48/4.68         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))))),
% 4.48/4.68      inference('sup+', [status(thm)], ['18', '33'])).
% 4.48/4.68  thf('35', plain,
% 4.48/4.68      ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C)))
% 4.48/4.68         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))))),
% 4.48/4.68      inference('split', [status(esa)], ['19'])).
% 4.48/4.68  thf('36', plain, ((l3_lattices @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('37', plain,
% 4.48/4.68      ((((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))
% 4.48/4.68         | (v2_struct_0 @ sk_A)))
% 4.48/4.68         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))))),
% 4.48/4.68      inference('demod', [status(thm)], ['34', '35', '36'])).
% 4.48/4.68  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('39', plain,
% 4.48/4.68      (((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 4.48/4.68         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))))),
% 4.48/4.68      inference('clc', [status(thm)], ['37', '38'])).
% 4.48/4.68  thf('40', plain,
% 4.48/4.68      (((m1_subset_1 @ sk_D_4 @ (u1_struct_0 @ sk_A)))
% 4.48/4.68         <= (((m1_subset_1 @ sk_D_4 @ (u1_struct_0 @ sk_A))))),
% 4.48/4.68      inference('split', [status(esa)], ['4'])).
% 4.48/4.68  thf('41', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf(d17_lattice3, axiom,
% 4.48/4.68    (![A:$i]:
% 4.48/4.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 4.48/4.68       ( ![B:$i]:
% 4.48/4.68         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 4.48/4.68           ( ![C:$i]:
% 4.48/4.68             ( ( r4_lattice3 @ A @ B @ C ) <=>
% 4.48/4.68               ( ![D:$i]:
% 4.48/4.68                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 4.48/4.68                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ))).
% 4.48/4.68  thf('42', plain,
% 4.48/4.68      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 4.48/4.68         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 4.48/4.68          | ~ (r4_lattice3 @ X10 @ X9 @ X11)
% 4.48/4.68          | ~ (r2_hidden @ X12 @ X11)
% 4.48/4.68          | (r1_lattices @ X10 @ X12 @ X9)
% 4.48/4.68          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X10))
% 4.48/4.68          | ~ (l3_lattices @ X10)
% 4.48/4.68          | (v2_struct_0 @ X10))),
% 4.48/4.68      inference('cnf', [status(esa)], [d17_lattice3])).
% 4.48/4.68  thf('43', plain,
% 4.48/4.68      (![X0 : $i, X1 : $i]:
% 4.48/4.68         ((v2_struct_0 @ sk_A)
% 4.48/4.68          | ~ (l3_lattices @ sk_A)
% 4.48/4.68          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 4.48/4.68          | (r1_lattices @ sk_A @ X0 @ sk_B)
% 4.48/4.68          | ~ (r2_hidden @ X0 @ X1)
% 4.48/4.68          | ~ (r4_lattice3 @ sk_A @ sk_B @ X1))),
% 4.48/4.68      inference('sup-', [status(thm)], ['41', '42'])).
% 4.48/4.68  thf('44', plain, ((l3_lattices @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('45', plain,
% 4.48/4.68      (![X0 : $i, X1 : $i]:
% 4.48/4.68         ((v2_struct_0 @ sk_A)
% 4.48/4.68          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 4.48/4.68          | (r1_lattices @ sk_A @ X0 @ sk_B)
% 4.48/4.68          | ~ (r2_hidden @ X0 @ X1)
% 4.48/4.68          | ~ (r4_lattice3 @ sk_A @ sk_B @ X1))),
% 4.48/4.68      inference('demod', [status(thm)], ['43', '44'])).
% 4.48/4.68  thf('46', plain,
% 4.48/4.68      ((![X0 : $i]:
% 4.48/4.68          (~ (r4_lattice3 @ sk_A @ sk_B @ X0)
% 4.48/4.68           | ~ (r2_hidden @ sk_D_4 @ X0)
% 4.48/4.68           | (r1_lattices @ sk_A @ sk_D_4 @ sk_B)
% 4.48/4.68           | (v2_struct_0 @ sk_A)))
% 4.48/4.68         <= (((m1_subset_1 @ sk_D_4 @ (u1_struct_0 @ sk_A))))),
% 4.48/4.68      inference('sup-', [status(thm)], ['40', '45'])).
% 4.48/4.68  thf('47', plain,
% 4.48/4.68      ((((v2_struct_0 @ sk_A)
% 4.48/4.68         | (r1_lattices @ sk_A @ sk_D_4 @ sk_B)
% 4.48/4.68         | ~ (r2_hidden @ sk_D_4 @ (a_2_1_lattice3 @ sk_A @ sk_C))))
% 4.48/4.68         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))) & 
% 4.48/4.68             ((m1_subset_1 @ sk_D_4 @ (u1_struct_0 @ sk_A))))),
% 4.48/4.68      inference('sup-', [status(thm)], ['39', '46'])).
% 4.48/4.68  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('49', plain,
% 4.48/4.68      (((~ (r2_hidden @ sk_D_4 @ (a_2_1_lattice3 @ sk_A @ sk_C))
% 4.48/4.68         | (r1_lattices @ sk_A @ sk_D_4 @ sk_B)))
% 4.48/4.68         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))) & 
% 4.48/4.68             ((m1_subset_1 @ sk_D_4 @ (u1_struct_0 @ sk_A))))),
% 4.48/4.68      inference('clc', [status(thm)], ['47', '48'])).
% 4.48/4.68  thf('50', plain,
% 4.48/4.68      (((r1_lattices @ sk_A @ sk_D_4 @ sk_B))
% 4.48/4.68         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))) & 
% 4.48/4.68             ((r3_lattice3 @ sk_A @ sk_D_4 @ sk_C)) & 
% 4.48/4.68             ((m1_subset_1 @ sk_D_4 @ (u1_struct_0 @ sk_A))))),
% 4.48/4.68      inference('sup-', [status(thm)], ['17', '49'])).
% 4.48/4.68  thf('51', plain,
% 4.48/4.68      (((m1_subset_1 @ sk_D_4 @ (u1_struct_0 @ sk_A)))
% 4.48/4.68         <= (((m1_subset_1 @ sk_D_4 @ (u1_struct_0 @ sk_A))))),
% 4.48/4.68      inference('split', [status(esa)], ['4'])).
% 4.48/4.68  thf(redefinition_r3_lattices, axiom,
% 4.48/4.68    (![A:$i,B:$i,C:$i]:
% 4.48/4.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 4.48/4.68         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 4.48/4.68         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 4.48/4.68         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 4.48/4.68       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 4.48/4.68  thf('52', plain,
% 4.48/4.68      (![X1 : $i, X2 : $i, X3 : $i]:
% 4.48/4.68         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 4.48/4.68          | ~ (l3_lattices @ X2)
% 4.48/4.68          | ~ (v9_lattices @ X2)
% 4.48/4.68          | ~ (v8_lattices @ X2)
% 4.48/4.68          | ~ (v6_lattices @ X2)
% 4.48/4.68          | (v2_struct_0 @ X2)
% 4.48/4.68          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 4.48/4.68          | (r3_lattices @ X2 @ X1 @ X3)
% 4.48/4.68          | ~ (r1_lattices @ X2 @ X1 @ X3))),
% 4.48/4.68      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 4.48/4.68  thf('53', plain,
% 4.48/4.68      ((![X0 : $i]:
% 4.48/4.68          (~ (r1_lattices @ sk_A @ sk_D_4 @ X0)
% 4.48/4.68           | (r3_lattices @ sk_A @ sk_D_4 @ X0)
% 4.48/4.68           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 4.48/4.68           | (v2_struct_0 @ sk_A)
% 4.48/4.68           | ~ (v6_lattices @ sk_A)
% 4.48/4.68           | ~ (v8_lattices @ sk_A)
% 4.48/4.68           | ~ (v9_lattices @ sk_A)
% 4.48/4.68           | ~ (l3_lattices @ sk_A)))
% 4.48/4.68         <= (((m1_subset_1 @ sk_D_4 @ (u1_struct_0 @ sk_A))))),
% 4.48/4.68      inference('sup-', [status(thm)], ['51', '52'])).
% 4.48/4.68  thf(cc1_lattices, axiom,
% 4.48/4.68    (![A:$i]:
% 4.48/4.68     ( ( l3_lattices @ A ) =>
% 4.48/4.68       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 4.48/4.68         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 4.48/4.68           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 4.48/4.68           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 4.48/4.68  thf('54', plain,
% 4.48/4.68      (![X0 : $i]:
% 4.48/4.68         ((v2_struct_0 @ X0)
% 4.48/4.68          | ~ (v10_lattices @ X0)
% 4.48/4.68          | (v6_lattices @ X0)
% 4.48/4.68          | ~ (l3_lattices @ X0))),
% 4.48/4.68      inference('cnf', [status(esa)], [cc1_lattices])).
% 4.48/4.68  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('56', plain,
% 4.48/4.68      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 4.48/4.68      inference('sup-', [status(thm)], ['54', '55'])).
% 4.48/4.68  thf('57', plain, ((l3_lattices @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('58', plain, ((v10_lattices @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('59', plain, ((v6_lattices @ sk_A)),
% 4.48/4.68      inference('demod', [status(thm)], ['56', '57', '58'])).
% 4.48/4.68  thf('60', plain,
% 4.48/4.68      (![X0 : $i]:
% 4.48/4.68         ((v2_struct_0 @ X0)
% 4.48/4.68          | ~ (v10_lattices @ X0)
% 4.48/4.68          | (v8_lattices @ X0)
% 4.48/4.68          | ~ (l3_lattices @ X0))),
% 4.48/4.68      inference('cnf', [status(esa)], [cc1_lattices])).
% 4.48/4.68  thf('61', plain, (~ (v2_struct_0 @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('62', plain,
% 4.48/4.68      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 4.48/4.68      inference('sup-', [status(thm)], ['60', '61'])).
% 4.48/4.68  thf('63', plain, ((l3_lattices @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('64', plain, ((v10_lattices @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('65', plain, ((v8_lattices @ sk_A)),
% 4.48/4.68      inference('demod', [status(thm)], ['62', '63', '64'])).
% 4.48/4.68  thf('66', plain,
% 4.48/4.68      (![X0 : $i]:
% 4.48/4.68         ((v2_struct_0 @ X0)
% 4.48/4.68          | ~ (v10_lattices @ X0)
% 4.48/4.68          | (v9_lattices @ X0)
% 4.48/4.68          | ~ (l3_lattices @ X0))),
% 4.48/4.68      inference('cnf', [status(esa)], [cc1_lattices])).
% 4.48/4.68  thf('67', plain, (~ (v2_struct_0 @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('68', plain,
% 4.48/4.68      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 4.48/4.68      inference('sup-', [status(thm)], ['66', '67'])).
% 4.48/4.68  thf('69', plain, ((l3_lattices @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('70', plain, ((v10_lattices @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('71', plain, ((v9_lattices @ sk_A)),
% 4.48/4.68      inference('demod', [status(thm)], ['68', '69', '70'])).
% 4.48/4.68  thf('72', plain, ((l3_lattices @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('73', plain,
% 4.48/4.68      ((![X0 : $i]:
% 4.48/4.68          (~ (r1_lattices @ sk_A @ sk_D_4 @ X0)
% 4.48/4.68           | (r3_lattices @ sk_A @ sk_D_4 @ X0)
% 4.48/4.68           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 4.48/4.68           | (v2_struct_0 @ sk_A)))
% 4.48/4.68         <= (((m1_subset_1 @ sk_D_4 @ (u1_struct_0 @ sk_A))))),
% 4.48/4.68      inference('demod', [status(thm)], ['53', '59', '65', '71', '72'])).
% 4.48/4.68  thf('74', plain,
% 4.48/4.68      ((((v2_struct_0 @ sk_A)
% 4.48/4.68         | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 4.48/4.68         | (r3_lattices @ sk_A @ sk_D_4 @ sk_B)))
% 4.48/4.68         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))) & 
% 4.48/4.68             ((r3_lattice3 @ sk_A @ sk_D_4 @ sk_C)) & 
% 4.48/4.68             ((m1_subset_1 @ sk_D_4 @ (u1_struct_0 @ sk_A))))),
% 4.48/4.68      inference('sup-', [status(thm)], ['50', '73'])).
% 4.48/4.68  thf('75', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('76', plain,
% 4.48/4.68      ((((v2_struct_0 @ sk_A) | (r3_lattices @ sk_A @ sk_D_4 @ sk_B)))
% 4.48/4.68         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))) & 
% 4.48/4.68             ((r3_lattice3 @ sk_A @ sk_D_4 @ sk_C)) & 
% 4.48/4.68             ((m1_subset_1 @ sk_D_4 @ (u1_struct_0 @ sk_A))))),
% 4.48/4.68      inference('demod', [status(thm)], ['74', '75'])).
% 4.48/4.68  thf('77', plain, (~ (v2_struct_0 @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('78', plain,
% 4.48/4.68      (((r3_lattices @ sk_A @ sk_D_4 @ sk_B))
% 4.48/4.68         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))) & 
% 4.48/4.68             ((r3_lattice3 @ sk_A @ sk_D_4 @ sk_C)) & 
% 4.48/4.68             ((m1_subset_1 @ sk_D_4 @ (u1_struct_0 @ sk_A))))),
% 4.48/4.68      inference('clc', [status(thm)], ['76', '77'])).
% 4.48/4.68  thf('79', plain,
% 4.48/4.68      ((~ (r3_lattices @ sk_A @ sk_D_4 @ sk_B))
% 4.48/4.68         <= (~ ((r3_lattices @ sk_A @ sk_D_4 @ sk_B)))),
% 4.48/4.68      inference('split', [status(esa)], ['6'])).
% 4.48/4.68  thf('80', plain,
% 4.48/4.68      (((r3_lattices @ sk_A @ sk_D_4 @ sk_B)) | 
% 4.48/4.68       ~ ((r3_lattice3 @ sk_A @ sk_D_4 @ sk_C)) | 
% 4.48/4.68       ~ (((sk_B) = (k16_lattice3 @ sk_A @ sk_C))) | 
% 4.48/4.68       ~ ((m1_subset_1 @ sk_D_4 @ (u1_struct_0 @ sk_A)))),
% 4.48/4.68      inference('sup-', [status(thm)], ['78', '79'])).
% 4.48/4.68  thf('81', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf(d16_lattice3, axiom,
% 4.48/4.68    (![A:$i]:
% 4.48/4.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 4.48/4.68       ( ![B:$i]:
% 4.48/4.68         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 4.48/4.68           ( ![C:$i]:
% 4.48/4.68             ( ( r3_lattice3 @ A @ B @ C ) <=>
% 4.48/4.68               ( ![D:$i]:
% 4.48/4.68                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 4.48/4.68                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 4.48/4.68  thf('82', plain,
% 4.48/4.68      (![X4 : $i, X5 : $i, X8 : $i]:
% 4.48/4.68         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 4.48/4.68          | (m1_subset_1 @ (sk_D @ X8 @ X4 @ X5) @ (u1_struct_0 @ X5))
% 4.48/4.68          | (r3_lattice3 @ X5 @ X4 @ X8)
% 4.48/4.68          | ~ (l3_lattices @ X5)
% 4.48/4.68          | (v2_struct_0 @ X5))),
% 4.48/4.68      inference('cnf', [status(esa)], [d16_lattice3])).
% 4.48/4.68  thf('83', plain,
% 4.48/4.68      (![X0 : $i]:
% 4.48/4.68         ((v2_struct_0 @ sk_A)
% 4.48/4.68          | ~ (l3_lattices @ sk_A)
% 4.48/4.68          | (r3_lattice3 @ sk_A @ sk_B @ X0)
% 4.48/4.68          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 4.48/4.68      inference('sup-', [status(thm)], ['81', '82'])).
% 4.48/4.68  thf('84', plain, ((l3_lattices @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('85', plain,
% 4.48/4.68      (![X0 : $i]:
% 4.48/4.68         ((v2_struct_0 @ sk_A)
% 4.48/4.68          | (r3_lattice3 @ sk_A @ sk_B @ X0)
% 4.48/4.68          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 4.48/4.68      inference('demod', [status(thm)], ['83', '84'])).
% 4.48/4.68  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('87', plain,
% 4.48/4.68      (![X0 : $i]:
% 4.48/4.68         ((m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 4.48/4.68          | (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 4.48/4.68      inference('clc', [status(thm)], ['85', '86'])).
% 4.48/4.68  thf('88', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('89', plain,
% 4.48/4.68      (![X4 : $i, X5 : $i, X8 : $i]:
% 4.48/4.68         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 4.48/4.68          | (r2_hidden @ (sk_D @ X8 @ X4 @ X5) @ X8)
% 4.48/4.68          | (r3_lattice3 @ X5 @ X4 @ X8)
% 4.48/4.68          | ~ (l3_lattices @ X5)
% 4.48/4.68          | (v2_struct_0 @ X5))),
% 4.48/4.68      inference('cnf', [status(esa)], [d16_lattice3])).
% 4.48/4.68  thf('90', plain,
% 4.48/4.68      (![X0 : $i]:
% 4.48/4.68         ((v2_struct_0 @ sk_A)
% 4.48/4.68          | ~ (l3_lattices @ sk_A)
% 4.48/4.68          | (r3_lattice3 @ sk_A @ sk_B @ X0)
% 4.48/4.68          | (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ X0))),
% 4.48/4.68      inference('sup-', [status(thm)], ['88', '89'])).
% 4.48/4.68  thf('91', plain, ((l3_lattices @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('92', plain,
% 4.48/4.68      (![X0 : $i]:
% 4.48/4.68         ((v2_struct_0 @ sk_A)
% 4.48/4.68          | (r3_lattice3 @ sk_A @ sk_B @ X0)
% 4.48/4.68          | (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ X0))),
% 4.48/4.68      inference('demod', [status(thm)], ['90', '91'])).
% 4.48/4.68  thf('93', plain, (~ (v2_struct_0 @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('94', plain,
% 4.48/4.68      (![X0 : $i]:
% 4.48/4.68         ((r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ X0)
% 4.48/4.68          | (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 4.48/4.68      inference('clc', [status(thm)], ['92', '93'])).
% 4.48/4.68  thf('95', plain,
% 4.48/4.68      (![X0 : $i]:
% 4.48/4.68         ((m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 4.48/4.68          | (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 4.48/4.68      inference('clc', [status(thm)], ['85', '86'])).
% 4.48/4.68  thf('96', plain,
% 4.48/4.68      (![X0 : $i]:
% 4.48/4.68         ((m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 4.48/4.68          | (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 4.48/4.68      inference('clc', [status(thm)], ['85', '86'])).
% 4.48/4.68  thf('97', plain,
% 4.48/4.68      (![X9 : $i, X10 : $i, X13 : $i]:
% 4.48/4.68         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 4.48/4.68          | (r2_hidden @ (sk_D_1 @ X13 @ X9 @ X10) @ X13)
% 4.48/4.68          | (r4_lattice3 @ X10 @ X9 @ X13)
% 4.48/4.68          | ~ (l3_lattices @ X10)
% 4.48/4.68          | (v2_struct_0 @ X10))),
% 4.48/4.68      inference('cnf', [status(esa)], [d17_lattice3])).
% 4.48/4.68  thf('98', plain,
% 4.48/4.68      (![X0 : $i, X1 : $i]:
% 4.48/4.68         ((r3_lattice3 @ sk_A @ sk_B @ X0)
% 4.48/4.68          | (v2_struct_0 @ sk_A)
% 4.48/4.68          | ~ (l3_lattices @ sk_A)
% 4.48/4.68          | (r4_lattice3 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ X1)
% 4.48/4.68          | (r2_hidden @ (sk_D_1 @ X1 @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A) @ X1))),
% 4.48/4.68      inference('sup-', [status(thm)], ['96', '97'])).
% 4.48/4.68  thf('99', plain, ((l3_lattices @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('100', plain,
% 4.48/4.68      (![X0 : $i, X1 : $i]:
% 4.48/4.68         ((r3_lattice3 @ sk_A @ sk_B @ X0)
% 4.48/4.68          | (v2_struct_0 @ sk_A)
% 4.48/4.68          | (r4_lattice3 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ X1)
% 4.48/4.68          | (r2_hidden @ (sk_D_1 @ X1 @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A) @ X1))),
% 4.48/4.68      inference('demod', [status(thm)], ['98', '99'])).
% 4.48/4.68  thf('101', plain,
% 4.48/4.68      (![X20 : $i, X21 : $i, X22 : $i]:
% 4.48/4.68         (~ (l3_lattices @ X20)
% 4.48/4.68          | (v2_struct_0 @ X20)
% 4.48/4.68          | ((X22) = (sk_D_3 @ X21 @ X20 @ X22))
% 4.48/4.68          | ~ (r2_hidden @ X22 @ (a_2_1_lattice3 @ X20 @ X21)))),
% 4.48/4.68      inference('cnf', [status(esa)], [fraenkel_a_2_1_lattice3])).
% 4.48/4.68  thf('102', plain,
% 4.48/4.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.48/4.68         ((r4_lattice3 @ sk_A @ (sk_D @ X2 @ sk_B @ sk_A) @ 
% 4.48/4.68           (a_2_1_lattice3 @ X1 @ X0))
% 4.48/4.68          | (v2_struct_0 @ sk_A)
% 4.48/4.68          | (r3_lattice3 @ sk_A @ sk_B @ X2)
% 4.48/4.68          | ((sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ 
% 4.48/4.68              (sk_D @ X2 @ sk_B @ sk_A) @ sk_A)
% 4.48/4.68              = (sk_D_3 @ X0 @ X1 @ 
% 4.48/4.68                 (sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ 
% 4.48/4.68                  (sk_D @ X2 @ sk_B @ sk_A) @ sk_A)))
% 4.48/4.68          | (v2_struct_0 @ X1)
% 4.48/4.68          | ~ (l3_lattices @ X1))),
% 4.48/4.68      inference('sup-', [status(thm)], ['100', '101'])).
% 4.48/4.68  thf('103', plain,
% 4.48/4.68      (![X0 : $i, X1 : $i]:
% 4.48/4.68         ((r3_lattice3 @ sk_A @ sk_B @ X0)
% 4.48/4.68          | (v2_struct_0 @ sk_A)
% 4.48/4.68          | (r4_lattice3 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ X1)
% 4.48/4.68          | (r2_hidden @ (sk_D_1 @ X1 @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A) @ X1))),
% 4.48/4.68      inference('demod', [status(thm)], ['98', '99'])).
% 4.48/4.68  thf('104', plain,
% 4.48/4.68      (![X20 : $i, X21 : $i, X22 : $i]:
% 4.48/4.68         (~ (l3_lattices @ X20)
% 4.48/4.68          | (v2_struct_0 @ X20)
% 4.48/4.68          | (r3_lattice3 @ X20 @ (sk_D_3 @ X21 @ X20 @ X22) @ X21)
% 4.48/4.68          | ~ (r2_hidden @ X22 @ (a_2_1_lattice3 @ X20 @ X21)))),
% 4.48/4.68      inference('cnf', [status(esa)], [fraenkel_a_2_1_lattice3])).
% 4.48/4.68  thf('105', plain,
% 4.48/4.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.48/4.68         ((r4_lattice3 @ sk_A @ (sk_D @ X2 @ sk_B @ sk_A) @ 
% 4.48/4.68           (a_2_1_lattice3 @ X1 @ X0))
% 4.48/4.68          | (v2_struct_0 @ sk_A)
% 4.48/4.68          | (r3_lattice3 @ sk_A @ sk_B @ X2)
% 4.48/4.68          | (r3_lattice3 @ X1 @ 
% 4.48/4.68             (sk_D_3 @ X0 @ X1 @ 
% 4.48/4.68              (sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ 
% 4.48/4.68               (sk_D @ X2 @ sk_B @ sk_A) @ sk_A)) @ 
% 4.48/4.68             X0)
% 4.48/4.68          | (v2_struct_0 @ X1)
% 4.48/4.68          | ~ (l3_lattices @ X1))),
% 4.48/4.68      inference('sup-', [status(thm)], ['103', '104'])).
% 4.48/4.68  thf('106', plain,
% 4.48/4.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.48/4.68         ((r3_lattice3 @ X2 @ 
% 4.48/4.68           (sk_D_1 @ (a_2_1_lattice3 @ X2 @ X1) @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 4.48/4.68            sk_A) @ 
% 4.48/4.68           X1)
% 4.48/4.68          | ~ (l3_lattices @ X2)
% 4.48/4.68          | (v2_struct_0 @ X2)
% 4.48/4.68          | (r3_lattice3 @ sk_A @ sk_B @ X0)
% 4.48/4.68          | (v2_struct_0 @ sk_A)
% 4.48/4.68          | (r4_lattice3 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 4.48/4.68             (a_2_1_lattice3 @ X2 @ X1))
% 4.48/4.68          | ~ (l3_lattices @ X2)
% 4.48/4.68          | (v2_struct_0 @ X2)
% 4.48/4.68          | (r3_lattice3 @ sk_A @ sk_B @ X0)
% 4.48/4.68          | (v2_struct_0 @ sk_A)
% 4.48/4.68          | (r4_lattice3 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 4.48/4.68             (a_2_1_lattice3 @ X2 @ X1)))),
% 4.48/4.68      inference('sup+', [status(thm)], ['102', '105'])).
% 4.48/4.68  thf('107', plain,
% 4.48/4.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.48/4.68         ((r4_lattice3 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 4.48/4.68           (a_2_1_lattice3 @ X2 @ X1))
% 4.48/4.68          | (v2_struct_0 @ sk_A)
% 4.48/4.68          | (r3_lattice3 @ sk_A @ sk_B @ X0)
% 4.48/4.68          | (v2_struct_0 @ X2)
% 4.48/4.68          | ~ (l3_lattices @ X2)
% 4.48/4.68          | (r3_lattice3 @ X2 @ 
% 4.48/4.68             (sk_D_1 @ (a_2_1_lattice3 @ X2 @ X1) @ 
% 4.48/4.68              (sk_D @ X0 @ sk_B @ sk_A) @ sk_A) @ 
% 4.48/4.68             X1))),
% 4.48/4.68      inference('simplify', [status(thm)], ['106'])).
% 4.48/4.68  thf('108', plain,
% 4.48/4.68      (![X0 : $i]:
% 4.48/4.68         ((m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 4.48/4.68          | (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 4.48/4.68      inference('clc', [status(thm)], ['85', '86'])).
% 4.48/4.68  thf('109', plain,
% 4.48/4.68      (![X9 : $i, X10 : $i, X13 : $i]:
% 4.48/4.68         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 4.48/4.68          | (m1_subset_1 @ (sk_D_1 @ X13 @ X9 @ X10) @ (u1_struct_0 @ X10))
% 4.48/4.68          | (r4_lattice3 @ X10 @ X9 @ X13)
% 4.48/4.68          | ~ (l3_lattices @ X10)
% 4.48/4.68          | (v2_struct_0 @ X10))),
% 4.48/4.68      inference('cnf', [status(esa)], [d17_lattice3])).
% 4.48/4.68  thf('110', plain,
% 4.48/4.68      (![X0 : $i, X1 : $i]:
% 4.48/4.68         ((r3_lattice3 @ sk_A @ sk_B @ X0)
% 4.48/4.68          | (v2_struct_0 @ sk_A)
% 4.48/4.68          | ~ (l3_lattices @ sk_A)
% 4.48/4.68          | (r4_lattice3 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ X1)
% 4.48/4.68          | (m1_subset_1 @ (sk_D_1 @ X1 @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A) @ 
% 4.48/4.68             (u1_struct_0 @ sk_A)))),
% 4.48/4.68      inference('sup-', [status(thm)], ['108', '109'])).
% 4.48/4.68  thf('111', plain, ((l3_lattices @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('112', plain,
% 4.48/4.68      (![X0 : $i, X1 : $i]:
% 4.48/4.68         ((r3_lattice3 @ sk_A @ sk_B @ X0)
% 4.48/4.68          | (v2_struct_0 @ sk_A)
% 4.48/4.68          | (r4_lattice3 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ X1)
% 4.48/4.68          | (m1_subset_1 @ (sk_D_1 @ X1 @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A) @ 
% 4.48/4.68             (u1_struct_0 @ sk_A)))),
% 4.48/4.68      inference('demod', [status(thm)], ['110', '111'])).
% 4.48/4.68  thf('113', plain,
% 4.48/4.68      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 4.48/4.68         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 4.48/4.68          | ~ (r3_lattice3 @ X5 @ X4 @ X6)
% 4.48/4.68          | ~ (r2_hidden @ X7 @ X6)
% 4.48/4.68          | (r1_lattices @ X5 @ X4 @ X7)
% 4.48/4.68          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X5))
% 4.48/4.68          | ~ (l3_lattices @ X5)
% 4.48/4.68          | (v2_struct_0 @ X5))),
% 4.48/4.68      inference('cnf', [status(esa)], [d16_lattice3])).
% 4.48/4.68  thf('114', plain,
% 4.48/4.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.48/4.68         ((r4_lattice3 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ X1)
% 4.48/4.68          | (v2_struct_0 @ sk_A)
% 4.48/4.68          | (r3_lattice3 @ sk_A @ sk_B @ X0)
% 4.48/4.68          | (v2_struct_0 @ sk_A)
% 4.48/4.68          | ~ (l3_lattices @ sk_A)
% 4.48/4.68          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_A))
% 4.48/4.68          | (r1_lattices @ sk_A @ 
% 4.48/4.68             (sk_D_1 @ X1 @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A) @ X2)
% 4.48/4.68          | ~ (r2_hidden @ X2 @ X3)
% 4.48/4.68          | ~ (r3_lattice3 @ sk_A @ 
% 4.48/4.68               (sk_D_1 @ X1 @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A) @ X3))),
% 4.48/4.68      inference('sup-', [status(thm)], ['112', '113'])).
% 4.48/4.68  thf('115', plain, ((l3_lattices @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('116', plain,
% 4.48/4.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.48/4.68         ((r4_lattice3 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ X1)
% 4.48/4.68          | (v2_struct_0 @ sk_A)
% 4.48/4.68          | (r3_lattice3 @ sk_A @ sk_B @ X0)
% 4.48/4.68          | (v2_struct_0 @ sk_A)
% 4.48/4.68          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_A))
% 4.48/4.68          | (r1_lattices @ sk_A @ 
% 4.48/4.68             (sk_D_1 @ X1 @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A) @ X2)
% 4.48/4.68          | ~ (r2_hidden @ X2 @ X3)
% 4.48/4.68          | ~ (r3_lattice3 @ sk_A @ 
% 4.48/4.68               (sk_D_1 @ X1 @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A) @ X3))),
% 4.48/4.68      inference('demod', [status(thm)], ['114', '115'])).
% 4.48/4.68  thf('117', plain,
% 4.48/4.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.48/4.68         (~ (r3_lattice3 @ sk_A @ 
% 4.48/4.68             (sk_D_1 @ X1 @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A) @ X3)
% 4.48/4.68          | ~ (r2_hidden @ X2 @ X3)
% 4.48/4.68          | (r1_lattices @ sk_A @ 
% 4.48/4.68             (sk_D_1 @ X1 @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A) @ X2)
% 4.48/4.68          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_A))
% 4.48/4.68          | (r3_lattice3 @ sk_A @ sk_B @ X0)
% 4.48/4.68          | (v2_struct_0 @ sk_A)
% 4.48/4.68          | (r4_lattice3 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ X1))),
% 4.48/4.68      inference('simplify', [status(thm)], ['116'])).
% 4.48/4.68  thf('118', plain,
% 4.48/4.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.48/4.68         (~ (l3_lattices @ sk_A)
% 4.48/4.68          | (v2_struct_0 @ sk_A)
% 4.48/4.68          | (r3_lattice3 @ sk_A @ sk_B @ X1)
% 4.48/4.68          | (v2_struct_0 @ sk_A)
% 4.48/4.68          | (r4_lattice3 @ sk_A @ (sk_D @ X1 @ sk_B @ sk_A) @ 
% 4.48/4.68             (a_2_1_lattice3 @ sk_A @ X0))
% 4.48/4.68          | (r4_lattice3 @ sk_A @ (sk_D @ X1 @ sk_B @ sk_A) @ 
% 4.48/4.68             (a_2_1_lattice3 @ sk_A @ X0))
% 4.48/4.68          | (v2_struct_0 @ sk_A)
% 4.48/4.68          | (r3_lattice3 @ sk_A @ sk_B @ X1)
% 4.48/4.68          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_A))
% 4.48/4.68          | (r1_lattices @ sk_A @ 
% 4.48/4.68             (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ X0) @ 
% 4.48/4.68              (sk_D @ X1 @ sk_B @ sk_A) @ sk_A) @ 
% 4.48/4.68             X2)
% 4.48/4.68          | ~ (r2_hidden @ X2 @ X0))),
% 4.48/4.68      inference('sup-', [status(thm)], ['107', '117'])).
% 4.48/4.68  thf('119', plain, ((l3_lattices @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('120', plain,
% 4.48/4.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.48/4.68         ((v2_struct_0 @ sk_A)
% 4.48/4.68          | (r3_lattice3 @ sk_A @ sk_B @ X1)
% 4.48/4.68          | (v2_struct_0 @ sk_A)
% 4.48/4.68          | (r4_lattice3 @ sk_A @ (sk_D @ X1 @ sk_B @ sk_A) @ 
% 4.48/4.68             (a_2_1_lattice3 @ sk_A @ X0))
% 4.48/4.68          | (r4_lattice3 @ sk_A @ (sk_D @ X1 @ sk_B @ sk_A) @ 
% 4.48/4.68             (a_2_1_lattice3 @ sk_A @ X0))
% 4.48/4.68          | (v2_struct_0 @ sk_A)
% 4.48/4.68          | (r3_lattice3 @ sk_A @ sk_B @ X1)
% 4.48/4.68          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_A))
% 4.48/4.68          | (r1_lattices @ sk_A @ 
% 4.48/4.68             (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ X0) @ 
% 4.48/4.68              (sk_D @ X1 @ sk_B @ sk_A) @ sk_A) @ 
% 4.48/4.68             X2)
% 4.48/4.68          | ~ (r2_hidden @ X2 @ X0))),
% 4.48/4.68      inference('demod', [status(thm)], ['118', '119'])).
% 4.48/4.68  thf('121', plain,
% 4.48/4.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.48/4.68         (~ (r2_hidden @ X2 @ X0)
% 4.48/4.68          | (r1_lattices @ sk_A @ 
% 4.48/4.68             (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ X0) @ 
% 4.48/4.68              (sk_D @ X1 @ sk_B @ sk_A) @ sk_A) @ 
% 4.48/4.68             X2)
% 4.48/4.68          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_A))
% 4.48/4.68          | (r4_lattice3 @ sk_A @ (sk_D @ X1 @ sk_B @ sk_A) @ 
% 4.48/4.68             (a_2_1_lattice3 @ sk_A @ X0))
% 4.48/4.68          | (r3_lattice3 @ sk_A @ sk_B @ X1)
% 4.48/4.68          | (v2_struct_0 @ sk_A))),
% 4.48/4.68      inference('simplify', [status(thm)], ['120'])).
% 4.48/4.68  thf('122', plain,
% 4.48/4.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.48/4.68         ((r3_lattice3 @ sk_A @ sk_B @ X0)
% 4.48/4.68          | (v2_struct_0 @ sk_A)
% 4.48/4.68          | (r3_lattice3 @ sk_A @ sk_B @ X1)
% 4.48/4.68          | (r4_lattice3 @ sk_A @ (sk_D @ X1 @ sk_B @ sk_A) @ 
% 4.48/4.68             (a_2_1_lattice3 @ sk_A @ X2))
% 4.48/4.68          | (r1_lattices @ sk_A @ 
% 4.48/4.68             (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ X2) @ 
% 4.48/4.68              (sk_D @ X1 @ sk_B @ sk_A) @ sk_A) @ 
% 4.48/4.68             (sk_D @ X0 @ sk_B @ sk_A))
% 4.48/4.68          | ~ (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ X2))),
% 4.48/4.68      inference('sup-', [status(thm)], ['95', '121'])).
% 4.48/4.68  thf('123', plain,
% 4.48/4.68      (![X0 : $i, X1 : $i]:
% 4.48/4.68         ((r3_lattice3 @ sk_A @ sk_B @ X0)
% 4.48/4.68          | (r1_lattices @ sk_A @ 
% 4.48/4.68             (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ X0) @ 
% 4.48/4.68              (sk_D @ X1 @ sk_B @ sk_A) @ sk_A) @ 
% 4.48/4.68             (sk_D @ X0 @ sk_B @ sk_A))
% 4.48/4.68          | (r4_lattice3 @ sk_A @ (sk_D @ X1 @ sk_B @ sk_A) @ 
% 4.48/4.68             (a_2_1_lattice3 @ sk_A @ X0))
% 4.48/4.68          | (r3_lattice3 @ sk_A @ sk_B @ X1)
% 4.48/4.68          | (v2_struct_0 @ sk_A)
% 4.48/4.68          | (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 4.48/4.68      inference('sup-', [status(thm)], ['94', '122'])).
% 4.48/4.68  thf('124', plain,
% 4.48/4.68      (![X0 : $i, X1 : $i]:
% 4.48/4.68         ((v2_struct_0 @ sk_A)
% 4.48/4.68          | (r3_lattice3 @ sk_A @ sk_B @ X1)
% 4.48/4.68          | (r4_lattice3 @ sk_A @ (sk_D @ X1 @ sk_B @ sk_A) @ 
% 4.48/4.68             (a_2_1_lattice3 @ sk_A @ X0))
% 4.48/4.68          | (r1_lattices @ sk_A @ 
% 4.48/4.68             (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ X0) @ 
% 4.48/4.68              (sk_D @ X1 @ sk_B @ sk_A) @ sk_A) @ 
% 4.48/4.68             (sk_D @ X0 @ sk_B @ sk_A))
% 4.48/4.68          | (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 4.48/4.68      inference('simplify', [status(thm)], ['123'])).
% 4.48/4.68  thf('125', plain,
% 4.48/4.68      (![X0 : $i]:
% 4.48/4.68         ((m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 4.48/4.68          | (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 4.48/4.68      inference('clc', [status(thm)], ['85', '86'])).
% 4.48/4.68  thf('126', plain,
% 4.48/4.68      (![X9 : $i, X10 : $i, X13 : $i]:
% 4.48/4.68         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 4.48/4.68          | ~ (r1_lattices @ X10 @ (sk_D_1 @ X13 @ X9 @ X10) @ X9)
% 4.48/4.68          | (r4_lattice3 @ X10 @ X9 @ X13)
% 4.48/4.68          | ~ (l3_lattices @ X10)
% 4.48/4.68          | (v2_struct_0 @ X10))),
% 4.48/4.68      inference('cnf', [status(esa)], [d17_lattice3])).
% 4.48/4.68  thf('127', plain,
% 4.48/4.68      (![X0 : $i, X1 : $i]:
% 4.48/4.68         ((r3_lattice3 @ sk_A @ sk_B @ X0)
% 4.48/4.68          | (v2_struct_0 @ sk_A)
% 4.48/4.68          | ~ (l3_lattices @ sk_A)
% 4.48/4.68          | (r4_lattice3 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ X1)
% 4.48/4.68          | ~ (r1_lattices @ sk_A @ 
% 4.48/4.68               (sk_D_1 @ X1 @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A) @ 
% 4.48/4.68               (sk_D @ X0 @ sk_B @ sk_A)))),
% 4.48/4.68      inference('sup-', [status(thm)], ['125', '126'])).
% 4.48/4.68  thf('128', plain, ((l3_lattices @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('129', plain,
% 4.48/4.68      (![X0 : $i, X1 : $i]:
% 4.48/4.68         ((r3_lattice3 @ sk_A @ sk_B @ X0)
% 4.48/4.68          | (v2_struct_0 @ sk_A)
% 4.48/4.68          | (r4_lattice3 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ X1)
% 4.48/4.68          | ~ (r1_lattices @ sk_A @ 
% 4.48/4.68               (sk_D_1 @ X1 @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A) @ 
% 4.48/4.68               (sk_D @ X0 @ sk_B @ sk_A)))),
% 4.48/4.68      inference('demod', [status(thm)], ['127', '128'])).
% 4.48/4.68  thf('130', plain,
% 4.48/4.68      (![X0 : $i]:
% 4.48/4.68         ((r3_lattice3 @ sk_A @ sk_B @ X0)
% 4.48/4.68          | (r4_lattice3 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 4.48/4.68             (a_2_1_lattice3 @ sk_A @ X0))
% 4.48/4.68          | (r3_lattice3 @ sk_A @ sk_B @ X0)
% 4.48/4.68          | (v2_struct_0 @ sk_A)
% 4.48/4.68          | (r4_lattice3 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 4.48/4.68             (a_2_1_lattice3 @ sk_A @ X0))
% 4.48/4.68          | (v2_struct_0 @ sk_A)
% 4.48/4.68          | (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 4.48/4.68      inference('sup-', [status(thm)], ['124', '129'])).
% 4.48/4.68  thf('131', plain,
% 4.48/4.68      (![X0 : $i]:
% 4.48/4.68         ((v2_struct_0 @ sk_A)
% 4.48/4.68          | (r4_lattice3 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 4.48/4.68             (a_2_1_lattice3 @ sk_A @ X0))
% 4.48/4.68          | (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 4.48/4.68      inference('simplify', [status(thm)], ['130'])).
% 4.48/4.68  thf('132', plain, (~ (v2_struct_0 @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('133', plain,
% 4.48/4.68      (![X0 : $i]:
% 4.48/4.68         ((r3_lattice3 @ sk_A @ sk_B @ X0)
% 4.48/4.68          | (r4_lattice3 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 4.48/4.68             (a_2_1_lattice3 @ sk_A @ X0)))),
% 4.48/4.68      inference('clc', [status(thm)], ['131', '132'])).
% 4.48/4.68  thf('134', plain,
% 4.48/4.68      ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C)))
% 4.48/4.68         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))))),
% 4.48/4.68      inference('split', [status(esa)], ['19'])).
% 4.48/4.68  thf('135', plain,
% 4.48/4.68      (![X18 : $i, X19 : $i]:
% 4.48/4.68         (((k16_lattice3 @ X18 @ X19)
% 4.48/4.68            = (k15_lattice3 @ X18 @ (a_2_1_lattice3 @ X18 @ X19)))
% 4.48/4.68          | ~ (l3_lattices @ X18)
% 4.48/4.68          | (v2_struct_0 @ X18))),
% 4.48/4.68      inference('cnf', [status(esa)], [d22_lattice3])).
% 4.48/4.68  thf('136', plain,
% 4.48/4.68      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 4.48/4.68         ((v2_struct_0 @ X14)
% 4.48/4.68          | ~ (v10_lattices @ X14)
% 4.48/4.68          | ~ (v4_lattice3 @ X14)
% 4.48/4.68          | ~ (l3_lattices @ X14)
% 4.48/4.68          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 4.48/4.68          | ((X15) != (k15_lattice3 @ X14 @ X16))
% 4.48/4.68          | ~ (r4_lattice3 @ X14 @ X17 @ X16)
% 4.48/4.68          | (r1_lattices @ X14 @ X15 @ X17)
% 4.48/4.68          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X14))
% 4.48/4.68          | ~ (l3_lattices @ X14)
% 4.48/4.68          | (v2_struct_0 @ X14))),
% 4.48/4.68      inference('cnf', [status(esa)], [d21_lattice3])).
% 4.48/4.68  thf('137', plain,
% 4.48/4.68      (![X14 : $i, X16 : $i, X17 : $i]:
% 4.48/4.68         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X14))
% 4.48/4.68          | (r1_lattices @ X14 @ (k15_lattice3 @ X14 @ X16) @ X17)
% 4.48/4.68          | ~ (r4_lattice3 @ X14 @ X17 @ X16)
% 4.48/4.68          | ~ (m1_subset_1 @ (k15_lattice3 @ X14 @ X16) @ (u1_struct_0 @ X14))
% 4.48/4.68          | ~ (l3_lattices @ X14)
% 4.48/4.68          | ~ (v4_lattice3 @ X14)
% 4.48/4.68          | ~ (v10_lattices @ X14)
% 4.48/4.68          | (v2_struct_0 @ X14))),
% 4.48/4.68      inference('simplify', [status(thm)], ['136'])).
% 4.48/4.68  thf('138', plain,
% 4.48/4.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.48/4.68         (~ (m1_subset_1 @ (k16_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1))
% 4.48/4.68          | (v2_struct_0 @ X1)
% 4.48/4.68          | ~ (l3_lattices @ X1)
% 4.48/4.68          | (v2_struct_0 @ X1)
% 4.48/4.68          | ~ (v10_lattices @ X1)
% 4.48/4.68          | ~ (v4_lattice3 @ X1)
% 4.48/4.68          | ~ (l3_lattices @ X1)
% 4.48/4.68          | ~ (r4_lattice3 @ X1 @ X2 @ (a_2_1_lattice3 @ X1 @ X0))
% 4.48/4.68          | (r1_lattices @ X1 @ 
% 4.48/4.68             (k15_lattice3 @ X1 @ (a_2_1_lattice3 @ X1 @ X0)) @ X2)
% 4.48/4.68          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1)))),
% 4.48/4.68      inference('sup-', [status(thm)], ['135', '137'])).
% 4.48/4.68  thf('139', plain,
% 4.48/4.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.48/4.68         (~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 4.48/4.68          | (r1_lattices @ X1 @ 
% 4.48/4.68             (k15_lattice3 @ X1 @ (a_2_1_lattice3 @ X1 @ X0)) @ X2)
% 4.48/4.68          | ~ (r4_lattice3 @ X1 @ X2 @ (a_2_1_lattice3 @ X1 @ X0))
% 4.48/4.68          | ~ (v4_lattice3 @ X1)
% 4.48/4.68          | ~ (v10_lattices @ X1)
% 4.48/4.68          | ~ (l3_lattices @ X1)
% 4.48/4.68          | (v2_struct_0 @ X1)
% 4.48/4.68          | ~ (m1_subset_1 @ (k16_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1)))),
% 4.48/4.68      inference('simplify', [status(thm)], ['138'])).
% 4.48/4.68  thf('140', plain,
% 4.48/4.68      ((![X0 : $i]:
% 4.48/4.68          (~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 4.48/4.68           | (v2_struct_0 @ sk_A)
% 4.48/4.68           | ~ (l3_lattices @ sk_A)
% 4.48/4.68           | ~ (v10_lattices @ sk_A)
% 4.48/4.68           | ~ (v4_lattice3 @ sk_A)
% 4.48/4.68           | ~ (r4_lattice3 @ sk_A @ X0 @ (a_2_1_lattice3 @ sk_A @ sk_C))
% 4.48/4.68           | (r1_lattices @ sk_A @ 
% 4.48/4.68              (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) @ X0)
% 4.48/4.68           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 4.48/4.68         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))))),
% 4.48/4.68      inference('sup-', [status(thm)], ['134', '139'])).
% 4.48/4.68  thf('141', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('142', plain, ((l3_lattices @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('143', plain, ((v10_lattices @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('144', plain, ((v4_lattice3 @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('145', plain,
% 4.48/4.68      ((![X0 : $i]:
% 4.48/4.68          ((v2_struct_0 @ sk_A)
% 4.48/4.68           | ~ (r4_lattice3 @ sk_A @ X0 @ (a_2_1_lattice3 @ sk_A @ sk_C))
% 4.48/4.68           | (r1_lattices @ sk_A @ 
% 4.48/4.68              (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) @ X0)
% 4.48/4.68           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 4.48/4.68         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))))),
% 4.48/4.68      inference('demod', [status(thm)], ['140', '141', '142', '143', '144'])).
% 4.48/4.68  thf('146', plain,
% 4.48/4.68      (![X18 : $i, X19 : $i]:
% 4.48/4.68         (((k16_lattice3 @ X18 @ X19)
% 4.48/4.68            = (k15_lattice3 @ X18 @ (a_2_1_lattice3 @ X18 @ X19)))
% 4.48/4.68          | ~ (l3_lattices @ X18)
% 4.48/4.68          | (v2_struct_0 @ X18))),
% 4.48/4.68      inference('cnf', [status(esa)], [d22_lattice3])).
% 4.48/4.68  thf('147', plain,
% 4.48/4.68      (((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 4.48/4.68         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))))),
% 4.48/4.68      inference('clc', [status(thm)], ['37', '38'])).
% 4.48/4.68  thf('148', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('149', plain,
% 4.48/4.68      (![X14 : $i, X15 : $i, X16 : $i]:
% 4.48/4.68         ((v2_struct_0 @ X14)
% 4.48/4.68          | ~ (v10_lattices @ X14)
% 4.48/4.68          | ~ (v4_lattice3 @ X14)
% 4.48/4.68          | ~ (l3_lattices @ X14)
% 4.48/4.68          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 4.48/4.68          | ~ (r4_lattice3 @ X14 @ X15 @ X16)
% 4.48/4.68          | (m1_subset_1 @ (sk_D_2 @ X15 @ X16 @ X14) @ (u1_struct_0 @ X14))
% 4.48/4.68          | ((X15) = (k15_lattice3 @ X14 @ X16))
% 4.48/4.68          | ~ (l3_lattices @ X14)
% 4.48/4.68          | (v2_struct_0 @ X14))),
% 4.48/4.68      inference('cnf', [status(esa)], [d21_lattice3])).
% 4.48/4.68  thf('150', plain,
% 4.48/4.68      (![X14 : $i, X15 : $i, X16 : $i]:
% 4.48/4.68         (((X15) = (k15_lattice3 @ X14 @ X16))
% 4.48/4.68          | (m1_subset_1 @ (sk_D_2 @ X15 @ X16 @ X14) @ (u1_struct_0 @ X14))
% 4.48/4.68          | ~ (r4_lattice3 @ X14 @ X15 @ X16)
% 4.48/4.68          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 4.48/4.68          | ~ (l3_lattices @ X14)
% 4.48/4.68          | ~ (v4_lattice3 @ X14)
% 4.48/4.68          | ~ (v10_lattices @ X14)
% 4.48/4.68          | (v2_struct_0 @ X14))),
% 4.48/4.68      inference('simplify', [status(thm)], ['149'])).
% 4.48/4.68  thf('151', plain,
% 4.48/4.68      (![X0 : $i]:
% 4.48/4.68         ((v2_struct_0 @ sk_A)
% 4.48/4.68          | ~ (v10_lattices @ sk_A)
% 4.48/4.68          | ~ (v4_lattice3 @ sk_A)
% 4.48/4.68          | ~ (l3_lattices @ sk_A)
% 4.48/4.68          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0)
% 4.48/4.68          | (m1_subset_1 @ (sk_D_2 @ sk_B @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 4.48/4.68          | ((sk_B) = (k15_lattice3 @ sk_A @ X0)))),
% 4.48/4.68      inference('sup-', [status(thm)], ['148', '150'])).
% 4.48/4.68  thf('152', plain, ((v10_lattices @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('153', plain, ((v4_lattice3 @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('154', plain, ((l3_lattices @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('155', plain,
% 4.48/4.68      (![X0 : $i]:
% 4.48/4.68         ((v2_struct_0 @ sk_A)
% 4.48/4.68          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0)
% 4.48/4.68          | (m1_subset_1 @ (sk_D_2 @ sk_B @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 4.48/4.68          | ((sk_B) = (k15_lattice3 @ sk_A @ X0)))),
% 4.48/4.68      inference('demod', [status(thm)], ['151', '152', '153', '154'])).
% 4.48/4.68  thf('156', plain,
% 4.48/4.68      (((((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 4.48/4.68         | (m1_subset_1 @ 
% 4.48/4.68            (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A) @ 
% 4.48/4.68            (u1_struct_0 @ sk_A))
% 4.48/4.68         | (v2_struct_0 @ sk_A)))
% 4.48/4.68         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))))),
% 4.48/4.68      inference('sup-', [status(thm)], ['147', '155'])).
% 4.48/4.68  thf('157', plain, (~ (v2_struct_0 @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('158', plain,
% 4.48/4.68      ((((m1_subset_1 @ 
% 4.48/4.68          (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A) @ 
% 4.48/4.68          (u1_struct_0 @ sk_A))
% 4.48/4.68         | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))))
% 4.48/4.68         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))))),
% 4.48/4.68      inference('clc', [status(thm)], ['156', '157'])).
% 4.48/4.68  thf('159', plain,
% 4.48/4.68      (((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 4.48/4.68         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))))),
% 4.48/4.68      inference('clc', [status(thm)], ['37', '38'])).
% 4.48/4.68  thf('160', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('161', plain,
% 4.48/4.68      (![X14 : $i, X15 : $i, X16 : $i]:
% 4.48/4.68         ((v2_struct_0 @ X14)
% 4.48/4.68          | ~ (v10_lattices @ X14)
% 4.48/4.68          | ~ (v4_lattice3 @ X14)
% 4.48/4.68          | ~ (l3_lattices @ X14)
% 4.48/4.68          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 4.48/4.68          | ~ (r4_lattice3 @ X14 @ X15 @ X16)
% 4.48/4.68          | (r4_lattice3 @ X14 @ (sk_D_2 @ X15 @ X16 @ X14) @ X16)
% 4.48/4.68          | ((X15) = (k15_lattice3 @ X14 @ X16))
% 4.48/4.68          | ~ (l3_lattices @ X14)
% 4.48/4.68          | (v2_struct_0 @ X14))),
% 4.48/4.68      inference('cnf', [status(esa)], [d21_lattice3])).
% 4.48/4.68  thf('162', plain,
% 4.48/4.68      (![X14 : $i, X15 : $i, X16 : $i]:
% 4.48/4.68         (((X15) = (k15_lattice3 @ X14 @ X16))
% 4.48/4.68          | (r4_lattice3 @ X14 @ (sk_D_2 @ X15 @ X16 @ X14) @ X16)
% 4.48/4.68          | ~ (r4_lattice3 @ X14 @ X15 @ X16)
% 4.48/4.68          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 4.48/4.68          | ~ (l3_lattices @ X14)
% 4.48/4.68          | ~ (v4_lattice3 @ X14)
% 4.48/4.68          | ~ (v10_lattices @ X14)
% 4.48/4.68          | (v2_struct_0 @ X14))),
% 4.48/4.68      inference('simplify', [status(thm)], ['161'])).
% 4.48/4.68  thf('163', plain,
% 4.48/4.68      (![X0 : $i]:
% 4.48/4.68         ((v2_struct_0 @ sk_A)
% 4.48/4.68          | ~ (v10_lattices @ sk_A)
% 4.48/4.68          | ~ (v4_lattice3 @ sk_A)
% 4.48/4.68          | ~ (l3_lattices @ sk_A)
% 4.48/4.68          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0)
% 4.48/4.68          | (r4_lattice3 @ sk_A @ (sk_D_2 @ sk_B @ X0 @ sk_A) @ X0)
% 4.48/4.68          | ((sk_B) = (k15_lattice3 @ sk_A @ X0)))),
% 4.48/4.68      inference('sup-', [status(thm)], ['160', '162'])).
% 4.48/4.68  thf('164', plain, ((v10_lattices @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('165', plain, ((v4_lattice3 @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('166', plain, ((l3_lattices @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('167', plain,
% 4.48/4.68      (![X0 : $i]:
% 4.48/4.68         ((v2_struct_0 @ sk_A)
% 4.48/4.68          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0)
% 4.48/4.68          | (r4_lattice3 @ sk_A @ (sk_D_2 @ sk_B @ X0 @ sk_A) @ X0)
% 4.48/4.68          | ((sk_B) = (k15_lattice3 @ sk_A @ X0)))),
% 4.48/4.68      inference('demod', [status(thm)], ['163', '164', '165', '166'])).
% 4.48/4.68  thf('168', plain,
% 4.48/4.68      (((((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 4.48/4.68         | (r4_lattice3 @ sk_A @ 
% 4.48/4.68            (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A) @ 
% 4.48/4.68            (a_2_1_lattice3 @ sk_A @ sk_C))
% 4.48/4.68         | (v2_struct_0 @ sk_A)))
% 4.48/4.68         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))))),
% 4.48/4.68      inference('sup-', [status(thm)], ['159', '167'])).
% 4.48/4.68  thf('169', plain, (~ (v2_struct_0 @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('170', plain,
% 4.48/4.68      ((((r4_lattice3 @ sk_A @ 
% 4.48/4.68          (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A) @ 
% 4.48/4.68          (a_2_1_lattice3 @ sk_A @ sk_C))
% 4.48/4.68         | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))))
% 4.48/4.68         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))))),
% 4.48/4.68      inference('clc', [status(thm)], ['168', '169'])).
% 4.48/4.68  thf('171', plain,
% 4.48/4.68      ((![X0 : $i]:
% 4.48/4.68          ((v2_struct_0 @ sk_A)
% 4.48/4.68           | ~ (r4_lattice3 @ sk_A @ X0 @ (a_2_1_lattice3 @ sk_A @ sk_C))
% 4.48/4.68           | (r1_lattices @ sk_A @ 
% 4.48/4.68              (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) @ X0)
% 4.48/4.68           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 4.48/4.68         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))))),
% 4.48/4.68      inference('demod', [status(thm)], ['140', '141', '142', '143', '144'])).
% 4.48/4.68  thf('172', plain,
% 4.48/4.68      (((((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 4.48/4.68         | ~ (m1_subset_1 @ 
% 4.48/4.68              (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A) @ 
% 4.48/4.68              (u1_struct_0 @ sk_A))
% 4.48/4.68         | (r1_lattices @ sk_A @ 
% 4.48/4.68            (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) @ 
% 4.48/4.68            (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A))
% 4.48/4.68         | (v2_struct_0 @ sk_A)))
% 4.48/4.68         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))))),
% 4.48/4.68      inference('sup-', [status(thm)], ['170', '171'])).
% 4.48/4.68  thf('173', plain,
% 4.48/4.68      (((((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 4.48/4.68         | (v2_struct_0 @ sk_A)
% 4.48/4.68         | (r1_lattices @ sk_A @ 
% 4.48/4.68            (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) @ 
% 4.48/4.68            (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A))
% 4.48/4.68         | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))))
% 4.48/4.68         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))))),
% 4.48/4.68      inference('sup-', [status(thm)], ['158', '172'])).
% 4.48/4.68  thf('174', plain,
% 4.48/4.68      ((((r1_lattices @ sk_A @ 
% 4.48/4.68          (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) @ 
% 4.48/4.68          (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A))
% 4.48/4.68         | (v2_struct_0 @ sk_A)
% 4.48/4.68         | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))))
% 4.48/4.68         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))))),
% 4.48/4.68      inference('simplify', [status(thm)], ['173'])).
% 4.48/4.68  thf('175', plain, (~ (v2_struct_0 @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('176', plain,
% 4.48/4.68      (((((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 4.48/4.68         | (r1_lattices @ sk_A @ 
% 4.48/4.68            (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) @ 
% 4.48/4.68            (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A))))
% 4.48/4.68         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))))),
% 4.48/4.68      inference('clc', [status(thm)], ['174', '175'])).
% 4.48/4.68  thf('177', plain,
% 4.48/4.68      ((((r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C) @ 
% 4.48/4.68          (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A))
% 4.48/4.68         | (v2_struct_0 @ sk_A)
% 4.48/4.68         | ~ (l3_lattices @ sk_A)
% 4.48/4.68         | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))))
% 4.48/4.68         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))))),
% 4.48/4.68      inference('sup+', [status(thm)], ['146', '176'])).
% 4.48/4.68  thf('178', plain,
% 4.48/4.68      ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C)))
% 4.48/4.68         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))))),
% 4.48/4.68      inference('split', [status(esa)], ['19'])).
% 4.48/4.68  thf('179', plain, ((l3_lattices @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('180', plain,
% 4.48/4.68      ((((r1_lattices @ sk_A @ sk_B @ 
% 4.48/4.68          (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A))
% 4.48/4.68         | (v2_struct_0 @ sk_A)
% 4.48/4.68         | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))))
% 4.48/4.68         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))))),
% 4.48/4.68      inference('demod', [status(thm)], ['177', '178', '179'])).
% 4.48/4.68  thf('181', plain, (~ (v2_struct_0 @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('182', plain,
% 4.48/4.68      (((((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 4.48/4.68         | (r1_lattices @ sk_A @ sk_B @ 
% 4.48/4.68            (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A))))
% 4.48/4.68         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))))),
% 4.48/4.68      inference('clc', [status(thm)], ['180', '181'])).
% 4.48/4.68  thf('183', plain,
% 4.48/4.68      (![X14 : $i, X15 : $i, X16 : $i]:
% 4.48/4.68         ((v2_struct_0 @ X14)
% 4.48/4.68          | ~ (v10_lattices @ X14)
% 4.48/4.68          | ~ (v4_lattice3 @ X14)
% 4.48/4.68          | ~ (l3_lattices @ X14)
% 4.48/4.68          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 4.48/4.68          | ~ (r4_lattice3 @ X14 @ X15 @ X16)
% 4.48/4.68          | ~ (r1_lattices @ X14 @ X15 @ (sk_D_2 @ X15 @ X16 @ X14))
% 4.48/4.68          | ((X15) = (k15_lattice3 @ X14 @ X16))
% 4.48/4.68          | ~ (l3_lattices @ X14)
% 4.48/4.68          | (v2_struct_0 @ X14))),
% 4.48/4.68      inference('cnf', [status(esa)], [d21_lattice3])).
% 4.48/4.68  thf('184', plain,
% 4.48/4.68      (![X14 : $i, X15 : $i, X16 : $i]:
% 4.48/4.68         (((X15) = (k15_lattice3 @ X14 @ X16))
% 4.48/4.68          | ~ (r1_lattices @ X14 @ X15 @ (sk_D_2 @ X15 @ X16 @ X14))
% 4.48/4.68          | ~ (r4_lattice3 @ X14 @ X15 @ X16)
% 4.48/4.68          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 4.48/4.68          | ~ (l3_lattices @ X14)
% 4.48/4.68          | ~ (v4_lattice3 @ X14)
% 4.48/4.68          | ~ (v10_lattices @ X14)
% 4.48/4.68          | (v2_struct_0 @ X14))),
% 4.48/4.68      inference('simplify', [status(thm)], ['183'])).
% 4.48/4.68  thf('185', plain,
% 4.48/4.68      (((((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 4.48/4.68         | (v2_struct_0 @ sk_A)
% 4.48/4.68         | ~ (v10_lattices @ sk_A)
% 4.48/4.68         | ~ (v4_lattice3 @ sk_A)
% 4.48/4.68         | ~ (l3_lattices @ sk_A)
% 4.48/4.68         | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 4.48/4.68         | ~ (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))
% 4.48/4.68         | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))))
% 4.48/4.68         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))))),
% 4.48/4.68      inference('sup-', [status(thm)], ['182', '184'])).
% 4.48/4.68  thf('186', plain, ((v10_lattices @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('187', plain, ((v4_lattice3 @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('188', plain, ((l3_lattices @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('189', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('190', plain,
% 4.48/4.68      (((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 4.48/4.68         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))))),
% 4.48/4.68      inference('clc', [status(thm)], ['37', '38'])).
% 4.48/4.68  thf('191', plain,
% 4.48/4.68      (((((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 4.48/4.68         | (v2_struct_0 @ sk_A)
% 4.48/4.68         | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))))
% 4.48/4.68         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))))),
% 4.48/4.68      inference('demod', [status(thm)],
% 4.48/4.68                ['185', '186', '187', '188', '189', '190'])).
% 4.48/4.68  thf('192', plain,
% 4.48/4.68      ((((v2_struct_0 @ sk_A)
% 4.48/4.68         | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))))
% 4.48/4.68         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))))),
% 4.48/4.68      inference('simplify', [status(thm)], ['191'])).
% 4.48/4.68  thf('193', plain, (~ (v2_struct_0 @ sk_A)),
% 4.48/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.68  thf('194', plain,
% 4.48/4.68      ((((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))
% 4.48/4.68         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))))),
% 4.48/4.68      inference('clc', [status(thm)], ['192', '193'])).
% 4.48/4.68  thf('195', plain,
% 4.48/4.68      ((![X0 : $i]:
% 4.48/4.68          ((v2_struct_0 @ sk_A)
% 4.48/4.68           | ~ (r4_lattice3 @ sk_A @ X0 @ (a_2_1_lattice3 @ sk_A @ sk_C))
% 4.48/4.68           | (r1_lattices @ sk_A @ sk_B @ X0)
% 4.48/4.68           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 4.48/4.68         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))))),
% 4.48/4.68      inference('demod', [status(thm)], ['145', '194'])).
% 4.48/4.68  thf('196', plain,
% 4.48/4.68      ((((r3_lattice3 @ sk_A @ sk_B @ sk_C)
% 4.48/4.68         | ~ (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 4.48/4.68         | (r1_lattices @ sk_A @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 4.48/4.68         | (v2_struct_0 @ sk_A)))
% 4.48/4.68         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))))),
% 4.48/4.68      inference('sup-', [status(thm)], ['133', '195'])).
% 4.48/4.68  thf('197', plain,
% 4.48/4.68      ((((r3_lattice3 @ sk_A @ sk_B @ sk_C)
% 4.48/4.68         | (v2_struct_0 @ sk_A)
% 4.48/4.68         | (r1_lattices @ sk_A @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 4.48/4.68         | (r3_lattice3 @ sk_A @ sk_B @ sk_C)))
% 4.48/4.68         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))))),
% 4.48/4.68      inference('sup-', [status(thm)], ['87', '196'])).
% 4.48/4.68  thf('198', plain,
% 4.48/4.68      ((((r1_lattices @ sk_A @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 4.48/4.68         | (v2_struct_0 @ sk_A)
% 4.48/4.68         | (r3_lattice3 @ sk_A @ sk_B @ sk_C)))
% 4.48/4.68         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))))),
% 4.48/4.68      inference('simplify', [status(thm)], ['197'])).
% 4.48/4.69  thf('199', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf('200', plain,
% 4.48/4.69      (![X4 : $i, X5 : $i, X8 : $i]:
% 4.48/4.69         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 4.48/4.69          | ~ (r1_lattices @ X5 @ X4 @ (sk_D @ X8 @ X4 @ X5))
% 4.48/4.69          | (r3_lattice3 @ X5 @ X4 @ X8)
% 4.48/4.69          | ~ (l3_lattices @ X5)
% 4.48/4.69          | (v2_struct_0 @ X5))),
% 4.48/4.69      inference('cnf', [status(esa)], [d16_lattice3])).
% 4.48/4.69  thf('201', plain,
% 4.48/4.69      (![X0 : $i]:
% 4.48/4.69         ((v2_struct_0 @ sk_A)
% 4.48/4.69          | ~ (l3_lattices @ sk_A)
% 4.48/4.69          | (r3_lattice3 @ sk_A @ sk_B @ X0)
% 4.48/4.69          | ~ (r1_lattices @ sk_A @ sk_B @ (sk_D @ X0 @ sk_B @ sk_A)))),
% 4.48/4.69      inference('sup-', [status(thm)], ['199', '200'])).
% 4.48/4.69  thf('202', plain, ((l3_lattices @ sk_A)),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf('203', plain,
% 4.48/4.69      (![X0 : $i]:
% 4.48/4.69         ((v2_struct_0 @ sk_A)
% 4.48/4.69          | (r3_lattice3 @ sk_A @ sk_B @ X0)
% 4.48/4.69          | ~ (r1_lattices @ sk_A @ sk_B @ (sk_D @ X0 @ sk_B @ sk_A)))),
% 4.48/4.69      inference('demod', [status(thm)], ['201', '202'])).
% 4.48/4.69  thf('204', plain, (~ (v2_struct_0 @ sk_A)),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf('205', plain,
% 4.48/4.69      (![X0 : $i]:
% 4.48/4.69         (~ (r1_lattices @ sk_A @ sk_B @ (sk_D @ X0 @ sk_B @ sk_A))
% 4.48/4.69          | (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 4.48/4.69      inference('clc', [status(thm)], ['203', '204'])).
% 4.48/4.69  thf('206', plain,
% 4.48/4.69      ((((r3_lattice3 @ sk_A @ sk_B @ sk_C) | (v2_struct_0 @ sk_A)))
% 4.48/4.69         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))))),
% 4.48/4.69      inference('clc', [status(thm)], ['198', '205'])).
% 4.48/4.69  thf('207', plain, (~ (v2_struct_0 @ sk_A)),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf('208', plain,
% 4.48/4.69      (((r3_lattice3 @ sk_A @ sk_B @ sk_C))
% 4.48/4.69         <= ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))))),
% 4.48/4.69      inference('clc', [status(thm)], ['206', '207'])).
% 4.48/4.69  thf('209', plain,
% 4.48/4.69      ((~ (r3_lattice3 @ sk_A @ sk_B @ sk_C))
% 4.48/4.69         <= (~ ((r3_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 4.48/4.69      inference('split', [status(esa)], ['2'])).
% 4.48/4.69  thf('210', plain,
% 4.48/4.69      (((r3_lattice3 @ sk_A @ sk_B @ sk_C)) | 
% 4.48/4.69       ~ (((sk_B) = (k16_lattice3 @ sk_A @ sk_C)))),
% 4.48/4.69      inference('sup-', [status(thm)], ['208', '209'])).
% 4.48/4.69  thf('211', plain,
% 4.48/4.69      (((r3_lattice3 @ sk_A @ sk_B @ sk_C)) | 
% 4.48/4.69       (((sk_B) = (k16_lattice3 @ sk_A @ sk_C)))),
% 4.48/4.69      inference('split', [status(esa)], ['19'])).
% 4.48/4.69  thf('212', plain,
% 4.48/4.69      (![X18 : $i, X19 : $i]:
% 4.48/4.69         (((k16_lattice3 @ X18 @ X19)
% 4.48/4.69            = (k15_lattice3 @ X18 @ (a_2_1_lattice3 @ X18 @ X19)))
% 4.48/4.69          | ~ (l3_lattices @ X18)
% 4.48/4.69          | (v2_struct_0 @ X18))),
% 4.48/4.69      inference('cnf', [status(esa)], [d22_lattice3])).
% 4.48/4.69  thf('213', plain,
% 4.48/4.69      (((r3_lattice3 @ sk_A @ sk_B @ sk_C))
% 4.48/4.69         <= (((r3_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 4.48/4.69      inference('split', [status(esa)], ['19'])).
% 4.48/4.69  thf('214', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf('215', plain,
% 4.48/4.69      (![X20 : $i, X21 : $i, X23 : $i]:
% 4.48/4.69         (~ (r3_lattice3 @ X20 @ X23 @ X21)
% 4.48/4.69          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X20))
% 4.48/4.69          | (r2_hidden @ X23 @ (a_2_1_lattice3 @ X20 @ X21))
% 4.48/4.69          | (v2_struct_0 @ X20)
% 4.48/4.69          | ~ (l3_lattices @ X20))),
% 4.48/4.69      inference('simplify', [status(thm)], ['10'])).
% 4.48/4.69  thf('216', plain,
% 4.48/4.69      (![X0 : $i]:
% 4.48/4.69         (~ (l3_lattices @ sk_A)
% 4.48/4.69          | (v2_struct_0 @ sk_A)
% 4.48/4.69          | (r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 4.48/4.69          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 4.48/4.69      inference('sup-', [status(thm)], ['214', '215'])).
% 4.48/4.69  thf('217', plain, ((l3_lattices @ sk_A)),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf('218', plain,
% 4.48/4.69      (![X0 : $i]:
% 4.48/4.69         ((v2_struct_0 @ sk_A)
% 4.48/4.69          | (r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 4.48/4.69          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 4.48/4.69      inference('demod', [status(thm)], ['216', '217'])).
% 4.48/4.69  thf('219', plain, (~ (v2_struct_0 @ sk_A)),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf('220', plain,
% 4.48/4.69      (![X0 : $i]:
% 4.48/4.69         (~ (r3_lattice3 @ sk_A @ sk_B @ X0)
% 4.48/4.69          | (r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0)))),
% 4.48/4.69      inference('clc', [status(thm)], ['218', '219'])).
% 4.48/4.69  thf('221', plain,
% 4.48/4.69      (((r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 4.48/4.69         <= (((r3_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 4.48/4.69      inference('sup-', [status(thm)], ['213', '220'])).
% 4.48/4.69  thf('222', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf('223', plain,
% 4.48/4.69      (![X9 : $i, X10 : $i, X13 : $i]:
% 4.48/4.69         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 4.48/4.69          | (r2_hidden @ (sk_D_1 @ X13 @ X9 @ X10) @ X13)
% 4.48/4.69          | (r4_lattice3 @ X10 @ X9 @ X13)
% 4.48/4.69          | ~ (l3_lattices @ X10)
% 4.48/4.69          | (v2_struct_0 @ X10))),
% 4.48/4.69      inference('cnf', [status(esa)], [d17_lattice3])).
% 4.48/4.69  thf('224', plain,
% 4.48/4.69      (![X0 : $i]:
% 4.48/4.69         ((v2_struct_0 @ sk_A)
% 4.48/4.69          | ~ (l3_lattices @ sk_A)
% 4.48/4.69          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 4.48/4.69          | (r2_hidden @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0))),
% 4.48/4.69      inference('sup-', [status(thm)], ['222', '223'])).
% 4.48/4.69  thf('225', plain, ((l3_lattices @ sk_A)),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf('226', plain,
% 4.48/4.69      (![X0 : $i]:
% 4.48/4.69         ((v2_struct_0 @ sk_A)
% 4.48/4.69          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 4.48/4.69          | (r2_hidden @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0))),
% 4.48/4.69      inference('demod', [status(thm)], ['224', '225'])).
% 4.48/4.69  thf('227', plain, (~ (v2_struct_0 @ sk_A)),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf('228', plain,
% 4.48/4.69      (![X0 : $i]:
% 4.48/4.69         ((r2_hidden @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0)
% 4.48/4.69          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 4.48/4.69      inference('clc', [status(thm)], ['226', '227'])).
% 4.48/4.69  thf('229', plain,
% 4.48/4.69      (![X20 : $i, X21 : $i, X22 : $i]:
% 4.48/4.69         (~ (l3_lattices @ X20)
% 4.48/4.69          | (v2_struct_0 @ X20)
% 4.48/4.69          | ((X22) = (sk_D_3 @ X21 @ X20 @ X22))
% 4.48/4.69          | ~ (r2_hidden @ X22 @ (a_2_1_lattice3 @ X20 @ X21)))),
% 4.48/4.69      inference('cnf', [status(esa)], [fraenkel_a_2_1_lattice3])).
% 4.48/4.69  thf('230', plain,
% 4.48/4.69      (![X0 : $i, X1 : $i]:
% 4.48/4.69         ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0))
% 4.48/4.69          | ((sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A)
% 4.48/4.69              = (sk_D_3 @ X0 @ X1 @ 
% 4.48/4.69                 (sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A)))
% 4.48/4.69          | (v2_struct_0 @ X1)
% 4.48/4.69          | ~ (l3_lattices @ X1))),
% 4.48/4.69      inference('sup-', [status(thm)], ['228', '229'])).
% 4.48/4.69  thf('231', plain,
% 4.48/4.69      (![X0 : $i]:
% 4.48/4.69         ((r2_hidden @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0)
% 4.48/4.69          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 4.48/4.69      inference('clc', [status(thm)], ['226', '227'])).
% 4.48/4.69  thf('232', plain,
% 4.48/4.69      (![X20 : $i, X21 : $i, X22 : $i]:
% 4.48/4.69         (~ (l3_lattices @ X20)
% 4.48/4.69          | (v2_struct_0 @ X20)
% 4.48/4.69          | (r3_lattice3 @ X20 @ (sk_D_3 @ X21 @ X20 @ X22) @ X21)
% 4.48/4.69          | ~ (r2_hidden @ X22 @ (a_2_1_lattice3 @ X20 @ X21)))),
% 4.48/4.69      inference('cnf', [status(esa)], [fraenkel_a_2_1_lattice3])).
% 4.48/4.69  thf('233', plain,
% 4.48/4.69      (![X0 : $i, X1 : $i]:
% 4.48/4.69         ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0))
% 4.48/4.69          | (r3_lattice3 @ X1 @ 
% 4.48/4.69             (sk_D_3 @ X0 @ X1 @ 
% 4.48/4.69              (sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A)) @ 
% 4.48/4.69             X0)
% 4.48/4.69          | (v2_struct_0 @ X1)
% 4.48/4.69          | ~ (l3_lattices @ X1))),
% 4.48/4.69      inference('sup-', [status(thm)], ['231', '232'])).
% 4.48/4.69  thf('234', plain,
% 4.48/4.69      (![X0 : $i, X1 : $i]:
% 4.48/4.69         ((r3_lattice3 @ X1 @ 
% 4.48/4.69           (sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A) @ X0)
% 4.48/4.69          | ~ (l3_lattices @ X1)
% 4.48/4.69          | (v2_struct_0 @ X1)
% 4.48/4.69          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0))
% 4.48/4.69          | ~ (l3_lattices @ X1)
% 4.48/4.69          | (v2_struct_0 @ X1)
% 4.48/4.69          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0)))),
% 4.48/4.69      inference('sup+', [status(thm)], ['230', '233'])).
% 4.48/4.69  thf('235', plain,
% 4.48/4.69      (![X0 : $i, X1 : $i]:
% 4.48/4.69         ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0))
% 4.48/4.69          | (v2_struct_0 @ X1)
% 4.48/4.69          | ~ (l3_lattices @ X1)
% 4.48/4.69          | (r3_lattice3 @ X1 @ 
% 4.48/4.69             (sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A) @ X0))),
% 4.48/4.69      inference('simplify', [status(thm)], ['234'])).
% 4.48/4.69  thf('236', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf('237', plain,
% 4.48/4.69      (![X9 : $i, X10 : $i, X13 : $i]:
% 4.48/4.69         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 4.48/4.69          | (m1_subset_1 @ (sk_D_1 @ X13 @ X9 @ X10) @ (u1_struct_0 @ X10))
% 4.48/4.69          | (r4_lattice3 @ X10 @ X9 @ X13)
% 4.48/4.69          | ~ (l3_lattices @ X10)
% 4.48/4.69          | (v2_struct_0 @ X10))),
% 4.48/4.69      inference('cnf', [status(esa)], [d17_lattice3])).
% 4.48/4.69  thf('238', plain,
% 4.48/4.69      (![X0 : $i]:
% 4.48/4.69         ((v2_struct_0 @ sk_A)
% 4.48/4.69          | ~ (l3_lattices @ sk_A)
% 4.48/4.69          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 4.48/4.69          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 4.48/4.69      inference('sup-', [status(thm)], ['236', '237'])).
% 4.48/4.69  thf('239', plain, ((l3_lattices @ sk_A)),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf('240', plain,
% 4.48/4.69      (![X0 : $i]:
% 4.48/4.69         ((v2_struct_0 @ sk_A)
% 4.48/4.69          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 4.48/4.69          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 4.48/4.69      inference('demod', [status(thm)], ['238', '239'])).
% 4.48/4.69  thf('241', plain, (~ (v2_struct_0 @ sk_A)),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf('242', plain,
% 4.48/4.69      (![X0 : $i]:
% 4.48/4.69         ((m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 4.48/4.69          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 4.48/4.69      inference('clc', [status(thm)], ['240', '241'])).
% 4.48/4.69  thf('243', plain,
% 4.48/4.69      ((![X24 : $i]:
% 4.48/4.69          (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_A))
% 4.48/4.69           | (r3_lattices @ sk_A @ X24 @ sk_B)
% 4.48/4.69           | ~ (r3_lattice3 @ sk_A @ X24 @ sk_C)))
% 4.48/4.69         <= ((![X24 : $i]:
% 4.48/4.69                (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_A))
% 4.48/4.69                 | (r3_lattices @ sk_A @ X24 @ sk_B)
% 4.48/4.69                 | ~ (r3_lattice3 @ sk_A @ X24 @ sk_C))))),
% 4.48/4.69      inference('split', [status(esa)], ['0'])).
% 4.48/4.69  thf('244', plain,
% 4.48/4.69      ((![X0 : $i]:
% 4.48/4.69          ((r4_lattice3 @ sk_A @ sk_B @ X0)
% 4.48/4.69           | ~ (r3_lattice3 @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_C)
% 4.48/4.69           | (r3_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_B)))
% 4.48/4.69         <= ((![X24 : $i]:
% 4.48/4.69                (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_A))
% 4.48/4.69                 | (r3_lattices @ sk_A @ X24 @ sk_B)
% 4.48/4.69                 | ~ (r3_lattice3 @ sk_A @ X24 @ sk_C))))),
% 4.48/4.69      inference('sup-', [status(thm)], ['242', '243'])).
% 4.48/4.69  thf('245', plain,
% 4.48/4.69      (((~ (l3_lattices @ sk_A)
% 4.48/4.69         | (v2_struct_0 @ sk_A)
% 4.48/4.69         | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))
% 4.48/4.69         | (r3_lattices @ sk_A @ 
% 4.48/4.69            (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_B @ sk_A) @ sk_B)
% 4.48/4.69         | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))))
% 4.48/4.69         <= ((![X24 : $i]:
% 4.48/4.69                (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_A))
% 4.48/4.69                 | (r3_lattices @ sk_A @ X24 @ sk_B)
% 4.48/4.69                 | ~ (r3_lattice3 @ sk_A @ X24 @ sk_C))))),
% 4.48/4.69      inference('sup-', [status(thm)], ['235', '244'])).
% 4.48/4.69  thf('246', plain, ((l3_lattices @ sk_A)),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf('247', plain,
% 4.48/4.69      ((((v2_struct_0 @ sk_A)
% 4.48/4.69         | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))
% 4.48/4.69         | (r3_lattices @ sk_A @ 
% 4.48/4.69            (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_B @ sk_A) @ sk_B)
% 4.48/4.69         | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))))
% 4.48/4.69         <= ((![X24 : $i]:
% 4.48/4.69                (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_A))
% 4.48/4.69                 | (r3_lattices @ sk_A @ X24 @ sk_B)
% 4.48/4.69                 | ~ (r3_lattice3 @ sk_A @ X24 @ sk_C))))),
% 4.48/4.69      inference('demod', [status(thm)], ['245', '246'])).
% 4.48/4.69  thf('248', plain,
% 4.48/4.69      ((((r3_lattices @ sk_A @ 
% 4.48/4.69          (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_B @ sk_A) @ sk_B)
% 4.48/4.69         | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))
% 4.48/4.69         | (v2_struct_0 @ sk_A)))
% 4.48/4.69         <= ((![X24 : $i]:
% 4.48/4.69                (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_A))
% 4.48/4.69                 | (r3_lattices @ sk_A @ X24 @ sk_B)
% 4.48/4.69                 | ~ (r3_lattice3 @ sk_A @ X24 @ sk_C))))),
% 4.48/4.69      inference('simplify', [status(thm)], ['247'])).
% 4.48/4.69  thf('249', plain, (~ (v2_struct_0 @ sk_A)),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf('250', plain,
% 4.48/4.69      ((((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))
% 4.48/4.69         | (r3_lattices @ sk_A @ 
% 4.48/4.69            (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_B @ sk_A) @ sk_B)))
% 4.48/4.69         <= ((![X24 : $i]:
% 4.48/4.69                (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_A))
% 4.48/4.69                 | (r3_lattices @ sk_A @ X24 @ sk_B)
% 4.48/4.69                 | ~ (r3_lattice3 @ sk_A @ X24 @ sk_C))))),
% 4.48/4.69      inference('clc', [status(thm)], ['248', '249'])).
% 4.48/4.69  thf('251', plain,
% 4.48/4.69      (![X0 : $i]:
% 4.48/4.69         ((m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 4.48/4.69          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 4.48/4.69      inference('clc', [status(thm)], ['240', '241'])).
% 4.48/4.69  thf('252', plain,
% 4.48/4.69      (![X1 : $i, X2 : $i, X3 : $i]:
% 4.48/4.69         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 4.48/4.69          | ~ (l3_lattices @ X2)
% 4.48/4.69          | ~ (v9_lattices @ X2)
% 4.48/4.69          | ~ (v8_lattices @ X2)
% 4.48/4.69          | ~ (v6_lattices @ X2)
% 4.48/4.69          | (v2_struct_0 @ X2)
% 4.48/4.69          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 4.48/4.69          | (r1_lattices @ X2 @ X1 @ X3)
% 4.48/4.69          | ~ (r3_lattices @ X2 @ X1 @ X3))),
% 4.48/4.69      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 4.48/4.69  thf('253', plain,
% 4.48/4.69      (![X0 : $i, X1 : $i]:
% 4.48/4.69         ((r4_lattice3 @ sk_A @ sk_B @ X0)
% 4.48/4.69          | ~ (r3_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X1)
% 4.48/4.69          | (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X1)
% 4.48/4.69          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 4.48/4.69          | (v2_struct_0 @ sk_A)
% 4.48/4.69          | ~ (v6_lattices @ sk_A)
% 4.48/4.69          | ~ (v8_lattices @ sk_A)
% 4.48/4.69          | ~ (v9_lattices @ sk_A)
% 4.48/4.69          | ~ (l3_lattices @ sk_A))),
% 4.48/4.69      inference('sup-', [status(thm)], ['251', '252'])).
% 4.48/4.69  thf('254', plain, ((v6_lattices @ sk_A)),
% 4.48/4.69      inference('demod', [status(thm)], ['56', '57', '58'])).
% 4.48/4.69  thf('255', plain, ((v8_lattices @ sk_A)),
% 4.48/4.69      inference('demod', [status(thm)], ['62', '63', '64'])).
% 4.48/4.69  thf('256', plain, ((v9_lattices @ sk_A)),
% 4.48/4.69      inference('demod', [status(thm)], ['68', '69', '70'])).
% 4.48/4.69  thf('257', plain, ((l3_lattices @ sk_A)),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf('258', plain,
% 4.48/4.69      (![X0 : $i, X1 : $i]:
% 4.48/4.69         ((r4_lattice3 @ sk_A @ sk_B @ X0)
% 4.48/4.69          | ~ (r3_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X1)
% 4.48/4.69          | (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X1)
% 4.48/4.69          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 4.48/4.69          | (v2_struct_0 @ sk_A))),
% 4.48/4.69      inference('demod', [status(thm)], ['253', '254', '255', '256', '257'])).
% 4.48/4.69  thf('259', plain,
% 4.48/4.69      ((((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))
% 4.48/4.69         | (v2_struct_0 @ sk_A)
% 4.48/4.69         | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 4.48/4.69         | (r1_lattices @ sk_A @ 
% 4.48/4.69            (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_B @ sk_A) @ sk_B)
% 4.48/4.69         | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))))
% 4.48/4.69         <= ((![X24 : $i]:
% 4.48/4.69                (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_A))
% 4.48/4.69                 | (r3_lattices @ sk_A @ X24 @ sk_B)
% 4.48/4.69                 | ~ (r3_lattice3 @ sk_A @ X24 @ sk_C))))),
% 4.48/4.69      inference('sup-', [status(thm)], ['250', '258'])).
% 4.48/4.69  thf('260', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf('261', plain,
% 4.48/4.69      ((((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))
% 4.48/4.69         | (v2_struct_0 @ sk_A)
% 4.48/4.69         | (r1_lattices @ sk_A @ 
% 4.48/4.69            (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_B @ sk_A) @ sk_B)
% 4.48/4.69         | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))))
% 4.48/4.69         <= ((![X24 : $i]:
% 4.48/4.69                (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_A))
% 4.48/4.69                 | (r3_lattices @ sk_A @ X24 @ sk_B)
% 4.48/4.69                 | ~ (r3_lattice3 @ sk_A @ X24 @ sk_C))))),
% 4.48/4.69      inference('demod', [status(thm)], ['259', '260'])).
% 4.48/4.69  thf('262', plain,
% 4.48/4.69      ((((r1_lattices @ sk_A @ 
% 4.48/4.69          (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_B @ sk_A) @ sk_B)
% 4.48/4.69         | (v2_struct_0 @ sk_A)
% 4.48/4.69         | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))))
% 4.48/4.69         <= ((![X24 : $i]:
% 4.48/4.69                (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_A))
% 4.48/4.69                 | (r3_lattices @ sk_A @ X24 @ sk_B)
% 4.48/4.69                 | ~ (r3_lattice3 @ sk_A @ X24 @ sk_C))))),
% 4.48/4.69      inference('simplify', [status(thm)], ['261'])).
% 4.48/4.69  thf('263', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf('264', plain,
% 4.48/4.69      (![X9 : $i, X10 : $i, X13 : $i]:
% 4.48/4.69         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 4.48/4.69          | ~ (r1_lattices @ X10 @ (sk_D_1 @ X13 @ X9 @ X10) @ X9)
% 4.48/4.69          | (r4_lattice3 @ X10 @ X9 @ X13)
% 4.48/4.69          | ~ (l3_lattices @ X10)
% 4.48/4.69          | (v2_struct_0 @ X10))),
% 4.48/4.69      inference('cnf', [status(esa)], [d17_lattice3])).
% 4.48/4.69  thf('265', plain,
% 4.48/4.69      (![X0 : $i]:
% 4.48/4.69         ((v2_struct_0 @ sk_A)
% 4.48/4.69          | ~ (l3_lattices @ sk_A)
% 4.48/4.69          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 4.48/4.69          | ~ (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_B))),
% 4.48/4.69      inference('sup-', [status(thm)], ['263', '264'])).
% 4.48/4.69  thf('266', plain, ((l3_lattices @ sk_A)),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf('267', plain,
% 4.48/4.69      (![X0 : $i]:
% 4.48/4.69         ((v2_struct_0 @ sk_A)
% 4.48/4.69          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 4.48/4.69          | ~ (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_B))),
% 4.48/4.69      inference('demod', [status(thm)], ['265', '266'])).
% 4.48/4.69  thf('268', plain, (~ (v2_struct_0 @ sk_A)),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf('269', plain,
% 4.48/4.69      (![X0 : $i]:
% 4.48/4.69         (~ (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_B)
% 4.48/4.69          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 4.48/4.69      inference('clc', [status(thm)], ['267', '268'])).
% 4.48/4.69  thf('270', plain,
% 4.48/4.69      ((((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))
% 4.48/4.69         | (v2_struct_0 @ sk_A)))
% 4.48/4.69         <= ((![X24 : $i]:
% 4.48/4.69                (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_A))
% 4.48/4.69                 | (r3_lattices @ sk_A @ X24 @ sk_B)
% 4.48/4.69                 | ~ (r3_lattice3 @ sk_A @ X24 @ sk_C))))),
% 4.48/4.69      inference('clc', [status(thm)], ['262', '269'])).
% 4.48/4.69  thf('271', plain, (~ (v2_struct_0 @ sk_A)),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf('272', plain,
% 4.48/4.69      (((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 4.48/4.69         <= ((![X24 : $i]:
% 4.48/4.69                (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_A))
% 4.48/4.69                 | (r3_lattices @ sk_A @ X24 @ sk_B)
% 4.48/4.69                 | ~ (r3_lattice3 @ sk_A @ X24 @ sk_C))))),
% 4.48/4.69      inference('clc', [status(thm)], ['270', '271'])).
% 4.48/4.69  thf('273', plain,
% 4.48/4.69      (![X0 : $i]:
% 4.48/4.69         ((v2_struct_0 @ sk_A)
% 4.48/4.69          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0)
% 4.48/4.69          | (r4_lattice3 @ sk_A @ (sk_D_2 @ sk_B @ X0 @ sk_A) @ X0)
% 4.48/4.69          | ((sk_B) = (k15_lattice3 @ sk_A @ X0)))),
% 4.48/4.69      inference('demod', [status(thm)], ['163', '164', '165', '166'])).
% 4.48/4.69  thf('274', plain,
% 4.48/4.69      (((((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 4.48/4.69         | (r4_lattice3 @ sk_A @ 
% 4.48/4.69            (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A) @ 
% 4.48/4.69            (a_2_1_lattice3 @ sk_A @ sk_C))
% 4.48/4.69         | (v2_struct_0 @ sk_A)))
% 4.48/4.69         <= ((![X24 : $i]:
% 4.48/4.69                (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_A))
% 4.48/4.69                 | (r3_lattices @ sk_A @ X24 @ sk_B)
% 4.48/4.69                 | ~ (r3_lattice3 @ sk_A @ X24 @ sk_C))))),
% 4.48/4.69      inference('sup-', [status(thm)], ['272', '273'])).
% 4.48/4.69  thf('275', plain, (~ (v2_struct_0 @ sk_A)),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf('276', plain,
% 4.48/4.69      ((((r4_lattice3 @ sk_A @ 
% 4.48/4.69          (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A) @ 
% 4.48/4.69          (a_2_1_lattice3 @ sk_A @ sk_C))
% 4.48/4.69         | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))))
% 4.48/4.69         <= ((![X24 : $i]:
% 4.48/4.69                (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_A))
% 4.48/4.69                 | (r3_lattices @ sk_A @ X24 @ sk_B)
% 4.48/4.69                 | ~ (r3_lattice3 @ sk_A @ X24 @ sk_C))))),
% 4.48/4.69      inference('clc', [status(thm)], ['274', '275'])).
% 4.48/4.69  thf('277', plain,
% 4.48/4.69      (((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 4.48/4.69         <= ((![X24 : $i]:
% 4.48/4.69                (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_A))
% 4.48/4.69                 | (r3_lattices @ sk_A @ X24 @ sk_B)
% 4.48/4.69                 | ~ (r3_lattice3 @ sk_A @ X24 @ sk_C))))),
% 4.48/4.69      inference('clc', [status(thm)], ['270', '271'])).
% 4.48/4.69  thf('278', plain,
% 4.48/4.69      (![X0 : $i]:
% 4.48/4.69         ((v2_struct_0 @ sk_A)
% 4.48/4.69          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0)
% 4.48/4.69          | (m1_subset_1 @ (sk_D_2 @ sk_B @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 4.48/4.69          | ((sk_B) = (k15_lattice3 @ sk_A @ X0)))),
% 4.48/4.69      inference('demod', [status(thm)], ['151', '152', '153', '154'])).
% 4.48/4.69  thf('279', plain,
% 4.48/4.69      (((((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 4.48/4.69         | (m1_subset_1 @ 
% 4.48/4.69            (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A) @ 
% 4.48/4.69            (u1_struct_0 @ sk_A))
% 4.48/4.69         | (v2_struct_0 @ sk_A)))
% 4.48/4.69         <= ((![X24 : $i]:
% 4.48/4.69                (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_A))
% 4.48/4.69                 | (r3_lattices @ sk_A @ X24 @ sk_B)
% 4.48/4.69                 | ~ (r3_lattice3 @ sk_A @ X24 @ sk_C))))),
% 4.48/4.69      inference('sup-', [status(thm)], ['277', '278'])).
% 4.48/4.69  thf('280', plain, (~ (v2_struct_0 @ sk_A)),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf('281', plain,
% 4.48/4.69      ((((m1_subset_1 @ 
% 4.48/4.69          (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A) @ 
% 4.48/4.69          (u1_struct_0 @ sk_A))
% 4.48/4.69         | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))))
% 4.48/4.69         <= ((![X24 : $i]:
% 4.48/4.69                (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_A))
% 4.48/4.69                 | (r3_lattices @ sk_A @ X24 @ sk_B)
% 4.48/4.69                 | ~ (r3_lattice3 @ sk_A @ X24 @ sk_C))))),
% 4.48/4.69      inference('clc', [status(thm)], ['279', '280'])).
% 4.48/4.69  thf('282', plain,
% 4.48/4.69      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 4.48/4.69         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 4.48/4.69          | ~ (r4_lattice3 @ X10 @ X9 @ X11)
% 4.48/4.69          | ~ (r2_hidden @ X12 @ X11)
% 4.48/4.69          | (r1_lattices @ X10 @ X12 @ X9)
% 4.48/4.69          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X10))
% 4.48/4.69          | ~ (l3_lattices @ X10)
% 4.48/4.69          | (v2_struct_0 @ X10))),
% 4.48/4.69      inference('cnf', [status(esa)], [d17_lattice3])).
% 4.48/4.69  thf('283', plain,
% 4.48/4.69      ((![X0 : $i, X1 : $i]:
% 4.48/4.69          (((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 4.48/4.69           | (v2_struct_0 @ sk_A)
% 4.48/4.69           | ~ (l3_lattices @ sk_A)
% 4.48/4.69           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 4.48/4.69           | (r1_lattices @ sk_A @ X0 @ 
% 4.48/4.69              (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A))
% 4.48/4.69           | ~ (r2_hidden @ X0 @ X1)
% 4.48/4.69           | ~ (r4_lattice3 @ sk_A @ 
% 4.48/4.69                (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A) @ X1)))
% 4.48/4.69         <= ((![X24 : $i]:
% 4.48/4.69                (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_A))
% 4.48/4.69                 | (r3_lattices @ sk_A @ X24 @ sk_B)
% 4.48/4.69                 | ~ (r3_lattice3 @ sk_A @ X24 @ sk_C))))),
% 4.48/4.69      inference('sup-', [status(thm)], ['281', '282'])).
% 4.48/4.69  thf('284', plain, ((l3_lattices @ sk_A)),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf('285', plain,
% 4.48/4.69      ((![X0 : $i, X1 : $i]:
% 4.48/4.69          (((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 4.48/4.69           | (v2_struct_0 @ sk_A)
% 4.48/4.69           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 4.48/4.69           | (r1_lattices @ sk_A @ X0 @ 
% 4.48/4.69              (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A))
% 4.48/4.69           | ~ (r2_hidden @ X0 @ X1)
% 4.48/4.69           | ~ (r4_lattice3 @ sk_A @ 
% 4.48/4.69                (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A) @ X1)))
% 4.48/4.69         <= ((![X24 : $i]:
% 4.48/4.69                (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_A))
% 4.48/4.69                 | (r3_lattices @ sk_A @ X24 @ sk_B)
% 4.48/4.69                 | ~ (r3_lattice3 @ sk_A @ X24 @ sk_C))))),
% 4.48/4.69      inference('demod', [status(thm)], ['283', '284'])).
% 4.48/4.69  thf('286', plain,
% 4.48/4.69      ((![X0 : $i]:
% 4.48/4.69          (((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 4.48/4.69           | ~ (r2_hidden @ X0 @ (a_2_1_lattice3 @ sk_A @ sk_C))
% 4.48/4.69           | (r1_lattices @ sk_A @ X0 @ 
% 4.48/4.69              (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A))
% 4.48/4.69           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 4.48/4.69           | (v2_struct_0 @ sk_A)
% 4.48/4.69           | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))))
% 4.48/4.69         <= ((![X24 : $i]:
% 4.48/4.69                (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_A))
% 4.48/4.69                 | (r3_lattices @ sk_A @ X24 @ sk_B)
% 4.48/4.69                 | ~ (r3_lattice3 @ sk_A @ X24 @ sk_C))))),
% 4.48/4.69      inference('sup-', [status(thm)], ['276', '285'])).
% 4.48/4.69  thf('287', plain,
% 4.48/4.69      ((![X0 : $i]:
% 4.48/4.69          ((v2_struct_0 @ sk_A)
% 4.48/4.69           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 4.48/4.69           | (r1_lattices @ sk_A @ X0 @ 
% 4.48/4.69              (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A))
% 4.48/4.69           | ~ (r2_hidden @ X0 @ (a_2_1_lattice3 @ sk_A @ sk_C))
% 4.48/4.69           | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))))
% 4.48/4.69         <= ((![X24 : $i]:
% 4.48/4.69                (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_A))
% 4.48/4.69                 | (r3_lattices @ sk_A @ X24 @ sk_B)
% 4.48/4.69                 | ~ (r3_lattice3 @ sk_A @ X24 @ sk_C))))),
% 4.48/4.69      inference('simplify', [status(thm)], ['286'])).
% 4.48/4.69  thf('288', plain,
% 4.48/4.69      (((((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 4.48/4.69         | (r1_lattices @ sk_A @ sk_B @ 
% 4.48/4.69            (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A))
% 4.48/4.69         | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 4.48/4.69         | (v2_struct_0 @ sk_A)))
% 4.48/4.69         <= (((r3_lattice3 @ sk_A @ sk_B @ sk_C)) & 
% 4.48/4.69             (![X24 : $i]:
% 4.48/4.69                (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_A))
% 4.48/4.69                 | (r3_lattices @ sk_A @ X24 @ sk_B)
% 4.48/4.69                 | ~ (r3_lattice3 @ sk_A @ X24 @ sk_C))))),
% 4.48/4.69      inference('sup-', [status(thm)], ['221', '287'])).
% 4.48/4.69  thf('289', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf('290', plain,
% 4.48/4.69      (((((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 4.48/4.69         | (r1_lattices @ sk_A @ sk_B @ 
% 4.48/4.69            (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A))
% 4.48/4.69         | (v2_struct_0 @ sk_A)))
% 4.48/4.69         <= (((r3_lattice3 @ sk_A @ sk_B @ sk_C)) & 
% 4.48/4.69             (![X24 : $i]:
% 4.48/4.69                (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_A))
% 4.48/4.69                 | (r3_lattices @ sk_A @ X24 @ sk_B)
% 4.48/4.69                 | ~ (r3_lattice3 @ sk_A @ X24 @ sk_C))))),
% 4.48/4.69      inference('demod', [status(thm)], ['288', '289'])).
% 4.48/4.69  thf('291', plain, (~ (v2_struct_0 @ sk_A)),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf('292', plain,
% 4.48/4.69      ((((r1_lattices @ sk_A @ sk_B @ 
% 4.48/4.69          (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A))
% 4.48/4.69         | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))))
% 4.48/4.69         <= (((r3_lattice3 @ sk_A @ sk_B @ sk_C)) & 
% 4.48/4.69             (![X24 : $i]:
% 4.48/4.69                (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_A))
% 4.48/4.69                 | (r3_lattices @ sk_A @ X24 @ sk_B)
% 4.48/4.69                 | ~ (r3_lattice3 @ sk_A @ X24 @ sk_C))))),
% 4.48/4.69      inference('clc', [status(thm)], ['290', '291'])).
% 4.48/4.69  thf('293', plain,
% 4.48/4.69      (![X14 : $i, X15 : $i, X16 : $i]:
% 4.48/4.69         (((X15) = (k15_lattice3 @ X14 @ X16))
% 4.48/4.69          | ~ (r1_lattices @ X14 @ X15 @ (sk_D_2 @ X15 @ X16 @ X14))
% 4.48/4.69          | ~ (r4_lattice3 @ X14 @ X15 @ X16)
% 4.48/4.69          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 4.48/4.69          | ~ (l3_lattices @ X14)
% 4.48/4.69          | ~ (v4_lattice3 @ X14)
% 4.48/4.69          | ~ (v10_lattices @ X14)
% 4.48/4.69          | (v2_struct_0 @ X14))),
% 4.48/4.69      inference('simplify', [status(thm)], ['183'])).
% 4.48/4.69  thf('294', plain,
% 4.48/4.69      (((((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 4.48/4.69         | (v2_struct_0 @ sk_A)
% 4.48/4.69         | ~ (v10_lattices @ sk_A)
% 4.48/4.69         | ~ (v4_lattice3 @ sk_A)
% 4.48/4.69         | ~ (l3_lattices @ sk_A)
% 4.48/4.69         | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 4.48/4.69         | ~ (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))
% 4.48/4.69         | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))))
% 4.48/4.69         <= (((r3_lattice3 @ sk_A @ sk_B @ sk_C)) & 
% 4.48/4.69             (![X24 : $i]:
% 4.48/4.69                (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_A))
% 4.48/4.69                 | (r3_lattices @ sk_A @ X24 @ sk_B)
% 4.48/4.69                 | ~ (r3_lattice3 @ sk_A @ X24 @ sk_C))))),
% 4.48/4.69      inference('sup-', [status(thm)], ['292', '293'])).
% 4.48/4.69  thf('295', plain, ((v10_lattices @ sk_A)),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf('296', plain, ((v4_lattice3 @ sk_A)),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf('297', plain, ((l3_lattices @ sk_A)),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf('298', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf('299', plain,
% 4.48/4.69      (((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 4.48/4.69         <= ((![X24 : $i]:
% 4.48/4.69                (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_A))
% 4.48/4.69                 | (r3_lattices @ sk_A @ X24 @ sk_B)
% 4.48/4.69                 | ~ (r3_lattice3 @ sk_A @ X24 @ sk_C))))),
% 4.48/4.69      inference('clc', [status(thm)], ['270', '271'])).
% 4.48/4.69  thf('300', plain,
% 4.48/4.69      (((((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 4.48/4.69         | (v2_struct_0 @ sk_A)
% 4.48/4.69         | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))))
% 4.48/4.69         <= (((r3_lattice3 @ sk_A @ sk_B @ sk_C)) & 
% 4.48/4.69             (![X24 : $i]:
% 4.48/4.69                (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_A))
% 4.48/4.69                 | (r3_lattices @ sk_A @ X24 @ sk_B)
% 4.48/4.69                 | ~ (r3_lattice3 @ sk_A @ X24 @ sk_C))))),
% 4.48/4.69      inference('demod', [status(thm)],
% 4.48/4.69                ['294', '295', '296', '297', '298', '299'])).
% 4.48/4.69  thf('301', plain,
% 4.48/4.69      ((((v2_struct_0 @ sk_A)
% 4.48/4.69         | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))))
% 4.48/4.69         <= (((r3_lattice3 @ sk_A @ sk_B @ sk_C)) & 
% 4.48/4.69             (![X24 : $i]:
% 4.48/4.69                (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_A))
% 4.48/4.69                 | (r3_lattices @ sk_A @ X24 @ sk_B)
% 4.48/4.69                 | ~ (r3_lattice3 @ sk_A @ X24 @ sk_C))))),
% 4.48/4.69      inference('simplify', [status(thm)], ['300'])).
% 4.48/4.69  thf('302', plain, (~ (v2_struct_0 @ sk_A)),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf('303', plain,
% 4.48/4.69      ((((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))
% 4.48/4.69         <= (((r3_lattice3 @ sk_A @ sk_B @ sk_C)) & 
% 4.48/4.69             (![X24 : $i]:
% 4.48/4.69                (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_A))
% 4.48/4.69                 | (r3_lattices @ sk_A @ X24 @ sk_B)
% 4.48/4.69                 | ~ (r3_lattice3 @ sk_A @ X24 @ sk_C))))),
% 4.48/4.69      inference('clc', [status(thm)], ['301', '302'])).
% 4.48/4.69  thf('304', plain,
% 4.48/4.69      (((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))
% 4.48/4.69         | (v2_struct_0 @ sk_A)
% 4.48/4.69         | ~ (l3_lattices @ sk_A)))
% 4.48/4.69         <= (((r3_lattice3 @ sk_A @ sk_B @ sk_C)) & 
% 4.48/4.69             (![X24 : $i]:
% 4.48/4.69                (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_A))
% 4.48/4.69                 | (r3_lattices @ sk_A @ X24 @ sk_B)
% 4.48/4.69                 | ~ (r3_lattice3 @ sk_A @ X24 @ sk_C))))),
% 4.48/4.69      inference('sup+', [status(thm)], ['212', '303'])).
% 4.48/4.69  thf('305', plain, ((l3_lattices @ sk_A)),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf('306', plain,
% 4.48/4.69      (((((sk_B) = (k16_lattice3 @ sk_A @ sk_C)) | (v2_struct_0 @ sk_A)))
% 4.48/4.69         <= (((r3_lattice3 @ sk_A @ sk_B @ sk_C)) & 
% 4.48/4.69             (![X24 : $i]:
% 4.48/4.69                (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_A))
% 4.48/4.69                 | (r3_lattices @ sk_A @ X24 @ sk_B)
% 4.48/4.69                 | ~ (r3_lattice3 @ sk_A @ X24 @ sk_C))))),
% 4.48/4.69      inference('demod', [status(thm)], ['304', '305'])).
% 4.48/4.69  thf('307', plain, (~ (v2_struct_0 @ sk_A)),
% 4.48/4.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.69  thf('308', plain,
% 4.48/4.69      ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C)))
% 4.48/4.69         <= (((r3_lattice3 @ sk_A @ sk_B @ sk_C)) & 
% 4.48/4.69             (![X24 : $i]:
% 4.48/4.69                (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_A))
% 4.48/4.69                 | (r3_lattices @ sk_A @ X24 @ sk_B)
% 4.48/4.69                 | ~ (r3_lattice3 @ sk_A @ X24 @ sk_C))))),
% 4.48/4.69      inference('clc', [status(thm)], ['306', '307'])).
% 4.48/4.69  thf('309', plain,
% 4.48/4.69      ((((sk_B) != (k16_lattice3 @ sk_A @ sk_C)))
% 4.48/4.69         <= (~ (((sk_B) = (k16_lattice3 @ sk_A @ sk_C))))),
% 4.48/4.69      inference('split', [status(esa)], ['2'])).
% 4.48/4.69  thf('310', plain,
% 4.48/4.69      ((((sk_B) != (sk_B)))
% 4.48/4.69         <= (~ (((sk_B) = (k16_lattice3 @ sk_A @ sk_C))) & 
% 4.48/4.69             ((r3_lattice3 @ sk_A @ sk_B @ sk_C)) & 
% 4.48/4.69             (![X24 : $i]:
% 4.48/4.69                (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_A))
% 4.48/4.69                 | (r3_lattices @ sk_A @ X24 @ sk_B)
% 4.48/4.69                 | ~ (r3_lattice3 @ sk_A @ X24 @ sk_C))))),
% 4.48/4.69      inference('sup-', [status(thm)], ['308', '309'])).
% 4.48/4.69  thf('311', plain,
% 4.48/4.69      (~ ((r3_lattice3 @ sk_A @ sk_B @ sk_C)) | 
% 4.48/4.69       ~
% 4.48/4.69       (![X24 : $i]:
% 4.48/4.69          (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ sk_A))
% 4.48/4.69           | (r3_lattices @ sk_A @ X24 @ sk_B)
% 4.48/4.69           | ~ (r3_lattice3 @ sk_A @ X24 @ sk_C))) | 
% 4.48/4.69       (((sk_B) = (k16_lattice3 @ sk_A @ sk_C)))),
% 4.48/4.69      inference('simplify', [status(thm)], ['310'])).
% 4.48/4.69  thf('312', plain, ($false),
% 4.48/4.69      inference('sat_resolution*', [status(thm)],
% 4.48/4.69                ['1', '3', '5', '7', '80', '210', '211', '311'])).
% 4.48/4.69  
% 4.48/4.69  % SZS output end Refutation
% 4.48/4.69  
% 4.48/4.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
