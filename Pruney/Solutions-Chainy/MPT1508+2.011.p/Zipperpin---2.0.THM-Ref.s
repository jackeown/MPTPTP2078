%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.x3kfLF2gFy

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:32 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 164 expanded)
%              Number of leaves         :   24 (  57 expanded)
%              Depth                    :   22
%              Number of atoms          :  943 (2448 expanded)
%              Number of equality atoms :   18 (  76 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(a_2_1_lattice3_type,type,(
    a_2_1_lattice3: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r3_lattice3_type,type,(
    r3_lattice3: $i > $i > $i > $o )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(r4_lattice3_type,type,(
    r4_lattice3: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

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

thf(d22_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( k16_lattice3 @ A @ B )
          = ( k15_lattice3 @ A @ ( a_2_1_lattice3 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k16_lattice3 @ X10 @ X11 )
        = ( k15_lattice3 @ X10 @ ( a_2_1_lattice3 @ X10 @ X11 ) ) )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d22_lattice3])).

thf('2',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ( r2_hidden @ ( sk_D_1 @ X9 @ X5 @ X6 ) @ X9 )
      | ( r4_lattice3 @ X6 @ X5 @ X9 )
      | ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(fraenkel_a_2_1_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( l3_lattices @ B ) )
     => ( ( r2_hidden @ A @ ( a_2_1_lattice3 @ B @ C ) )
      <=> ? [D: $i] :
            ( ( r3_lattice3 @ B @ D @ C )
            & ( A = D )
            & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( l3_lattices @ X12 )
      | ( v2_struct_0 @ X12 )
      | ( X14
        = ( sk_D_2 @ X13 @ X12 @ X14 ) )
      | ~ ( r2_hidden @ X14 @ ( a_2_1_lattice3 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_lattice3])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ X1 @ X0 ) )
      | ( ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A )
        = ( sk_D_2 @ X0 @ X1 @ ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('14',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( l3_lattices @ X12 )
      | ( v2_struct_0 @ X12 )
      | ( r3_lattice3 @ X12 @ ( sk_D_2 @ X13 @ X12 @ X14 ) @ X13 )
      | ~ ( r2_hidden @ X14 @ ( a_2_1_lattice3 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_lattice3])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ X1 @ X0 ) )
      | ( r3_lattice3 @ X1 @ ( sk_D_2 @ X0 @ X1 @ ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A ) ) @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ X1 @ ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A ) @ X0 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ X1 @ X0 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( r3_lattice3 @ X1 @ ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X9 @ X5 @ X6 ) @ ( u1_struct_0 @ X6 ) )
      | ( r4_lattice3 @ X6 @ X5 @ X9 )
      | ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['22','23'])).

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

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r3_lattice3 @ X1 @ X0 @ X2 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r1_lattices @ X1 @ X0 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X1 )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X1 )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X2 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ X0 ) @ sk_B @ sk_A ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','28'])).

thf('30',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ X0 ) @ sk_B @ sk_A ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ X0 ) @ sk_B @ sk_A ) @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ X0 ) @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','32'])).

thf('34',plain,
    ( ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_B @ sk_A ) @ sk_B )
    | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ~ ( r1_lattices @ X6 @ ( sk_D_1 @ X9 @ X5 @ X6 ) @ X5 )
      | ( r4_lattice3 @ X6 @ X5 @ X9 )
      | ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['34','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
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

thf('46',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ( ( k15_lattice3 @ X17 @ X18 )
        = X16 )
      | ~ ( r4_lattice3 @ X17 @ X16 @ X18 )
      | ~ ( r2_hidden @ X16 @ X18 )
      | ~ ( l3_lattices @ X17 )
      | ~ ( v4_lattice3 @ X17 )
      | ~ ( v10_lattices @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t41_lattice3])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( ( k15_lattice3 @ sk_A @ X0 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( ( k15_lattice3 @ sk_A @ X0 )
        = sk_B ) ) ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('52',plain,
    ( ( ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
      = sk_B )
    | ~ ( r2_hidden @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','51'])).

thf('53',plain,(
    r3_lattice3 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( l3_lattices @ X12 )
      | ( v2_struct_0 @ X12 )
      | ( r2_hidden @ X14 @ ( a_2_1_lattice3 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X12 ) )
      | ( X14 != X15 )
      | ~ ( r3_lattice3 @ X12 @ X15 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_lattice3])).

thf('56',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ~ ( r3_lattice3 @ X12 @ X15 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X12 ) )
      | ( r2_hidden @ X15 @ ( a_2_1_lattice3 @ X12 @ X13 ) )
      | ( v2_struct_0 @ X12 )
      | ~ ( l3_lattices @ X12 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','56'])).

thf('58',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    r2_hidden @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['53','61'])).

thf('63',plain,
    ( ( ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
      = sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['52','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
    = sk_B ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( k16_lattice3 @ sk_A @ sk_C )
      = sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup+',[status(thm)],['1','65'])).

thf('67',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( ( k16_lattice3 @ sk_A @ sk_C )
      = sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ( k16_lattice3 @ sk_A @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['68','69'])).

thf('71',plain,(
    $false ),
    inference(demod,[status(thm)],['0','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.x3kfLF2gFy
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:02:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.19/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.53  % Solved by: fo/fo7.sh
% 0.19/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.53  % done 92 iterations in 0.085s
% 0.19/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.53  % SZS output start Refutation
% 0.19/0.53  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.19/0.53  thf(a_2_1_lattice3_type, type, a_2_1_lattice3: $i > $i > $i).
% 0.19/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.53  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 0.19/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.53  thf(r3_lattice3_type, type, r3_lattice3: $i > $i > $i > $o).
% 0.19/0.53  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 0.19/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.53  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 0.19/0.53  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 0.19/0.53  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.19/0.53  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.19/0.53  thf(r4_lattice3_type, type, r4_lattice3: $i > $i > $i > $o).
% 0.19/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.53  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.19/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.53  thf(t42_lattice3, conjecture,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.19/0.53         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.19/0.53       ( ![B:$i]:
% 0.19/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.53           ( ![C:$i]:
% 0.19/0.53             ( ( ( r2_hidden @ B @ C ) & ( r3_lattice3 @ A @ B @ C ) ) =>
% 0.19/0.53               ( ( k16_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ))).
% 0.19/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.53    (~( ![A:$i]:
% 0.19/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.19/0.53            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.19/0.53          ( ![B:$i]:
% 0.19/0.53            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.53              ( ![C:$i]:
% 0.19/0.53                ( ( ( r2_hidden @ B @ C ) & ( r3_lattice3 @ A @ B @ C ) ) =>
% 0.19/0.53                  ( ( k16_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ) )),
% 0.19/0.53    inference('cnf.neg', [status(esa)], [t42_lattice3])).
% 0.19/0.53  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(d22_lattice3, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.19/0.53       ( ![B:$i]:
% 0.19/0.53         ( ( k16_lattice3 @ A @ B ) =
% 0.19/0.53           ( k15_lattice3 @ A @ ( a_2_1_lattice3 @ A @ B ) ) ) ) ))).
% 0.19/0.53  thf('1', plain,
% 0.19/0.53      (![X10 : $i, X11 : $i]:
% 0.19/0.53         (((k16_lattice3 @ X10 @ X11)
% 0.19/0.53            = (k15_lattice3 @ X10 @ (a_2_1_lattice3 @ X10 @ X11)))
% 0.19/0.53          | ~ (l3_lattices @ X10)
% 0.19/0.53          | (v2_struct_0 @ X10))),
% 0.19/0.53      inference('cnf', [status(esa)], [d22_lattice3])).
% 0.19/0.53  thf('2', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('3', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('4', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(d17_lattice3, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.19/0.53       ( ![B:$i]:
% 0.19/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.53           ( ![C:$i]:
% 0.19/0.53             ( ( r4_lattice3 @ A @ B @ C ) <=>
% 0.19/0.53               ( ![D:$i]:
% 0.19/0.53                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.53                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ))).
% 0.19/0.53  thf('5', plain,
% 0.19/0.53      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 0.19/0.53          | (r2_hidden @ (sk_D_1 @ X9 @ X5 @ X6) @ X9)
% 0.19/0.53          | (r4_lattice3 @ X6 @ X5 @ X9)
% 0.19/0.53          | ~ (l3_lattices @ X6)
% 0.19/0.53          | (v2_struct_0 @ X6))),
% 0.19/0.53      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.19/0.53  thf('6', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((v2_struct_0 @ sk_A)
% 0.19/0.53          | ~ (l3_lattices @ sk_A)
% 0.19/0.53          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.19/0.53          | (r2_hidden @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0))),
% 0.19/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.53  thf('7', plain, ((l3_lattices @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('8', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((v2_struct_0 @ sk_A)
% 0.19/0.53          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.19/0.53          | (r2_hidden @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0))),
% 0.19/0.53      inference('demod', [status(thm)], ['6', '7'])).
% 0.19/0.53  thf('9', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('10', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((r2_hidden @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0)
% 0.19/0.53          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 0.19/0.53      inference('clc', [status(thm)], ['8', '9'])).
% 0.19/0.53  thf(fraenkel_a_2_1_lattice3, axiom,
% 0.19/0.53    (![A:$i,B:$i,C:$i]:
% 0.19/0.53     ( ( ( ~( v2_struct_0 @ B ) ) & ( l3_lattices @ B ) ) =>
% 0.19/0.53       ( ( r2_hidden @ A @ ( a_2_1_lattice3 @ B @ C ) ) <=>
% 0.19/0.53         ( ?[D:$i]:
% 0.19/0.53           ( ( r3_lattice3 @ B @ D @ C ) & ( ( A ) = ( D ) ) & 
% 0.19/0.53             ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.19/0.53  thf('11', plain,
% 0.19/0.53      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.53         (~ (l3_lattices @ X12)
% 0.19/0.53          | (v2_struct_0 @ X12)
% 0.19/0.53          | ((X14) = (sk_D_2 @ X13 @ X12 @ X14))
% 0.19/0.53          | ~ (r2_hidden @ X14 @ (a_2_1_lattice3 @ X12 @ X13)))),
% 0.19/0.53      inference('cnf', [status(esa)], [fraenkel_a_2_1_lattice3])).
% 0.19/0.53  thf('12', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0))
% 0.19/0.53          | ((sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A)
% 0.19/0.53              = (sk_D_2 @ X0 @ X1 @ 
% 0.19/0.53                 (sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A)))
% 0.19/0.53          | (v2_struct_0 @ X1)
% 0.19/0.53          | ~ (l3_lattices @ X1))),
% 0.19/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.53  thf('13', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((r2_hidden @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0)
% 0.19/0.53          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 0.19/0.53      inference('clc', [status(thm)], ['8', '9'])).
% 0.19/0.53  thf('14', plain,
% 0.19/0.53      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.53         (~ (l3_lattices @ X12)
% 0.19/0.53          | (v2_struct_0 @ X12)
% 0.19/0.53          | (r3_lattice3 @ X12 @ (sk_D_2 @ X13 @ X12 @ X14) @ X13)
% 0.19/0.53          | ~ (r2_hidden @ X14 @ (a_2_1_lattice3 @ X12 @ X13)))),
% 0.19/0.53      inference('cnf', [status(esa)], [fraenkel_a_2_1_lattice3])).
% 0.19/0.53  thf('15', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0))
% 0.19/0.53          | (r3_lattice3 @ X1 @ 
% 0.19/0.53             (sk_D_2 @ X0 @ X1 @ 
% 0.19/0.53              (sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A)) @ 
% 0.19/0.53             X0)
% 0.19/0.53          | (v2_struct_0 @ X1)
% 0.19/0.53          | ~ (l3_lattices @ X1))),
% 0.19/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.53  thf('16', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((r3_lattice3 @ X1 @ 
% 0.19/0.53           (sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A) @ X0)
% 0.19/0.53          | ~ (l3_lattices @ X1)
% 0.19/0.53          | (v2_struct_0 @ X1)
% 0.19/0.53          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0))
% 0.19/0.53          | ~ (l3_lattices @ X1)
% 0.19/0.53          | (v2_struct_0 @ X1)
% 0.19/0.53          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0)))),
% 0.19/0.53      inference('sup+', [status(thm)], ['12', '15'])).
% 0.19/0.53  thf('17', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0))
% 0.19/0.53          | (v2_struct_0 @ X1)
% 0.19/0.53          | ~ (l3_lattices @ X1)
% 0.19/0.53          | (r3_lattice3 @ X1 @ 
% 0.19/0.53             (sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A) @ X0))),
% 0.19/0.53      inference('simplify', [status(thm)], ['16'])).
% 0.19/0.53  thf('18', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('19', plain,
% 0.19/0.53      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 0.19/0.53          | (m1_subset_1 @ (sk_D_1 @ X9 @ X5 @ X6) @ (u1_struct_0 @ X6))
% 0.19/0.53          | (r4_lattice3 @ X6 @ X5 @ X9)
% 0.19/0.53          | ~ (l3_lattices @ X6)
% 0.19/0.53          | (v2_struct_0 @ X6))),
% 0.19/0.53      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.19/0.53  thf('20', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((v2_struct_0 @ sk_A)
% 0.19/0.53          | ~ (l3_lattices @ sk_A)
% 0.19/0.53          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.19/0.53          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.53  thf('21', plain, ((l3_lattices @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('22', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((v2_struct_0 @ sk_A)
% 0.19/0.53          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.19/0.53          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.19/0.53      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.54  thf('23', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('24', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         ((m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.19/0.54          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 0.19/0.54      inference('clc', [status(thm)], ['22', '23'])).
% 0.19/0.54  thf(d16_lattice3, axiom,
% 0.19/0.54    (![A:$i]:
% 0.19/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.19/0.54       ( ![B:$i]:
% 0.19/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.54           ( ![C:$i]:
% 0.19/0.54             ( ( r3_lattice3 @ A @ B @ C ) <=>
% 0.19/0.54               ( ![D:$i]:
% 0.19/0.54                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.54                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 0.19/0.54  thf('25', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.19/0.54          | ~ (r3_lattice3 @ X1 @ X0 @ X2)
% 0.19/0.54          | ~ (r2_hidden @ X3 @ X2)
% 0.19/0.54          | (r1_lattices @ X1 @ X0 @ X3)
% 0.19/0.54          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.19/0.54          | ~ (l3_lattices @ X1)
% 0.19/0.54          | (v2_struct_0 @ X1))),
% 0.19/0.54      inference('cnf', [status(esa)], [d16_lattice3])).
% 0.19/0.54  thf('26', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.54         ((r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.19/0.54          | (v2_struct_0 @ sk_A)
% 0.19/0.54          | ~ (l3_lattices @ sk_A)
% 0.19/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.19/0.54          | (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X1)
% 0.19/0.54          | ~ (r2_hidden @ X1 @ X2)
% 0.19/0.54          | ~ (r3_lattice3 @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X2))),
% 0.19/0.54      inference('sup-', [status(thm)], ['24', '25'])).
% 0.19/0.54  thf('27', plain, ((l3_lattices @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('28', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.54         ((r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.19/0.54          | (v2_struct_0 @ sk_A)
% 0.19/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.19/0.54          | (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X1)
% 0.19/0.54          | ~ (r2_hidden @ X1 @ X2)
% 0.19/0.54          | ~ (r3_lattice3 @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X2))),
% 0.19/0.54      inference('demod', [status(thm)], ['26', '27'])).
% 0.19/0.54  thf('29', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i]:
% 0.19/0.54         (~ (l3_lattices @ sk_A)
% 0.19/0.54          | (v2_struct_0 @ sk_A)
% 0.19/0.54          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 0.19/0.54          | ~ (r2_hidden @ X1 @ X0)
% 0.19/0.54          | (r1_lattices @ sk_A @ 
% 0.19/0.54             (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ X0) @ sk_B @ sk_A) @ X1)
% 0.19/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.19/0.54          | (v2_struct_0 @ sk_A)
% 0.19/0.54          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['17', '28'])).
% 0.19/0.54  thf('30', plain, ((l3_lattices @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('31', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i]:
% 0.19/0.54         ((v2_struct_0 @ sk_A)
% 0.19/0.54          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 0.19/0.54          | ~ (r2_hidden @ X1 @ X0)
% 0.19/0.54          | (r1_lattices @ sk_A @ 
% 0.19/0.54             (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ X0) @ sk_B @ sk_A) @ X1)
% 0.19/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.19/0.54          | (v2_struct_0 @ sk_A)
% 0.19/0.54          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0)))),
% 0.19/0.54      inference('demod', [status(thm)], ['29', '30'])).
% 0.19/0.54  thf('32', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i]:
% 0.19/0.54         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.19/0.54          | (r1_lattices @ sk_A @ 
% 0.19/0.54             (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ X0) @ sk_B @ sk_A) @ X1)
% 0.19/0.54          | ~ (r2_hidden @ X1 @ X0)
% 0.19/0.54          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 0.19/0.54          | (v2_struct_0 @ sk_A))),
% 0.19/0.54      inference('simplify', [status(thm)], ['31'])).
% 0.19/0.54  thf('33', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         ((v2_struct_0 @ sk_A)
% 0.19/0.54          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 0.19/0.54          | ~ (r2_hidden @ sk_B @ X0)
% 0.19/0.54          | (r1_lattices @ sk_A @ 
% 0.19/0.54             (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ X0) @ sk_B @ sk_A) @ sk_B))),
% 0.19/0.54      inference('sup-', [status(thm)], ['3', '32'])).
% 0.19/0.54  thf('34', plain,
% 0.19/0.54      (((r1_lattices @ sk_A @ 
% 0.19/0.54         (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_B @ sk_A) @ sk_B)
% 0.19/0.54        | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))
% 0.19/0.54        | (v2_struct_0 @ sk_A))),
% 0.19/0.54      inference('sup-', [status(thm)], ['2', '33'])).
% 0.19/0.54  thf('35', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('36', plain,
% 0.19/0.54      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.19/0.54         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 0.19/0.54          | ~ (r1_lattices @ X6 @ (sk_D_1 @ X9 @ X5 @ X6) @ X5)
% 0.19/0.54          | (r4_lattice3 @ X6 @ X5 @ X9)
% 0.19/0.54          | ~ (l3_lattices @ X6)
% 0.19/0.54          | (v2_struct_0 @ X6))),
% 0.19/0.54      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.19/0.54  thf('37', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         ((v2_struct_0 @ sk_A)
% 0.19/0.54          | ~ (l3_lattices @ sk_A)
% 0.19/0.54          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.19/0.54          | ~ (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_B))),
% 0.19/0.54      inference('sup-', [status(thm)], ['35', '36'])).
% 0.19/0.54  thf('38', plain, ((l3_lattices @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('39', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         ((v2_struct_0 @ sk_A)
% 0.19/0.54          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.19/0.54          | ~ (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_B))),
% 0.19/0.54      inference('demod', [status(thm)], ['37', '38'])).
% 0.19/0.54  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('41', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         (~ (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_B)
% 0.19/0.54          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 0.19/0.54      inference('clc', [status(thm)], ['39', '40'])).
% 0.19/0.54  thf('42', plain,
% 0.19/0.54      (((v2_struct_0 @ sk_A)
% 0.19/0.54        | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C)))),
% 0.19/0.54      inference('clc', [status(thm)], ['34', '41'])).
% 0.19/0.54  thf('43', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('44', plain,
% 0.19/0.54      ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))),
% 0.19/0.54      inference('clc', [status(thm)], ['42', '43'])).
% 0.19/0.54  thf('45', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf(t41_lattice3, axiom,
% 0.19/0.54    (![A:$i]:
% 0.19/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.19/0.54         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.19/0.54       ( ![B:$i]:
% 0.19/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.54           ( ![C:$i]:
% 0.19/0.54             ( ( ( r2_hidden @ B @ C ) & ( r4_lattice3 @ A @ B @ C ) ) =>
% 0.19/0.54               ( ( k15_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ))).
% 0.19/0.54  thf('46', plain,
% 0.19/0.54      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.54         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.19/0.54          | ((k15_lattice3 @ X17 @ X18) = (X16))
% 0.19/0.54          | ~ (r4_lattice3 @ X17 @ X16 @ X18)
% 0.19/0.54          | ~ (r2_hidden @ X16 @ X18)
% 0.19/0.54          | ~ (l3_lattices @ X17)
% 0.19/0.54          | ~ (v4_lattice3 @ X17)
% 0.19/0.54          | ~ (v10_lattices @ X17)
% 0.19/0.54          | (v2_struct_0 @ X17))),
% 0.19/0.54      inference('cnf', [status(esa)], [t41_lattice3])).
% 0.19/0.54  thf('47', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         ((v2_struct_0 @ sk_A)
% 0.19/0.54          | ~ (v10_lattices @ sk_A)
% 0.19/0.54          | ~ (v4_lattice3 @ sk_A)
% 0.19/0.54          | ~ (l3_lattices @ sk_A)
% 0.19/0.54          | ~ (r2_hidden @ sk_B @ X0)
% 0.19/0.54          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.19/0.54          | ((k15_lattice3 @ sk_A @ X0) = (sk_B)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['45', '46'])).
% 0.19/0.54  thf('48', plain, ((v10_lattices @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('49', plain, ((v4_lattice3 @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('50', plain, ((l3_lattices @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('51', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         ((v2_struct_0 @ sk_A)
% 0.19/0.54          | ~ (r2_hidden @ sk_B @ X0)
% 0.19/0.54          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.19/0.54          | ((k15_lattice3 @ sk_A @ X0) = (sk_B)))),
% 0.19/0.54      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 0.19/0.54  thf('52', plain,
% 0.19/0.54      ((((k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) = (sk_B))
% 0.19/0.54        | ~ (r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))
% 0.19/0.54        | (v2_struct_0 @ sk_A))),
% 0.19/0.54      inference('sup-', [status(thm)], ['44', '51'])).
% 0.19/0.54  thf('53', plain, ((r3_lattice3 @ sk_A @ sk_B @ sk_C)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('54', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('55', plain,
% 0.19/0.54      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.19/0.54         (~ (l3_lattices @ X12)
% 0.19/0.54          | (v2_struct_0 @ X12)
% 0.19/0.54          | (r2_hidden @ X14 @ (a_2_1_lattice3 @ X12 @ X13))
% 0.19/0.54          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X12))
% 0.19/0.54          | ((X14) != (X15))
% 0.19/0.54          | ~ (r3_lattice3 @ X12 @ X15 @ X13))),
% 0.19/0.54      inference('cnf', [status(esa)], [fraenkel_a_2_1_lattice3])).
% 0.19/0.54  thf('56', plain,
% 0.19/0.54      (![X12 : $i, X13 : $i, X15 : $i]:
% 0.19/0.54         (~ (r3_lattice3 @ X12 @ X15 @ X13)
% 0.19/0.54          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X12))
% 0.19/0.54          | (r2_hidden @ X15 @ (a_2_1_lattice3 @ X12 @ X13))
% 0.19/0.54          | (v2_struct_0 @ X12)
% 0.19/0.54          | ~ (l3_lattices @ X12))),
% 0.19/0.54      inference('simplify', [status(thm)], ['55'])).
% 0.19/0.54  thf('57', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         (~ (l3_lattices @ sk_A)
% 0.19/0.54          | (v2_struct_0 @ sk_A)
% 0.19/0.54          | (r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 0.19/0.54          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.19/0.54      inference('sup-', [status(thm)], ['54', '56'])).
% 0.19/0.54  thf('58', plain, ((l3_lattices @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('59', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         ((v2_struct_0 @ sk_A)
% 0.19/0.54          | (r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 0.19/0.54          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.19/0.54      inference('demod', [status(thm)], ['57', '58'])).
% 0.19/0.54  thf('60', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('61', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         (~ (r3_lattice3 @ sk_A @ sk_B @ X0)
% 0.19/0.54          | (r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0)))),
% 0.19/0.54      inference('clc', [status(thm)], ['59', '60'])).
% 0.19/0.54  thf('62', plain, ((r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))),
% 0.19/0.54      inference('sup-', [status(thm)], ['53', '61'])).
% 0.19/0.54  thf('63', plain,
% 0.19/0.54      ((((k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) = (sk_B))
% 0.19/0.54        | (v2_struct_0 @ sk_A))),
% 0.19/0.54      inference('demod', [status(thm)], ['52', '62'])).
% 0.19/0.54  thf('64', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('65', plain,
% 0.19/0.54      (((k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)) = (sk_B))),
% 0.19/0.54      inference('clc', [status(thm)], ['63', '64'])).
% 0.19/0.54  thf('66', plain,
% 0.19/0.54      ((((k16_lattice3 @ sk_A @ sk_C) = (sk_B))
% 0.19/0.54        | (v2_struct_0 @ sk_A)
% 0.19/0.54        | ~ (l3_lattices @ sk_A))),
% 0.19/0.54      inference('sup+', [status(thm)], ['1', '65'])).
% 0.19/0.54  thf('67', plain, ((l3_lattices @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('68', plain,
% 0.19/0.54      ((((k16_lattice3 @ sk_A @ sk_C) = (sk_B)) | (v2_struct_0 @ sk_A))),
% 0.19/0.54      inference('demod', [status(thm)], ['66', '67'])).
% 0.19/0.54  thf('69', plain, (((k16_lattice3 @ sk_A @ sk_C) != (sk_B))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('70', plain, ((v2_struct_0 @ sk_A)),
% 0.19/0.54      inference('simplify_reflect-', [status(thm)], ['68', '69'])).
% 0.19/0.54  thf('71', plain, ($false), inference('demod', [status(thm)], ['0', '70'])).
% 0.19/0.54  
% 0.19/0.54  % SZS output end Refutation
% 0.19/0.54  
% 0.19/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
