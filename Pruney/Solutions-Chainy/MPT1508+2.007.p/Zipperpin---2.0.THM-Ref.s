%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YukDWlsq98

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:31 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 407 expanded)
%              Number of leaves         :   25 ( 122 expanded)
%              Depth                    :   32
%              Number of atoms          : 1522 (6910 expanded)
%              Number of equality atoms :   40 ( 202 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r3_lattice3_type,type,(
    r3_lattice3: $i > $i > $i > $o )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(r4_lattice3_type,type,(
    r4_lattice3: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(a_2_1_lattice3_type,type,(
    a_2_1_lattice3: $i > $i > $i )).

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
    ! [X14: $i,X15: $i] :
      ( ( ( k16_lattice3 @ X14 @ X15 )
        = ( k15_lattice3 @ X14 @ ( a_2_1_lattice3 @ X14 @ X15 ) ) )
      | ~ ( l3_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d22_lattice3])).

thf('2',plain,(
    r3_lattice3 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fraenkel_a_2_1_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( l3_lattices @ B ) )
     => ( ( r2_hidden @ A @ ( a_2_1_lattice3 @ B @ C ) )
      <=> ? [D: $i] :
            ( ( r3_lattice3 @ B @ D @ C )
            & ( A = D )
            & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( l3_lattices @ X16 )
      | ( v2_struct_0 @ X16 )
      | ( r2_hidden @ X18 @ ( a_2_1_lattice3 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X16 ) )
      | ( X18 != X19 )
      | ~ ( r3_lattice3 @ X16 @ X19 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_lattice3])).

thf('5',plain,(
    ! [X16: $i,X17: $i,X19: $i] :
      ( ~ ( r3_lattice3 @ X16 @ X19 @ X17 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X16 ) )
      | ( r2_hidden @ X19 @ ( a_2_1_lattice3 @ X16 @ X17 ) )
      | ( v2_struct_0 @ X16 )
      | ~ ( l3_lattices @ X16 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    r2_hidden @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf('12',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ( r2_hidden @ ( sk_D_1 @ X9 @ X5 @ X6 ) @ X9 )
      | ( r4_lattice3 @ X6 @ X5 @ X9 )
      | ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( l3_lattices @ X16 )
      | ( v2_struct_0 @ X16 )
      | ( X18
        = ( sk_D_3 @ X17 @ X16 @ X18 ) )
      | ~ ( r2_hidden @ X18 @ ( a_2_1_lattice3 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_lattice3])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ X1 @ X0 ) )
      | ( ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A )
        = ( sk_D_3 @ X0 @ X1 @ ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('24',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( l3_lattices @ X16 )
      | ( v2_struct_0 @ X16 )
      | ( r3_lattice3 @ X16 @ ( sk_D_3 @ X17 @ X16 @ X18 ) @ X17 )
      | ~ ( r2_hidden @ X18 @ ( a_2_1_lattice3 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_lattice3])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ X1 @ X0 ) )
      | ( r3_lattice3 @ X1 @ ( sk_D_3 @ X0 @ X1 @ ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A ) ) @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ X1 @ ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A ) @ X0 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ X1 @ X0 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( r3_lattice3 @ X1 @ ( sk_D_1 @ ( a_2_1_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X9 @ X5 @ X6 ) @ ( u1_struct_0 @ X6 ) )
      | ( r4_lattice3 @ X6 @ X5 @ X9 )
      | ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['32','33'])).

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

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r3_lattice3 @ X1 @ X0 @ X2 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r1_lattices @ X1 @ X0 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X1 )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X1 )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X2 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ X0 ) @ sk_B @ sk_A ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','38'])).

thf('40',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ X0 ) @ sk_B @ sk_A ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ X0 ) @ sk_B @ sk_A ) @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ X0 ) @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','42'])).

thf('44',plain,
    ( ( r1_lattices @ sk_A @ ( sk_D_1 @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_B @ sk_A ) @ sk_B )
    | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ~ ( r1_lattices @ X6 @ ( sk_D_1 @ X9 @ X5 @ X6 ) @ X5 )
      | ( r4_lattice3 @ X6 @ X5 @ X9 )
      | ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['44','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
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

thf('56',plain,(
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

thf('57',plain,(
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
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r4_lattice3 @ sk_A @ ( sk_D_2 @ sk_B @ X0 @ sk_A ) @ X0 )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r4_lattice3 @ sk_A @ ( sk_D_2 @ sk_B @ X0 @ sk_A ) @ X0 )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','59','60','61'])).

thf('63',plain,
    ( ( sk_B
      = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
    | ( r4_lattice3 @ sk_A @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['54','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( r4_lattice3 @ sk_A @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
    | ( sk_B
      = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('67',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
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

thf('69',plain,(
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
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_B @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','69'])).

thf('71',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_B @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf('75',plain,
    ( ( sk_B
      = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
    | ( m1_subset_1 @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['66','74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( m1_subset_1 @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ~ ( r4_lattice3 @ X6 @ X5 @ X7 )
      | ~ ( r2_hidden @ X8 @ X7 )
      | ( r1_lattices @ X6 @ X8 @ X5 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ X0 @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r4_lattice3 @ sk_A @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ X0 @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r4_lattice3 @ sk_A @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) @ X1 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
      | ( r1_lattices @ sk_A @ X0 @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['65','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ X0 @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_1_lattice3 @ sk_A @ sk_C ) )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ( sk_B
      = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
    | ( r1_lattices @ sk_A @ sk_B @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( sk_B
      = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
    | ( r1_lattices @ sk_A @ sk_B @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( r1_lattices @ sk_A @ sk_B @ ( sk_D_2 @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) @ sk_A ) )
    | ( sk_B
      = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
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

thf('90',plain,(
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
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,
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
    inference('sup-',[status(thm)],['88','90'])).

thf('92',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    r4_lattice3 @ sk_A @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('97',plain,
    ( ( sk_B
      = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['91','92','93','94','95','96'])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( sk_B
    = ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup+',[status(thm)],['1','100'])).

thf('102',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ( k16_lattice3 @ sk_A @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['103','104'])).

thf('106',plain,(
    $false ),
    inference(demod,[status(thm)],['0','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YukDWlsq98
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:39:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.42/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.59  % Solved by: fo/fo7.sh
% 0.42/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.59  % done 132 iterations in 0.137s
% 0.42/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.59  % SZS output start Refutation
% 0.42/0.59  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.42/0.59  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 0.42/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.42/0.59  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.42/0.59  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 0.42/0.59  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.42/0.59  thf(r3_lattice3_type, type, r3_lattice3: $i > $i > $i > $o).
% 0.42/0.59  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 0.42/0.59  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.42/0.59  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.42/0.59  thf(r4_lattice3_type, type, r4_lattice3: $i > $i > $i > $o).
% 0.42/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.59  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 0.42/0.59  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i > $i).
% 0.42/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.59  thf(a_2_1_lattice3_type, type, a_2_1_lattice3: $i > $i > $i).
% 0.42/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.42/0.59  thf(t42_lattice3, conjecture,
% 0.42/0.59    (![A:$i]:
% 0.42/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.42/0.59         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.42/0.59       ( ![B:$i]:
% 0.42/0.59         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.42/0.59           ( ![C:$i]:
% 0.42/0.59             ( ( ( r2_hidden @ B @ C ) & ( r3_lattice3 @ A @ B @ C ) ) =>
% 0.42/0.59               ( ( k16_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ))).
% 0.42/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.59    (~( ![A:$i]:
% 0.42/0.59        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.42/0.59            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.42/0.59          ( ![B:$i]:
% 0.42/0.59            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.42/0.59              ( ![C:$i]:
% 0.42/0.59                ( ( ( r2_hidden @ B @ C ) & ( r3_lattice3 @ A @ B @ C ) ) =>
% 0.42/0.59                  ( ( k16_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ) )),
% 0.42/0.59    inference('cnf.neg', [status(esa)], [t42_lattice3])).
% 0.42/0.59  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf(d22_lattice3, axiom,
% 0.42/0.59    (![A:$i]:
% 0.42/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.42/0.59       ( ![B:$i]:
% 0.42/0.59         ( ( k16_lattice3 @ A @ B ) =
% 0.42/0.59           ( k15_lattice3 @ A @ ( a_2_1_lattice3 @ A @ B ) ) ) ) ))).
% 0.42/0.59  thf('1', plain,
% 0.42/0.59      (![X14 : $i, X15 : $i]:
% 0.42/0.59         (((k16_lattice3 @ X14 @ X15)
% 0.42/0.59            = (k15_lattice3 @ X14 @ (a_2_1_lattice3 @ X14 @ X15)))
% 0.42/0.59          | ~ (l3_lattices @ X14)
% 0.42/0.59          | (v2_struct_0 @ X14))),
% 0.42/0.59      inference('cnf', [status(esa)], [d22_lattice3])).
% 0.42/0.59  thf('2', plain, ((r3_lattice3 @ sk_A @ sk_B @ sk_C)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('3', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf(fraenkel_a_2_1_lattice3, axiom,
% 0.42/0.59    (![A:$i,B:$i,C:$i]:
% 0.42/0.59     ( ( ( ~( v2_struct_0 @ B ) ) & ( l3_lattices @ B ) ) =>
% 0.42/0.59       ( ( r2_hidden @ A @ ( a_2_1_lattice3 @ B @ C ) ) <=>
% 0.42/0.59         ( ?[D:$i]:
% 0.42/0.59           ( ( r3_lattice3 @ B @ D @ C ) & ( ( A ) = ( D ) ) & 
% 0.42/0.59             ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.42/0.59  thf('4', plain,
% 0.42/0.59      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.42/0.59         (~ (l3_lattices @ X16)
% 0.42/0.59          | (v2_struct_0 @ X16)
% 0.42/0.59          | (r2_hidden @ X18 @ (a_2_1_lattice3 @ X16 @ X17))
% 0.42/0.59          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X16))
% 0.42/0.59          | ((X18) != (X19))
% 0.42/0.59          | ~ (r3_lattice3 @ X16 @ X19 @ X17))),
% 0.42/0.59      inference('cnf', [status(esa)], [fraenkel_a_2_1_lattice3])).
% 0.42/0.59  thf('5', plain,
% 0.42/0.59      (![X16 : $i, X17 : $i, X19 : $i]:
% 0.42/0.59         (~ (r3_lattice3 @ X16 @ X19 @ X17)
% 0.42/0.59          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X16))
% 0.42/0.59          | (r2_hidden @ X19 @ (a_2_1_lattice3 @ X16 @ X17))
% 0.42/0.59          | (v2_struct_0 @ X16)
% 0.42/0.59          | ~ (l3_lattices @ X16))),
% 0.42/0.59      inference('simplify', [status(thm)], ['4'])).
% 0.42/0.59  thf('6', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         (~ (l3_lattices @ sk_A)
% 0.42/0.59          | (v2_struct_0 @ sk_A)
% 0.42/0.59          | (r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 0.42/0.59          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.42/0.59      inference('sup-', [status(thm)], ['3', '5'])).
% 0.42/0.59  thf('7', plain, ((l3_lattices @ sk_A)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('8', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         ((v2_struct_0 @ sk_A)
% 0.42/0.59          | (r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 0.42/0.59          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.42/0.59      inference('demod', [status(thm)], ['6', '7'])).
% 0.42/0.59  thf('9', plain, (~ (v2_struct_0 @ sk_A)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('10', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         (~ (r3_lattice3 @ sk_A @ sk_B @ X0)
% 0.42/0.59          | (r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0)))),
% 0.42/0.59      inference('clc', [status(thm)], ['8', '9'])).
% 0.42/0.59  thf('11', plain, ((r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))),
% 0.42/0.59      inference('sup-', [status(thm)], ['2', '10'])).
% 0.42/0.59  thf('12', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('13', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('14', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf(d17_lattice3, axiom,
% 0.42/0.59    (![A:$i]:
% 0.42/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.42/0.59       ( ![B:$i]:
% 0.42/0.59         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.42/0.59           ( ![C:$i]:
% 0.42/0.59             ( ( r4_lattice3 @ A @ B @ C ) <=>
% 0.42/0.59               ( ![D:$i]:
% 0.42/0.59                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.42/0.59                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ))).
% 0.42/0.59  thf('15', plain,
% 0.42/0.59      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.42/0.59         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 0.42/0.59          | (r2_hidden @ (sk_D_1 @ X9 @ X5 @ X6) @ X9)
% 0.42/0.59          | (r4_lattice3 @ X6 @ X5 @ X9)
% 0.42/0.59          | ~ (l3_lattices @ X6)
% 0.42/0.59          | (v2_struct_0 @ X6))),
% 0.42/0.59      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.42/0.59  thf('16', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         ((v2_struct_0 @ sk_A)
% 0.42/0.59          | ~ (l3_lattices @ sk_A)
% 0.42/0.59          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.42/0.59          | (r2_hidden @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0))),
% 0.42/0.59      inference('sup-', [status(thm)], ['14', '15'])).
% 0.42/0.59  thf('17', plain, ((l3_lattices @ sk_A)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('18', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         ((v2_struct_0 @ sk_A)
% 0.42/0.59          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.42/0.59          | (r2_hidden @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0))),
% 0.42/0.59      inference('demod', [status(thm)], ['16', '17'])).
% 0.42/0.59  thf('19', plain, (~ (v2_struct_0 @ sk_A)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('20', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         ((r2_hidden @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0)
% 0.42/0.59          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 0.42/0.59      inference('clc', [status(thm)], ['18', '19'])).
% 0.42/0.59  thf('21', plain,
% 0.42/0.59      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.42/0.59         (~ (l3_lattices @ X16)
% 0.42/0.59          | (v2_struct_0 @ X16)
% 0.42/0.59          | ((X18) = (sk_D_3 @ X17 @ X16 @ X18))
% 0.42/0.59          | ~ (r2_hidden @ X18 @ (a_2_1_lattice3 @ X16 @ X17)))),
% 0.42/0.59      inference('cnf', [status(esa)], [fraenkel_a_2_1_lattice3])).
% 0.42/0.59  thf('22', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i]:
% 0.42/0.59         ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0))
% 0.42/0.59          | ((sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A)
% 0.42/0.59              = (sk_D_3 @ X0 @ X1 @ 
% 0.42/0.59                 (sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A)))
% 0.42/0.59          | (v2_struct_0 @ X1)
% 0.42/0.59          | ~ (l3_lattices @ X1))),
% 0.42/0.59      inference('sup-', [status(thm)], ['20', '21'])).
% 0.42/0.59  thf('23', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         ((r2_hidden @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0)
% 0.42/0.59          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 0.42/0.59      inference('clc', [status(thm)], ['18', '19'])).
% 0.42/0.59  thf('24', plain,
% 0.42/0.59      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.42/0.59         (~ (l3_lattices @ X16)
% 0.42/0.59          | (v2_struct_0 @ X16)
% 0.42/0.59          | (r3_lattice3 @ X16 @ (sk_D_3 @ X17 @ X16 @ X18) @ X17)
% 0.42/0.59          | ~ (r2_hidden @ X18 @ (a_2_1_lattice3 @ X16 @ X17)))),
% 0.42/0.59      inference('cnf', [status(esa)], [fraenkel_a_2_1_lattice3])).
% 0.42/0.59  thf('25', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i]:
% 0.42/0.59         ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0))
% 0.42/0.59          | (r3_lattice3 @ X1 @ 
% 0.42/0.59             (sk_D_3 @ X0 @ X1 @ 
% 0.42/0.59              (sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A)) @ 
% 0.42/0.59             X0)
% 0.42/0.59          | (v2_struct_0 @ X1)
% 0.42/0.59          | ~ (l3_lattices @ X1))),
% 0.42/0.59      inference('sup-', [status(thm)], ['23', '24'])).
% 0.42/0.59  thf('26', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i]:
% 0.42/0.59         ((r3_lattice3 @ X1 @ 
% 0.42/0.59           (sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A) @ X0)
% 0.42/0.59          | ~ (l3_lattices @ X1)
% 0.42/0.59          | (v2_struct_0 @ X1)
% 0.42/0.59          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0))
% 0.42/0.59          | ~ (l3_lattices @ X1)
% 0.42/0.59          | (v2_struct_0 @ X1)
% 0.42/0.59          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0)))),
% 0.42/0.59      inference('sup+', [status(thm)], ['22', '25'])).
% 0.42/0.59  thf('27', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i]:
% 0.42/0.59         ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ X1 @ X0))
% 0.42/0.59          | (v2_struct_0 @ X1)
% 0.42/0.59          | ~ (l3_lattices @ X1)
% 0.42/0.59          | (r3_lattice3 @ X1 @ 
% 0.42/0.59             (sk_D_1 @ (a_2_1_lattice3 @ X1 @ X0) @ sk_B @ sk_A) @ X0))),
% 0.42/0.59      inference('simplify', [status(thm)], ['26'])).
% 0.42/0.59  thf('28', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('29', plain,
% 0.42/0.59      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.42/0.59         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 0.42/0.59          | (m1_subset_1 @ (sk_D_1 @ X9 @ X5 @ X6) @ (u1_struct_0 @ X6))
% 0.42/0.59          | (r4_lattice3 @ X6 @ X5 @ X9)
% 0.42/0.59          | ~ (l3_lattices @ X6)
% 0.42/0.59          | (v2_struct_0 @ X6))),
% 0.42/0.59      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.42/0.59  thf('30', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         ((v2_struct_0 @ sk_A)
% 0.42/0.59          | ~ (l3_lattices @ sk_A)
% 0.42/0.59          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.42/0.59          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['28', '29'])).
% 0.42/0.59  thf('31', plain, ((l3_lattices @ sk_A)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('32', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         ((v2_struct_0 @ sk_A)
% 0.42/0.59          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.42/0.59          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.42/0.59      inference('demod', [status(thm)], ['30', '31'])).
% 0.42/0.59  thf('33', plain, (~ (v2_struct_0 @ sk_A)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('34', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         ((m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.42/0.59          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 0.42/0.59      inference('clc', [status(thm)], ['32', '33'])).
% 0.42/0.59  thf(d16_lattice3, axiom,
% 0.42/0.59    (![A:$i]:
% 0.42/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.42/0.59       ( ![B:$i]:
% 0.42/0.59         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.42/0.59           ( ![C:$i]:
% 0.42/0.59             ( ( r3_lattice3 @ A @ B @ C ) <=>
% 0.42/0.59               ( ![D:$i]:
% 0.42/0.59                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.42/0.59                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 0.42/0.59  thf('35', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.42/0.59         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.42/0.59          | ~ (r3_lattice3 @ X1 @ X0 @ X2)
% 0.42/0.59          | ~ (r2_hidden @ X3 @ X2)
% 0.42/0.59          | (r1_lattices @ X1 @ X0 @ X3)
% 0.42/0.59          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.42/0.59          | ~ (l3_lattices @ X1)
% 0.42/0.59          | (v2_struct_0 @ X1))),
% 0.42/0.59      inference('cnf', [status(esa)], [d16_lattice3])).
% 0.42/0.59  thf('36', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.59         ((r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.42/0.59          | (v2_struct_0 @ sk_A)
% 0.42/0.59          | ~ (l3_lattices @ sk_A)
% 0.42/0.59          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.42/0.59          | (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X1)
% 0.42/0.59          | ~ (r2_hidden @ X1 @ X2)
% 0.42/0.59          | ~ (r3_lattice3 @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X2))),
% 0.42/0.59      inference('sup-', [status(thm)], ['34', '35'])).
% 0.42/0.59  thf('37', plain, ((l3_lattices @ sk_A)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('38', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.59         ((r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.42/0.59          | (v2_struct_0 @ sk_A)
% 0.42/0.59          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.42/0.59          | (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X1)
% 0.42/0.59          | ~ (r2_hidden @ X1 @ X2)
% 0.42/0.59          | ~ (r3_lattice3 @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X2))),
% 0.42/0.59      inference('demod', [status(thm)], ['36', '37'])).
% 0.42/0.59  thf('39', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i]:
% 0.42/0.59         (~ (l3_lattices @ sk_A)
% 0.42/0.59          | (v2_struct_0 @ sk_A)
% 0.42/0.59          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 0.42/0.59          | ~ (r2_hidden @ X1 @ X0)
% 0.42/0.59          | (r1_lattices @ sk_A @ 
% 0.42/0.59             (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ X0) @ sk_B @ sk_A) @ X1)
% 0.42/0.59          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.42/0.59          | (v2_struct_0 @ sk_A)
% 0.42/0.59          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['27', '38'])).
% 0.42/0.59  thf('40', plain, ((l3_lattices @ sk_A)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('41', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i]:
% 0.42/0.59         ((v2_struct_0 @ sk_A)
% 0.42/0.59          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 0.42/0.59          | ~ (r2_hidden @ X1 @ X0)
% 0.42/0.59          | (r1_lattices @ sk_A @ 
% 0.42/0.59             (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ X0) @ sk_B @ sk_A) @ X1)
% 0.42/0.59          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.42/0.59          | (v2_struct_0 @ sk_A)
% 0.42/0.59          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0)))),
% 0.42/0.59      inference('demod', [status(thm)], ['39', '40'])).
% 0.42/0.59  thf('42', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i]:
% 0.42/0.59         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.42/0.59          | (r1_lattices @ sk_A @ 
% 0.42/0.59             (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ X0) @ sk_B @ sk_A) @ X1)
% 0.42/0.59          | ~ (r2_hidden @ X1 @ X0)
% 0.42/0.59          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 0.42/0.59          | (v2_struct_0 @ sk_A))),
% 0.42/0.59      inference('simplify', [status(thm)], ['41'])).
% 0.42/0.59  thf('43', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         ((v2_struct_0 @ sk_A)
% 0.42/0.59          | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 0.42/0.59          | ~ (r2_hidden @ sk_B @ X0)
% 0.42/0.59          | (r1_lattices @ sk_A @ 
% 0.42/0.59             (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ X0) @ sk_B @ sk_A) @ sk_B))),
% 0.42/0.59      inference('sup-', [status(thm)], ['13', '42'])).
% 0.42/0.59  thf('44', plain,
% 0.42/0.59      (((r1_lattices @ sk_A @ 
% 0.42/0.59         (sk_D_1 @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_B @ sk_A) @ sk_B)
% 0.42/0.59        | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))
% 0.42/0.59        | (v2_struct_0 @ sk_A))),
% 0.42/0.59      inference('sup-', [status(thm)], ['12', '43'])).
% 0.42/0.59  thf('45', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('46', plain,
% 0.42/0.60      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.42/0.60         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 0.42/0.60          | ~ (r1_lattices @ X6 @ (sk_D_1 @ X9 @ X5 @ X6) @ X5)
% 0.42/0.60          | (r4_lattice3 @ X6 @ X5 @ X9)
% 0.42/0.60          | ~ (l3_lattices @ X6)
% 0.42/0.60          | (v2_struct_0 @ X6))),
% 0.42/0.60      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.42/0.60  thf('47', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((v2_struct_0 @ sk_A)
% 0.42/0.60          | ~ (l3_lattices @ sk_A)
% 0.42/0.60          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.42/0.60          | ~ (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_B))),
% 0.42/0.60      inference('sup-', [status(thm)], ['45', '46'])).
% 0.42/0.60  thf('48', plain, ((l3_lattices @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('49', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((v2_struct_0 @ sk_A)
% 0.42/0.60          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.42/0.60          | ~ (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_B))),
% 0.42/0.60      inference('demod', [status(thm)], ['47', '48'])).
% 0.42/0.60  thf('50', plain, (~ (v2_struct_0 @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('51', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_B)
% 0.42/0.60          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 0.42/0.60      inference('clc', [status(thm)], ['49', '50'])).
% 0.42/0.60  thf('52', plain,
% 0.42/0.60      (((v2_struct_0 @ sk_A)
% 0.42/0.60        | (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C)))),
% 0.42/0.60      inference('clc', [status(thm)], ['44', '51'])).
% 0.42/0.60  thf('53', plain, (~ (v2_struct_0 @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('54', plain,
% 0.42/0.60      ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))),
% 0.42/0.60      inference('clc', [status(thm)], ['52', '53'])).
% 0.42/0.60  thf('55', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf(d21_lattice3, axiom,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.42/0.60       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.42/0.60           ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.42/0.60         ( ![B:$i,C:$i]:
% 0.42/0.60           ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.42/0.60             ( ( ( C ) = ( k15_lattice3 @ A @ B ) ) <=>
% 0.42/0.60               ( ( r4_lattice3 @ A @ C @ B ) & 
% 0.42/0.60                 ( ![D:$i]:
% 0.42/0.60                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.42/0.60                     ( ( r4_lattice3 @ A @ D @ B ) =>
% 0.42/0.60                       ( r1_lattices @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.42/0.60  thf('56', plain,
% 0.42/0.60      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.42/0.60         ((v2_struct_0 @ X10)
% 0.42/0.60          | ~ (v10_lattices @ X10)
% 0.42/0.60          | ~ (v4_lattice3 @ X10)
% 0.42/0.60          | ~ (l3_lattices @ X10)
% 0.42/0.60          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.42/0.60          | ~ (r4_lattice3 @ X10 @ X11 @ X12)
% 0.42/0.60          | (r4_lattice3 @ X10 @ (sk_D_2 @ X11 @ X12 @ X10) @ X12)
% 0.42/0.60          | ((X11) = (k15_lattice3 @ X10 @ X12))
% 0.42/0.60          | ~ (l3_lattices @ X10)
% 0.42/0.60          | (v2_struct_0 @ X10))),
% 0.42/0.60      inference('cnf', [status(esa)], [d21_lattice3])).
% 0.42/0.60  thf('57', plain,
% 0.42/0.60      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.42/0.60         (((X11) = (k15_lattice3 @ X10 @ X12))
% 0.42/0.60          | (r4_lattice3 @ X10 @ (sk_D_2 @ X11 @ X12 @ X10) @ X12)
% 0.42/0.60          | ~ (r4_lattice3 @ X10 @ X11 @ X12)
% 0.42/0.60          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.42/0.60          | ~ (l3_lattices @ X10)
% 0.42/0.60          | ~ (v4_lattice3 @ X10)
% 0.42/0.60          | ~ (v10_lattices @ X10)
% 0.42/0.60          | (v2_struct_0 @ X10))),
% 0.42/0.60      inference('simplify', [status(thm)], ['56'])).
% 0.42/0.60  thf('58', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((v2_struct_0 @ sk_A)
% 0.42/0.60          | ~ (v10_lattices @ sk_A)
% 0.42/0.60          | ~ (v4_lattice3 @ sk_A)
% 0.42/0.60          | ~ (l3_lattices @ sk_A)
% 0.42/0.60          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.42/0.60          | (r4_lattice3 @ sk_A @ (sk_D_2 @ sk_B @ X0 @ sk_A) @ X0)
% 0.42/0.60          | ((sk_B) = (k15_lattice3 @ sk_A @ X0)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['55', '57'])).
% 0.42/0.60  thf('59', plain, ((v10_lattices @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('60', plain, ((v4_lattice3 @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('61', plain, ((l3_lattices @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('62', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((v2_struct_0 @ sk_A)
% 0.42/0.60          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.42/0.60          | (r4_lattice3 @ sk_A @ (sk_D_2 @ sk_B @ X0 @ sk_A) @ X0)
% 0.42/0.60          | ((sk_B) = (k15_lattice3 @ sk_A @ X0)))),
% 0.42/0.60      inference('demod', [status(thm)], ['58', '59', '60', '61'])).
% 0.42/0.60  thf('63', plain,
% 0.42/0.60      ((((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 0.42/0.60        | (r4_lattice3 @ sk_A @ 
% 0.42/0.60           (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A) @ 
% 0.42/0.60           (a_2_1_lattice3 @ sk_A @ sk_C))
% 0.42/0.60        | (v2_struct_0 @ sk_A))),
% 0.42/0.60      inference('sup-', [status(thm)], ['54', '62'])).
% 0.42/0.60  thf('64', plain, (~ (v2_struct_0 @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('65', plain,
% 0.42/0.60      (((r4_lattice3 @ sk_A @ 
% 0.42/0.60         (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A) @ 
% 0.42/0.60         (a_2_1_lattice3 @ sk_A @ sk_C))
% 0.42/0.60        | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 0.42/0.60      inference('clc', [status(thm)], ['63', '64'])).
% 0.42/0.60  thf('66', plain,
% 0.42/0.60      ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))),
% 0.42/0.60      inference('clc', [status(thm)], ['52', '53'])).
% 0.42/0.60  thf('67', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('68', plain,
% 0.42/0.60      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.42/0.60         ((v2_struct_0 @ X10)
% 0.42/0.60          | ~ (v10_lattices @ X10)
% 0.42/0.60          | ~ (v4_lattice3 @ X10)
% 0.42/0.60          | ~ (l3_lattices @ X10)
% 0.42/0.60          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.42/0.60          | ~ (r4_lattice3 @ X10 @ X11 @ X12)
% 0.42/0.60          | (m1_subset_1 @ (sk_D_2 @ X11 @ X12 @ X10) @ (u1_struct_0 @ X10))
% 0.42/0.60          | ((X11) = (k15_lattice3 @ X10 @ X12))
% 0.42/0.60          | ~ (l3_lattices @ X10)
% 0.42/0.60          | (v2_struct_0 @ X10))),
% 0.42/0.60      inference('cnf', [status(esa)], [d21_lattice3])).
% 0.42/0.60  thf('69', plain,
% 0.42/0.60      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.42/0.60         (((X11) = (k15_lattice3 @ X10 @ X12))
% 0.42/0.60          | (m1_subset_1 @ (sk_D_2 @ X11 @ X12 @ X10) @ (u1_struct_0 @ X10))
% 0.42/0.60          | ~ (r4_lattice3 @ X10 @ X11 @ X12)
% 0.42/0.60          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.42/0.60          | ~ (l3_lattices @ X10)
% 0.42/0.60          | ~ (v4_lattice3 @ X10)
% 0.42/0.60          | ~ (v10_lattices @ X10)
% 0.42/0.60          | (v2_struct_0 @ X10))),
% 0.42/0.60      inference('simplify', [status(thm)], ['68'])).
% 0.42/0.60  thf('70', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((v2_struct_0 @ sk_A)
% 0.42/0.60          | ~ (v10_lattices @ sk_A)
% 0.42/0.60          | ~ (v4_lattice3 @ sk_A)
% 0.42/0.60          | ~ (l3_lattices @ sk_A)
% 0.42/0.60          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.42/0.60          | (m1_subset_1 @ (sk_D_2 @ sk_B @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.42/0.60          | ((sk_B) = (k15_lattice3 @ sk_A @ X0)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['67', '69'])).
% 0.42/0.60  thf('71', plain, ((v10_lattices @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('72', plain, ((v4_lattice3 @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('73', plain, ((l3_lattices @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('74', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((v2_struct_0 @ sk_A)
% 0.42/0.60          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.42/0.60          | (m1_subset_1 @ (sk_D_2 @ sk_B @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.42/0.60          | ((sk_B) = (k15_lattice3 @ sk_A @ X0)))),
% 0.42/0.60      inference('demod', [status(thm)], ['70', '71', '72', '73'])).
% 0.42/0.60  thf('75', plain,
% 0.42/0.60      ((((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 0.42/0.60        | (m1_subset_1 @ 
% 0.42/0.60           (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A) @ 
% 0.42/0.60           (u1_struct_0 @ sk_A))
% 0.42/0.60        | (v2_struct_0 @ sk_A))),
% 0.42/0.60      inference('sup-', [status(thm)], ['66', '74'])).
% 0.42/0.60  thf('76', plain, (~ (v2_struct_0 @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('77', plain,
% 0.42/0.60      (((m1_subset_1 @ 
% 0.42/0.60         (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A) @ 
% 0.42/0.60         (u1_struct_0 @ sk_A))
% 0.42/0.60        | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 0.42/0.60      inference('clc', [status(thm)], ['75', '76'])).
% 0.42/0.60  thf('78', plain,
% 0.42/0.60      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.42/0.60         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 0.42/0.60          | ~ (r4_lattice3 @ X6 @ X5 @ X7)
% 0.42/0.60          | ~ (r2_hidden @ X8 @ X7)
% 0.42/0.60          | (r1_lattices @ X6 @ X8 @ X5)
% 0.42/0.60          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X6))
% 0.42/0.60          | ~ (l3_lattices @ X6)
% 0.42/0.60          | (v2_struct_0 @ X6))),
% 0.42/0.60      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.42/0.60  thf('79', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         (((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 0.42/0.60          | (v2_struct_0 @ sk_A)
% 0.42/0.60          | ~ (l3_lattices @ sk_A)
% 0.42/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.42/0.60          | (r1_lattices @ sk_A @ X0 @ 
% 0.42/0.60             (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A))
% 0.42/0.60          | ~ (r2_hidden @ X0 @ X1)
% 0.42/0.60          | ~ (r4_lattice3 @ sk_A @ 
% 0.42/0.60               (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A) @ X1))),
% 0.42/0.60      inference('sup-', [status(thm)], ['77', '78'])).
% 0.42/0.60  thf('80', plain, ((l3_lattices @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('81', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         (((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 0.42/0.60          | (v2_struct_0 @ sk_A)
% 0.42/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.42/0.60          | (r1_lattices @ sk_A @ X0 @ 
% 0.42/0.60             (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A))
% 0.42/0.60          | ~ (r2_hidden @ X0 @ X1)
% 0.42/0.60          | ~ (r4_lattice3 @ sk_A @ 
% 0.42/0.60               (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A) @ X1))),
% 0.42/0.60      inference('demod', [status(thm)], ['79', '80'])).
% 0.42/0.60  thf('82', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 0.42/0.60          | ~ (r2_hidden @ X0 @ (a_2_1_lattice3 @ sk_A @ sk_C))
% 0.42/0.60          | (r1_lattices @ sk_A @ X0 @ 
% 0.42/0.60             (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A))
% 0.42/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.42/0.60          | (v2_struct_0 @ sk_A)
% 0.42/0.60          | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['65', '81'])).
% 0.42/0.60  thf('83', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((v2_struct_0 @ sk_A)
% 0.42/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.42/0.60          | (r1_lattices @ sk_A @ X0 @ 
% 0.42/0.60             (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A))
% 0.42/0.60          | ~ (r2_hidden @ X0 @ (a_2_1_lattice3 @ sk_A @ sk_C))
% 0.42/0.60          | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 0.42/0.60      inference('simplify', [status(thm)], ['82'])).
% 0.42/0.60  thf('84', plain,
% 0.42/0.60      ((((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 0.42/0.60        | (r1_lattices @ sk_A @ sk_B @ 
% 0.42/0.60           (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A))
% 0.42/0.60        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.42/0.60        | (v2_struct_0 @ sk_A))),
% 0.42/0.60      inference('sup-', [status(thm)], ['11', '83'])).
% 0.42/0.60  thf('85', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('86', plain,
% 0.42/0.60      ((((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 0.42/0.60        | (r1_lattices @ sk_A @ sk_B @ 
% 0.42/0.60           (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A))
% 0.42/0.60        | (v2_struct_0 @ sk_A))),
% 0.42/0.60      inference('demod', [status(thm)], ['84', '85'])).
% 0.42/0.60  thf('87', plain, (~ (v2_struct_0 @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('88', plain,
% 0.42/0.60      (((r1_lattices @ sk_A @ sk_B @ 
% 0.42/0.60         (sk_D_2 @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C) @ sk_A))
% 0.42/0.60        | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 0.42/0.60      inference('clc', [status(thm)], ['86', '87'])).
% 0.42/0.60  thf('89', plain,
% 0.42/0.60      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.42/0.60         ((v2_struct_0 @ X10)
% 0.42/0.60          | ~ (v10_lattices @ X10)
% 0.42/0.60          | ~ (v4_lattice3 @ X10)
% 0.42/0.60          | ~ (l3_lattices @ X10)
% 0.42/0.60          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.42/0.60          | ~ (r4_lattice3 @ X10 @ X11 @ X12)
% 0.42/0.60          | ~ (r1_lattices @ X10 @ X11 @ (sk_D_2 @ X11 @ X12 @ X10))
% 0.42/0.60          | ((X11) = (k15_lattice3 @ X10 @ X12))
% 0.42/0.60          | ~ (l3_lattices @ X10)
% 0.42/0.60          | (v2_struct_0 @ X10))),
% 0.42/0.60      inference('cnf', [status(esa)], [d21_lattice3])).
% 0.42/0.60  thf('90', plain,
% 0.42/0.60      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.42/0.60         (((X11) = (k15_lattice3 @ X10 @ X12))
% 0.42/0.60          | ~ (r1_lattices @ X10 @ X11 @ (sk_D_2 @ X11 @ X12 @ X10))
% 0.42/0.60          | ~ (r4_lattice3 @ X10 @ X11 @ X12)
% 0.42/0.60          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.42/0.60          | ~ (l3_lattices @ X10)
% 0.42/0.60          | ~ (v4_lattice3 @ X10)
% 0.42/0.60          | ~ (v10_lattices @ X10)
% 0.42/0.60          | (v2_struct_0 @ X10))),
% 0.42/0.60      inference('simplify', [status(thm)], ['89'])).
% 0.42/0.60  thf('91', plain,
% 0.42/0.60      ((((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 0.42/0.60        | (v2_struct_0 @ sk_A)
% 0.42/0.60        | ~ (v10_lattices @ sk_A)
% 0.42/0.60        | ~ (v4_lattice3 @ sk_A)
% 0.42/0.60        | ~ (l3_lattices @ sk_A)
% 0.42/0.60        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.42/0.60        | ~ (r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))
% 0.42/0.60        | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['88', '90'])).
% 0.42/0.60  thf('92', plain, ((v10_lattices @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('93', plain, ((v4_lattice3 @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('94', plain, ((l3_lattices @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('95', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('96', plain,
% 0.42/0.60      ((r4_lattice3 @ sk_A @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))),
% 0.42/0.60      inference('clc', [status(thm)], ['52', '53'])).
% 0.42/0.60  thf('97', plain,
% 0.42/0.60      ((((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))
% 0.42/0.60        | (v2_struct_0 @ sk_A)
% 0.42/0.60        | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 0.42/0.60      inference('demod', [status(thm)], ['91', '92', '93', '94', '95', '96'])).
% 0.42/0.60  thf('98', plain,
% 0.42/0.60      (((v2_struct_0 @ sk_A)
% 0.42/0.60        | ((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C))))),
% 0.42/0.60      inference('simplify', [status(thm)], ['97'])).
% 0.42/0.60  thf('99', plain, (~ (v2_struct_0 @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('100', plain,
% 0.42/0.60      (((sk_B) = (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))),
% 0.42/0.60      inference('clc', [status(thm)], ['98', '99'])).
% 0.42/0.60  thf('101', plain,
% 0.42/0.60      ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C))
% 0.42/0.60        | (v2_struct_0 @ sk_A)
% 0.42/0.60        | ~ (l3_lattices @ sk_A))),
% 0.42/0.60      inference('sup+', [status(thm)], ['1', '100'])).
% 0.42/0.60  thf('102', plain, ((l3_lattices @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('103', plain,
% 0.42/0.60      ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C)) | (v2_struct_0 @ sk_A))),
% 0.42/0.60      inference('demod', [status(thm)], ['101', '102'])).
% 0.42/0.60  thf('104', plain, (((k16_lattice3 @ sk_A @ sk_C) != (sk_B))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('105', plain, ((v2_struct_0 @ sk_A)),
% 0.42/0.60      inference('simplify_reflect-', [status(thm)], ['103', '104'])).
% 0.42/0.60  thf('106', plain, ($false), inference('demod', [status(thm)], ['0', '105'])).
% 0.42/0.60  
% 0.42/0.60  % SZS output end Refutation
% 0.42/0.60  
% 0.42/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
