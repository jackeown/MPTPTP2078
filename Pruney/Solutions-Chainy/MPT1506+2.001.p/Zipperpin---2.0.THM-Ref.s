%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yhdmFTV2pt

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:29 EST 2020

% Result     : Theorem 49.60s
% Output     : Refutation 49.60s
% Verified   : 
% Statistics : Number of formulae       :  200 ( 737 expanded)
%              Number of leaves         :   35 ( 214 expanded)
%              Depth                    :   40
%              Number of atoms          : 3817 (17789 expanded)
%              Number of equality atoms :   42 (  74 expanded)
%              Maximal formula depth    :   30 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(a_2_9_lattice3_type,type,(
    a_2_9_lattice3: $i > $i > $i )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r3_lattice3_type,type,(
    r3_lattice3: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r4_lattice3_type,type,(
    r4_lattice3: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(sk_D_4_type,type,(
    sk_D_4: $i > $i > $i > $i )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i > $i )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t40_lattice3,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v4_lattice3 @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( r3_lattice3 @ A @ B @ C )
               => ( r3_lattices @ A @ B @ ( k16_lattice3 @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t40_lattice3])).

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
    ! [X15: $i,X16: $i] :
      ( ~ ( v4_lattice3 @ X15 )
      | ( m1_subset_1 @ ( sk_C @ X16 @ X15 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( l3_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
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

thf('2',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X4 @ X5 ) @ X8 )
      | ( r3_lattice3 @ X5 @ X4 @ X8 )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X2 )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v4_lattice3 @ X15 )
      | ( m1_subset_1 @ ( sk_C @ X16 @ X15 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( l3_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('6',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( m1_subset_1 @ ( sk_D @ X8 @ X4 @ X5 ) @ ( u1_struct_0 @ X5 ) )
      | ( r3_lattice3 @ X5 @ X4 @ X8 )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( m1_subset_1 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

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

thf('10',plain,(
    ! [X9: $i,X10: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ( r2_hidden @ ( sk_D_1 @ X13 @ X9 @ X10 ) @ X13 )
      | ( r4_lattice3 @ X10 @ X9 @ X13 )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X3 )
      | ( r2_hidden @ ( sk_D_1 @ X3 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X0 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X3 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X0 ) @ X3 )
      | ( r4_lattice3 @ X0 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X3 )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

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

thf('13',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( l3_lattices @ X18 )
      | ~ ( v4_lattice3 @ X18 )
      | ~ ( v10_lattices @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( X20
        = ( sk_D_3 @ X19 @ X18 @ X20 ) )
      | ~ ( r2_hidden @ X20 @ ( a_2_9_lattice3 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_9_lattice3])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( l3_lattices @ X2 )
      | ~ ( v4_lattice3 @ X2 )
      | ( r3_lattice3 @ X2 @ ( sk_C @ X3 @ X2 ) @ X4 )
      | ( r4_lattice3 @ X2 @ ( sk_D @ X4 @ ( sk_C @ X3 @ X2 ) @ X2 ) @ ( a_2_9_lattice3 @ X1 @ X0 ) )
      | ( ( sk_D_1 @ ( a_2_9_lattice3 @ X1 @ X0 ) @ ( sk_D @ X4 @ ( sk_C @ X3 @ X2 ) @ X2 ) @ X2 )
        = ( sk_D_3 @ X0 @ X1 @ ( sk_D_1 @ ( a_2_9_lattice3 @ X1 @ X0 ) @ ( sk_D @ X4 @ ( sk_C @ X3 @ X2 ) @ X2 ) @ X2 ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X3 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X0 ) @ X3 )
      | ( r4_lattice3 @ X0 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X3 )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('16',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( l3_lattices @ X18 )
      | ~ ( v4_lattice3 @ X18 )
      | ~ ( v10_lattices @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( r3_lattice3 @ X18 @ ( sk_D_3 @ X19 @ X18 @ X20 ) @ X19 )
      | ~ ( r2_hidden @ X20 @ ( a_2_9_lattice3 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_9_lattice3])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( l3_lattices @ X2 )
      | ~ ( v4_lattice3 @ X2 )
      | ( r3_lattice3 @ X2 @ ( sk_C @ X3 @ X2 ) @ X4 )
      | ( r4_lattice3 @ X2 @ ( sk_D @ X4 @ ( sk_C @ X3 @ X2 ) @ X2 ) @ ( a_2_9_lattice3 @ X1 @ X0 ) )
      | ( r3_lattice3 @ X1 @ ( sk_D_3 @ X0 @ X1 @ ( sk_D_1 @ ( a_2_9_lattice3 @ X1 @ X0 ) @ ( sk_D @ X4 @ ( sk_C @ X3 @ X2 ) @ X2 ) @ X2 ) ) @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r3_lattice3 @ X4 @ ( sk_D_1 @ ( a_2_9_lattice3 @ X4 @ X3 ) @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X0 ) @ X3 )
      | ~ ( l3_lattices @ X4 )
      | ~ ( v4_lattice3 @ X4 )
      | ~ ( v10_lattices @ X4 )
      | ( v2_struct_0 @ X4 )
      | ( r4_lattice3 @ X0 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ ( a_2_9_lattice3 @ X4 @ X3 ) )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X4 )
      | ~ ( v4_lattice3 @ X4 )
      | ~ ( v10_lattices @ X4 )
      | ( v2_struct_0 @ X4 )
      | ( r4_lattice3 @ X0 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ ( a_2_9_lattice3 @ X4 @ X3 ) )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r4_lattice3 @ X0 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ ( a_2_9_lattice3 @ X4 @ X3 ) )
      | ( v2_struct_0 @ X4 )
      | ~ ( v10_lattices @ X4 )
      | ~ ( v4_lattice3 @ X4 )
      | ~ ( l3_lattices @ X4 )
      | ( r3_lattice3 @ X4 @ ( sk_D_1 @ ( a_2_9_lattice3 @ X4 @ X3 ) @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X0 ) @ X3 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('21',plain,(
    ! [X9: $i,X10: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X13 @ X9 @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ( r4_lattice3 @ X10 @ X9 @ X13 )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X3 )
      | ( m1_subset_1 @ ( sk_D_1 @ X3 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( sk_D_1 @ X3 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r4_lattice3 @ X0 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X3 )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r3_lattice3 @ X5 @ X4 @ X6 )
      | ~ ( r2_hidden @ X7 @ X6 )
      | ( r1_lattices @ X5 @ X4 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r4_lattice3 @ X0 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X3 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( sk_D_1 @ X3 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X0 ) @ X4 )
      | ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r3_lattice3 @ X0 @ ( sk_D_1 @ X3 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X0 ) @ X5 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r3_lattice3 @ X0 @ ( sk_D_1 @ X3 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X0 ) @ X5 )
      | ~ ( r2_hidden @ X4 @ X5 )
      | ( r1_lattices @ X0 @ ( sk_D_1 @ X3 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X0 ) @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X0 ) )
      | ( r4_lattice3 @ X0 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X3 )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( r4_lattice3 @ X1 @ ( sk_D @ X3 @ ( sk_C @ X2 @ X1 ) @ X1 ) @ ( a_2_9_lattice3 @ X1 @ X0 ) )
      | ( r3_lattice3 @ X1 @ ( sk_C @ X2 @ X1 ) @ X3 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ( r3_lattice3 @ X1 @ ( sk_C @ X2 @ X1 ) @ X3 )
      | ( r4_lattice3 @ X1 @ ( sk_D @ X3 @ ( sk_C @ X2 @ X1 ) @ X1 ) @ ( a_2_9_lattice3 @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X1 ) )
      | ( r1_lattices @ X1 @ ( sk_D_1 @ ( a_2_9_lattice3 @ X1 @ X0 ) @ ( sk_D @ X3 @ ( sk_C @ X2 @ X1 ) @ X1 ) @ X1 ) @ X4 )
      | ~ ( r2_hidden @ X4 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X0 )
      | ( r1_lattices @ X1 @ ( sk_D_1 @ ( a_2_9_lattice3 @ X1 @ X0 ) @ ( sk_D @ X3 @ ( sk_C @ X2 @ X1 ) @ X1 ) @ X1 ) @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X1 ) )
      | ( r3_lattice3 @ X1 @ ( sk_C @ X2 @ X1 ) @ X3 )
      | ( r4_lattice3 @ X1 @ ( sk_D @ X3 @ ( sk_C @ X2 @ X1 ) @ X1 ) @ ( a_2_9_lattice3 @ X1 @ X0 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r4_lattice3 @ X0 @ ( sk_D @ X5 @ ( sk_C @ X4 @ X0 ) @ X0 ) @ ( a_2_9_lattice3 @ X0 @ X3 ) )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X4 @ X0 ) @ X5 )
      | ( r1_lattices @ X0 @ ( sk_D_1 @ ( a_2_9_lattice3 @ X0 @ X3 ) @ ( sk_D @ X5 @ ( sk_C @ X4 @ X0 ) @ X0 ) @ X0 ) @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['8','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X3 )
      | ( r1_lattices @ X0 @ ( sk_D_1 @ ( a_2_9_lattice3 @ X0 @ X3 ) @ ( sk_D @ X5 @ ( sk_C @ X4 @ X0 ) @ X0 ) @ X0 ) @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X4 @ X0 ) @ X5 )
      | ( r4_lattice3 @ X0 @ ( sk_D @ X5 @ ( sk_C @ X4 @ X0 ) @ X0 ) @ ( a_2_9_lattice3 @ X0 @ X3 ) )
      | ~ ( v10_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ( r3_lattice3 @ X1 @ ( sk_C @ X2 @ X1 ) @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ( r3_lattice3 @ X1 @ ( sk_C @ X2 @ X1 ) @ X0 )
      | ~ ( v10_lattices @ X1 )
      | ( r4_lattice3 @ X1 @ ( sk_D @ X4 @ ( sk_C @ X3 @ X1 ) @ X1 ) @ ( a_2_9_lattice3 @ X1 @ X0 ) )
      | ( r3_lattice3 @ X1 @ ( sk_C @ X3 @ X1 ) @ X4 )
      | ( r1_lattices @ X1 @ ( sk_D_1 @ ( a_2_9_lattice3 @ X1 @ X0 ) @ ( sk_D @ X4 @ ( sk_C @ X3 @ X1 ) @ X1 ) @ X1 ) @ ( sk_D @ X0 @ ( sk_C @ X2 @ X1 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r1_lattices @ X1 @ ( sk_D_1 @ ( a_2_9_lattice3 @ X1 @ X0 ) @ ( sk_D @ X4 @ ( sk_C @ X3 @ X1 ) @ X1 ) @ X1 ) @ ( sk_D @ X0 @ ( sk_C @ X2 @ X1 ) @ X1 ) )
      | ( r3_lattice3 @ X1 @ ( sk_C @ X3 @ X1 ) @ X4 )
      | ( r4_lattice3 @ X1 @ ( sk_D @ X4 @ ( sk_C @ X3 @ X1 ) @ X1 ) @ ( a_2_9_lattice3 @ X1 @ X0 ) )
      | ~ ( v10_lattices @ X1 )
      | ( r3_lattice3 @ X1 @ ( sk_C @ X2 @ X1 ) @ X0 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('34',plain,(
    ! [X9: $i,X10: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( r1_lattices @ X10 @ ( sk_D_1 @ X13 @ X9 @ X10 ) @ X9 )
      | ( r4_lattice3 @ X10 @ X9 @ X13 )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X3 )
      | ~ ( r1_lattices @ X0 @ ( sk_D_1 @ X3 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X0 ) @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_lattices @ X0 @ ( sk_D_1 @ X3 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X0 ) @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) )
      | ( r4_lattice3 @ X0 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X3 )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( v10_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ ( a_2_9_lattice3 @ X0 @ X2 ) )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r4_lattice3 @ X0 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ ( a_2_9_lattice3 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['32','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r4_lattice3 @ X0 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ ( a_2_9_lattice3 @ X0 @ X2 ) )
      | ~ ( v10_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('40',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v4_lattice3 @ X15 )
      | ~ ( r4_lattice3 @ X15 @ X17 @ X16 )
      | ( r1_lattices @ X15 @ ( sk_C @ X16 @ X15 ) @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l3_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r1_lattices @ X0 @ ( sk_C @ X3 @ X0 ) @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) )
      | ~ ( r4_lattice3 @ X0 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X3 )
      | ~ ( v4_lattice3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r4_lattice3 @ X0 @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X3 )
      | ( r1_lattices @ X0 @ ( sk_C @ X3 @ X0 ) @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ( r3_lattice3 @ X1 @ ( sk_C @ X2 @ X1 ) @ X0 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ( r3_lattice3 @ X1 @ ( sk_C @ X2 @ X1 ) @ X0 )
      | ( r1_lattices @ X1 @ ( sk_C @ ( a_2_9_lattice3 @ X1 @ X0 ) @ X1 ) @ ( sk_D @ X0 @ ( sk_C @ X2 @ X1 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['38','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_lattices @ X1 @ ( sk_C @ ( a_2_9_lattice3 @ X1 @ X0 ) @ X1 ) @ ( sk_D @ X0 @ ( sk_C @ X2 @ X1 ) @ X1 ) )
      | ~ ( v10_lattices @ X1 )
      | ( r3_lattice3 @ X1 @ ( sk_C @ X2 @ X1 ) @ X0 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v4_lattice3 @ X15 )
      | ( m1_subset_1 @ ( sk_C @ X16 @ X15 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( l3_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('46',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r1_lattices @ X5 @ X4 @ ( sk_D @ X8 @ X4 @ X5 ) )
      | ( r3_lattice3 @ X5 @ X4 @ X8 )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( r1_lattices @ X0 @ ( sk_C @ X1 @ X0 ) @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattices @ X0 @ ( sk_C @ X1 @ X0 ) @ ( sk_D @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) )
      | ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r3_lattice3 @ X0 @ ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 ) @ X1 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r3_lattice3 @ X0 @ ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v10_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 ) @ X1 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v4_lattice3 @ X15 )
      | ( m1_subset_1 @ ( sk_C @ X16 @ X15 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( l3_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v10_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 ) @ X1 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('53',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v4_lattice3 @ X15 )
      | ( m1_subset_1 @ ( sk_C @ X16 @ X15 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( l3_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

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

thf('54',plain,(
    ! [X22: $i,X23: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ~ ( r3_lattice3 @ X23 @ X22 @ X26 )
      | ( r3_lattice3 @ X23 @ ( sk_D_4 @ X26 @ X22 @ X23 ) @ X26 )
      | ( X22
        = ( k16_lattice3 @ X23 @ X26 ) )
      | ~ ( l3_lattices @ X23 )
      | ~ ( v4_lattice3 @ X23 )
      | ~ ( v10_lattices @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( ( sk_C @ X1 @ X0 )
        = ( k16_lattice3 @ X0 @ X2 ) )
      | ( r3_lattice3 @ X0 @ ( sk_D_4 @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X2 )
      | ~ ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r3_lattice3 @ X0 @ ( sk_D_4 @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X2 )
      | ( ( sk_C @ X1 @ X0 )
        = ( k16_lattice3 @ X0 @ X2 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( ( sk_C @ ( a_2_9_lattice3 @ X1 @ X0 ) @ X1 )
        = ( k16_lattice3 @ X1 @ X0 ) )
      | ( r3_lattice3 @ X1 @ ( sk_D_4 @ X0 @ ( sk_C @ ( a_2_9_lattice3 @ X1 @ X0 ) @ X1 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ X1 @ ( sk_D_4 @ X0 @ ( sk_C @ ( a_2_9_lattice3 @ X1 @ X0 ) @ X1 ) @ X1 ) @ X0 )
      | ( ( sk_C @ ( a_2_9_lattice3 @ X1 @ X0 ) @ X1 )
        = ( k16_lattice3 @ X1 @ X0 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v10_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 ) @ X1 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('60',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v4_lattice3 @ X15 )
      | ( m1_subset_1 @ ( sk_C @ X16 @ X15 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( l3_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('61',plain,(
    ! [X22: $i,X23: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ~ ( r3_lattice3 @ X23 @ X22 @ X26 )
      | ( m1_subset_1 @ ( sk_D_4 @ X26 @ X22 @ X23 ) @ ( u1_struct_0 @ X23 ) )
      | ( X22
        = ( k16_lattice3 @ X23 @ X26 ) )
      | ~ ( l3_lattices @ X23 )
      | ~ ( v4_lattice3 @ X23 )
      | ~ ( v10_lattices @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( ( sk_C @ X1 @ X0 )
        = ( k16_lattice3 @ X0 @ X2 ) )
      | ( m1_subset_1 @ ( sk_D_4 @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( m1_subset_1 @ ( sk_D_4 @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( sk_C @ X1 @ X0 )
        = ( k16_lattice3 @ X0 @ X2 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( ( sk_C @ ( a_2_9_lattice3 @ X1 @ X0 ) @ X1 )
        = ( k16_lattice3 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( sk_D_4 @ X0 @ ( sk_C @ ( a_2_9_lattice3 @ X1 @ X0 ) @ X1 ) @ X1 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['59','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_D_4 @ X0 @ ( sk_C @ ( a_2_9_lattice3 @ X1 @ X0 ) @ X1 ) @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ( ( sk_C @ ( a_2_9_lattice3 @ X1 @ X0 ) @ X1 )
        = ( k16_lattice3 @ X1 @ X0 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( l3_lattices @ X18 )
      | ~ ( v4_lattice3 @ X18 )
      | ~ ( v10_lattices @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( r2_hidden @ X20 @ ( a_2_9_lattice3 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X18 ) )
      | ( X20 != X21 )
      | ~ ( r3_lattice3 @ X18 @ X21 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_9_lattice3])).

thf('67',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ~ ( r3_lattice3 @ X18 @ X21 @ X19 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X18 ) )
      | ( r2_hidden @ X21 @ ( a_2_9_lattice3 @ X18 @ X19 ) )
      | ( v2_struct_0 @ X18 )
      | ~ ( v10_lattices @ X18 )
      | ~ ( v4_lattice3 @ X18 )
      | ~ ( l3_lattices @ X18 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 )
        = ( k16_lattice3 @ X0 @ X1 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r2_hidden @ ( sk_D_4 @ X1 @ ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 ) @ X0 ) @ ( a_2_9_lattice3 @ X0 @ X2 ) )
      | ~ ( r3_lattice3 @ X0 @ ( sk_D_4 @ X1 @ ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 ) @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['65','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r3_lattice3 @ X0 @ ( sk_D_4 @ X1 @ ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 ) @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_D_4 @ X1 @ ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 ) @ X0 ) @ ( a_2_9_lattice3 @ X0 @ X2 ) )
      | ( ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 )
        = ( k16_lattice3 @ X0 @ X1 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( ( sk_C @ ( a_2_9_lattice3 @ X1 @ X0 ) @ X1 )
        = ( k16_lattice3 @ X1 @ X0 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( ( sk_C @ ( a_2_9_lattice3 @ X1 @ X0 ) @ X1 )
        = ( k16_lattice3 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D_4 @ X0 @ ( sk_C @ ( a_2_9_lattice3 @ X1 @ X0 ) @ X1 ) @ X1 ) @ ( a_2_9_lattice3 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['58','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_4 @ X0 @ ( sk_C @ ( a_2_9_lattice3 @ X1 @ X0 ) @ X1 ) @ X1 ) @ ( a_2_9_lattice3 @ X1 @ X0 ) )
      | ( ( sk_C @ ( a_2_9_lattice3 @ X1 @ X0 ) @ X1 )
        = ( k16_lattice3 @ X1 @ X0 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_D_4 @ X0 @ ( sk_C @ ( a_2_9_lattice3 @ X1 @ X0 ) @ X1 ) @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ( ( sk_C @ ( a_2_9_lattice3 @ X1 @ X0 ) @ X1 )
        = ( k16_lattice3 @ X1 @ X0 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('73',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v4_lattice3 @ X15 )
      | ( r4_lattice3 @ X15 @ ( sk_C @ X16 @ X15 ) @ X16 )
      | ~ ( l3_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('74',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v4_lattice3 @ X15 )
      | ( m1_subset_1 @ ( sk_C @ X16 @ X15 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( l3_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('75',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( r4_lattice3 @ X10 @ X9 @ X11 )
      | ~ ( r2_hidden @ X12 @ X11 )
      | ( r1_lattices @ X10 @ X12 @ X9 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ X2 @ ( sk_C @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X3 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ( r1_lattices @ X0 @ X2 @ ( sk_C @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r1_lattices @ X1 @ X2 @ ( sk_C @ X0 @ X1 ) )
      | ~ ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r1_lattices @ X1 @ X2 @ ( sk_C @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 )
        = ( k16_lattice3 @ X0 @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r1_lattices @ X0 @ ( sk_D_4 @ X1 @ ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 ) @ X0 ) @ ( sk_C @ X2 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D_4 @ X1 @ ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 ) @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['72','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_D_4 @ X1 @ ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 ) @ X0 ) @ X2 )
      | ( r1_lattices @ X0 @ ( sk_D_4 @ X1 @ ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 ) @ X0 ) @ ( sk_C @ X2 @ X0 ) )
      | ( ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 )
        = ( k16_lattice3 @ X0 @ X1 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( ( sk_C @ ( a_2_9_lattice3 @ X1 @ X0 ) @ X1 )
        = ( k16_lattice3 @ X1 @ X0 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( ( sk_C @ ( a_2_9_lattice3 @ X1 @ X0 ) @ X1 )
        = ( k16_lattice3 @ X1 @ X0 ) )
      | ( r1_lattices @ X1 @ ( sk_D_4 @ X0 @ ( sk_C @ ( a_2_9_lattice3 @ X1 @ X0 ) @ X1 ) @ X1 ) @ ( sk_C @ ( a_2_9_lattice3 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['71','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattices @ X1 @ ( sk_D_4 @ X0 @ ( sk_C @ ( a_2_9_lattice3 @ X1 @ X0 ) @ X1 ) @ X1 ) @ ( sk_C @ ( a_2_9_lattice3 @ X1 @ X0 ) @ X1 ) )
      | ( ( sk_C @ ( a_2_9_lattice3 @ X1 @ X0 ) @ X1 )
        = ( k16_lattice3 @ X1 @ X0 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_D_4 @ X0 @ ( sk_C @ ( a_2_9_lattice3 @ X1 @ X0 ) @ X1 ) @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ( ( sk_C @ ( a_2_9_lattice3 @ X1 @ X0 ) @ X1 )
        = ( k16_lattice3 @ X1 @ X0 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['64'])).

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

thf('85',plain,(
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

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 )
        = ( k16_lattice3 @ X0 @ X1 ) )
      | ~ ( r1_lattices @ X0 @ ( sk_D_4 @ X1 @ ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 ) @ X0 ) @ X2 )
      | ( r3_lattices @ X0 @ ( sk_D_4 @ X1 @ ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 ) @ X0 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r3_lattices @ X0 @ ( sk_D_4 @ X1 @ ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 ) @ X0 ) @ X2 )
      | ~ ( r1_lattices @ X0 @ ( sk_D_4 @ X1 @ ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 ) @ X0 ) @ X2 )
      | ( ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 )
        = ( k16_lattice3 @ X0 @ X1 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 )
        = ( k16_lattice3 @ X0 @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 )
        = ( k16_lattice3 @ X0 @ X1 ) )
      | ( r3_lattices @ X0 @ ( sk_D_4 @ X1 @ ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 ) @ X0 ) @ ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ~ ( m1_subset_1 @ ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r3_lattices @ X0 @ ( sk_D_4 @ X1 @ ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 ) @ X0 ) @ ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ( ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 )
        = ( k16_lattice3 @ X0 @ X1 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 )
        = ( k16_lattice3 @ X0 @ X1 ) )
      | ( r3_lattices @ X0 @ ( sk_D_4 @ X1 @ ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 ) @ X0 ) @ ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ( r3_lattices @ X0 @ ( sk_D_4 @ X1 @ ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 ) @ X0 ) @ ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ( ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 )
        = ( k16_lattice3 @ X0 @ X1 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v4_lattice3 @ X15 )
      | ( m1_subset_1 @ ( sk_C @ X16 @ X15 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( l3_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('93',plain,(
    ! [X22: $i,X23: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ~ ( r3_lattice3 @ X23 @ X22 @ X26 )
      | ~ ( r3_lattices @ X23 @ ( sk_D_4 @ X26 @ X22 @ X23 ) @ X22 )
      | ( X22
        = ( k16_lattice3 @ X23 @ X26 ) )
      | ~ ( l3_lattices @ X23 )
      | ~ ( v4_lattice3 @ X23 )
      | ~ ( v10_lattices @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( ( sk_C @ X1 @ X0 )
        = ( k16_lattice3 @ X0 @ X2 ) )
      | ~ ( r3_lattices @ X0 @ ( sk_D_4 @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ ( sk_C @ X1 @ X0 ) )
      | ~ ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r3_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( r3_lattices @ X0 @ ( sk_D_4 @ X2 @ ( sk_C @ X1 @ X0 ) @ X0 ) @ ( sk_C @ X1 @ X0 ) )
      | ( ( sk_C @ X1 @ X0 )
        = ( k16_lattice3 @ X0 @ X2 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 )
        = ( k16_lattice3 @ X0 @ X1 ) )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 )
        = ( k16_lattice3 @ X0 @ X1 ) )
      | ~ ( r3_lattice3 @ X0 @ ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['91','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r3_lattice3 @ X0 @ ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 ) @ X1 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ( ( sk_C @ ( a_2_9_lattice3 @ X0 @ X1 ) @ X0 )
        = ( k16_lattice3 @ X0 @ X1 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( ( sk_C @ ( a_2_9_lattice3 @ X1 @ X0 ) @ X1 )
        = ( k16_lattice3 @ X1 @ X0 ) )
      | ~ ( v6_lattices @ X1 )
      | ~ ( v8_lattices @ X1 )
      | ~ ( v9_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['50','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v9_lattices @ X1 )
      | ~ ( v8_lattices @ X1 )
      | ~ ( v6_lattices @ X1 )
      | ( ( sk_C @ ( a_2_9_lattice3 @ X1 @ X0 ) @ X1 )
        = ( k16_lattice3 @ X1 @ X0 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v4_lattice3 @ X15 )
      | ( m1_subset_1 @ ( sk_C @ X16 @ X15 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( l3_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('101',plain,(
    r3_lattice3 @ sk_A @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ~ ( r3_lattice3 @ X18 @ X21 @ X19 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X18 ) )
      | ( r2_hidden @ X21 @ ( a_2_9_lattice3 @ X18 @ X19 ) )
      | ( v2_struct_0 @ X18 )
      | ~ ( v10_lattices @ X18 )
      | ~ ( v4_lattice3 @ X18 )
      | ~ ( l3_lattices @ X18 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_B_1 @ ( a_2_9_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattice3 @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_B_1 @ ( a_2_9_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattice3 @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['104','105','106','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattice3 @ sk_A @ sk_B_1 @ X0 )
      | ( r2_hidden @ sk_B_1 @ ( a_2_9_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    r2_hidden @ sk_B_1 @ ( a_2_9_lattice3 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['101','110'])).

thf('112',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r1_lattices @ X1 @ X2 @ ( sk_C @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ( r1_lattices @ sk_A @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) )
      | ~ ( r2_hidden @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_lattices @ sk_A @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) )
      | ~ ( r2_hidden @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B_1 @ X0 )
      | ( r1_lattices @ sk_A @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,(
    r1_lattices @ sk_A @ sk_B_1 @ ( sk_C @ ( a_2_9_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['111','119'])).

thf('121',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
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

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ sk_B_1 @ X0 )
      | ( r3_lattices @ sk_A @ sk_B_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

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

thf('124',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('125',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['126','127','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('131',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['132','133','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('137',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['138','139','140'])).

thf('142',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ sk_B_1 @ X0 )
      | ( r3_lattices @ sk_A @ sk_B_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['123','129','135','141','142'])).

thf('144',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_C @ ( a_2_9_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r3_lattices @ sk_A @ sk_B_1 @ ( sk_C @ ( a_2_9_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['120','143'])).

thf('145',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( r3_lattices @ sk_A @ sk_B_1 @ ( sk_C @ ( a_2_9_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_C @ ( a_2_9_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['144','145'])).

thf('147',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ( r3_lattices @ sk_A @ sk_B_1 @ ( sk_C @ ( a_2_9_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['100','146'])).

thf('148',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_lattices @ sk_A @ sk_B_1 @ ( sk_C @ ( a_2_9_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['147','148','149'])).

thf('151',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    r3_lattices @ sk_A @ sk_B_1 @ ( sk_C @ ( a_2_9_lattice3 @ sk_A @ sk_C_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['150','151'])).

thf('153',plain,
    ( ( r3_lattices @ sk_A @ sk_B_1 @ ( k16_lattice3 @ sk_A @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v6_lattices @ sk_A )
    | ~ ( v8_lattices @ sk_A )
    | ~ ( v9_lattices @ sk_A ) ),
    inference('sup+',[status(thm)],['99','152'])).

thf('154',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['126','127','128'])).

thf('158',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['132','133','134'])).

thf('159',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['138','139','140'])).

thf('160',plain,
    ( ( r3_lattices @ sk_A @ sk_B_1 @ ( k16_lattice3 @ sk_A @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['153','154','155','156','157','158','159'])).

thf('161',plain,(
    ~ ( r3_lattices @ sk_A @ sk_B_1 @ ( k16_lattice3 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['160','161'])).

thf('163',plain,(
    $false ),
    inference(demod,[status(thm)],['0','162'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yhdmFTV2pt
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:46:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 49.60/49.85  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 49.60/49.85  % Solved by: fo/fo7.sh
% 49.60/49.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 49.60/49.85  % done 16720 iterations in 49.398s
% 49.60/49.85  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 49.60/49.85  % SZS output start Refutation
% 49.60/49.85  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 49.60/49.85  thf(sk_A_type, type, sk_A: $i).
% 49.60/49.85  thf(sk_B_1_type, type, sk_B_1: $i).
% 49.60/49.85  thf(a_2_9_lattice3_type, type, a_2_9_lattice3: $i > $i > $i).
% 49.60/49.85  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 49.60/49.85  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 49.60/49.85  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 49.60/49.85  thf(sk_C_1_type, type, sk_C_1: $i).
% 49.60/49.85  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 49.60/49.85  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 49.60/49.85  thf(r3_lattice3_type, type, r3_lattice3: $i > $i > $i > $o).
% 49.60/49.85  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 49.60/49.85  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 49.60/49.85  thf(r4_lattice3_type, type, r4_lattice3: $i > $i > $i > $o).
% 49.60/49.85  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 49.60/49.85  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 49.60/49.85  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 49.60/49.85  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 49.60/49.85  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 49.60/49.85  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 49.60/49.85  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 49.60/49.85  thf(sk_D_4_type, type, sk_D_4: $i > $i > $i > $i).
% 49.60/49.85  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 49.60/49.85  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 49.60/49.85  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i > $i).
% 49.60/49.85  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 49.60/49.85  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 49.60/49.85  thf(t40_lattice3, conjecture,
% 49.60/49.85    (![A:$i]:
% 49.60/49.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 49.60/49.85         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 49.60/49.85       ( ![B:$i]:
% 49.60/49.85         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 49.60/49.85           ( ![C:$i]:
% 49.60/49.85             ( ( r3_lattice3 @ A @ B @ C ) =>
% 49.60/49.85               ( r3_lattices @ A @ B @ ( k16_lattice3 @ A @ C ) ) ) ) ) ) ))).
% 49.60/49.85  thf(zf_stmt_0, negated_conjecture,
% 49.60/49.85    (~( ![A:$i]:
% 49.60/49.85        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 49.60/49.85            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 49.60/49.85          ( ![B:$i]:
% 49.60/49.85            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 49.60/49.85              ( ![C:$i]:
% 49.60/49.85                ( ( r3_lattice3 @ A @ B @ C ) =>
% 49.60/49.85                  ( r3_lattices @ A @ B @ ( k16_lattice3 @ A @ C ) ) ) ) ) ) ) )),
% 49.60/49.85    inference('cnf.neg', [status(esa)], [t40_lattice3])).
% 49.60/49.85  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 49.60/49.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.60/49.85  thf(d18_lattice3, axiom,
% 49.60/49.85    (![A:$i]:
% 49.60/49.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 49.60/49.85       ( ( v4_lattice3 @ A ) <=>
% 49.60/49.85         ( ![B:$i]:
% 49.60/49.85           ( ?[C:$i]:
% 49.60/49.85             ( ( ![D:$i]:
% 49.60/49.85                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 49.60/49.85                   ( ( r4_lattice3 @ A @ D @ B ) => ( r1_lattices @ A @ C @ D ) ) ) ) & 
% 49.60/49.85               ( r4_lattice3 @ A @ C @ B ) & 
% 49.60/49.85               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 49.60/49.85  thf('1', plain,
% 49.60/49.85      (![X15 : $i, X16 : $i]:
% 49.60/49.85         (~ (v4_lattice3 @ X15)
% 49.60/49.85          | (m1_subset_1 @ (sk_C @ X16 @ X15) @ (u1_struct_0 @ X15))
% 49.60/49.85          | ~ (l3_lattices @ X15)
% 49.60/49.85          | (v2_struct_0 @ X15))),
% 49.60/49.85      inference('cnf', [status(esa)], [d18_lattice3])).
% 49.60/49.85  thf(d16_lattice3, axiom,
% 49.60/49.85    (![A:$i]:
% 49.60/49.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 49.60/49.85       ( ![B:$i]:
% 49.60/49.85         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 49.60/49.85           ( ![C:$i]:
% 49.60/49.85             ( ( r3_lattice3 @ A @ B @ C ) <=>
% 49.60/49.85               ( ![D:$i]:
% 49.60/49.85                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 49.60/49.85                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 49.60/49.85  thf('2', plain,
% 49.60/49.85      (![X4 : $i, X5 : $i, X8 : $i]:
% 49.60/49.85         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 49.60/49.85          | (r2_hidden @ (sk_D @ X8 @ X4 @ X5) @ X8)
% 49.60/49.85          | (r3_lattice3 @ X5 @ X4 @ X8)
% 49.60/49.85          | ~ (l3_lattices @ X5)
% 49.60/49.85          | (v2_struct_0 @ X5))),
% 49.60/49.85      inference('cnf', [status(esa)], [d16_lattice3])).
% 49.60/49.85  thf('3', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.60/49.85         ((v2_struct_0 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | (v2_struct_0 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 49.60/49.85          | (r2_hidden @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X2))),
% 49.60/49.85      inference('sup-', [status(thm)], ['1', '2'])).
% 49.60/49.85  thf('4', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.60/49.85         ((r2_hidden @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X2)
% 49.60/49.85          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | (v2_struct_0 @ X0))),
% 49.60/49.85      inference('simplify', [status(thm)], ['3'])).
% 49.60/49.85  thf('5', plain,
% 49.60/49.85      (![X15 : $i, X16 : $i]:
% 49.60/49.85         (~ (v4_lattice3 @ X15)
% 49.60/49.85          | (m1_subset_1 @ (sk_C @ X16 @ X15) @ (u1_struct_0 @ X15))
% 49.60/49.85          | ~ (l3_lattices @ X15)
% 49.60/49.85          | (v2_struct_0 @ X15))),
% 49.60/49.85      inference('cnf', [status(esa)], [d18_lattice3])).
% 49.60/49.85  thf('6', plain,
% 49.60/49.85      (![X4 : $i, X5 : $i, X8 : $i]:
% 49.60/49.85         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 49.60/49.85          | (m1_subset_1 @ (sk_D @ X8 @ X4 @ X5) @ (u1_struct_0 @ X5))
% 49.60/49.85          | (r3_lattice3 @ X5 @ X4 @ X8)
% 49.60/49.85          | ~ (l3_lattices @ X5)
% 49.60/49.85          | (v2_struct_0 @ X5))),
% 49.60/49.85      inference('cnf', [status(esa)], [d16_lattice3])).
% 49.60/49.85  thf('7', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.60/49.85         ((v2_struct_0 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | (v2_struct_0 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 49.60/49.85          | (m1_subset_1 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ 
% 49.60/49.85             (u1_struct_0 @ X0)))),
% 49.60/49.85      inference('sup-', [status(thm)], ['5', '6'])).
% 49.60/49.85  thf('8', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.60/49.85         ((m1_subset_1 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ 
% 49.60/49.85           (u1_struct_0 @ X0))
% 49.60/49.85          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | (v2_struct_0 @ X0))),
% 49.60/49.85      inference('simplify', [status(thm)], ['7'])).
% 49.60/49.85  thf('9', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.60/49.85         ((m1_subset_1 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ 
% 49.60/49.85           (u1_struct_0 @ X0))
% 49.60/49.85          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | (v2_struct_0 @ X0))),
% 49.60/49.85      inference('simplify', [status(thm)], ['7'])).
% 49.60/49.85  thf(d17_lattice3, axiom,
% 49.60/49.85    (![A:$i]:
% 49.60/49.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 49.60/49.85       ( ![B:$i]:
% 49.60/49.85         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 49.60/49.85           ( ![C:$i]:
% 49.60/49.85             ( ( r4_lattice3 @ A @ B @ C ) <=>
% 49.60/49.85               ( ![D:$i]:
% 49.60/49.85                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 49.60/49.85                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ))).
% 49.60/49.85  thf('10', plain,
% 49.60/49.85      (![X9 : $i, X10 : $i, X13 : $i]:
% 49.60/49.85         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 49.60/49.85          | (r2_hidden @ (sk_D_1 @ X13 @ X9 @ X10) @ X13)
% 49.60/49.85          | (r4_lattice3 @ X10 @ X9 @ X13)
% 49.60/49.85          | ~ (l3_lattices @ X10)
% 49.60/49.85          | (v2_struct_0 @ X10))),
% 49.60/49.85      inference('cnf', [status(esa)], [d17_lattice3])).
% 49.60/49.85  thf('11', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 49.60/49.85         ((v2_struct_0 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 49.60/49.85          | (v2_struct_0 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | (r4_lattice3 @ X0 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X3)
% 49.60/49.85          | (r2_hidden @ 
% 49.60/49.85             (sk_D_1 @ X3 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X0) @ X3))),
% 49.60/49.85      inference('sup-', [status(thm)], ['9', '10'])).
% 49.60/49.85  thf('12', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 49.60/49.85         ((r2_hidden @ 
% 49.60/49.85           (sk_D_1 @ X3 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X0) @ X3)
% 49.60/49.85          | (r4_lattice3 @ X0 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X3)
% 49.60/49.85          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | (v2_struct_0 @ X0))),
% 49.60/49.85      inference('simplify', [status(thm)], ['11'])).
% 49.60/49.85  thf(fraenkel_a_2_9_lattice3, axiom,
% 49.60/49.85    (![A:$i,B:$i,C:$i]:
% 49.60/49.85     ( ( ( ~( v2_struct_0 @ B ) ) & ( v10_lattices @ B ) & 
% 49.60/49.85         ( v4_lattice3 @ B ) & ( l3_lattices @ B ) ) =>
% 49.60/49.85       ( ( r2_hidden @ A @ ( a_2_9_lattice3 @ B @ C ) ) <=>
% 49.60/49.85         ( ?[D:$i]:
% 49.60/49.85           ( ( r3_lattice3 @ B @ D @ C ) & ( ( A ) = ( D ) ) & 
% 49.60/49.85             ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 49.60/49.85  thf('13', plain,
% 49.60/49.85      (![X18 : $i, X19 : $i, X20 : $i]:
% 49.60/49.85         (~ (l3_lattices @ X18)
% 49.60/49.85          | ~ (v4_lattice3 @ X18)
% 49.60/49.85          | ~ (v10_lattices @ X18)
% 49.60/49.85          | (v2_struct_0 @ X18)
% 49.60/49.85          | ((X20) = (sk_D_3 @ X19 @ X18 @ X20))
% 49.60/49.85          | ~ (r2_hidden @ X20 @ (a_2_9_lattice3 @ X18 @ X19)))),
% 49.60/49.85      inference('cnf', [status(esa)], [fraenkel_a_2_9_lattice3])).
% 49.60/49.85  thf('14', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 49.60/49.85         ((v2_struct_0 @ X2)
% 49.60/49.85          | ~ (l3_lattices @ X2)
% 49.60/49.85          | ~ (v4_lattice3 @ X2)
% 49.60/49.85          | (r3_lattice3 @ X2 @ (sk_C @ X3 @ X2) @ X4)
% 49.60/49.85          | (r4_lattice3 @ X2 @ (sk_D @ X4 @ (sk_C @ X3 @ X2) @ X2) @ 
% 49.60/49.85             (a_2_9_lattice3 @ X1 @ X0))
% 49.60/49.85          | ((sk_D_1 @ (a_2_9_lattice3 @ X1 @ X0) @ 
% 49.60/49.85              (sk_D @ X4 @ (sk_C @ X3 @ X2) @ X2) @ X2)
% 49.60/49.85              = (sk_D_3 @ X0 @ X1 @ 
% 49.60/49.85                 (sk_D_1 @ (a_2_9_lattice3 @ X1 @ X0) @ 
% 49.60/49.85                  (sk_D @ X4 @ (sk_C @ X3 @ X2) @ X2) @ X2)))
% 49.60/49.85          | (v2_struct_0 @ X1)
% 49.60/49.85          | ~ (v10_lattices @ X1)
% 49.60/49.85          | ~ (v4_lattice3 @ X1)
% 49.60/49.85          | ~ (l3_lattices @ X1))),
% 49.60/49.85      inference('sup-', [status(thm)], ['12', '13'])).
% 49.60/49.85  thf('15', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 49.60/49.85         ((r2_hidden @ 
% 49.60/49.85           (sk_D_1 @ X3 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X0) @ X3)
% 49.60/49.85          | (r4_lattice3 @ X0 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X3)
% 49.60/49.85          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | (v2_struct_0 @ X0))),
% 49.60/49.85      inference('simplify', [status(thm)], ['11'])).
% 49.60/49.85  thf('16', plain,
% 49.60/49.85      (![X18 : $i, X19 : $i, X20 : $i]:
% 49.60/49.85         (~ (l3_lattices @ X18)
% 49.60/49.85          | ~ (v4_lattice3 @ X18)
% 49.60/49.85          | ~ (v10_lattices @ X18)
% 49.60/49.85          | (v2_struct_0 @ X18)
% 49.60/49.85          | (r3_lattice3 @ X18 @ (sk_D_3 @ X19 @ X18 @ X20) @ X19)
% 49.60/49.85          | ~ (r2_hidden @ X20 @ (a_2_9_lattice3 @ X18 @ X19)))),
% 49.60/49.85      inference('cnf', [status(esa)], [fraenkel_a_2_9_lattice3])).
% 49.60/49.85  thf('17', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 49.60/49.85         ((v2_struct_0 @ X2)
% 49.60/49.85          | ~ (l3_lattices @ X2)
% 49.60/49.85          | ~ (v4_lattice3 @ X2)
% 49.60/49.85          | (r3_lattice3 @ X2 @ (sk_C @ X3 @ X2) @ X4)
% 49.60/49.85          | (r4_lattice3 @ X2 @ (sk_D @ X4 @ (sk_C @ X3 @ X2) @ X2) @ 
% 49.60/49.85             (a_2_9_lattice3 @ X1 @ X0))
% 49.60/49.85          | (r3_lattice3 @ X1 @ 
% 49.60/49.85             (sk_D_3 @ X0 @ X1 @ 
% 49.60/49.85              (sk_D_1 @ (a_2_9_lattice3 @ X1 @ X0) @ 
% 49.60/49.85               (sk_D @ X4 @ (sk_C @ X3 @ X2) @ X2) @ X2)) @ 
% 49.60/49.85             X0)
% 49.60/49.85          | (v2_struct_0 @ X1)
% 49.60/49.85          | ~ (v10_lattices @ X1)
% 49.60/49.85          | ~ (v4_lattice3 @ X1)
% 49.60/49.85          | ~ (l3_lattices @ X1))),
% 49.60/49.85      inference('sup-', [status(thm)], ['15', '16'])).
% 49.60/49.85  thf('18', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 49.60/49.85         ((r3_lattice3 @ X4 @ 
% 49.60/49.85           (sk_D_1 @ (a_2_9_lattice3 @ X4 @ X3) @ 
% 49.60/49.85            (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X0) @ 
% 49.60/49.85           X3)
% 49.60/49.85          | ~ (l3_lattices @ X4)
% 49.60/49.85          | ~ (v4_lattice3 @ X4)
% 49.60/49.85          | ~ (v10_lattices @ X4)
% 49.60/49.85          | (v2_struct_0 @ X4)
% 49.60/49.85          | (r4_lattice3 @ X0 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ 
% 49.60/49.85             (a_2_9_lattice3 @ X4 @ X3))
% 49.60/49.85          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | (v2_struct_0 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X4)
% 49.60/49.85          | ~ (v4_lattice3 @ X4)
% 49.60/49.85          | ~ (v10_lattices @ X4)
% 49.60/49.85          | (v2_struct_0 @ X4)
% 49.60/49.85          | (r4_lattice3 @ X0 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ 
% 49.60/49.85             (a_2_9_lattice3 @ X4 @ X3))
% 49.60/49.85          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | (v2_struct_0 @ X0))),
% 49.60/49.85      inference('sup+', [status(thm)], ['14', '17'])).
% 49.60/49.85  thf('19', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 49.60/49.85         ((v2_struct_0 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 49.60/49.85          | (r4_lattice3 @ X0 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ 
% 49.60/49.85             (a_2_9_lattice3 @ X4 @ X3))
% 49.60/49.85          | (v2_struct_0 @ X4)
% 49.60/49.85          | ~ (v10_lattices @ X4)
% 49.60/49.85          | ~ (v4_lattice3 @ X4)
% 49.60/49.85          | ~ (l3_lattices @ X4)
% 49.60/49.85          | (r3_lattice3 @ X4 @ 
% 49.60/49.85             (sk_D_1 @ (a_2_9_lattice3 @ X4 @ X3) @ 
% 49.60/49.85              (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X0) @ 
% 49.60/49.85             X3))),
% 49.60/49.85      inference('simplify', [status(thm)], ['18'])).
% 49.60/49.85  thf('20', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.60/49.85         ((m1_subset_1 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ 
% 49.60/49.85           (u1_struct_0 @ X0))
% 49.60/49.85          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | (v2_struct_0 @ X0))),
% 49.60/49.85      inference('simplify', [status(thm)], ['7'])).
% 49.60/49.85  thf('21', plain,
% 49.60/49.85      (![X9 : $i, X10 : $i, X13 : $i]:
% 49.60/49.85         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 49.60/49.85          | (m1_subset_1 @ (sk_D_1 @ X13 @ X9 @ X10) @ (u1_struct_0 @ X10))
% 49.60/49.85          | (r4_lattice3 @ X10 @ X9 @ X13)
% 49.60/49.85          | ~ (l3_lattices @ X10)
% 49.60/49.85          | (v2_struct_0 @ X10))),
% 49.60/49.85      inference('cnf', [status(esa)], [d17_lattice3])).
% 49.60/49.85  thf('22', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 49.60/49.85         ((v2_struct_0 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 49.60/49.85          | (v2_struct_0 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | (r4_lattice3 @ X0 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X3)
% 49.60/49.85          | (m1_subset_1 @ 
% 49.60/49.85             (sk_D_1 @ X3 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X0) @ 
% 49.60/49.85             (u1_struct_0 @ X0)))),
% 49.60/49.85      inference('sup-', [status(thm)], ['20', '21'])).
% 49.60/49.85  thf('23', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 49.60/49.85         ((m1_subset_1 @ 
% 49.60/49.85           (sk_D_1 @ X3 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X0) @ 
% 49.60/49.85           (u1_struct_0 @ X0))
% 49.60/49.85          | (r4_lattice3 @ X0 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X3)
% 49.60/49.85          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | (v2_struct_0 @ X0))),
% 49.60/49.85      inference('simplify', [status(thm)], ['22'])).
% 49.60/49.85  thf('24', plain,
% 49.60/49.85      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 49.60/49.85         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 49.60/49.85          | ~ (r3_lattice3 @ X5 @ X4 @ X6)
% 49.60/49.85          | ~ (r2_hidden @ X7 @ X6)
% 49.60/49.85          | (r1_lattices @ X5 @ X4 @ X7)
% 49.60/49.85          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X5))
% 49.60/49.85          | ~ (l3_lattices @ X5)
% 49.60/49.85          | (v2_struct_0 @ X5))),
% 49.60/49.85      inference('cnf', [status(esa)], [d16_lattice3])).
% 49.60/49.85  thf('25', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 49.60/49.85         ((v2_struct_0 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 49.60/49.85          | (r4_lattice3 @ X0 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X3)
% 49.60/49.85          | (v2_struct_0 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X0))
% 49.60/49.85          | (r1_lattices @ X0 @ 
% 49.60/49.85             (sk_D_1 @ X3 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X0) @ X4)
% 49.60/49.85          | ~ (r2_hidden @ X4 @ X5)
% 49.60/49.85          | ~ (r3_lattice3 @ X0 @ 
% 49.60/49.85               (sk_D_1 @ X3 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X0) @ X5))),
% 49.60/49.85      inference('sup-', [status(thm)], ['23', '24'])).
% 49.60/49.85  thf('26', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 49.60/49.85         (~ (r3_lattice3 @ X0 @ 
% 49.60/49.85             (sk_D_1 @ X3 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X0) @ X5)
% 49.60/49.85          | ~ (r2_hidden @ X4 @ X5)
% 49.60/49.85          | (r1_lattices @ X0 @ 
% 49.60/49.85             (sk_D_1 @ X3 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X0) @ X4)
% 49.60/49.85          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X0))
% 49.60/49.85          | (r4_lattice3 @ X0 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X3)
% 49.60/49.85          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | (v2_struct_0 @ X0))),
% 49.60/49.85      inference('simplify', [status(thm)], ['25'])).
% 49.60/49.85  thf('27', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 49.60/49.85         (~ (l3_lattices @ X1)
% 49.60/49.85          | ~ (v4_lattice3 @ X1)
% 49.60/49.85          | ~ (v10_lattices @ X1)
% 49.60/49.85          | (v2_struct_0 @ X1)
% 49.60/49.85          | (r4_lattice3 @ X1 @ (sk_D @ X3 @ (sk_C @ X2 @ X1) @ X1) @ 
% 49.60/49.85             (a_2_9_lattice3 @ X1 @ X0))
% 49.60/49.85          | (r3_lattice3 @ X1 @ (sk_C @ X2 @ X1) @ X3)
% 49.60/49.85          | ~ (v4_lattice3 @ X1)
% 49.60/49.85          | ~ (l3_lattices @ X1)
% 49.60/49.85          | (v2_struct_0 @ X1)
% 49.60/49.85          | (v2_struct_0 @ X1)
% 49.60/49.85          | ~ (l3_lattices @ X1)
% 49.60/49.85          | ~ (v4_lattice3 @ X1)
% 49.60/49.85          | (r3_lattice3 @ X1 @ (sk_C @ X2 @ X1) @ X3)
% 49.60/49.85          | (r4_lattice3 @ X1 @ (sk_D @ X3 @ (sk_C @ X2 @ X1) @ X1) @ 
% 49.60/49.85             (a_2_9_lattice3 @ X1 @ X0))
% 49.60/49.85          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X1))
% 49.60/49.85          | (r1_lattices @ X1 @ 
% 49.60/49.85             (sk_D_1 @ (a_2_9_lattice3 @ X1 @ X0) @ 
% 49.60/49.85              (sk_D @ X3 @ (sk_C @ X2 @ X1) @ X1) @ X1) @ 
% 49.60/49.85             X4)
% 49.60/49.85          | ~ (r2_hidden @ X4 @ X0))),
% 49.60/49.85      inference('sup-', [status(thm)], ['19', '26'])).
% 49.60/49.85  thf('28', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 49.60/49.85         (~ (r2_hidden @ X4 @ X0)
% 49.60/49.85          | (r1_lattices @ X1 @ 
% 49.60/49.85             (sk_D_1 @ (a_2_9_lattice3 @ X1 @ X0) @ 
% 49.60/49.85              (sk_D @ X3 @ (sk_C @ X2 @ X1) @ X1) @ X1) @ 
% 49.60/49.85             X4)
% 49.60/49.85          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X1))
% 49.60/49.85          | (r3_lattice3 @ X1 @ (sk_C @ X2 @ X1) @ X3)
% 49.60/49.85          | (r4_lattice3 @ X1 @ (sk_D @ X3 @ (sk_C @ X2 @ X1) @ X1) @ 
% 49.60/49.85             (a_2_9_lattice3 @ X1 @ X0))
% 49.60/49.85          | (v2_struct_0 @ X1)
% 49.60/49.85          | ~ (v10_lattices @ X1)
% 49.60/49.85          | ~ (v4_lattice3 @ X1)
% 49.60/49.85          | ~ (l3_lattices @ X1))),
% 49.60/49.85      inference('simplify', [status(thm)], ['27'])).
% 49.60/49.85  thf('29', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 49.60/49.85         ((v2_struct_0 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (v10_lattices @ X0)
% 49.60/49.85          | (v2_struct_0 @ X0)
% 49.60/49.85          | (r4_lattice3 @ X0 @ (sk_D @ X5 @ (sk_C @ X4 @ X0) @ X0) @ 
% 49.60/49.85             (a_2_9_lattice3 @ X0 @ X3))
% 49.60/49.85          | (r3_lattice3 @ X0 @ (sk_C @ X4 @ X0) @ X5)
% 49.60/49.85          | (r1_lattices @ X0 @ 
% 49.60/49.85             (sk_D_1 @ (a_2_9_lattice3 @ X0 @ X3) @ 
% 49.60/49.85              (sk_D @ X5 @ (sk_C @ X4 @ X0) @ X0) @ X0) @ 
% 49.60/49.85             (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0))
% 49.60/49.85          | ~ (r2_hidden @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X3))),
% 49.60/49.85      inference('sup-', [status(thm)], ['8', '28'])).
% 49.60/49.85  thf('30', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 49.60/49.85         (~ (r2_hidden @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X3)
% 49.60/49.85          | (r1_lattices @ X0 @ 
% 49.60/49.85             (sk_D_1 @ (a_2_9_lattice3 @ X0 @ X3) @ 
% 49.60/49.85              (sk_D @ X5 @ (sk_C @ X4 @ X0) @ X0) @ X0) @ 
% 49.60/49.85             (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0))
% 49.60/49.85          | (r3_lattice3 @ X0 @ (sk_C @ X4 @ X0) @ X5)
% 49.60/49.85          | (r4_lattice3 @ X0 @ (sk_D @ X5 @ (sk_C @ X4 @ X0) @ X0) @ 
% 49.60/49.85             (a_2_9_lattice3 @ X0 @ X3))
% 49.60/49.85          | ~ (v10_lattices @ X0)
% 49.60/49.85          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | (v2_struct_0 @ X0))),
% 49.60/49.85      inference('simplify', [status(thm)], ['29'])).
% 49.60/49.85  thf('31', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 49.60/49.85         ((v2_struct_0 @ X1)
% 49.60/49.85          | ~ (l3_lattices @ X1)
% 49.60/49.85          | ~ (v4_lattice3 @ X1)
% 49.60/49.85          | (r3_lattice3 @ X1 @ (sk_C @ X2 @ X1) @ X0)
% 49.60/49.85          | (v2_struct_0 @ X1)
% 49.60/49.85          | ~ (l3_lattices @ X1)
% 49.60/49.85          | ~ (v4_lattice3 @ X1)
% 49.60/49.85          | (r3_lattice3 @ X1 @ (sk_C @ X2 @ X1) @ X0)
% 49.60/49.85          | ~ (v10_lattices @ X1)
% 49.60/49.85          | (r4_lattice3 @ X1 @ (sk_D @ X4 @ (sk_C @ X3 @ X1) @ X1) @ 
% 49.60/49.85             (a_2_9_lattice3 @ X1 @ X0))
% 49.60/49.85          | (r3_lattice3 @ X1 @ (sk_C @ X3 @ X1) @ X4)
% 49.60/49.85          | (r1_lattices @ X1 @ 
% 49.60/49.85             (sk_D_1 @ (a_2_9_lattice3 @ X1 @ X0) @ 
% 49.60/49.85              (sk_D @ X4 @ (sk_C @ X3 @ X1) @ X1) @ X1) @ 
% 49.60/49.85             (sk_D @ X0 @ (sk_C @ X2 @ X1) @ X1)))),
% 49.60/49.85      inference('sup-', [status(thm)], ['4', '30'])).
% 49.60/49.85  thf('32', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 49.60/49.85         ((r1_lattices @ X1 @ 
% 49.60/49.85           (sk_D_1 @ (a_2_9_lattice3 @ X1 @ X0) @ 
% 49.60/49.85            (sk_D @ X4 @ (sk_C @ X3 @ X1) @ X1) @ X1) @ 
% 49.60/49.85           (sk_D @ X0 @ (sk_C @ X2 @ X1) @ X1))
% 49.60/49.85          | (r3_lattice3 @ X1 @ (sk_C @ X3 @ X1) @ X4)
% 49.60/49.85          | (r4_lattice3 @ X1 @ (sk_D @ X4 @ (sk_C @ X3 @ X1) @ X1) @ 
% 49.60/49.85             (a_2_9_lattice3 @ X1 @ X0))
% 49.60/49.85          | ~ (v10_lattices @ X1)
% 49.60/49.85          | (r3_lattice3 @ X1 @ (sk_C @ X2 @ X1) @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X1)
% 49.60/49.85          | ~ (l3_lattices @ X1)
% 49.60/49.85          | (v2_struct_0 @ X1))),
% 49.60/49.85      inference('simplify', [status(thm)], ['31'])).
% 49.60/49.85  thf('33', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.60/49.85         ((m1_subset_1 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ 
% 49.60/49.85           (u1_struct_0 @ X0))
% 49.60/49.85          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | (v2_struct_0 @ X0))),
% 49.60/49.85      inference('simplify', [status(thm)], ['7'])).
% 49.60/49.85  thf('34', plain,
% 49.60/49.85      (![X9 : $i, X10 : $i, X13 : $i]:
% 49.60/49.85         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 49.60/49.85          | ~ (r1_lattices @ X10 @ (sk_D_1 @ X13 @ X9 @ X10) @ X9)
% 49.60/49.85          | (r4_lattice3 @ X10 @ X9 @ X13)
% 49.60/49.85          | ~ (l3_lattices @ X10)
% 49.60/49.85          | (v2_struct_0 @ X10))),
% 49.60/49.85      inference('cnf', [status(esa)], [d17_lattice3])).
% 49.60/49.85  thf('35', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 49.60/49.85         ((v2_struct_0 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 49.60/49.85          | (v2_struct_0 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | (r4_lattice3 @ X0 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X3)
% 49.60/49.85          | ~ (r1_lattices @ X0 @ 
% 49.60/49.85               (sk_D_1 @ X3 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X0) @ 
% 49.60/49.85               (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0)))),
% 49.60/49.85      inference('sup-', [status(thm)], ['33', '34'])).
% 49.60/49.85  thf('36', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 49.60/49.85         (~ (r1_lattices @ X0 @ 
% 49.60/49.85             (sk_D_1 @ X3 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X0) @ 
% 49.60/49.85             (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0))
% 49.60/49.85          | (r4_lattice3 @ X0 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X3)
% 49.60/49.85          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | (v2_struct_0 @ X0))),
% 49.60/49.85      inference('simplify', [status(thm)], ['35'])).
% 49.60/49.85  thf('37', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.60/49.85         ((v2_struct_0 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 49.60/49.85          | ~ (v10_lattices @ X0)
% 49.60/49.85          | (r4_lattice3 @ X0 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ 
% 49.60/49.85             (a_2_9_lattice3 @ X0 @ X2))
% 49.60/49.85          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 49.60/49.85          | (v2_struct_0 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 49.60/49.85          | (r4_lattice3 @ X0 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ 
% 49.60/49.85             (a_2_9_lattice3 @ X0 @ X2)))),
% 49.60/49.85      inference('sup-', [status(thm)], ['32', '36'])).
% 49.60/49.85  thf('38', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.60/49.85         ((r4_lattice3 @ X0 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ 
% 49.60/49.85           (a_2_9_lattice3 @ X0 @ X2))
% 49.60/49.85          | ~ (v10_lattices @ X0)
% 49.60/49.85          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | (v2_struct_0 @ X0))),
% 49.60/49.85      inference('simplify', [status(thm)], ['37'])).
% 49.60/49.85  thf('39', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.60/49.85         ((m1_subset_1 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ 
% 49.60/49.85           (u1_struct_0 @ X0))
% 49.60/49.85          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | (v2_struct_0 @ X0))),
% 49.60/49.85      inference('simplify', [status(thm)], ['7'])).
% 49.60/49.85  thf('40', plain,
% 49.60/49.85      (![X15 : $i, X16 : $i, X17 : $i]:
% 49.60/49.85         (~ (v4_lattice3 @ X15)
% 49.60/49.85          | ~ (r4_lattice3 @ X15 @ X17 @ X16)
% 49.60/49.85          | (r1_lattices @ X15 @ (sk_C @ X16 @ X15) @ X17)
% 49.60/49.85          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X15))
% 49.60/49.85          | ~ (l3_lattices @ X15)
% 49.60/49.85          | (v2_struct_0 @ X15))),
% 49.60/49.85      inference('cnf', [status(esa)], [d18_lattice3])).
% 49.60/49.85  thf('41', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 49.60/49.85         ((v2_struct_0 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 49.60/49.85          | (v2_struct_0 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | (r1_lattices @ X0 @ (sk_C @ X3 @ X0) @ 
% 49.60/49.85             (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0))
% 49.60/49.85          | ~ (r4_lattice3 @ X0 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X3)
% 49.60/49.85          | ~ (v4_lattice3 @ X0))),
% 49.60/49.85      inference('sup-', [status(thm)], ['39', '40'])).
% 49.60/49.85  thf('42', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 49.60/49.85         (~ (r4_lattice3 @ X0 @ (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X3)
% 49.60/49.85          | (r1_lattices @ X0 @ (sk_C @ X3 @ X0) @ 
% 49.60/49.85             (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0))
% 49.60/49.85          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | (v2_struct_0 @ X0))),
% 49.60/49.85      inference('simplify', [status(thm)], ['41'])).
% 49.60/49.85  thf('43', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.60/49.85         ((v2_struct_0 @ X1)
% 49.60/49.85          | ~ (l3_lattices @ X1)
% 49.60/49.85          | ~ (v4_lattice3 @ X1)
% 49.60/49.85          | (r3_lattice3 @ X1 @ (sk_C @ X2 @ X1) @ X0)
% 49.60/49.85          | ~ (v10_lattices @ X1)
% 49.60/49.85          | (v2_struct_0 @ X1)
% 49.60/49.85          | ~ (l3_lattices @ X1)
% 49.60/49.85          | ~ (v4_lattice3 @ X1)
% 49.60/49.85          | (r3_lattice3 @ X1 @ (sk_C @ X2 @ X1) @ X0)
% 49.60/49.85          | (r1_lattices @ X1 @ (sk_C @ (a_2_9_lattice3 @ X1 @ X0) @ X1) @ 
% 49.60/49.85             (sk_D @ X0 @ (sk_C @ X2 @ X1) @ X1)))),
% 49.60/49.85      inference('sup-', [status(thm)], ['38', '42'])).
% 49.60/49.85  thf('44', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.60/49.85         ((r1_lattices @ X1 @ (sk_C @ (a_2_9_lattice3 @ X1 @ X0) @ X1) @ 
% 49.60/49.85           (sk_D @ X0 @ (sk_C @ X2 @ X1) @ X1))
% 49.60/49.85          | ~ (v10_lattices @ X1)
% 49.60/49.85          | (r3_lattice3 @ X1 @ (sk_C @ X2 @ X1) @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X1)
% 49.60/49.85          | ~ (l3_lattices @ X1)
% 49.60/49.85          | (v2_struct_0 @ X1))),
% 49.60/49.85      inference('simplify', [status(thm)], ['43'])).
% 49.60/49.85  thf('45', plain,
% 49.60/49.85      (![X15 : $i, X16 : $i]:
% 49.60/49.85         (~ (v4_lattice3 @ X15)
% 49.60/49.85          | (m1_subset_1 @ (sk_C @ X16 @ X15) @ (u1_struct_0 @ X15))
% 49.60/49.85          | ~ (l3_lattices @ X15)
% 49.60/49.85          | (v2_struct_0 @ X15))),
% 49.60/49.85      inference('cnf', [status(esa)], [d18_lattice3])).
% 49.60/49.85  thf('46', plain,
% 49.60/49.85      (![X4 : $i, X5 : $i, X8 : $i]:
% 49.60/49.85         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 49.60/49.85          | ~ (r1_lattices @ X5 @ X4 @ (sk_D @ X8 @ X4 @ X5))
% 49.60/49.85          | (r3_lattice3 @ X5 @ X4 @ X8)
% 49.60/49.85          | ~ (l3_lattices @ X5)
% 49.60/49.85          | (v2_struct_0 @ X5))),
% 49.60/49.85      inference('cnf', [status(esa)], [d16_lattice3])).
% 49.60/49.85  thf('47', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.60/49.85         ((v2_struct_0 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | (v2_struct_0 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 49.60/49.85          | ~ (r1_lattices @ X0 @ (sk_C @ X1 @ X0) @ 
% 49.60/49.85               (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0)))),
% 49.60/49.85      inference('sup-', [status(thm)], ['45', '46'])).
% 49.60/49.85  thf('48', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.60/49.85         (~ (r1_lattices @ X0 @ (sk_C @ X1 @ X0) @ 
% 49.60/49.85             (sk_D @ X2 @ (sk_C @ X1 @ X0) @ X0))
% 49.60/49.85          | (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | (v2_struct_0 @ X0))),
% 49.60/49.85      inference('simplify', [status(thm)], ['47'])).
% 49.60/49.85  thf('49', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i]:
% 49.60/49.85         ((v2_struct_0 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | (r3_lattice3 @ X0 @ (sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0) @ X1)
% 49.60/49.85          | ~ (v10_lattices @ X0)
% 49.60/49.85          | (v2_struct_0 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | (r3_lattice3 @ X0 @ (sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0) @ X1))),
% 49.60/49.85      inference('sup-', [status(thm)], ['44', '48'])).
% 49.60/49.85  thf('50', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i]:
% 49.60/49.85         (~ (v10_lattices @ X0)
% 49.60/49.85          | (r3_lattice3 @ X0 @ (sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0) @ X1)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | (v2_struct_0 @ X0))),
% 49.60/49.85      inference('simplify', [status(thm)], ['49'])).
% 49.60/49.85  thf('51', plain,
% 49.60/49.85      (![X15 : $i, X16 : $i]:
% 49.60/49.85         (~ (v4_lattice3 @ X15)
% 49.60/49.85          | (m1_subset_1 @ (sk_C @ X16 @ X15) @ (u1_struct_0 @ X15))
% 49.60/49.85          | ~ (l3_lattices @ X15)
% 49.60/49.85          | (v2_struct_0 @ X15))),
% 49.60/49.85      inference('cnf', [status(esa)], [d18_lattice3])).
% 49.60/49.85  thf('52', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i]:
% 49.60/49.85         (~ (v10_lattices @ X0)
% 49.60/49.85          | (r3_lattice3 @ X0 @ (sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0) @ X1)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | (v2_struct_0 @ X0))),
% 49.60/49.85      inference('simplify', [status(thm)], ['49'])).
% 49.60/49.85  thf('53', plain,
% 49.60/49.85      (![X15 : $i, X16 : $i]:
% 49.60/49.85         (~ (v4_lattice3 @ X15)
% 49.60/49.85          | (m1_subset_1 @ (sk_C @ X16 @ X15) @ (u1_struct_0 @ X15))
% 49.60/49.85          | ~ (l3_lattices @ X15)
% 49.60/49.85          | (v2_struct_0 @ X15))),
% 49.60/49.85      inference('cnf', [status(esa)], [d18_lattice3])).
% 49.60/49.85  thf(t34_lattice3, axiom,
% 49.60/49.85    (![A:$i]:
% 49.60/49.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 49.60/49.85         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 49.60/49.85       ( ![B:$i]:
% 49.60/49.85         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 49.60/49.85           ( ![C:$i]:
% 49.60/49.85             ( ( ( B ) = ( k16_lattice3 @ A @ C ) ) <=>
% 49.60/49.85               ( ( r3_lattice3 @ A @ B @ C ) & 
% 49.60/49.85                 ( ![D:$i]:
% 49.60/49.85                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 49.60/49.85                     ( ( r3_lattice3 @ A @ D @ C ) =>
% 49.60/49.85                       ( r3_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 49.60/49.85  thf('54', plain,
% 49.60/49.85      (![X22 : $i, X23 : $i, X26 : $i]:
% 49.60/49.85         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 49.60/49.85          | ~ (r3_lattice3 @ X23 @ X22 @ X26)
% 49.60/49.85          | (r3_lattice3 @ X23 @ (sk_D_4 @ X26 @ X22 @ X23) @ X26)
% 49.60/49.85          | ((X22) = (k16_lattice3 @ X23 @ X26))
% 49.60/49.85          | ~ (l3_lattices @ X23)
% 49.60/49.85          | ~ (v4_lattice3 @ X23)
% 49.60/49.85          | ~ (v10_lattices @ X23)
% 49.60/49.85          | (v2_struct_0 @ X23))),
% 49.60/49.85      inference('cnf', [status(esa)], [t34_lattice3])).
% 49.60/49.85  thf('55', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.60/49.85         ((v2_struct_0 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | (v2_struct_0 @ X0)
% 49.60/49.85          | ~ (v10_lattices @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | ((sk_C @ X1 @ X0) = (k16_lattice3 @ X0 @ X2))
% 49.60/49.85          | (r3_lattice3 @ X0 @ (sk_D_4 @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X2)
% 49.60/49.85          | ~ (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2))),
% 49.60/49.85      inference('sup-', [status(thm)], ['53', '54'])).
% 49.60/49.85  thf('56', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.60/49.85         (~ (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 49.60/49.85          | (r3_lattice3 @ X0 @ (sk_D_4 @ X2 @ (sk_C @ X1 @ X0) @ X0) @ X2)
% 49.60/49.85          | ((sk_C @ X1 @ X0) = (k16_lattice3 @ X0 @ X2))
% 49.60/49.85          | ~ (v10_lattices @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | (v2_struct_0 @ X0))),
% 49.60/49.85      inference('simplify', [status(thm)], ['55'])).
% 49.60/49.85  thf('57', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i]:
% 49.60/49.85         ((v2_struct_0 @ X1)
% 49.60/49.85          | ~ (l3_lattices @ X1)
% 49.60/49.85          | ~ (v4_lattice3 @ X1)
% 49.60/49.85          | ~ (v10_lattices @ X1)
% 49.60/49.85          | (v2_struct_0 @ X1)
% 49.60/49.85          | ~ (l3_lattices @ X1)
% 49.60/49.85          | ~ (v4_lattice3 @ X1)
% 49.60/49.85          | ~ (v10_lattices @ X1)
% 49.60/49.85          | ((sk_C @ (a_2_9_lattice3 @ X1 @ X0) @ X1)
% 49.60/49.85              = (k16_lattice3 @ X1 @ X0))
% 49.60/49.85          | (r3_lattice3 @ X1 @ 
% 49.60/49.85             (sk_D_4 @ X0 @ (sk_C @ (a_2_9_lattice3 @ X1 @ X0) @ X1) @ X1) @ X0))),
% 49.60/49.85      inference('sup-', [status(thm)], ['52', '56'])).
% 49.60/49.85  thf('58', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i]:
% 49.60/49.85         ((r3_lattice3 @ X1 @ 
% 49.60/49.85           (sk_D_4 @ X0 @ (sk_C @ (a_2_9_lattice3 @ X1 @ X0) @ X1) @ X1) @ X0)
% 49.60/49.85          | ((sk_C @ (a_2_9_lattice3 @ X1 @ X0) @ X1)
% 49.60/49.85              = (k16_lattice3 @ X1 @ X0))
% 49.60/49.85          | ~ (v10_lattices @ X1)
% 49.60/49.85          | ~ (v4_lattice3 @ X1)
% 49.60/49.85          | ~ (l3_lattices @ X1)
% 49.60/49.85          | (v2_struct_0 @ X1))),
% 49.60/49.85      inference('simplify', [status(thm)], ['57'])).
% 49.60/49.85  thf('59', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i]:
% 49.60/49.85         (~ (v10_lattices @ X0)
% 49.60/49.85          | (r3_lattice3 @ X0 @ (sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0) @ X1)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | (v2_struct_0 @ X0))),
% 49.60/49.85      inference('simplify', [status(thm)], ['49'])).
% 49.60/49.85  thf('60', plain,
% 49.60/49.85      (![X15 : $i, X16 : $i]:
% 49.60/49.85         (~ (v4_lattice3 @ X15)
% 49.60/49.85          | (m1_subset_1 @ (sk_C @ X16 @ X15) @ (u1_struct_0 @ X15))
% 49.60/49.85          | ~ (l3_lattices @ X15)
% 49.60/49.85          | (v2_struct_0 @ X15))),
% 49.60/49.85      inference('cnf', [status(esa)], [d18_lattice3])).
% 49.60/49.85  thf('61', plain,
% 49.60/49.85      (![X22 : $i, X23 : $i, X26 : $i]:
% 49.60/49.85         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 49.60/49.85          | ~ (r3_lattice3 @ X23 @ X22 @ X26)
% 49.60/49.85          | (m1_subset_1 @ (sk_D_4 @ X26 @ X22 @ X23) @ (u1_struct_0 @ X23))
% 49.60/49.85          | ((X22) = (k16_lattice3 @ X23 @ X26))
% 49.60/49.85          | ~ (l3_lattices @ X23)
% 49.60/49.85          | ~ (v4_lattice3 @ X23)
% 49.60/49.85          | ~ (v10_lattices @ X23)
% 49.60/49.85          | (v2_struct_0 @ X23))),
% 49.60/49.85      inference('cnf', [status(esa)], [t34_lattice3])).
% 49.60/49.85  thf('62', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.60/49.85         ((v2_struct_0 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | (v2_struct_0 @ X0)
% 49.60/49.85          | ~ (v10_lattices @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | ((sk_C @ X1 @ X0) = (k16_lattice3 @ X0 @ X2))
% 49.60/49.85          | (m1_subset_1 @ (sk_D_4 @ X2 @ (sk_C @ X1 @ X0) @ X0) @ 
% 49.60/49.85             (u1_struct_0 @ X0))
% 49.60/49.85          | ~ (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2))),
% 49.60/49.85      inference('sup-', [status(thm)], ['60', '61'])).
% 49.60/49.85  thf('63', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.60/49.85         (~ (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 49.60/49.85          | (m1_subset_1 @ (sk_D_4 @ X2 @ (sk_C @ X1 @ X0) @ X0) @ 
% 49.60/49.85             (u1_struct_0 @ X0))
% 49.60/49.85          | ((sk_C @ X1 @ X0) = (k16_lattice3 @ X0 @ X2))
% 49.60/49.85          | ~ (v10_lattices @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | (v2_struct_0 @ X0))),
% 49.60/49.85      inference('simplify', [status(thm)], ['62'])).
% 49.60/49.85  thf('64', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i]:
% 49.60/49.85         ((v2_struct_0 @ X1)
% 49.60/49.85          | ~ (l3_lattices @ X1)
% 49.60/49.85          | ~ (v4_lattice3 @ X1)
% 49.60/49.85          | ~ (v10_lattices @ X1)
% 49.60/49.85          | (v2_struct_0 @ X1)
% 49.60/49.85          | ~ (l3_lattices @ X1)
% 49.60/49.85          | ~ (v4_lattice3 @ X1)
% 49.60/49.85          | ~ (v10_lattices @ X1)
% 49.60/49.85          | ((sk_C @ (a_2_9_lattice3 @ X1 @ X0) @ X1)
% 49.60/49.85              = (k16_lattice3 @ X1 @ X0))
% 49.60/49.85          | (m1_subset_1 @ 
% 49.60/49.85             (sk_D_4 @ X0 @ (sk_C @ (a_2_9_lattice3 @ X1 @ X0) @ X1) @ X1) @ 
% 49.60/49.85             (u1_struct_0 @ X1)))),
% 49.60/49.85      inference('sup-', [status(thm)], ['59', '63'])).
% 49.60/49.85  thf('65', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i]:
% 49.60/49.85         ((m1_subset_1 @ 
% 49.60/49.85           (sk_D_4 @ X0 @ (sk_C @ (a_2_9_lattice3 @ X1 @ X0) @ X1) @ X1) @ 
% 49.60/49.85           (u1_struct_0 @ X1))
% 49.60/49.85          | ((sk_C @ (a_2_9_lattice3 @ X1 @ X0) @ X1)
% 49.60/49.85              = (k16_lattice3 @ X1 @ X0))
% 49.60/49.85          | ~ (v10_lattices @ X1)
% 49.60/49.85          | ~ (v4_lattice3 @ X1)
% 49.60/49.85          | ~ (l3_lattices @ X1)
% 49.60/49.85          | (v2_struct_0 @ X1))),
% 49.60/49.85      inference('simplify', [status(thm)], ['64'])).
% 49.60/49.85  thf('66', plain,
% 49.60/49.85      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 49.60/49.85         (~ (l3_lattices @ X18)
% 49.60/49.85          | ~ (v4_lattice3 @ X18)
% 49.60/49.85          | ~ (v10_lattices @ X18)
% 49.60/49.85          | (v2_struct_0 @ X18)
% 49.60/49.85          | (r2_hidden @ X20 @ (a_2_9_lattice3 @ X18 @ X19))
% 49.60/49.85          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X18))
% 49.60/49.85          | ((X20) != (X21))
% 49.60/49.85          | ~ (r3_lattice3 @ X18 @ X21 @ X19))),
% 49.60/49.85      inference('cnf', [status(esa)], [fraenkel_a_2_9_lattice3])).
% 49.60/49.85  thf('67', plain,
% 49.60/49.85      (![X18 : $i, X19 : $i, X21 : $i]:
% 49.60/49.85         (~ (r3_lattice3 @ X18 @ X21 @ X19)
% 49.60/49.85          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X18))
% 49.60/49.85          | (r2_hidden @ X21 @ (a_2_9_lattice3 @ X18 @ X19))
% 49.60/49.85          | (v2_struct_0 @ X18)
% 49.60/49.85          | ~ (v10_lattices @ X18)
% 49.60/49.85          | ~ (v4_lattice3 @ X18)
% 49.60/49.85          | ~ (l3_lattices @ X18))),
% 49.60/49.85      inference('simplify', [status(thm)], ['66'])).
% 49.60/49.85  thf('68', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.60/49.85         ((v2_struct_0 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (v10_lattices @ X0)
% 49.60/49.85          | ((sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0)
% 49.60/49.85              = (k16_lattice3 @ X0 @ X1))
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (v10_lattices @ X0)
% 49.60/49.85          | (v2_struct_0 @ X0)
% 49.60/49.85          | (r2_hidden @ 
% 49.60/49.85             (sk_D_4 @ X1 @ (sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0) @ X0) @ 
% 49.60/49.85             (a_2_9_lattice3 @ X0 @ X2))
% 49.60/49.85          | ~ (r3_lattice3 @ X0 @ 
% 49.60/49.85               (sk_D_4 @ X1 @ (sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0) @ X0) @ 
% 49.60/49.85               X2))),
% 49.60/49.85      inference('sup-', [status(thm)], ['65', '67'])).
% 49.60/49.85  thf('69', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.60/49.85         (~ (r3_lattice3 @ X0 @ 
% 49.60/49.85             (sk_D_4 @ X1 @ (sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0) @ X0) @ X2)
% 49.60/49.85          | (r2_hidden @ 
% 49.60/49.85             (sk_D_4 @ X1 @ (sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0) @ X0) @ 
% 49.60/49.85             (a_2_9_lattice3 @ X0 @ X2))
% 49.60/49.85          | ((sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0)
% 49.60/49.85              = (k16_lattice3 @ X0 @ X1))
% 49.60/49.85          | ~ (v10_lattices @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | (v2_struct_0 @ X0))),
% 49.60/49.85      inference('simplify', [status(thm)], ['68'])).
% 49.60/49.85  thf('70', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i]:
% 49.60/49.85         ((v2_struct_0 @ X1)
% 49.60/49.85          | ~ (l3_lattices @ X1)
% 49.60/49.85          | ~ (v4_lattice3 @ X1)
% 49.60/49.85          | ~ (v10_lattices @ X1)
% 49.60/49.85          | ((sk_C @ (a_2_9_lattice3 @ X1 @ X0) @ X1)
% 49.60/49.85              = (k16_lattice3 @ X1 @ X0))
% 49.60/49.85          | (v2_struct_0 @ X1)
% 49.60/49.85          | ~ (l3_lattices @ X1)
% 49.60/49.85          | ~ (v4_lattice3 @ X1)
% 49.60/49.85          | ~ (v10_lattices @ X1)
% 49.60/49.85          | ((sk_C @ (a_2_9_lattice3 @ X1 @ X0) @ X1)
% 49.60/49.85              = (k16_lattice3 @ X1 @ X0))
% 49.60/49.85          | (r2_hidden @ 
% 49.60/49.85             (sk_D_4 @ X0 @ (sk_C @ (a_2_9_lattice3 @ X1 @ X0) @ X1) @ X1) @ 
% 49.60/49.85             (a_2_9_lattice3 @ X1 @ X0)))),
% 49.60/49.85      inference('sup-', [status(thm)], ['58', '69'])).
% 49.60/49.85  thf('71', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i]:
% 49.60/49.85         ((r2_hidden @ 
% 49.60/49.85           (sk_D_4 @ X0 @ (sk_C @ (a_2_9_lattice3 @ X1 @ X0) @ X1) @ X1) @ 
% 49.60/49.85           (a_2_9_lattice3 @ X1 @ X0))
% 49.60/49.85          | ((sk_C @ (a_2_9_lattice3 @ X1 @ X0) @ X1)
% 49.60/49.85              = (k16_lattice3 @ X1 @ X0))
% 49.60/49.85          | ~ (v10_lattices @ X1)
% 49.60/49.85          | ~ (v4_lattice3 @ X1)
% 49.60/49.85          | ~ (l3_lattices @ X1)
% 49.60/49.85          | (v2_struct_0 @ X1))),
% 49.60/49.85      inference('simplify', [status(thm)], ['70'])).
% 49.60/49.85  thf('72', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i]:
% 49.60/49.85         ((m1_subset_1 @ 
% 49.60/49.85           (sk_D_4 @ X0 @ (sk_C @ (a_2_9_lattice3 @ X1 @ X0) @ X1) @ X1) @ 
% 49.60/49.85           (u1_struct_0 @ X1))
% 49.60/49.85          | ((sk_C @ (a_2_9_lattice3 @ X1 @ X0) @ X1)
% 49.60/49.85              = (k16_lattice3 @ X1 @ X0))
% 49.60/49.85          | ~ (v10_lattices @ X1)
% 49.60/49.85          | ~ (v4_lattice3 @ X1)
% 49.60/49.85          | ~ (l3_lattices @ X1)
% 49.60/49.85          | (v2_struct_0 @ X1))),
% 49.60/49.85      inference('simplify', [status(thm)], ['64'])).
% 49.60/49.85  thf('73', plain,
% 49.60/49.85      (![X15 : $i, X16 : $i]:
% 49.60/49.85         (~ (v4_lattice3 @ X15)
% 49.60/49.85          | (r4_lattice3 @ X15 @ (sk_C @ X16 @ X15) @ X16)
% 49.60/49.85          | ~ (l3_lattices @ X15)
% 49.60/49.85          | (v2_struct_0 @ X15))),
% 49.60/49.85      inference('cnf', [status(esa)], [d18_lattice3])).
% 49.60/49.85  thf('74', plain,
% 49.60/49.85      (![X15 : $i, X16 : $i]:
% 49.60/49.85         (~ (v4_lattice3 @ X15)
% 49.60/49.85          | (m1_subset_1 @ (sk_C @ X16 @ X15) @ (u1_struct_0 @ X15))
% 49.60/49.85          | ~ (l3_lattices @ X15)
% 49.60/49.85          | (v2_struct_0 @ X15))),
% 49.60/49.85      inference('cnf', [status(esa)], [d18_lattice3])).
% 49.60/49.85  thf('75', plain,
% 49.60/49.85      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 49.60/49.85         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 49.60/49.85          | ~ (r4_lattice3 @ X10 @ X9 @ X11)
% 49.60/49.85          | ~ (r2_hidden @ X12 @ X11)
% 49.60/49.85          | (r1_lattices @ X10 @ X12 @ X9)
% 49.60/49.85          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X10))
% 49.60/49.85          | ~ (l3_lattices @ X10)
% 49.60/49.85          | (v2_struct_0 @ X10))),
% 49.60/49.85      inference('cnf', [status(esa)], [d17_lattice3])).
% 49.60/49.85  thf('76', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 49.60/49.85         ((v2_struct_0 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | (v2_struct_0 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 49.60/49.85          | (r1_lattices @ X0 @ X2 @ (sk_C @ X1 @ X0))
% 49.60/49.85          | ~ (r2_hidden @ X2 @ X3)
% 49.60/49.85          | ~ (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X3))),
% 49.60/49.85      inference('sup-', [status(thm)], ['74', '75'])).
% 49.60/49.85  thf('77', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 49.60/49.85         (~ (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X3)
% 49.60/49.85          | ~ (r2_hidden @ X2 @ X3)
% 49.60/49.85          | (r1_lattices @ X0 @ X2 @ (sk_C @ X1 @ X0))
% 49.60/49.85          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | (v2_struct_0 @ X0))),
% 49.60/49.85      inference('simplify', [status(thm)], ['76'])).
% 49.60/49.85  thf('78', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.60/49.85         ((v2_struct_0 @ X1)
% 49.60/49.85          | ~ (l3_lattices @ X1)
% 49.60/49.85          | ~ (v4_lattice3 @ X1)
% 49.60/49.85          | (v2_struct_0 @ X1)
% 49.60/49.85          | ~ (l3_lattices @ X1)
% 49.60/49.85          | ~ (v4_lattice3 @ X1)
% 49.60/49.85          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 49.60/49.85          | (r1_lattices @ X1 @ X2 @ (sk_C @ X0 @ X1))
% 49.60/49.85          | ~ (r2_hidden @ X2 @ X0))),
% 49.60/49.85      inference('sup-', [status(thm)], ['73', '77'])).
% 49.60/49.85  thf('79', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.60/49.85         (~ (r2_hidden @ X2 @ X0)
% 49.60/49.85          | (r1_lattices @ X1 @ X2 @ (sk_C @ X0 @ X1))
% 49.60/49.85          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 49.60/49.85          | ~ (v4_lattice3 @ X1)
% 49.60/49.85          | ~ (l3_lattices @ X1)
% 49.60/49.85          | (v2_struct_0 @ X1))),
% 49.60/49.85      inference('simplify', [status(thm)], ['78'])).
% 49.60/49.85  thf('80', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.60/49.85         ((v2_struct_0 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (v10_lattices @ X0)
% 49.60/49.85          | ((sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0)
% 49.60/49.85              = (k16_lattice3 @ X0 @ X1))
% 49.60/49.85          | (v2_struct_0 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | (r1_lattices @ X0 @ 
% 49.60/49.85             (sk_D_4 @ X1 @ (sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0) @ X0) @ 
% 49.60/49.85             (sk_C @ X2 @ X0))
% 49.60/49.85          | ~ (r2_hidden @ 
% 49.60/49.85               (sk_D_4 @ X1 @ (sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0) @ X0) @ 
% 49.60/49.85               X2))),
% 49.60/49.85      inference('sup-', [status(thm)], ['72', '79'])).
% 49.60/49.85  thf('81', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.60/49.85         (~ (r2_hidden @ 
% 49.60/49.85             (sk_D_4 @ X1 @ (sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0) @ X0) @ X2)
% 49.60/49.85          | (r1_lattices @ X0 @ 
% 49.60/49.85             (sk_D_4 @ X1 @ (sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0) @ X0) @ 
% 49.60/49.85             (sk_C @ X2 @ X0))
% 49.60/49.85          | ((sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0)
% 49.60/49.85              = (k16_lattice3 @ X0 @ X1))
% 49.60/49.85          | ~ (v10_lattices @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | (v2_struct_0 @ X0))),
% 49.60/49.85      inference('simplify', [status(thm)], ['80'])).
% 49.60/49.85  thf('82', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i]:
% 49.60/49.85         ((v2_struct_0 @ X1)
% 49.60/49.85          | ~ (l3_lattices @ X1)
% 49.60/49.85          | ~ (v4_lattice3 @ X1)
% 49.60/49.85          | ~ (v10_lattices @ X1)
% 49.60/49.85          | ((sk_C @ (a_2_9_lattice3 @ X1 @ X0) @ X1)
% 49.60/49.85              = (k16_lattice3 @ X1 @ X0))
% 49.60/49.85          | (v2_struct_0 @ X1)
% 49.60/49.85          | ~ (l3_lattices @ X1)
% 49.60/49.85          | ~ (v4_lattice3 @ X1)
% 49.60/49.85          | ~ (v10_lattices @ X1)
% 49.60/49.85          | ((sk_C @ (a_2_9_lattice3 @ X1 @ X0) @ X1)
% 49.60/49.85              = (k16_lattice3 @ X1 @ X0))
% 49.60/49.85          | (r1_lattices @ X1 @ 
% 49.60/49.85             (sk_D_4 @ X0 @ (sk_C @ (a_2_9_lattice3 @ X1 @ X0) @ X1) @ X1) @ 
% 49.60/49.85             (sk_C @ (a_2_9_lattice3 @ X1 @ X0) @ X1)))),
% 49.60/49.85      inference('sup-', [status(thm)], ['71', '81'])).
% 49.60/49.85  thf('83', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i]:
% 49.60/49.85         ((r1_lattices @ X1 @ 
% 49.60/49.85           (sk_D_4 @ X0 @ (sk_C @ (a_2_9_lattice3 @ X1 @ X0) @ X1) @ X1) @ 
% 49.60/49.85           (sk_C @ (a_2_9_lattice3 @ X1 @ X0) @ X1))
% 49.60/49.85          | ((sk_C @ (a_2_9_lattice3 @ X1 @ X0) @ X1)
% 49.60/49.85              = (k16_lattice3 @ X1 @ X0))
% 49.60/49.85          | ~ (v10_lattices @ X1)
% 49.60/49.85          | ~ (v4_lattice3 @ X1)
% 49.60/49.85          | ~ (l3_lattices @ X1)
% 49.60/49.85          | (v2_struct_0 @ X1))),
% 49.60/49.85      inference('simplify', [status(thm)], ['82'])).
% 49.60/49.85  thf('84', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i]:
% 49.60/49.85         ((m1_subset_1 @ 
% 49.60/49.85           (sk_D_4 @ X0 @ (sk_C @ (a_2_9_lattice3 @ X1 @ X0) @ X1) @ X1) @ 
% 49.60/49.85           (u1_struct_0 @ X1))
% 49.60/49.85          | ((sk_C @ (a_2_9_lattice3 @ X1 @ X0) @ X1)
% 49.60/49.85              = (k16_lattice3 @ X1 @ X0))
% 49.60/49.85          | ~ (v10_lattices @ X1)
% 49.60/49.85          | ~ (v4_lattice3 @ X1)
% 49.60/49.85          | ~ (l3_lattices @ X1)
% 49.60/49.85          | (v2_struct_0 @ X1))),
% 49.60/49.85      inference('simplify', [status(thm)], ['64'])).
% 49.60/49.85  thf(redefinition_r3_lattices, axiom,
% 49.60/49.85    (![A:$i,B:$i,C:$i]:
% 49.60/49.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 49.60/49.85         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 49.60/49.85         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 49.60/49.85         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 49.60/49.85       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 49.60/49.85  thf('85', plain,
% 49.60/49.85      (![X1 : $i, X2 : $i, X3 : $i]:
% 49.60/49.85         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 49.60/49.85          | ~ (l3_lattices @ X2)
% 49.60/49.85          | ~ (v9_lattices @ X2)
% 49.60/49.85          | ~ (v8_lattices @ X2)
% 49.60/49.85          | ~ (v6_lattices @ X2)
% 49.60/49.85          | (v2_struct_0 @ X2)
% 49.60/49.85          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 49.60/49.85          | (r3_lattices @ X2 @ X1 @ X3)
% 49.60/49.85          | ~ (r1_lattices @ X2 @ X1 @ X3))),
% 49.60/49.85      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 49.60/49.85  thf('86', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.60/49.85         ((v2_struct_0 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (v10_lattices @ X0)
% 49.60/49.85          | ((sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0)
% 49.60/49.85              = (k16_lattice3 @ X0 @ X1))
% 49.60/49.85          | ~ (r1_lattices @ X0 @ 
% 49.60/49.85               (sk_D_4 @ X1 @ (sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0) @ X0) @ 
% 49.60/49.85               X2)
% 49.60/49.85          | (r3_lattices @ X0 @ 
% 49.60/49.85             (sk_D_4 @ X1 @ (sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0) @ X0) @ X2)
% 49.60/49.85          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 49.60/49.85          | (v2_struct_0 @ X0)
% 49.60/49.85          | ~ (v6_lattices @ X0)
% 49.60/49.85          | ~ (v8_lattices @ X0)
% 49.60/49.85          | ~ (v9_lattices @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0))),
% 49.60/49.85      inference('sup-', [status(thm)], ['84', '85'])).
% 49.60/49.85  thf('87', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.60/49.85         (~ (v9_lattices @ X0)
% 49.60/49.85          | ~ (v8_lattices @ X0)
% 49.60/49.85          | ~ (v6_lattices @ X0)
% 49.60/49.85          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 49.60/49.85          | (r3_lattices @ X0 @ 
% 49.60/49.85             (sk_D_4 @ X1 @ (sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0) @ X0) @ X2)
% 49.60/49.85          | ~ (r1_lattices @ X0 @ 
% 49.60/49.85               (sk_D_4 @ X1 @ (sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0) @ X0) @ 
% 49.60/49.85               X2)
% 49.60/49.85          | ((sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0)
% 49.60/49.85              = (k16_lattice3 @ X0 @ X1))
% 49.60/49.85          | ~ (v10_lattices @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | (v2_struct_0 @ X0))),
% 49.60/49.85      inference('simplify', [status(thm)], ['86'])).
% 49.60/49.85  thf('88', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i]:
% 49.60/49.85         ((v2_struct_0 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (v10_lattices @ X0)
% 49.60/49.85          | ((sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0)
% 49.60/49.85              = (k16_lattice3 @ X0 @ X1))
% 49.60/49.85          | (v2_struct_0 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (v10_lattices @ X0)
% 49.60/49.85          | ((sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0)
% 49.60/49.85              = (k16_lattice3 @ X0 @ X1))
% 49.60/49.85          | (r3_lattices @ X0 @ 
% 49.60/49.85             (sk_D_4 @ X1 @ (sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0) @ X0) @ 
% 49.60/49.85             (sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0))
% 49.60/49.85          | ~ (m1_subset_1 @ (sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0) @ 
% 49.60/49.85               (u1_struct_0 @ X0))
% 49.60/49.85          | ~ (v6_lattices @ X0)
% 49.60/49.85          | ~ (v8_lattices @ X0)
% 49.60/49.85          | ~ (v9_lattices @ X0))),
% 49.60/49.85      inference('sup-', [status(thm)], ['83', '87'])).
% 49.60/49.85  thf('89', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i]:
% 49.60/49.85         (~ (v9_lattices @ X0)
% 49.60/49.85          | ~ (v8_lattices @ X0)
% 49.60/49.85          | ~ (v6_lattices @ X0)
% 49.60/49.85          | ~ (m1_subset_1 @ (sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0) @ 
% 49.60/49.85               (u1_struct_0 @ X0))
% 49.60/49.85          | (r3_lattices @ X0 @ 
% 49.60/49.85             (sk_D_4 @ X1 @ (sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0) @ X0) @ 
% 49.60/49.85             (sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0))
% 49.60/49.85          | ((sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0)
% 49.60/49.85              = (k16_lattice3 @ X0 @ X1))
% 49.60/49.85          | ~ (v10_lattices @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | (v2_struct_0 @ X0))),
% 49.60/49.85      inference('simplify', [status(thm)], ['88'])).
% 49.60/49.85  thf('90', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i]:
% 49.60/49.85         ((v2_struct_0 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | (v2_struct_0 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (v10_lattices @ X0)
% 49.60/49.85          | ((sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0)
% 49.60/49.85              = (k16_lattice3 @ X0 @ X1))
% 49.60/49.85          | (r3_lattices @ X0 @ 
% 49.60/49.85             (sk_D_4 @ X1 @ (sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0) @ X0) @ 
% 49.60/49.85             (sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0))
% 49.60/49.85          | ~ (v6_lattices @ X0)
% 49.60/49.85          | ~ (v8_lattices @ X0)
% 49.60/49.85          | ~ (v9_lattices @ X0))),
% 49.60/49.85      inference('sup-', [status(thm)], ['51', '89'])).
% 49.60/49.85  thf('91', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i]:
% 49.60/49.85         (~ (v9_lattices @ X0)
% 49.60/49.85          | ~ (v8_lattices @ X0)
% 49.60/49.85          | ~ (v6_lattices @ X0)
% 49.60/49.85          | (r3_lattices @ X0 @ 
% 49.60/49.85             (sk_D_4 @ X1 @ (sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0) @ X0) @ 
% 49.60/49.85             (sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0))
% 49.60/49.85          | ((sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0)
% 49.60/49.85              = (k16_lattice3 @ X0 @ X1))
% 49.60/49.85          | ~ (v10_lattices @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | (v2_struct_0 @ X0))),
% 49.60/49.85      inference('simplify', [status(thm)], ['90'])).
% 49.60/49.85  thf('92', plain,
% 49.60/49.85      (![X15 : $i, X16 : $i]:
% 49.60/49.85         (~ (v4_lattice3 @ X15)
% 49.60/49.85          | (m1_subset_1 @ (sk_C @ X16 @ X15) @ (u1_struct_0 @ X15))
% 49.60/49.85          | ~ (l3_lattices @ X15)
% 49.60/49.85          | (v2_struct_0 @ X15))),
% 49.60/49.85      inference('cnf', [status(esa)], [d18_lattice3])).
% 49.60/49.85  thf('93', plain,
% 49.60/49.85      (![X22 : $i, X23 : $i, X26 : $i]:
% 49.60/49.85         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 49.60/49.85          | ~ (r3_lattice3 @ X23 @ X22 @ X26)
% 49.60/49.85          | ~ (r3_lattices @ X23 @ (sk_D_4 @ X26 @ X22 @ X23) @ X22)
% 49.60/49.85          | ((X22) = (k16_lattice3 @ X23 @ X26))
% 49.60/49.85          | ~ (l3_lattices @ X23)
% 49.60/49.85          | ~ (v4_lattice3 @ X23)
% 49.60/49.85          | ~ (v10_lattices @ X23)
% 49.60/49.85          | (v2_struct_0 @ X23))),
% 49.60/49.85      inference('cnf', [status(esa)], [t34_lattice3])).
% 49.60/49.85  thf('94', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.60/49.85         ((v2_struct_0 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | (v2_struct_0 @ X0)
% 49.60/49.85          | ~ (v10_lattices @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | ((sk_C @ X1 @ X0) = (k16_lattice3 @ X0 @ X2))
% 49.60/49.85          | ~ (r3_lattices @ X0 @ (sk_D_4 @ X2 @ (sk_C @ X1 @ X0) @ X0) @ 
% 49.60/49.85               (sk_C @ X1 @ X0))
% 49.60/49.85          | ~ (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2))),
% 49.60/49.85      inference('sup-', [status(thm)], ['92', '93'])).
% 49.60/49.85  thf('95', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.60/49.85         (~ (r3_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 49.60/49.85          | ~ (r3_lattices @ X0 @ (sk_D_4 @ X2 @ (sk_C @ X1 @ X0) @ X0) @ 
% 49.60/49.85               (sk_C @ X1 @ X0))
% 49.60/49.85          | ((sk_C @ X1 @ X0) = (k16_lattice3 @ X0 @ X2))
% 49.60/49.85          | ~ (v10_lattices @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | (v2_struct_0 @ X0))),
% 49.60/49.85      inference('simplify', [status(thm)], ['94'])).
% 49.60/49.85  thf('96', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i]:
% 49.60/49.85         ((v2_struct_0 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (v10_lattices @ X0)
% 49.60/49.85          | ((sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0)
% 49.60/49.85              = (k16_lattice3 @ X0 @ X1))
% 49.60/49.85          | ~ (v6_lattices @ X0)
% 49.60/49.85          | ~ (v8_lattices @ X0)
% 49.60/49.85          | ~ (v9_lattices @ X0)
% 49.60/49.85          | (v2_struct_0 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (v10_lattices @ X0)
% 49.60/49.85          | ((sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0)
% 49.60/49.85              = (k16_lattice3 @ X0 @ X1))
% 49.60/49.85          | ~ (r3_lattice3 @ X0 @ (sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0) @ X1))),
% 49.60/49.85      inference('sup-', [status(thm)], ['91', '95'])).
% 49.60/49.85  thf('97', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i]:
% 49.60/49.85         (~ (r3_lattice3 @ X0 @ (sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0) @ X1)
% 49.60/49.85          | ~ (v9_lattices @ X0)
% 49.60/49.85          | ~ (v8_lattices @ X0)
% 49.60/49.85          | ~ (v6_lattices @ X0)
% 49.60/49.85          | ((sk_C @ (a_2_9_lattice3 @ X0 @ X1) @ X0)
% 49.60/49.85              = (k16_lattice3 @ X0 @ X1))
% 49.60/49.85          | ~ (v10_lattices @ X0)
% 49.60/49.85          | ~ (v4_lattice3 @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0)
% 49.60/49.85          | (v2_struct_0 @ X0))),
% 49.60/49.85      inference('simplify', [status(thm)], ['96'])).
% 49.60/49.85  thf('98', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i]:
% 49.60/49.85         ((v2_struct_0 @ X1)
% 49.60/49.85          | ~ (l3_lattices @ X1)
% 49.60/49.85          | ~ (v4_lattice3 @ X1)
% 49.60/49.85          | ~ (v10_lattices @ X1)
% 49.60/49.85          | (v2_struct_0 @ X1)
% 49.60/49.85          | ~ (l3_lattices @ X1)
% 49.60/49.85          | ~ (v4_lattice3 @ X1)
% 49.60/49.85          | ~ (v10_lattices @ X1)
% 49.60/49.85          | ((sk_C @ (a_2_9_lattice3 @ X1 @ X0) @ X1)
% 49.60/49.85              = (k16_lattice3 @ X1 @ X0))
% 49.60/49.85          | ~ (v6_lattices @ X1)
% 49.60/49.85          | ~ (v8_lattices @ X1)
% 49.60/49.85          | ~ (v9_lattices @ X1))),
% 49.60/49.85      inference('sup-', [status(thm)], ['50', '97'])).
% 49.60/49.85  thf('99', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i]:
% 49.60/49.85         (~ (v9_lattices @ X1)
% 49.60/49.85          | ~ (v8_lattices @ X1)
% 49.60/49.85          | ~ (v6_lattices @ X1)
% 49.60/49.85          | ((sk_C @ (a_2_9_lattice3 @ X1 @ X0) @ X1)
% 49.60/49.85              = (k16_lattice3 @ X1 @ X0))
% 49.60/49.85          | ~ (v10_lattices @ X1)
% 49.60/49.85          | ~ (v4_lattice3 @ X1)
% 49.60/49.85          | ~ (l3_lattices @ X1)
% 49.60/49.85          | (v2_struct_0 @ X1))),
% 49.60/49.85      inference('simplify', [status(thm)], ['98'])).
% 49.60/49.85  thf('100', plain,
% 49.60/49.85      (![X15 : $i, X16 : $i]:
% 49.60/49.85         (~ (v4_lattice3 @ X15)
% 49.60/49.85          | (m1_subset_1 @ (sk_C @ X16 @ X15) @ (u1_struct_0 @ X15))
% 49.60/49.85          | ~ (l3_lattices @ X15)
% 49.60/49.85          | (v2_struct_0 @ X15))),
% 49.60/49.85      inference('cnf', [status(esa)], [d18_lattice3])).
% 49.60/49.85  thf('101', plain, ((r3_lattice3 @ sk_A @ sk_B_1 @ sk_C_1)),
% 49.60/49.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.60/49.85  thf('102', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 49.60/49.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.60/49.85  thf('103', plain,
% 49.60/49.85      (![X18 : $i, X19 : $i, X21 : $i]:
% 49.60/49.85         (~ (r3_lattice3 @ X18 @ X21 @ X19)
% 49.60/49.85          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X18))
% 49.60/49.85          | (r2_hidden @ X21 @ (a_2_9_lattice3 @ X18 @ X19))
% 49.60/49.85          | (v2_struct_0 @ X18)
% 49.60/49.85          | ~ (v10_lattices @ X18)
% 49.60/49.85          | ~ (v4_lattice3 @ X18)
% 49.60/49.85          | ~ (l3_lattices @ X18))),
% 49.60/49.85      inference('simplify', [status(thm)], ['66'])).
% 49.60/49.85  thf('104', plain,
% 49.60/49.85      (![X0 : $i]:
% 49.60/49.85         (~ (l3_lattices @ sk_A)
% 49.60/49.85          | ~ (v4_lattice3 @ sk_A)
% 49.60/49.85          | ~ (v10_lattices @ sk_A)
% 49.60/49.85          | (v2_struct_0 @ sk_A)
% 49.60/49.85          | (r2_hidden @ sk_B_1 @ (a_2_9_lattice3 @ sk_A @ X0))
% 49.60/49.85          | ~ (r3_lattice3 @ sk_A @ sk_B_1 @ X0))),
% 49.60/49.85      inference('sup-', [status(thm)], ['102', '103'])).
% 49.60/49.85  thf('105', plain, ((l3_lattices @ sk_A)),
% 49.60/49.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.60/49.85  thf('106', plain, ((v4_lattice3 @ sk_A)),
% 49.60/49.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.60/49.85  thf('107', plain, ((v10_lattices @ sk_A)),
% 49.60/49.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.60/49.85  thf('108', plain,
% 49.60/49.85      (![X0 : $i]:
% 49.60/49.85         ((v2_struct_0 @ sk_A)
% 49.60/49.85          | (r2_hidden @ sk_B_1 @ (a_2_9_lattice3 @ sk_A @ X0))
% 49.60/49.85          | ~ (r3_lattice3 @ sk_A @ sk_B_1 @ X0))),
% 49.60/49.85      inference('demod', [status(thm)], ['104', '105', '106', '107'])).
% 49.60/49.85  thf('109', plain, (~ (v2_struct_0 @ sk_A)),
% 49.60/49.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.60/49.85  thf('110', plain,
% 49.60/49.85      (![X0 : $i]:
% 49.60/49.85         (~ (r3_lattice3 @ sk_A @ sk_B_1 @ X0)
% 49.60/49.85          | (r2_hidden @ sk_B_1 @ (a_2_9_lattice3 @ sk_A @ X0)))),
% 49.60/49.85      inference('clc', [status(thm)], ['108', '109'])).
% 49.60/49.85  thf('111', plain, ((r2_hidden @ sk_B_1 @ (a_2_9_lattice3 @ sk_A @ sk_C_1))),
% 49.60/49.85      inference('sup-', [status(thm)], ['101', '110'])).
% 49.60/49.85  thf('112', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 49.60/49.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.60/49.85  thf('113', plain,
% 49.60/49.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.60/49.85         (~ (r2_hidden @ X2 @ X0)
% 49.60/49.85          | (r1_lattices @ X1 @ X2 @ (sk_C @ X0 @ X1))
% 49.60/49.85          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 49.60/49.85          | ~ (v4_lattice3 @ X1)
% 49.60/49.85          | ~ (l3_lattices @ X1)
% 49.60/49.85          | (v2_struct_0 @ X1))),
% 49.60/49.85      inference('simplify', [status(thm)], ['78'])).
% 49.60/49.85  thf('114', plain,
% 49.60/49.85      (![X0 : $i]:
% 49.60/49.85         ((v2_struct_0 @ sk_A)
% 49.60/49.85          | ~ (l3_lattices @ sk_A)
% 49.60/49.85          | ~ (v4_lattice3 @ sk_A)
% 49.60/49.85          | (r1_lattices @ sk_A @ sk_B_1 @ (sk_C @ X0 @ sk_A))
% 49.60/49.85          | ~ (r2_hidden @ sk_B_1 @ X0))),
% 49.60/49.85      inference('sup-', [status(thm)], ['112', '113'])).
% 49.60/49.85  thf('115', plain, ((l3_lattices @ sk_A)),
% 49.60/49.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.60/49.85  thf('116', plain, ((v4_lattice3 @ sk_A)),
% 49.60/49.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.60/49.85  thf('117', plain,
% 49.60/49.85      (![X0 : $i]:
% 49.60/49.85         ((v2_struct_0 @ sk_A)
% 49.60/49.85          | (r1_lattices @ sk_A @ sk_B_1 @ (sk_C @ X0 @ sk_A))
% 49.60/49.85          | ~ (r2_hidden @ sk_B_1 @ X0))),
% 49.60/49.85      inference('demod', [status(thm)], ['114', '115', '116'])).
% 49.60/49.85  thf('118', plain, (~ (v2_struct_0 @ sk_A)),
% 49.60/49.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.60/49.85  thf('119', plain,
% 49.60/49.85      (![X0 : $i]:
% 49.60/49.85         (~ (r2_hidden @ sk_B_1 @ X0)
% 49.60/49.85          | (r1_lattices @ sk_A @ sk_B_1 @ (sk_C @ X0 @ sk_A)))),
% 49.60/49.85      inference('clc', [status(thm)], ['117', '118'])).
% 49.60/49.85  thf('120', plain,
% 49.60/49.85      ((r1_lattices @ sk_A @ sk_B_1 @ 
% 49.60/49.85        (sk_C @ (a_2_9_lattice3 @ sk_A @ sk_C_1) @ sk_A))),
% 49.60/49.85      inference('sup-', [status(thm)], ['111', '119'])).
% 49.60/49.85  thf('121', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 49.60/49.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.60/49.85  thf('122', plain,
% 49.60/49.85      (![X1 : $i, X2 : $i, X3 : $i]:
% 49.60/49.85         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 49.60/49.85          | ~ (l3_lattices @ X2)
% 49.60/49.85          | ~ (v9_lattices @ X2)
% 49.60/49.85          | ~ (v8_lattices @ X2)
% 49.60/49.85          | ~ (v6_lattices @ X2)
% 49.60/49.85          | (v2_struct_0 @ X2)
% 49.60/49.85          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 49.60/49.85          | (r3_lattices @ X2 @ X1 @ X3)
% 49.60/49.85          | ~ (r1_lattices @ X2 @ X1 @ X3))),
% 49.60/49.85      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 49.60/49.85  thf('123', plain,
% 49.60/49.85      (![X0 : $i]:
% 49.60/49.85         (~ (r1_lattices @ sk_A @ sk_B_1 @ X0)
% 49.60/49.85          | (r3_lattices @ sk_A @ sk_B_1 @ X0)
% 49.60/49.85          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 49.60/49.85          | (v2_struct_0 @ sk_A)
% 49.60/49.85          | ~ (v6_lattices @ sk_A)
% 49.60/49.85          | ~ (v8_lattices @ sk_A)
% 49.60/49.85          | ~ (v9_lattices @ sk_A)
% 49.60/49.85          | ~ (l3_lattices @ sk_A))),
% 49.60/49.85      inference('sup-', [status(thm)], ['121', '122'])).
% 49.60/49.85  thf(cc1_lattices, axiom,
% 49.60/49.85    (![A:$i]:
% 49.60/49.85     ( ( l3_lattices @ A ) =>
% 49.60/49.85       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 49.60/49.85         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 49.60/49.85           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 49.60/49.85           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 49.60/49.85  thf('124', plain,
% 49.60/49.85      (![X0 : $i]:
% 49.60/49.85         ((v2_struct_0 @ X0)
% 49.60/49.85          | ~ (v10_lattices @ X0)
% 49.60/49.85          | (v6_lattices @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0))),
% 49.60/49.85      inference('cnf', [status(esa)], [cc1_lattices])).
% 49.60/49.85  thf('125', plain, (~ (v2_struct_0 @ sk_A)),
% 49.60/49.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.60/49.85  thf('126', plain,
% 49.60/49.85      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 49.60/49.85      inference('sup-', [status(thm)], ['124', '125'])).
% 49.60/49.85  thf('127', plain, ((l3_lattices @ sk_A)),
% 49.60/49.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.60/49.85  thf('128', plain, ((v10_lattices @ sk_A)),
% 49.60/49.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.60/49.85  thf('129', plain, ((v6_lattices @ sk_A)),
% 49.60/49.85      inference('demod', [status(thm)], ['126', '127', '128'])).
% 49.60/49.85  thf('130', plain,
% 49.60/49.85      (![X0 : $i]:
% 49.60/49.85         ((v2_struct_0 @ X0)
% 49.60/49.85          | ~ (v10_lattices @ X0)
% 49.60/49.85          | (v8_lattices @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0))),
% 49.60/49.85      inference('cnf', [status(esa)], [cc1_lattices])).
% 49.60/49.85  thf('131', plain, (~ (v2_struct_0 @ sk_A)),
% 49.60/49.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.60/49.85  thf('132', plain,
% 49.60/49.85      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 49.60/49.85      inference('sup-', [status(thm)], ['130', '131'])).
% 49.60/49.85  thf('133', plain, ((l3_lattices @ sk_A)),
% 49.60/49.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.60/49.85  thf('134', plain, ((v10_lattices @ sk_A)),
% 49.60/49.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.60/49.85  thf('135', plain, ((v8_lattices @ sk_A)),
% 49.60/49.85      inference('demod', [status(thm)], ['132', '133', '134'])).
% 49.60/49.85  thf('136', plain,
% 49.60/49.85      (![X0 : $i]:
% 49.60/49.85         ((v2_struct_0 @ X0)
% 49.60/49.85          | ~ (v10_lattices @ X0)
% 49.60/49.85          | (v9_lattices @ X0)
% 49.60/49.85          | ~ (l3_lattices @ X0))),
% 49.60/49.85      inference('cnf', [status(esa)], [cc1_lattices])).
% 49.60/49.85  thf('137', plain, (~ (v2_struct_0 @ sk_A)),
% 49.60/49.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.60/49.85  thf('138', plain,
% 49.60/49.85      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 49.60/49.85      inference('sup-', [status(thm)], ['136', '137'])).
% 49.60/49.85  thf('139', plain, ((l3_lattices @ sk_A)),
% 49.60/49.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.60/49.85  thf('140', plain, ((v10_lattices @ sk_A)),
% 49.60/49.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.60/49.85  thf('141', plain, ((v9_lattices @ sk_A)),
% 49.60/49.85      inference('demod', [status(thm)], ['138', '139', '140'])).
% 49.60/49.85  thf('142', plain, ((l3_lattices @ sk_A)),
% 49.60/49.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.60/49.85  thf('143', plain,
% 49.60/49.85      (![X0 : $i]:
% 49.60/49.85         (~ (r1_lattices @ sk_A @ sk_B_1 @ X0)
% 49.60/49.85          | (r3_lattices @ sk_A @ sk_B_1 @ X0)
% 49.60/49.85          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 49.60/49.85          | (v2_struct_0 @ sk_A))),
% 49.60/49.85      inference('demod', [status(thm)], ['123', '129', '135', '141', '142'])).
% 49.60/49.85  thf('144', plain,
% 49.60/49.86      (((v2_struct_0 @ sk_A)
% 49.60/49.86        | ~ (m1_subset_1 @ (sk_C @ (a_2_9_lattice3 @ sk_A @ sk_C_1) @ sk_A) @ 
% 49.60/49.86             (u1_struct_0 @ sk_A))
% 49.60/49.86        | (r3_lattices @ sk_A @ sk_B_1 @ 
% 49.60/49.86           (sk_C @ (a_2_9_lattice3 @ sk_A @ sk_C_1) @ sk_A)))),
% 49.60/49.86      inference('sup-', [status(thm)], ['120', '143'])).
% 49.60/49.86  thf('145', plain, (~ (v2_struct_0 @ sk_A)),
% 49.60/49.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.60/49.86  thf('146', plain,
% 49.60/49.86      (((r3_lattices @ sk_A @ sk_B_1 @ 
% 49.60/49.86         (sk_C @ (a_2_9_lattice3 @ sk_A @ sk_C_1) @ sk_A))
% 49.60/49.86        | ~ (m1_subset_1 @ (sk_C @ (a_2_9_lattice3 @ sk_A @ sk_C_1) @ sk_A) @ 
% 49.60/49.86             (u1_struct_0 @ sk_A)))),
% 49.60/49.86      inference('clc', [status(thm)], ['144', '145'])).
% 49.60/49.86  thf('147', plain,
% 49.60/49.86      (((v2_struct_0 @ sk_A)
% 49.60/49.86        | ~ (l3_lattices @ sk_A)
% 49.60/49.86        | ~ (v4_lattice3 @ sk_A)
% 49.60/49.86        | (r3_lattices @ sk_A @ sk_B_1 @ 
% 49.60/49.86           (sk_C @ (a_2_9_lattice3 @ sk_A @ sk_C_1) @ sk_A)))),
% 49.60/49.86      inference('sup-', [status(thm)], ['100', '146'])).
% 49.60/49.86  thf('148', plain, ((l3_lattices @ sk_A)),
% 49.60/49.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.60/49.86  thf('149', plain, ((v4_lattice3 @ sk_A)),
% 49.60/49.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.60/49.86  thf('150', plain,
% 49.60/49.86      (((v2_struct_0 @ sk_A)
% 49.60/49.86        | (r3_lattices @ sk_A @ sk_B_1 @ 
% 49.60/49.86           (sk_C @ (a_2_9_lattice3 @ sk_A @ sk_C_1) @ sk_A)))),
% 49.60/49.86      inference('demod', [status(thm)], ['147', '148', '149'])).
% 49.60/49.86  thf('151', plain, (~ (v2_struct_0 @ sk_A)),
% 49.60/49.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.60/49.86  thf('152', plain,
% 49.60/49.86      ((r3_lattices @ sk_A @ sk_B_1 @ 
% 49.60/49.86        (sk_C @ (a_2_9_lattice3 @ sk_A @ sk_C_1) @ sk_A))),
% 49.60/49.86      inference('clc', [status(thm)], ['150', '151'])).
% 49.60/49.86  thf('153', plain,
% 49.60/49.86      (((r3_lattices @ sk_A @ sk_B_1 @ (k16_lattice3 @ sk_A @ sk_C_1))
% 49.60/49.86        | (v2_struct_0 @ sk_A)
% 49.60/49.86        | ~ (l3_lattices @ sk_A)
% 49.60/49.86        | ~ (v4_lattice3 @ sk_A)
% 49.60/49.86        | ~ (v10_lattices @ sk_A)
% 49.60/49.86        | ~ (v6_lattices @ sk_A)
% 49.60/49.86        | ~ (v8_lattices @ sk_A)
% 49.60/49.86        | ~ (v9_lattices @ sk_A))),
% 49.60/49.86      inference('sup+', [status(thm)], ['99', '152'])).
% 49.60/49.86  thf('154', plain, ((l3_lattices @ sk_A)),
% 49.60/49.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.60/49.86  thf('155', plain, ((v4_lattice3 @ sk_A)),
% 49.60/49.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.60/49.86  thf('156', plain, ((v10_lattices @ sk_A)),
% 49.60/49.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.60/49.86  thf('157', plain, ((v6_lattices @ sk_A)),
% 49.60/49.86      inference('demod', [status(thm)], ['126', '127', '128'])).
% 49.60/49.86  thf('158', plain, ((v8_lattices @ sk_A)),
% 49.60/49.86      inference('demod', [status(thm)], ['132', '133', '134'])).
% 49.60/49.86  thf('159', plain, ((v9_lattices @ sk_A)),
% 49.60/49.86      inference('demod', [status(thm)], ['138', '139', '140'])).
% 49.60/49.86  thf('160', plain,
% 49.60/49.86      (((r3_lattices @ sk_A @ sk_B_1 @ (k16_lattice3 @ sk_A @ sk_C_1))
% 49.60/49.86        | (v2_struct_0 @ sk_A))),
% 49.60/49.86      inference('demod', [status(thm)],
% 49.60/49.86                ['153', '154', '155', '156', '157', '158', '159'])).
% 49.60/49.86  thf('161', plain,
% 49.60/49.86      (~ (r3_lattices @ sk_A @ sk_B_1 @ (k16_lattice3 @ sk_A @ sk_C_1))),
% 49.60/49.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.60/49.86  thf('162', plain, ((v2_struct_0 @ sk_A)),
% 49.60/49.86      inference('clc', [status(thm)], ['160', '161'])).
% 49.60/49.86  thf('163', plain, ($false), inference('demod', [status(thm)], ['0', '162'])).
% 49.60/49.86  
% 49.60/49.86  % SZS output end Refutation
% 49.60/49.86  
% 49.60/49.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
