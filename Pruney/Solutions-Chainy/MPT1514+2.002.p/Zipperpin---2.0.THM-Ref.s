%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DShOa0KOUf

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:34 EST 2020

% Result     : Theorem 6.74s
% Output     : Refutation 6.74s
% Verified   : 
% Statistics : Number of formulae       :  225 ( 715 expanded)
%              Number of leaves         :   34 ( 211 expanded)
%              Depth                    :   47
%              Number of atoms          : 3198 (15524 expanded)
%              Number of equality atoms :   25 (  58 expanded)
%              Maximal formula depth    :   22 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(a_2_6_lattice3_type,type,(
    a_2_6_lattice3: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r4_lattice3_type,type,(
    r4_lattice3: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(a_2_5_lattice3_type,type,(
    a_2_5_lattice3: $i > $i > $i )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t48_lattice3,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v4_lattice3 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i,C: $i] :
          ( ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
             => ~ ( ( r2_hidden @ D @ B )
                  & ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                     => ~ ( ( r3_lattices @ A @ D @ E )
                          & ( r2_hidden @ E @ C ) ) ) ) )
         => ( r3_lattices @ A @ ( k15_lattice3 @ A @ B ) @ ( k15_lattice3 @ A @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v4_lattice3 @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i,C: $i] :
            ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ~ ( ( r2_hidden @ D @ B )
                    & ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                       => ~ ( ( r3_lattices @ A @ D @ E )
                            & ( r2_hidden @ E @ C ) ) ) ) )
           => ( r3_lattices @ A @ ( k15_lattice3 @ A @ B ) @ ( k15_lattice3 @ A @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_lattice3])).

thf('0',plain,(
    ~ ( r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t47_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v4_lattice3 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( ( k16_lattice3 @ A @ B )
            = ( k16_lattice3 @ A @ ( a_2_6_lattice3 @ A @ B ) ) )
          & ( ( k15_lattice3 @ A @ B )
            = ( k15_lattice3 @ A @ ( a_2_5_lattice3 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X20: $i,X22: $i] :
      ( ( ( k15_lattice3 @ X20 @ X22 )
        = ( k15_lattice3 @ X20 @ ( a_2_5_lattice3 @ X20 @ X22 ) ) )
      | ~ ( l3_lattices @ X20 )
      | ~ ( v4_lattice3 @ X20 )
      | ~ ( v10_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t47_lattice3])).

thf('2',plain,(
    ! [X20: $i,X22: $i] :
      ( ( ( k15_lattice3 @ X20 @ X22 )
        = ( k15_lattice3 @ X20 @ ( a_2_5_lattice3 @ X20 @ X22 ) ) )
      | ~ ( l3_lattices @ X20 )
      | ~ ( v4_lattice3 @ X20 )
      | ~ ( v10_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t47_lattice3])).

thf(dt_k15_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l3_lattices @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X13 @ X14 ) @ ( u1_struct_0 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

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

thf('4',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( m1_subset_1 @ ( sk_D @ X8 @ X4 @ X5 ) @ ( u1_struct_0 @ X5 ) )
      | ( r4_lattice3 @ X5 @ X4 @ X8 )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( m1_subset_1 @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X2 @ ( k15_lattice3 @ X1 @ X0 ) @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( r4_lattice3 @ X1 @ ( k15_lattice3 @ X1 @ ( a_2_5_lattice3 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['2','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r4_lattice3 @ X1 @ ( k15_lattice3 @ X1 @ ( a_2_5_lattice3 @ X1 @ X0 ) ) @ X2 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( m1_subset_1 @ ( sk_D @ X2 @ ( k15_lattice3 @ X1 @ X0 ) @ X1 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l3_lattices @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X13 @ X14 ) @ ( u1_struct_0 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('10',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X4 @ X5 ) @ X8 )
      | ( r4_lattice3 @ X5 @ X4 @ X8 )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('14',plain,(
    ! [X23: $i] :
      ( ( r2_hidden @ ( sk_E_1 @ X23 ) @ sk_C )
      | ~ ( r2_hidden @ X23 @ sk_B )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_D @ X1 @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_D @ X1 @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ sk_C )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ sk_C )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_E_1 @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ sk_C )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X20: $i,X22: $i] :
      ( ( ( k15_lattice3 @ X20 @ X22 )
        = ( k15_lattice3 @ X20 @ ( a_2_5_lattice3 @ X20 @ X22 ) ) )
      | ~ ( l3_lattices @ X20 )
      | ~ ( v4_lattice3 @ X20 )
      | ~ ( v10_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t47_lattice3])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('27',plain,(
    ! [X23: $i] :
      ( ( r3_lattices @ sk_A @ X23 @ ( sk_E_1 @ X23 ) )
      | ~ ( r2_hidden @ X23 @ sk_B )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ sk_B )
      | ( r3_lattices @ sk_A @ ( sk_D @ X1 @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( sk_E_1 @ ( sk_D @ X1 @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ sk_B )
      | ( r3_lattices @ sk_A @ ( sk_D @ X1 @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( sk_E_1 @ ( sk_D @ X1 @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( r3_lattices @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( sk_E_1 @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( r3_lattices @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( sk_E_1 @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( sk_E_1 @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( r3_lattices @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( sk_E_1 @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( sk_E_1 @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['24','36'])).

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
      ( ( r3_lattices @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( sk_E_1 @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_B )
      | ( r3_lattices @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( sk_E_1 @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('46',plain,(
    ! [X23: $i] :
      ( ( m1_subset_1 @ ( sk_E_1 @ X23 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X23 @ sk_B )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ sk_B )
      | ( m1_subset_1 @ ( sk_E_1 @ ( sk_D @ X1 @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ sk_B )
      | ( m1_subset_1 @ ( sk_E_1 @ ( sk_D @ X1 @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( m1_subset_1 @ ( sk_E_1 @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( m1_subset_1 @ ( sk_E_1 @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_E_1 @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( m1_subset_1 @ ( sk_E_1 @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf(fraenkel_a_2_5_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( v10_lattices @ B )
        & ( v4_lattice3 @ B )
        & ( l3_lattices @ B ) )
     => ( ( r2_hidden @ A @ ( a_2_5_lattice3 @ B @ C ) )
      <=> ? [D: $i] :
            ( ? [E: $i] :
                ( ( r2_hidden @ E @ C )
                & ( r3_lattices @ B @ D @ E )
                & ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) )
            & ( A = D )
            & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('56',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( l3_lattices @ X15 )
      | ~ ( v4_lattice3 @ X15 )
      | ~ ( v10_lattices @ X15 )
      | ( v2_struct_0 @ X15 )
      | ( r2_hidden @ X17 @ ( a_2_5_lattice3 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X15 ) )
      | ( X17 != X18 )
      | ~ ( r2_hidden @ X19 @ X16 )
      | ~ ( r3_lattices @ X15 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_5_lattice3])).

thf('57',plain,(
    ! [X15: $i,X16: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X15 ) )
      | ~ ( r3_lattices @ X15 @ X18 @ X19 )
      | ~ ( r2_hidden @ X19 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X15 ) )
      | ( r2_hidden @ X18 @ ( a_2_5_lattice3 @ X15 @ X16 ) )
      | ( v2_struct_0 @ X15 )
      | ~ ( v10_lattices @ X15 )
      | ~ ( v4_lattice3 @ X15 )
      | ~ ( l3_lattices @ X15 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X2 @ ( a_2_5_lattice3 @ sk_A @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ ( sk_E_1 @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ X1 )
      | ~ ( r3_lattices @ sk_A @ X2 @ ( sk_E_1 @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X2 @ ( a_2_5_lattice3 @ sk_A @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ ( sk_E_1 @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ X1 )
      | ~ ( r3_lattices @ sk_A @ X2 @ ( sk_E_1 @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['58','59','60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_B )
      | ~ ( r2_hidden @ ( sk_E_1 @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_A ) ) @ X1 )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( a_2_5_lattice3 @ sk_A @ X1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( a_2_5_lattice3 @ sk_A @ X1 ) )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ ( sk_E_1 @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_A ) ) @ X1 )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_B )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( a_2_5_lattice3 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( a_2_5_lattice3 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_B )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_B )
      | ( r2_hidden @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( a_2_5_lattice3 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','66'])).

thf('68',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_B )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_B )
      | ( r2_hidden @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( a_2_5_lattice3 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68','69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( a_2_5_lattice3 @ sk_A @ sk_C ) )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_B )
      | ( r2_hidden @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( a_2_5_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r4_lattice3 @ X1 @ ( k15_lattice3 @ X1 @ ( a_2_5_lattice3 @ X1 @ X0 ) ) @ X2 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( m1_subset_1 @ ( sk_D @ X2 @ ( k15_lattice3 @ X1 @ X0 ) @ X1 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('76',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l3_lattices @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X13 @ X14 ) @ ( u1_struct_0 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

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

thf('77',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v10_lattices @ X9 )
      | ~ ( v4_lattice3 @ X9 )
      | ~ ( l3_lattices @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( X10
       != ( k15_lattice3 @ X9 @ X11 ) )
      | ( r4_lattice3 @ X9 @ X10 @ X11 )
      | ~ ( l3_lattices @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('78',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r4_lattice3 @ X9 @ ( k15_lattice3 @ X9 @ X11 ) @ X11 )
      | ~ ( m1_subset_1 @ ( k15_lattice3 @ X9 @ X11 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( l3_lattices @ X9 )
      | ~ ( v4_lattice3 @ X9 )
      | ~ ( v10_lattices @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['76','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X1 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l3_lattices @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X13 @ X14 ) @ ( u1_struct_0 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('82',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r4_lattice3 @ X5 @ X4 @ X6 )
      | ~ ( r2_hidden @ X7 @ X6 )
      | ( r1_lattices @ X5 @ X7 @ X4 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X3 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ( r1_lattices @ X0 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r1_lattices @ X1 @ X2 @ ( k15_lattice3 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r1_lattices @ X1 @ X2 @ ( k15_lattice3 @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ X1 ) ) @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r1_lattices @ X0 @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X3 ) )
      | ~ ( r2_hidden @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['75','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X3 )
      | ( r1_lattices @ X0 @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X3 ) )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ X1 ) ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_B )
      | ( r1_lattices @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['74','88'])).

thf('90',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_B )
      | ( r1_lattices @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['89','90','91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( r1_lattices @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ sk_C ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_B )
      | ( r1_lattices @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ sk_C ) ) ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_B )
      | ( r2_hidden @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( a_2_5_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('98',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( l3_lattices @ X15 )
      | ~ ( v4_lattice3 @ X15 )
      | ~ ( v10_lattices @ X15 )
      | ( v2_struct_0 @ X15 )
      | ( X17
        = ( sk_D_2 @ X16 @ X15 @ X17 ) )
      | ~ ( r2_hidden @ X17 @ ( a_2_5_lattice3 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_5_lattice3])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_B )
      | ( ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A )
        = ( sk_D_2 @ sk_C @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_B )
      | ( ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A )
        = ( sk_D_2 @ sk_C @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['99','100','101','102'])).

thf('104',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A )
        = ( sk_D_2 @ sk_C @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X20: $i,X22: $i] :
      ( ( ( k15_lattice3 @ X20 @ X22 )
        = ( k15_lattice3 @ X20 @ ( a_2_5_lattice3 @ X20 @ X22 ) ) )
      | ~ ( l3_lattices @ X20 )
      | ~ ( v4_lattice3 @ X20 )
      | ~ ( v10_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t47_lattice3])).

thf('107',plain,(
    ! [X20: $i,X22: $i] :
      ( ( ( k15_lattice3 @ X20 @ X22 )
        = ( k15_lattice3 @ X20 @ ( a_2_5_lattice3 @ X20 @ X22 ) ) )
      | ~ ( l3_lattices @ X20 )
      | ~ ( v4_lattice3 @ X20 )
      | ~ ( v10_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t47_lattice3])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A )
        = ( sk_D_2 @ sk_C @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_A )
        = ( sk_D_2 @ sk_C @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_A )
        = ( sk_D_2 @ sk_C @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['109','110','111','112'])).

thf('114',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) ) @ sk_B )
      | ( ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_A )
        = ( sk_D_2 @ sk_C @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_A )
        = ( sk_D_2 @ sk_C @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['106','115'])).

thf('117',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_A )
        = ( sk_D_2 @ sk_C @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['116','117','118','119'])).

thf('121',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_A )
        = ( sk_D_2 @ sk_C @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_A )
        = ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_B )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['105','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_B )
      | ( ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_A )
        = ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l3_lattices @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X13 @ X14 ) @ ( u1_struct_0 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('126',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r1_lattices @ X5 @ ( sk_D @ X8 @ X4 @ X5 ) @ X4 )
      | ( r4_lattice3 @ X5 @ X4 @ X8 )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_lattices @ X0 @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattices @ X0 @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['124','128'])).

thf('130',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_B )
      | ~ ( r1_lattices @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ X0 ) ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ sk_C ) ) @ sk_B )
    | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['96','134'])).

thf('136',plain,(
    r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ ( a_2_5_lattice3 @ sk_A @ sk_C ) ) @ sk_B ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,
    ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ sk_C ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup+',[status(thm)],['1','136'])).

thf('138',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ sk_C ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['137','138','139','140'])).

thf('142',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ sk_C ) @ sk_B ),
    inference(clc,[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l3_lattices @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X13 @ X14 ) @ ( u1_struct_0 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('145',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l3_lattices @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X13 @ X14 ) @ ( u1_struct_0 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('146',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v10_lattices @ X9 )
      | ~ ( v4_lattice3 @ X9 )
      | ~ ( l3_lattices @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( X10
       != ( k15_lattice3 @ X9 @ X11 ) )
      | ~ ( r4_lattice3 @ X9 @ X12 @ X11 )
      | ( r1_lattices @ X9 @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l3_lattices @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('147',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X9 ) )
      | ( r1_lattices @ X9 @ ( k15_lattice3 @ X9 @ X11 ) @ X12 )
      | ~ ( r4_lattice3 @ X9 @ X12 @ X11 )
      | ~ ( m1_subset_1 @ ( k15_lattice3 @ X9 @ X11 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( l3_lattices @ X9 )
      | ~ ( v4_lattice3 @ X9 )
      | ~ ( v10_lattices @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r4_lattice3 @ X0 @ X2 @ X1 )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['145','147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r4_lattice3 @ X0 @ X2 @ X1 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['144','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ( r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['143','151'])).

thf('153',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['152','153','154','155'])).

thf('157',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l3_lattices @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X13 @ X14 ) @ ( u1_struct_0 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('160',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l3_lattices @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X13 @ X14 ) @ ( u1_struct_0 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

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

thf('161',plain,(
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

thf('162',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['159','163'])).

thf('165',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['164'])).

thf('166',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_C ) )
    | ~ ( v6_lattices @ sk_A )
    | ~ ( v8_lattices @ sk_A )
    | ~ ( v9_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['158','165'])).

thf('167',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('168',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('169',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['170','171','172'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('175',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['176','177','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('181',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['182','183','184'])).

thf('186',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['166','167','173','179','185'])).

thf('187',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['186','187'])).

thf('189',plain,(
    $false ),
    inference(demod,[status(thm)],['0','188'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DShOa0KOUf
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:34:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 6.74/7.01  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.74/7.01  % Solved by: fo/fo7.sh
% 6.74/7.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.74/7.01  % done 3820 iterations in 6.589s
% 6.74/7.01  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.74/7.01  % SZS output start Refutation
% 6.74/7.01  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 6.74/7.01  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 6.74/7.01  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 6.74/7.01  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 6.74/7.01  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 6.74/7.01  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 6.74/7.01  thf(sk_E_1_type, type, sk_E_1: $i > $i).
% 6.74/7.01  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 6.74/7.01  thf(a_2_6_lattice3_type, type, a_2_6_lattice3: $i > $i > $i).
% 6.74/7.01  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.74/7.01  thf(r4_lattice3_type, type, r4_lattice3: $i > $i > $i > $o).
% 6.74/7.01  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.74/7.01  thf(sk_B_type, type, sk_B: $i).
% 6.74/7.01  thf(sk_A_type, type, sk_A: $i).
% 6.74/7.01  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 6.74/7.01  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 6.74/7.01  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 6.74/7.01  thf(sk_C_type, type, sk_C: $i).
% 6.74/7.01  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 6.74/7.01  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 6.74/7.01  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 6.74/7.01  thf(a_2_5_lattice3_type, type, a_2_5_lattice3: $i > $i > $i).
% 6.74/7.01  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 6.74/7.01  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 6.74/7.01  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 6.74/7.01  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 6.74/7.01  thf(t48_lattice3, conjecture,
% 6.74/7.01    (![A:$i]:
% 6.74/7.01     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 6.74/7.01         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 6.74/7.01       ( ![B:$i,C:$i]:
% 6.74/7.01         ( ( ![D:$i]:
% 6.74/7.01             ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 6.74/7.01               ( ~( ( r2_hidden @ D @ B ) & 
% 6.74/7.01                    ( ![E:$i]:
% 6.74/7.01                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 6.74/7.01                        ( ~( ( r3_lattices @ A @ D @ E ) & 
% 6.74/7.01                             ( r2_hidden @ E @ C ) ) ) ) ) ) ) ) ) =>
% 6.74/7.01           ( r3_lattices @
% 6.74/7.01             A @ ( k15_lattice3 @ A @ B ) @ ( k15_lattice3 @ A @ C ) ) ) ) ))).
% 6.74/7.01  thf(zf_stmt_0, negated_conjecture,
% 6.74/7.01    (~( ![A:$i]:
% 6.74/7.01        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 6.74/7.01            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 6.74/7.01          ( ![B:$i,C:$i]:
% 6.74/7.01            ( ( ![D:$i]:
% 6.74/7.01                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 6.74/7.01                  ( ~( ( r2_hidden @ D @ B ) & 
% 6.74/7.01                       ( ![E:$i]:
% 6.74/7.01                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 6.74/7.01                           ( ~( ( r3_lattices @ A @ D @ E ) & 
% 6.74/7.01                                ( r2_hidden @ E @ C ) ) ) ) ) ) ) ) ) =>
% 6.74/7.01              ( r3_lattices @
% 6.74/7.01                A @ ( k15_lattice3 @ A @ B ) @ ( k15_lattice3 @ A @ C ) ) ) ) ) )),
% 6.74/7.01    inference('cnf.neg', [status(esa)], [t48_lattice3])).
% 6.74/7.01  thf('0', plain,
% 6.74/7.01      (~ (r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 6.74/7.01          (k15_lattice3 @ sk_A @ sk_C))),
% 6.74/7.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.01  thf(t47_lattice3, axiom,
% 6.74/7.01    (![A:$i]:
% 6.74/7.01     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 6.74/7.01         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 6.74/7.01       ( ![B:$i]:
% 6.74/7.01         ( ( ( k16_lattice3 @ A @ B ) =
% 6.74/7.01             ( k16_lattice3 @ A @ ( a_2_6_lattice3 @ A @ B ) ) ) & 
% 6.74/7.01           ( ( k15_lattice3 @ A @ B ) =
% 6.74/7.01             ( k15_lattice3 @ A @ ( a_2_5_lattice3 @ A @ B ) ) ) ) ) ))).
% 6.74/7.01  thf('1', plain,
% 6.74/7.01      (![X20 : $i, X22 : $i]:
% 6.74/7.01         (((k15_lattice3 @ X20 @ X22)
% 6.74/7.01            = (k15_lattice3 @ X20 @ (a_2_5_lattice3 @ X20 @ X22)))
% 6.74/7.01          | ~ (l3_lattices @ X20)
% 6.74/7.01          | ~ (v4_lattice3 @ X20)
% 6.74/7.01          | ~ (v10_lattices @ X20)
% 6.74/7.01          | (v2_struct_0 @ X20))),
% 6.74/7.01      inference('cnf', [status(esa)], [t47_lattice3])).
% 6.74/7.01  thf('2', plain,
% 6.74/7.01      (![X20 : $i, X22 : $i]:
% 6.74/7.01         (((k15_lattice3 @ X20 @ X22)
% 6.74/7.01            = (k15_lattice3 @ X20 @ (a_2_5_lattice3 @ X20 @ X22)))
% 6.74/7.01          | ~ (l3_lattices @ X20)
% 6.74/7.01          | ~ (v4_lattice3 @ X20)
% 6.74/7.01          | ~ (v10_lattices @ X20)
% 6.74/7.01          | (v2_struct_0 @ X20))),
% 6.74/7.01      inference('cnf', [status(esa)], [t47_lattice3])).
% 6.74/7.01  thf(dt_k15_lattice3, axiom,
% 6.74/7.01    (![A:$i,B:$i]:
% 6.74/7.01     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 6.74/7.01       ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 6.74/7.01  thf('3', plain,
% 6.74/7.01      (![X13 : $i, X14 : $i]:
% 6.74/7.01         (~ (l3_lattices @ X13)
% 6.74/7.01          | (v2_struct_0 @ X13)
% 6.74/7.01          | (m1_subset_1 @ (k15_lattice3 @ X13 @ X14) @ (u1_struct_0 @ X13)))),
% 6.74/7.01      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 6.74/7.01  thf(d17_lattice3, axiom,
% 6.74/7.01    (![A:$i]:
% 6.74/7.01     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 6.74/7.01       ( ![B:$i]:
% 6.74/7.01         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 6.74/7.01           ( ![C:$i]:
% 6.74/7.01             ( ( r4_lattice3 @ A @ B @ C ) <=>
% 6.74/7.01               ( ![D:$i]:
% 6.74/7.01                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 6.74/7.01                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ))).
% 6.74/7.01  thf('4', plain,
% 6.74/7.01      (![X4 : $i, X5 : $i, X8 : $i]:
% 6.74/7.01         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 6.74/7.01          | (m1_subset_1 @ (sk_D @ X8 @ X4 @ X5) @ (u1_struct_0 @ X5))
% 6.74/7.01          | (r4_lattice3 @ X5 @ X4 @ X8)
% 6.74/7.01          | ~ (l3_lattices @ X5)
% 6.74/7.01          | (v2_struct_0 @ X5))),
% 6.74/7.01      inference('cnf', [status(esa)], [d17_lattice3])).
% 6.74/7.01  thf('5', plain,
% 6.74/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.74/7.01         ((v2_struct_0 @ X0)
% 6.74/7.01          | ~ (l3_lattices @ X0)
% 6.74/7.01          | (v2_struct_0 @ X0)
% 6.74/7.01          | ~ (l3_lattices @ X0)
% 6.74/7.01          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 6.74/7.01          | (m1_subset_1 @ (sk_D @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 6.74/7.01             (u1_struct_0 @ X0)))),
% 6.74/7.01      inference('sup-', [status(thm)], ['3', '4'])).
% 6.74/7.01  thf('6', plain,
% 6.74/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.74/7.01         ((m1_subset_1 @ (sk_D @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 6.74/7.01           (u1_struct_0 @ X0))
% 6.74/7.01          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 6.74/7.01          | ~ (l3_lattices @ X0)
% 6.74/7.01          | (v2_struct_0 @ X0))),
% 6.74/7.01      inference('simplify', [status(thm)], ['5'])).
% 6.74/7.01  thf('7', plain,
% 6.74/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.74/7.01         ((m1_subset_1 @ (sk_D @ X2 @ (k15_lattice3 @ X1 @ X0) @ X1) @ 
% 6.74/7.01           (u1_struct_0 @ X1))
% 6.74/7.01          | (v2_struct_0 @ X1)
% 6.74/7.01          | ~ (v10_lattices @ X1)
% 6.74/7.01          | ~ (v4_lattice3 @ X1)
% 6.74/7.01          | ~ (l3_lattices @ X1)
% 6.74/7.01          | (v2_struct_0 @ X1)
% 6.74/7.01          | ~ (l3_lattices @ X1)
% 6.74/7.01          | (r4_lattice3 @ X1 @ 
% 6.74/7.01             (k15_lattice3 @ X1 @ (a_2_5_lattice3 @ X1 @ X0)) @ X2))),
% 6.74/7.01      inference('sup+', [status(thm)], ['2', '6'])).
% 6.74/7.01  thf('8', plain,
% 6.74/7.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.74/7.01         ((r4_lattice3 @ X1 @ 
% 6.74/7.01           (k15_lattice3 @ X1 @ (a_2_5_lattice3 @ X1 @ X0)) @ X2)
% 6.74/7.01          | ~ (l3_lattices @ X1)
% 6.74/7.01          | ~ (v4_lattice3 @ X1)
% 6.74/7.01          | ~ (v10_lattices @ X1)
% 6.74/7.01          | (v2_struct_0 @ X1)
% 6.74/7.01          | (m1_subset_1 @ (sk_D @ X2 @ (k15_lattice3 @ X1 @ X0) @ X1) @ 
% 6.74/7.01             (u1_struct_0 @ X1)))),
% 6.74/7.01      inference('simplify', [status(thm)], ['7'])).
% 6.74/7.01  thf('9', plain,
% 6.74/7.01      (![X13 : $i, X14 : $i]:
% 6.74/7.01         (~ (l3_lattices @ X13)
% 6.74/7.01          | (v2_struct_0 @ X13)
% 6.74/7.01          | (m1_subset_1 @ (k15_lattice3 @ X13 @ X14) @ (u1_struct_0 @ X13)))),
% 6.74/7.01      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 6.74/7.02  thf('10', plain,
% 6.74/7.02      (![X4 : $i, X5 : $i, X8 : $i]:
% 6.74/7.02         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 6.74/7.02          | (r2_hidden @ (sk_D @ X8 @ X4 @ X5) @ X8)
% 6.74/7.02          | (r4_lattice3 @ X5 @ X4 @ X8)
% 6.74/7.02          | ~ (l3_lattices @ X5)
% 6.74/7.02          | (v2_struct_0 @ X5))),
% 6.74/7.02      inference('cnf', [status(esa)], [d17_lattice3])).
% 6.74/7.02  thf('11', plain,
% 6.74/7.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.74/7.02         ((v2_struct_0 @ X0)
% 6.74/7.02          | ~ (l3_lattices @ X0)
% 6.74/7.02          | (v2_struct_0 @ X0)
% 6.74/7.02          | ~ (l3_lattices @ X0)
% 6.74/7.02          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 6.74/7.02          | (r2_hidden @ (sk_D @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X2))),
% 6.74/7.02      inference('sup-', [status(thm)], ['9', '10'])).
% 6.74/7.02  thf('12', plain,
% 6.74/7.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.74/7.02         ((r2_hidden @ (sk_D @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X2)
% 6.74/7.02          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 6.74/7.02          | ~ (l3_lattices @ X0)
% 6.74/7.02          | (v2_struct_0 @ X0))),
% 6.74/7.02      inference('simplify', [status(thm)], ['11'])).
% 6.74/7.02  thf('13', plain,
% 6.74/7.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.74/7.02         ((m1_subset_1 @ (sk_D @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 6.74/7.02           (u1_struct_0 @ X0))
% 6.74/7.02          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 6.74/7.02          | ~ (l3_lattices @ X0)
% 6.74/7.02          | (v2_struct_0 @ X0))),
% 6.74/7.02      inference('simplify', [status(thm)], ['5'])).
% 6.74/7.02  thf('14', plain,
% 6.74/7.02      (![X23 : $i]:
% 6.74/7.02         ((r2_hidden @ (sk_E_1 @ X23) @ sk_C)
% 6.74/7.02          | ~ (r2_hidden @ X23 @ sk_B)
% 6.74/7.02          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ sk_A)))),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('15', plain,
% 6.74/7.02      (![X0 : $i, X1 : $i]:
% 6.74/7.02         ((v2_struct_0 @ sk_A)
% 6.74/7.02          | ~ (l3_lattices @ sk_A)
% 6.74/7.02          | (r4_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ X1)
% 6.74/7.02          | ~ (r2_hidden @ (sk_D @ X1 @ (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 6.74/7.02               sk_B)
% 6.74/7.02          | (r2_hidden @ 
% 6.74/7.02             (sk_E_1 @ (sk_D @ X1 @ (k15_lattice3 @ sk_A @ X0) @ sk_A)) @ sk_C))),
% 6.74/7.02      inference('sup-', [status(thm)], ['13', '14'])).
% 6.74/7.02  thf('16', plain, ((l3_lattices @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('17', plain,
% 6.74/7.02      (![X0 : $i, X1 : $i]:
% 6.74/7.02         ((v2_struct_0 @ sk_A)
% 6.74/7.02          | (r4_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ X1)
% 6.74/7.02          | ~ (r2_hidden @ (sk_D @ X1 @ (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 6.74/7.02               sk_B)
% 6.74/7.02          | (r2_hidden @ 
% 6.74/7.02             (sk_E_1 @ (sk_D @ X1 @ (k15_lattice3 @ sk_A @ X0) @ sk_A)) @ sk_C))),
% 6.74/7.02      inference('demod', [status(thm)], ['15', '16'])).
% 6.74/7.02  thf('18', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         ((v2_struct_0 @ sk_A)
% 6.74/7.02          | ~ (l3_lattices @ sk_A)
% 6.74/7.02          | (r4_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B)
% 6.74/7.02          | (r2_hidden @ 
% 6.74/7.02             (sk_E_1 @ (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A)) @ 
% 6.74/7.02             sk_C)
% 6.74/7.02          | (r4_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B)
% 6.74/7.02          | (v2_struct_0 @ sk_A))),
% 6.74/7.02      inference('sup-', [status(thm)], ['12', '17'])).
% 6.74/7.02  thf('19', plain, ((l3_lattices @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('20', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         ((v2_struct_0 @ sk_A)
% 6.74/7.02          | (r4_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B)
% 6.74/7.02          | (r2_hidden @ 
% 6.74/7.02             (sk_E_1 @ (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A)) @ 
% 6.74/7.02             sk_C)
% 6.74/7.02          | (r4_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B)
% 6.74/7.02          | (v2_struct_0 @ sk_A))),
% 6.74/7.02      inference('demod', [status(thm)], ['18', '19'])).
% 6.74/7.02  thf('21', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         ((r2_hidden @ 
% 6.74/7.02           (sk_E_1 @ (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A)) @ sk_C)
% 6.74/7.02          | (r4_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B)
% 6.74/7.02          | (v2_struct_0 @ sk_A))),
% 6.74/7.02      inference('simplify', [status(thm)], ['20'])).
% 6.74/7.02  thf('22', plain, (~ (v2_struct_0 @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('23', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         ((r4_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B)
% 6.74/7.02          | (r2_hidden @ 
% 6.74/7.02             (sk_E_1 @ (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A)) @ 
% 6.74/7.02             sk_C))),
% 6.74/7.02      inference('clc', [status(thm)], ['21', '22'])).
% 6.74/7.02  thf('24', plain,
% 6.74/7.02      (![X20 : $i, X22 : $i]:
% 6.74/7.02         (((k15_lattice3 @ X20 @ X22)
% 6.74/7.02            = (k15_lattice3 @ X20 @ (a_2_5_lattice3 @ X20 @ X22)))
% 6.74/7.02          | ~ (l3_lattices @ X20)
% 6.74/7.02          | ~ (v4_lattice3 @ X20)
% 6.74/7.02          | ~ (v10_lattices @ X20)
% 6.74/7.02          | (v2_struct_0 @ X20))),
% 6.74/7.02      inference('cnf', [status(esa)], [t47_lattice3])).
% 6.74/7.02  thf('25', plain,
% 6.74/7.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.74/7.02         ((r2_hidden @ (sk_D @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X2)
% 6.74/7.02          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 6.74/7.02          | ~ (l3_lattices @ X0)
% 6.74/7.02          | (v2_struct_0 @ X0))),
% 6.74/7.02      inference('simplify', [status(thm)], ['11'])).
% 6.74/7.02  thf('26', plain,
% 6.74/7.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.74/7.02         ((m1_subset_1 @ (sk_D @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 6.74/7.02           (u1_struct_0 @ X0))
% 6.74/7.02          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 6.74/7.02          | ~ (l3_lattices @ X0)
% 6.74/7.02          | (v2_struct_0 @ X0))),
% 6.74/7.02      inference('simplify', [status(thm)], ['5'])).
% 6.74/7.02  thf('27', plain,
% 6.74/7.02      (![X23 : $i]:
% 6.74/7.02         ((r3_lattices @ sk_A @ X23 @ (sk_E_1 @ X23))
% 6.74/7.02          | ~ (r2_hidden @ X23 @ sk_B)
% 6.74/7.02          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ sk_A)))),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('28', plain,
% 6.74/7.02      (![X0 : $i, X1 : $i]:
% 6.74/7.02         ((v2_struct_0 @ sk_A)
% 6.74/7.02          | ~ (l3_lattices @ sk_A)
% 6.74/7.02          | (r4_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ X1)
% 6.74/7.02          | ~ (r2_hidden @ (sk_D @ X1 @ (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 6.74/7.02               sk_B)
% 6.74/7.02          | (r3_lattices @ sk_A @ 
% 6.74/7.02             (sk_D @ X1 @ (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 6.74/7.02             (sk_E_1 @ (sk_D @ X1 @ (k15_lattice3 @ sk_A @ X0) @ sk_A))))),
% 6.74/7.02      inference('sup-', [status(thm)], ['26', '27'])).
% 6.74/7.02  thf('29', plain, ((l3_lattices @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('30', plain,
% 6.74/7.02      (![X0 : $i, X1 : $i]:
% 6.74/7.02         ((v2_struct_0 @ sk_A)
% 6.74/7.02          | (r4_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ X1)
% 6.74/7.02          | ~ (r2_hidden @ (sk_D @ X1 @ (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 6.74/7.02               sk_B)
% 6.74/7.02          | (r3_lattices @ sk_A @ 
% 6.74/7.02             (sk_D @ X1 @ (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 6.74/7.02             (sk_E_1 @ (sk_D @ X1 @ (k15_lattice3 @ sk_A @ X0) @ sk_A))))),
% 6.74/7.02      inference('demod', [status(thm)], ['28', '29'])).
% 6.74/7.02  thf('31', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         ((v2_struct_0 @ sk_A)
% 6.74/7.02          | ~ (l3_lattices @ sk_A)
% 6.74/7.02          | (r4_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B)
% 6.74/7.02          | (r3_lattices @ sk_A @ 
% 6.74/7.02             (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 6.74/7.02             (sk_E_1 @ (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A)))
% 6.74/7.02          | (r4_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B)
% 6.74/7.02          | (v2_struct_0 @ sk_A))),
% 6.74/7.02      inference('sup-', [status(thm)], ['25', '30'])).
% 6.74/7.02  thf('32', plain, ((l3_lattices @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('33', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         ((v2_struct_0 @ sk_A)
% 6.74/7.02          | (r4_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B)
% 6.74/7.02          | (r3_lattices @ sk_A @ 
% 6.74/7.02             (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 6.74/7.02             (sk_E_1 @ (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A)))
% 6.74/7.02          | (r4_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B)
% 6.74/7.02          | (v2_struct_0 @ sk_A))),
% 6.74/7.02      inference('demod', [status(thm)], ['31', '32'])).
% 6.74/7.02  thf('34', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         ((r3_lattices @ sk_A @ 
% 6.74/7.02           (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 6.74/7.02           (sk_E_1 @ (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A)))
% 6.74/7.02          | (r4_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B)
% 6.74/7.02          | (v2_struct_0 @ sk_A))),
% 6.74/7.02      inference('simplify', [status(thm)], ['33'])).
% 6.74/7.02  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('36', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         ((r4_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B)
% 6.74/7.02          | (r3_lattices @ sk_A @ 
% 6.74/7.02             (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 6.74/7.02             (sk_E_1 @ (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A))))),
% 6.74/7.02      inference('clc', [status(thm)], ['34', '35'])).
% 6.74/7.02  thf('37', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         ((r3_lattices @ sk_A @ 
% 6.74/7.02           (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 6.74/7.02           (sk_E_1 @ 
% 6.74/7.02            (sk_D @ sk_B @ 
% 6.74/7.02             (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_A)))
% 6.74/7.02          | (v2_struct_0 @ sk_A)
% 6.74/7.02          | ~ (v10_lattices @ sk_A)
% 6.74/7.02          | ~ (v4_lattice3 @ sk_A)
% 6.74/7.02          | ~ (l3_lattices @ sk_A)
% 6.74/7.02          | (r4_lattice3 @ sk_A @ 
% 6.74/7.02             (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_B))),
% 6.74/7.02      inference('sup+', [status(thm)], ['24', '36'])).
% 6.74/7.02  thf('38', plain, ((v10_lattices @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('39', plain, ((v4_lattice3 @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('40', plain, ((l3_lattices @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('41', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         ((r3_lattices @ sk_A @ 
% 6.74/7.02           (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 6.74/7.02           (sk_E_1 @ 
% 6.74/7.02            (sk_D @ sk_B @ 
% 6.74/7.02             (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_A)))
% 6.74/7.02          | (v2_struct_0 @ sk_A)
% 6.74/7.02          | (r4_lattice3 @ sk_A @ 
% 6.74/7.02             (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_B))),
% 6.74/7.02      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 6.74/7.02  thf('42', plain, (~ (v2_struct_0 @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('43', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         ((r4_lattice3 @ sk_A @ 
% 6.74/7.02           (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_B)
% 6.74/7.02          | (r3_lattices @ sk_A @ 
% 6.74/7.02             (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 6.74/7.02             (sk_E_1 @ 
% 6.74/7.02              (sk_D @ sk_B @ 
% 6.74/7.02               (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_A))))),
% 6.74/7.02      inference('clc', [status(thm)], ['41', '42'])).
% 6.74/7.02  thf('44', plain,
% 6.74/7.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.74/7.02         ((r2_hidden @ (sk_D @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X2)
% 6.74/7.02          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 6.74/7.02          | ~ (l3_lattices @ X0)
% 6.74/7.02          | (v2_struct_0 @ X0))),
% 6.74/7.02      inference('simplify', [status(thm)], ['11'])).
% 6.74/7.02  thf('45', plain,
% 6.74/7.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.74/7.02         ((m1_subset_1 @ (sk_D @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 6.74/7.02           (u1_struct_0 @ X0))
% 6.74/7.02          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 6.74/7.02          | ~ (l3_lattices @ X0)
% 6.74/7.02          | (v2_struct_0 @ X0))),
% 6.74/7.02      inference('simplify', [status(thm)], ['5'])).
% 6.74/7.02  thf('46', plain,
% 6.74/7.02      (![X23 : $i]:
% 6.74/7.02         ((m1_subset_1 @ (sk_E_1 @ X23) @ (u1_struct_0 @ sk_A))
% 6.74/7.02          | ~ (r2_hidden @ X23 @ sk_B)
% 6.74/7.02          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ sk_A)))),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('47', plain,
% 6.74/7.02      (![X0 : $i, X1 : $i]:
% 6.74/7.02         ((v2_struct_0 @ sk_A)
% 6.74/7.02          | ~ (l3_lattices @ sk_A)
% 6.74/7.02          | (r4_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ X1)
% 6.74/7.02          | ~ (r2_hidden @ (sk_D @ X1 @ (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 6.74/7.02               sk_B)
% 6.74/7.02          | (m1_subset_1 @ 
% 6.74/7.02             (sk_E_1 @ (sk_D @ X1 @ (k15_lattice3 @ sk_A @ X0) @ sk_A)) @ 
% 6.74/7.02             (u1_struct_0 @ sk_A)))),
% 6.74/7.02      inference('sup-', [status(thm)], ['45', '46'])).
% 6.74/7.02  thf('48', plain, ((l3_lattices @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('49', plain,
% 6.74/7.02      (![X0 : $i, X1 : $i]:
% 6.74/7.02         ((v2_struct_0 @ sk_A)
% 6.74/7.02          | (r4_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ X1)
% 6.74/7.02          | ~ (r2_hidden @ (sk_D @ X1 @ (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 6.74/7.02               sk_B)
% 6.74/7.02          | (m1_subset_1 @ 
% 6.74/7.02             (sk_E_1 @ (sk_D @ X1 @ (k15_lattice3 @ sk_A @ X0) @ sk_A)) @ 
% 6.74/7.02             (u1_struct_0 @ sk_A)))),
% 6.74/7.02      inference('demod', [status(thm)], ['47', '48'])).
% 6.74/7.02  thf('50', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         ((v2_struct_0 @ sk_A)
% 6.74/7.02          | ~ (l3_lattices @ sk_A)
% 6.74/7.02          | (r4_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B)
% 6.74/7.02          | (m1_subset_1 @ 
% 6.74/7.02             (sk_E_1 @ (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A)) @ 
% 6.74/7.02             (u1_struct_0 @ sk_A))
% 6.74/7.02          | (r4_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B)
% 6.74/7.02          | (v2_struct_0 @ sk_A))),
% 6.74/7.02      inference('sup-', [status(thm)], ['44', '49'])).
% 6.74/7.02  thf('51', plain, ((l3_lattices @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('52', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         ((v2_struct_0 @ sk_A)
% 6.74/7.02          | (r4_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B)
% 6.74/7.02          | (m1_subset_1 @ 
% 6.74/7.02             (sk_E_1 @ (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A)) @ 
% 6.74/7.02             (u1_struct_0 @ sk_A))
% 6.74/7.02          | (r4_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B)
% 6.74/7.02          | (v2_struct_0 @ sk_A))),
% 6.74/7.02      inference('demod', [status(thm)], ['50', '51'])).
% 6.74/7.02  thf('53', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         ((m1_subset_1 @ 
% 6.74/7.02           (sk_E_1 @ (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A)) @ 
% 6.74/7.02           (u1_struct_0 @ sk_A))
% 6.74/7.02          | (r4_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B)
% 6.74/7.02          | (v2_struct_0 @ sk_A))),
% 6.74/7.02      inference('simplify', [status(thm)], ['52'])).
% 6.74/7.02  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('55', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         ((r4_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B)
% 6.74/7.02          | (m1_subset_1 @ 
% 6.74/7.02             (sk_E_1 @ (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A)) @ 
% 6.74/7.02             (u1_struct_0 @ sk_A)))),
% 6.74/7.02      inference('clc', [status(thm)], ['53', '54'])).
% 6.74/7.02  thf(fraenkel_a_2_5_lattice3, axiom,
% 6.74/7.02    (![A:$i,B:$i,C:$i]:
% 6.74/7.02     ( ( ( ~( v2_struct_0 @ B ) ) & ( v10_lattices @ B ) & 
% 6.74/7.02         ( v4_lattice3 @ B ) & ( l3_lattices @ B ) ) =>
% 6.74/7.02       ( ( r2_hidden @ A @ ( a_2_5_lattice3 @ B @ C ) ) <=>
% 6.74/7.02         ( ?[D:$i]:
% 6.74/7.02           ( ( ?[E:$i]:
% 6.74/7.02               ( ( r2_hidden @ E @ C ) & ( r3_lattices @ B @ D @ E ) & 
% 6.74/7.02                 ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) & 
% 6.74/7.02             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 6.74/7.02  thf('56', plain,
% 6.74/7.02      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 6.74/7.02         (~ (l3_lattices @ X15)
% 6.74/7.02          | ~ (v4_lattice3 @ X15)
% 6.74/7.02          | ~ (v10_lattices @ X15)
% 6.74/7.02          | (v2_struct_0 @ X15)
% 6.74/7.02          | (r2_hidden @ X17 @ (a_2_5_lattice3 @ X15 @ X16))
% 6.74/7.02          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X15))
% 6.74/7.02          | ((X17) != (X18))
% 6.74/7.02          | ~ (r2_hidden @ X19 @ X16)
% 6.74/7.02          | ~ (r3_lattices @ X15 @ X18 @ X19)
% 6.74/7.02          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X15)))),
% 6.74/7.02      inference('cnf', [status(esa)], [fraenkel_a_2_5_lattice3])).
% 6.74/7.02  thf('57', plain,
% 6.74/7.02      (![X15 : $i, X16 : $i, X18 : $i, X19 : $i]:
% 6.74/7.02         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X15))
% 6.74/7.02          | ~ (r3_lattices @ X15 @ X18 @ X19)
% 6.74/7.02          | ~ (r2_hidden @ X19 @ X16)
% 6.74/7.02          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X15))
% 6.74/7.02          | (r2_hidden @ X18 @ (a_2_5_lattice3 @ X15 @ X16))
% 6.74/7.02          | (v2_struct_0 @ X15)
% 6.74/7.02          | ~ (v10_lattices @ X15)
% 6.74/7.02          | ~ (v4_lattice3 @ X15)
% 6.74/7.02          | ~ (l3_lattices @ X15))),
% 6.74/7.02      inference('simplify', [status(thm)], ['56'])).
% 6.74/7.02  thf('58', plain,
% 6.74/7.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.74/7.02         ((r4_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B)
% 6.74/7.02          | ~ (l3_lattices @ sk_A)
% 6.74/7.02          | ~ (v4_lattice3 @ sk_A)
% 6.74/7.02          | ~ (v10_lattices @ sk_A)
% 6.74/7.02          | (v2_struct_0 @ sk_A)
% 6.74/7.02          | (r2_hidden @ X2 @ (a_2_5_lattice3 @ sk_A @ X1))
% 6.74/7.02          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_A))
% 6.74/7.02          | ~ (r2_hidden @ 
% 6.74/7.02               (sk_E_1 @ (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A)) @ 
% 6.74/7.02               X1)
% 6.74/7.02          | ~ (r3_lattices @ sk_A @ X2 @ 
% 6.74/7.02               (sk_E_1 @ (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A))))),
% 6.74/7.02      inference('sup-', [status(thm)], ['55', '57'])).
% 6.74/7.02  thf('59', plain, ((l3_lattices @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('60', plain, ((v4_lattice3 @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('61', plain, ((v10_lattices @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('62', plain,
% 6.74/7.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.74/7.02         ((r4_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B)
% 6.74/7.02          | (v2_struct_0 @ sk_A)
% 6.74/7.02          | (r2_hidden @ X2 @ (a_2_5_lattice3 @ sk_A @ X1))
% 6.74/7.02          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_A))
% 6.74/7.02          | ~ (r2_hidden @ 
% 6.74/7.02               (sk_E_1 @ (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A)) @ 
% 6.74/7.02               X1)
% 6.74/7.02          | ~ (r3_lattices @ sk_A @ X2 @ 
% 6.74/7.02               (sk_E_1 @ (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A))))),
% 6.74/7.02      inference('demod', [status(thm)], ['58', '59', '60', '61'])).
% 6.74/7.02  thf('63', plain,
% 6.74/7.02      (![X0 : $i, X1 : $i]:
% 6.74/7.02         ((r4_lattice3 @ sk_A @ 
% 6.74/7.02           (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_B)
% 6.74/7.02          | ~ (r2_hidden @ 
% 6.74/7.02               (sk_E_1 @ 
% 6.74/7.02                (sk_D @ sk_B @ 
% 6.74/7.02                 (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_A)) @ 
% 6.74/7.02               X1)
% 6.74/7.02          | ~ (m1_subset_1 @ 
% 6.74/7.02               (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 6.74/7.02               (u1_struct_0 @ sk_A))
% 6.74/7.02          | (r2_hidden @ (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 6.74/7.02             (a_2_5_lattice3 @ sk_A @ X1))
% 6.74/7.02          | (v2_struct_0 @ sk_A)
% 6.74/7.02          | (r4_lattice3 @ sk_A @ 
% 6.74/7.02             (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_B))),
% 6.74/7.02      inference('sup-', [status(thm)], ['43', '62'])).
% 6.74/7.02  thf('64', plain,
% 6.74/7.02      (![X0 : $i, X1 : $i]:
% 6.74/7.02         ((v2_struct_0 @ sk_A)
% 6.74/7.02          | (r2_hidden @ (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 6.74/7.02             (a_2_5_lattice3 @ sk_A @ X1))
% 6.74/7.02          | ~ (m1_subset_1 @ 
% 6.74/7.02               (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 6.74/7.02               (u1_struct_0 @ sk_A))
% 6.74/7.02          | ~ (r2_hidden @ 
% 6.74/7.02               (sk_E_1 @ 
% 6.74/7.02                (sk_D @ sk_B @ 
% 6.74/7.02                 (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_A)) @ 
% 6.74/7.02               X1)
% 6.74/7.02          | (r4_lattice3 @ sk_A @ 
% 6.74/7.02             (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_B))),
% 6.74/7.02      inference('simplify', [status(thm)], ['63'])).
% 6.74/7.02  thf('65', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         ((r4_lattice3 @ sk_A @ 
% 6.74/7.02           (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_B)
% 6.74/7.02          | (r4_lattice3 @ sk_A @ 
% 6.74/7.02             (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_B)
% 6.74/7.02          | ~ (m1_subset_1 @ 
% 6.74/7.02               (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 6.74/7.02               (u1_struct_0 @ sk_A))
% 6.74/7.02          | (r2_hidden @ (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 6.74/7.02             (a_2_5_lattice3 @ sk_A @ sk_C))
% 6.74/7.02          | (v2_struct_0 @ sk_A))),
% 6.74/7.02      inference('sup-', [status(thm)], ['23', '64'])).
% 6.74/7.02  thf('66', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         ((v2_struct_0 @ sk_A)
% 6.74/7.02          | (r2_hidden @ (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 6.74/7.02             (a_2_5_lattice3 @ sk_A @ sk_C))
% 6.74/7.02          | ~ (m1_subset_1 @ 
% 6.74/7.02               (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 6.74/7.02               (u1_struct_0 @ sk_A))
% 6.74/7.02          | (r4_lattice3 @ sk_A @ 
% 6.74/7.02             (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_B))),
% 6.74/7.02      inference('simplify', [status(thm)], ['65'])).
% 6.74/7.02  thf('67', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         ((v2_struct_0 @ sk_A)
% 6.74/7.02          | ~ (v10_lattices @ sk_A)
% 6.74/7.02          | ~ (v4_lattice3 @ sk_A)
% 6.74/7.02          | ~ (l3_lattices @ sk_A)
% 6.74/7.02          | (r4_lattice3 @ sk_A @ 
% 6.74/7.02             (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_B)
% 6.74/7.02          | (r4_lattice3 @ sk_A @ 
% 6.74/7.02             (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_B)
% 6.74/7.02          | (r2_hidden @ (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 6.74/7.02             (a_2_5_lattice3 @ sk_A @ sk_C))
% 6.74/7.02          | (v2_struct_0 @ sk_A))),
% 6.74/7.02      inference('sup-', [status(thm)], ['8', '66'])).
% 6.74/7.02  thf('68', plain, ((v10_lattices @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('69', plain, ((v4_lattice3 @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('70', plain, ((l3_lattices @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('71', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         ((v2_struct_0 @ sk_A)
% 6.74/7.02          | (r4_lattice3 @ sk_A @ 
% 6.74/7.02             (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_B)
% 6.74/7.02          | (r4_lattice3 @ sk_A @ 
% 6.74/7.02             (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_B)
% 6.74/7.02          | (r2_hidden @ (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 6.74/7.02             (a_2_5_lattice3 @ sk_A @ sk_C))
% 6.74/7.02          | (v2_struct_0 @ sk_A))),
% 6.74/7.02      inference('demod', [status(thm)], ['67', '68', '69', '70'])).
% 6.74/7.02  thf('72', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         ((r2_hidden @ (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 6.74/7.02           (a_2_5_lattice3 @ sk_A @ sk_C))
% 6.74/7.02          | (r4_lattice3 @ sk_A @ 
% 6.74/7.02             (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_B)
% 6.74/7.02          | (v2_struct_0 @ sk_A))),
% 6.74/7.02      inference('simplify', [status(thm)], ['71'])).
% 6.74/7.02  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('74', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         ((r4_lattice3 @ sk_A @ 
% 6.74/7.02           (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_B)
% 6.74/7.02          | (r2_hidden @ (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 6.74/7.02             (a_2_5_lattice3 @ sk_A @ sk_C)))),
% 6.74/7.02      inference('clc', [status(thm)], ['72', '73'])).
% 6.74/7.02  thf('75', plain,
% 6.74/7.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.74/7.02         ((r4_lattice3 @ X1 @ 
% 6.74/7.02           (k15_lattice3 @ X1 @ (a_2_5_lattice3 @ X1 @ X0)) @ X2)
% 6.74/7.02          | ~ (l3_lattices @ X1)
% 6.74/7.02          | ~ (v4_lattice3 @ X1)
% 6.74/7.02          | ~ (v10_lattices @ X1)
% 6.74/7.02          | (v2_struct_0 @ X1)
% 6.74/7.02          | (m1_subset_1 @ (sk_D @ X2 @ (k15_lattice3 @ X1 @ X0) @ X1) @ 
% 6.74/7.02             (u1_struct_0 @ X1)))),
% 6.74/7.02      inference('simplify', [status(thm)], ['7'])).
% 6.74/7.02  thf('76', plain,
% 6.74/7.02      (![X13 : $i, X14 : $i]:
% 6.74/7.02         (~ (l3_lattices @ X13)
% 6.74/7.02          | (v2_struct_0 @ X13)
% 6.74/7.02          | (m1_subset_1 @ (k15_lattice3 @ X13 @ X14) @ (u1_struct_0 @ X13)))),
% 6.74/7.02      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 6.74/7.02  thf(d21_lattice3, axiom,
% 6.74/7.02    (![A:$i]:
% 6.74/7.02     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 6.74/7.02       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 6.74/7.02           ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 6.74/7.02         ( ![B:$i,C:$i]:
% 6.74/7.02           ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 6.74/7.02             ( ( ( C ) = ( k15_lattice3 @ A @ B ) ) <=>
% 6.74/7.02               ( ( r4_lattice3 @ A @ C @ B ) & 
% 6.74/7.02                 ( ![D:$i]:
% 6.74/7.02                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 6.74/7.02                     ( ( r4_lattice3 @ A @ D @ B ) =>
% 6.74/7.02                       ( r1_lattices @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 6.74/7.02  thf('77', plain,
% 6.74/7.02      (![X9 : $i, X10 : $i, X11 : $i]:
% 6.74/7.02         ((v2_struct_0 @ X9)
% 6.74/7.02          | ~ (v10_lattices @ X9)
% 6.74/7.02          | ~ (v4_lattice3 @ X9)
% 6.74/7.02          | ~ (l3_lattices @ X9)
% 6.74/7.02          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 6.74/7.02          | ((X10) != (k15_lattice3 @ X9 @ X11))
% 6.74/7.02          | (r4_lattice3 @ X9 @ X10 @ X11)
% 6.74/7.02          | ~ (l3_lattices @ X9)
% 6.74/7.02          | (v2_struct_0 @ X9))),
% 6.74/7.02      inference('cnf', [status(esa)], [d21_lattice3])).
% 6.74/7.02  thf('78', plain,
% 6.74/7.02      (![X9 : $i, X11 : $i]:
% 6.74/7.02         ((r4_lattice3 @ X9 @ (k15_lattice3 @ X9 @ X11) @ X11)
% 6.74/7.02          | ~ (m1_subset_1 @ (k15_lattice3 @ X9 @ X11) @ (u1_struct_0 @ X9))
% 6.74/7.02          | ~ (l3_lattices @ X9)
% 6.74/7.02          | ~ (v4_lattice3 @ X9)
% 6.74/7.02          | ~ (v10_lattices @ X9)
% 6.74/7.02          | (v2_struct_0 @ X9))),
% 6.74/7.02      inference('simplify', [status(thm)], ['77'])).
% 6.74/7.02  thf('79', plain,
% 6.74/7.02      (![X0 : $i, X1 : $i]:
% 6.74/7.02         ((v2_struct_0 @ X0)
% 6.74/7.02          | ~ (l3_lattices @ X0)
% 6.74/7.02          | (v2_struct_0 @ X0)
% 6.74/7.02          | ~ (v10_lattices @ X0)
% 6.74/7.02          | ~ (v4_lattice3 @ X0)
% 6.74/7.02          | ~ (l3_lattices @ X0)
% 6.74/7.02          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X1))),
% 6.74/7.02      inference('sup-', [status(thm)], ['76', '78'])).
% 6.74/7.02  thf('80', plain,
% 6.74/7.02      (![X0 : $i, X1 : $i]:
% 6.74/7.02         ((r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X1)
% 6.74/7.02          | ~ (v4_lattice3 @ X0)
% 6.74/7.02          | ~ (v10_lattices @ X0)
% 6.74/7.02          | ~ (l3_lattices @ X0)
% 6.74/7.02          | (v2_struct_0 @ X0))),
% 6.74/7.02      inference('simplify', [status(thm)], ['79'])).
% 6.74/7.02  thf('81', plain,
% 6.74/7.02      (![X13 : $i, X14 : $i]:
% 6.74/7.02         (~ (l3_lattices @ X13)
% 6.74/7.02          | (v2_struct_0 @ X13)
% 6.74/7.02          | (m1_subset_1 @ (k15_lattice3 @ X13 @ X14) @ (u1_struct_0 @ X13)))),
% 6.74/7.02      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 6.74/7.02  thf('82', plain,
% 6.74/7.02      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 6.74/7.02         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 6.74/7.02          | ~ (r4_lattice3 @ X5 @ X4 @ X6)
% 6.74/7.02          | ~ (r2_hidden @ X7 @ X6)
% 6.74/7.02          | (r1_lattices @ X5 @ X7 @ X4)
% 6.74/7.02          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X5))
% 6.74/7.02          | ~ (l3_lattices @ X5)
% 6.74/7.02          | (v2_struct_0 @ X5))),
% 6.74/7.02      inference('cnf', [status(esa)], [d17_lattice3])).
% 6.74/7.02  thf('83', plain,
% 6.74/7.02      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.74/7.02         ((v2_struct_0 @ X0)
% 6.74/7.02          | ~ (l3_lattices @ X0)
% 6.74/7.02          | (v2_struct_0 @ X0)
% 6.74/7.02          | ~ (l3_lattices @ X0)
% 6.74/7.02          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 6.74/7.02          | (r1_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))
% 6.74/7.02          | ~ (r2_hidden @ X2 @ X3)
% 6.74/7.02          | ~ (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X3))),
% 6.74/7.02      inference('sup-', [status(thm)], ['81', '82'])).
% 6.74/7.02  thf('84', plain,
% 6.74/7.02      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.74/7.02         (~ (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X3)
% 6.74/7.02          | ~ (r2_hidden @ X2 @ X3)
% 6.74/7.02          | (r1_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))
% 6.74/7.02          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 6.74/7.02          | ~ (l3_lattices @ X0)
% 6.74/7.02          | (v2_struct_0 @ X0))),
% 6.74/7.02      inference('simplify', [status(thm)], ['83'])).
% 6.74/7.02  thf('85', plain,
% 6.74/7.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.74/7.02         ((v2_struct_0 @ X1)
% 6.74/7.02          | ~ (l3_lattices @ X1)
% 6.74/7.02          | ~ (v10_lattices @ X1)
% 6.74/7.02          | ~ (v4_lattice3 @ X1)
% 6.74/7.02          | (v2_struct_0 @ X1)
% 6.74/7.02          | ~ (l3_lattices @ X1)
% 6.74/7.02          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 6.74/7.02          | (r1_lattices @ X1 @ X2 @ (k15_lattice3 @ X1 @ X0))
% 6.74/7.02          | ~ (r2_hidden @ X2 @ X0))),
% 6.74/7.02      inference('sup-', [status(thm)], ['80', '84'])).
% 6.74/7.02  thf('86', plain,
% 6.74/7.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.74/7.02         (~ (r2_hidden @ X2 @ X0)
% 6.74/7.02          | (r1_lattices @ X1 @ X2 @ (k15_lattice3 @ X1 @ X0))
% 6.74/7.02          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 6.74/7.02          | ~ (v4_lattice3 @ X1)
% 6.74/7.02          | ~ (v10_lattices @ X1)
% 6.74/7.02          | ~ (l3_lattices @ X1)
% 6.74/7.02          | (v2_struct_0 @ X1))),
% 6.74/7.02      inference('simplify', [status(thm)], ['85'])).
% 6.74/7.02  thf('87', plain,
% 6.74/7.02      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.74/7.02         ((v2_struct_0 @ X0)
% 6.74/7.02          | ~ (v10_lattices @ X0)
% 6.74/7.02          | ~ (v4_lattice3 @ X0)
% 6.74/7.02          | ~ (l3_lattices @ X0)
% 6.74/7.02          | (r4_lattice3 @ X0 @ 
% 6.74/7.02             (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ X1)) @ X2)
% 6.74/7.02          | (v2_struct_0 @ X0)
% 6.74/7.02          | ~ (l3_lattices @ X0)
% 6.74/7.02          | ~ (v10_lattices @ X0)
% 6.74/7.02          | ~ (v4_lattice3 @ X0)
% 6.74/7.02          | (r1_lattices @ X0 @ (sk_D @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 6.74/7.02             (k15_lattice3 @ X0 @ X3))
% 6.74/7.02          | ~ (r2_hidden @ (sk_D @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X3))),
% 6.74/7.02      inference('sup-', [status(thm)], ['75', '86'])).
% 6.74/7.02  thf('88', plain,
% 6.74/7.02      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.74/7.02         (~ (r2_hidden @ (sk_D @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X3)
% 6.74/7.02          | (r1_lattices @ X0 @ (sk_D @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 6.74/7.02             (k15_lattice3 @ X0 @ X3))
% 6.74/7.02          | (r4_lattice3 @ X0 @ 
% 6.74/7.02             (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ X1)) @ X2)
% 6.74/7.02          | ~ (l3_lattices @ X0)
% 6.74/7.02          | ~ (v4_lattice3 @ X0)
% 6.74/7.02          | ~ (v10_lattices @ X0)
% 6.74/7.02          | (v2_struct_0 @ X0))),
% 6.74/7.02      inference('simplify', [status(thm)], ['87'])).
% 6.74/7.02  thf('89', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         ((r4_lattice3 @ sk_A @ 
% 6.74/7.02           (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_B)
% 6.74/7.02          | (v2_struct_0 @ sk_A)
% 6.74/7.02          | ~ (v10_lattices @ sk_A)
% 6.74/7.02          | ~ (v4_lattice3 @ sk_A)
% 6.74/7.02          | ~ (l3_lattices @ sk_A)
% 6.74/7.02          | (r4_lattice3 @ sk_A @ 
% 6.74/7.02             (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_B)
% 6.74/7.02          | (r1_lattices @ sk_A @ 
% 6.74/7.02             (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 6.74/7.02             (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ sk_C))))),
% 6.74/7.02      inference('sup-', [status(thm)], ['74', '88'])).
% 6.74/7.02  thf('90', plain, ((v10_lattices @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('91', plain, ((v4_lattice3 @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('92', plain, ((l3_lattices @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('93', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         ((r4_lattice3 @ sk_A @ 
% 6.74/7.02           (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_B)
% 6.74/7.02          | (v2_struct_0 @ sk_A)
% 6.74/7.02          | (r4_lattice3 @ sk_A @ 
% 6.74/7.02             (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_B)
% 6.74/7.02          | (r1_lattices @ sk_A @ 
% 6.74/7.02             (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 6.74/7.02             (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ sk_C))))),
% 6.74/7.02      inference('demod', [status(thm)], ['89', '90', '91', '92'])).
% 6.74/7.02  thf('94', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         ((r1_lattices @ sk_A @ 
% 6.74/7.02           (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 6.74/7.02           (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ sk_C)))
% 6.74/7.02          | (v2_struct_0 @ sk_A)
% 6.74/7.02          | (r4_lattice3 @ sk_A @ 
% 6.74/7.02             (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_B))),
% 6.74/7.02      inference('simplify', [status(thm)], ['93'])).
% 6.74/7.02  thf('95', plain, (~ (v2_struct_0 @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('96', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         ((r4_lattice3 @ sk_A @ 
% 6.74/7.02           (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_B)
% 6.74/7.02          | (r1_lattices @ sk_A @ 
% 6.74/7.02             (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 6.74/7.02             (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ sk_C))))),
% 6.74/7.02      inference('clc', [status(thm)], ['94', '95'])).
% 6.74/7.02  thf('97', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         ((r4_lattice3 @ sk_A @ 
% 6.74/7.02           (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_B)
% 6.74/7.02          | (r2_hidden @ (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 6.74/7.02             (a_2_5_lattice3 @ sk_A @ sk_C)))),
% 6.74/7.02      inference('clc', [status(thm)], ['72', '73'])).
% 6.74/7.02  thf('98', plain,
% 6.74/7.02      (![X15 : $i, X16 : $i, X17 : $i]:
% 6.74/7.02         (~ (l3_lattices @ X15)
% 6.74/7.02          | ~ (v4_lattice3 @ X15)
% 6.74/7.02          | ~ (v10_lattices @ X15)
% 6.74/7.02          | (v2_struct_0 @ X15)
% 6.74/7.02          | ((X17) = (sk_D_2 @ X16 @ X15 @ X17))
% 6.74/7.02          | ~ (r2_hidden @ X17 @ (a_2_5_lattice3 @ X15 @ X16)))),
% 6.74/7.02      inference('cnf', [status(esa)], [fraenkel_a_2_5_lattice3])).
% 6.74/7.02  thf('99', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         ((r4_lattice3 @ sk_A @ 
% 6.74/7.02           (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_B)
% 6.74/7.02          | ((sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A)
% 6.74/7.02              = (sk_D_2 @ sk_C @ sk_A @ 
% 6.74/7.02                 (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A)))
% 6.74/7.02          | (v2_struct_0 @ sk_A)
% 6.74/7.02          | ~ (v10_lattices @ sk_A)
% 6.74/7.02          | ~ (v4_lattice3 @ sk_A)
% 6.74/7.02          | ~ (l3_lattices @ sk_A))),
% 6.74/7.02      inference('sup-', [status(thm)], ['97', '98'])).
% 6.74/7.02  thf('100', plain, ((v10_lattices @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('101', plain, ((v4_lattice3 @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('102', plain, ((l3_lattices @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('103', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         ((r4_lattice3 @ sk_A @ 
% 6.74/7.02           (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_B)
% 6.74/7.02          | ((sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A)
% 6.74/7.02              = (sk_D_2 @ sk_C @ sk_A @ 
% 6.74/7.02                 (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A)))
% 6.74/7.02          | (v2_struct_0 @ sk_A))),
% 6.74/7.02      inference('demod', [status(thm)], ['99', '100', '101', '102'])).
% 6.74/7.02  thf('104', plain, (~ (v2_struct_0 @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('105', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         (((sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A)
% 6.74/7.02            = (sk_D_2 @ sk_C @ sk_A @ 
% 6.74/7.02               (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A)))
% 6.74/7.02          | (r4_lattice3 @ sk_A @ 
% 6.74/7.02             (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_B))),
% 6.74/7.02      inference('clc', [status(thm)], ['103', '104'])).
% 6.74/7.02  thf('106', plain,
% 6.74/7.02      (![X20 : $i, X22 : $i]:
% 6.74/7.02         (((k15_lattice3 @ X20 @ X22)
% 6.74/7.02            = (k15_lattice3 @ X20 @ (a_2_5_lattice3 @ X20 @ X22)))
% 6.74/7.02          | ~ (l3_lattices @ X20)
% 6.74/7.02          | ~ (v4_lattice3 @ X20)
% 6.74/7.02          | ~ (v10_lattices @ X20)
% 6.74/7.02          | (v2_struct_0 @ X20))),
% 6.74/7.02      inference('cnf', [status(esa)], [t47_lattice3])).
% 6.74/7.02  thf('107', plain,
% 6.74/7.02      (![X20 : $i, X22 : $i]:
% 6.74/7.02         (((k15_lattice3 @ X20 @ X22)
% 6.74/7.02            = (k15_lattice3 @ X20 @ (a_2_5_lattice3 @ X20 @ X22)))
% 6.74/7.02          | ~ (l3_lattices @ X20)
% 6.74/7.02          | ~ (v4_lattice3 @ X20)
% 6.74/7.02          | ~ (v10_lattices @ X20)
% 6.74/7.02          | (v2_struct_0 @ X20))),
% 6.74/7.02      inference('cnf', [status(esa)], [t47_lattice3])).
% 6.74/7.02  thf('108', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         (((sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A)
% 6.74/7.02            = (sk_D_2 @ sk_C @ sk_A @ 
% 6.74/7.02               (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A)))
% 6.74/7.02          | (r4_lattice3 @ sk_A @ 
% 6.74/7.02             (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_B))),
% 6.74/7.02      inference('clc', [status(thm)], ['103', '104'])).
% 6.74/7.02  thf('109', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         (((sk_D @ sk_B @ 
% 6.74/7.02            (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_A)
% 6.74/7.02            = (sk_D_2 @ sk_C @ sk_A @ 
% 6.74/7.02               (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A)))
% 6.74/7.02          | (v2_struct_0 @ sk_A)
% 6.74/7.02          | ~ (v10_lattices @ sk_A)
% 6.74/7.02          | ~ (v4_lattice3 @ sk_A)
% 6.74/7.02          | ~ (l3_lattices @ sk_A)
% 6.74/7.02          | (r4_lattice3 @ sk_A @ 
% 6.74/7.02             (k15_lattice3 @ sk_A @ 
% 6.74/7.02              (a_2_5_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0))) @ 
% 6.74/7.02             sk_B))),
% 6.74/7.02      inference('sup+', [status(thm)], ['107', '108'])).
% 6.74/7.02  thf('110', plain, ((v10_lattices @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('111', plain, ((v4_lattice3 @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('112', plain, ((l3_lattices @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('113', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         (((sk_D @ sk_B @ 
% 6.74/7.02            (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_A)
% 6.74/7.02            = (sk_D_2 @ sk_C @ sk_A @ 
% 6.74/7.02               (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A)))
% 6.74/7.02          | (v2_struct_0 @ sk_A)
% 6.74/7.02          | (r4_lattice3 @ sk_A @ 
% 6.74/7.02             (k15_lattice3 @ sk_A @ 
% 6.74/7.02              (a_2_5_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0))) @ 
% 6.74/7.02             sk_B))),
% 6.74/7.02      inference('demod', [status(thm)], ['109', '110', '111', '112'])).
% 6.74/7.02  thf('114', plain, (~ (v2_struct_0 @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('115', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         ((r4_lattice3 @ sk_A @ 
% 6.74/7.02           (k15_lattice3 @ sk_A @ 
% 6.74/7.02            (a_2_5_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0))) @ 
% 6.74/7.02           sk_B)
% 6.74/7.02          | ((sk_D @ sk_B @ 
% 6.74/7.02              (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_A)
% 6.74/7.02              = (sk_D_2 @ sk_C @ sk_A @ 
% 6.74/7.02                 (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A))))),
% 6.74/7.02      inference('clc', [status(thm)], ['113', '114'])).
% 6.74/7.02  thf('116', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         ((r4_lattice3 @ sk_A @ 
% 6.74/7.02           (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_B)
% 6.74/7.02          | (v2_struct_0 @ sk_A)
% 6.74/7.02          | ~ (v10_lattices @ sk_A)
% 6.74/7.02          | ~ (v4_lattice3 @ sk_A)
% 6.74/7.02          | ~ (l3_lattices @ sk_A)
% 6.74/7.02          | ((sk_D @ sk_B @ 
% 6.74/7.02              (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_A)
% 6.74/7.02              = (sk_D_2 @ sk_C @ sk_A @ 
% 6.74/7.02                 (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A))))),
% 6.74/7.02      inference('sup+', [status(thm)], ['106', '115'])).
% 6.74/7.02  thf('117', plain, ((v10_lattices @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('118', plain, ((v4_lattice3 @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('119', plain, ((l3_lattices @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('120', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         ((r4_lattice3 @ sk_A @ 
% 6.74/7.02           (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_B)
% 6.74/7.02          | (v2_struct_0 @ sk_A)
% 6.74/7.02          | ((sk_D @ sk_B @ 
% 6.74/7.02              (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_A)
% 6.74/7.02              = (sk_D_2 @ sk_C @ sk_A @ 
% 6.74/7.02                 (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A))))),
% 6.74/7.02      inference('demod', [status(thm)], ['116', '117', '118', '119'])).
% 6.74/7.02  thf('121', plain, (~ (v2_struct_0 @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('122', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         (((sk_D @ sk_B @ 
% 6.74/7.02            (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_A)
% 6.74/7.02            = (sk_D_2 @ sk_C @ sk_A @ 
% 6.74/7.02               (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A)))
% 6.74/7.02          | (r4_lattice3 @ sk_A @ 
% 6.74/7.02             (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_B))),
% 6.74/7.02      inference('clc', [status(thm)], ['120', '121'])).
% 6.74/7.02  thf('123', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         (((sk_D @ sk_B @ 
% 6.74/7.02            (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_A)
% 6.74/7.02            = (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A))
% 6.74/7.02          | (r4_lattice3 @ sk_A @ 
% 6.74/7.02             (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_B)
% 6.74/7.02          | (r4_lattice3 @ sk_A @ 
% 6.74/7.02             (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_B))),
% 6.74/7.02      inference('sup+', [status(thm)], ['105', '122'])).
% 6.74/7.02  thf('124', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         ((r4_lattice3 @ sk_A @ 
% 6.74/7.02           (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_B)
% 6.74/7.02          | ((sk_D @ sk_B @ 
% 6.74/7.02              (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_A)
% 6.74/7.02              = (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A)))),
% 6.74/7.02      inference('simplify', [status(thm)], ['123'])).
% 6.74/7.02  thf('125', plain,
% 6.74/7.02      (![X13 : $i, X14 : $i]:
% 6.74/7.02         (~ (l3_lattices @ X13)
% 6.74/7.02          | (v2_struct_0 @ X13)
% 6.74/7.02          | (m1_subset_1 @ (k15_lattice3 @ X13 @ X14) @ (u1_struct_0 @ X13)))),
% 6.74/7.02      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 6.74/7.02  thf('126', plain,
% 6.74/7.02      (![X4 : $i, X5 : $i, X8 : $i]:
% 6.74/7.02         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 6.74/7.02          | ~ (r1_lattices @ X5 @ (sk_D @ X8 @ X4 @ X5) @ X4)
% 6.74/7.02          | (r4_lattice3 @ X5 @ X4 @ X8)
% 6.74/7.02          | ~ (l3_lattices @ X5)
% 6.74/7.02          | (v2_struct_0 @ X5))),
% 6.74/7.02      inference('cnf', [status(esa)], [d17_lattice3])).
% 6.74/7.02  thf('127', plain,
% 6.74/7.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.74/7.02         ((v2_struct_0 @ X0)
% 6.74/7.02          | ~ (l3_lattices @ X0)
% 6.74/7.02          | (v2_struct_0 @ X0)
% 6.74/7.02          | ~ (l3_lattices @ X0)
% 6.74/7.02          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 6.74/7.02          | ~ (r1_lattices @ X0 @ 
% 6.74/7.02               (sk_D @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 6.74/7.02               (k15_lattice3 @ X0 @ X1)))),
% 6.74/7.02      inference('sup-', [status(thm)], ['125', '126'])).
% 6.74/7.02  thf('128', plain,
% 6.74/7.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.74/7.02         (~ (r1_lattices @ X0 @ (sk_D @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 6.74/7.02             (k15_lattice3 @ X0 @ X1))
% 6.74/7.02          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 6.74/7.02          | ~ (l3_lattices @ X0)
% 6.74/7.02          | (v2_struct_0 @ X0))),
% 6.74/7.02      inference('simplify', [status(thm)], ['127'])).
% 6.74/7.02  thf('129', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         (~ (r1_lattices @ sk_A @ 
% 6.74/7.02             (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 6.74/7.02             (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)))
% 6.74/7.02          | (r4_lattice3 @ sk_A @ 
% 6.74/7.02             (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_B)
% 6.74/7.02          | (v2_struct_0 @ sk_A)
% 6.74/7.02          | ~ (l3_lattices @ sk_A)
% 6.74/7.02          | (r4_lattice3 @ sk_A @ 
% 6.74/7.02             (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_B))),
% 6.74/7.02      inference('sup-', [status(thm)], ['124', '128'])).
% 6.74/7.02  thf('130', plain, ((l3_lattices @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('131', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         (~ (r1_lattices @ sk_A @ 
% 6.74/7.02             (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 6.74/7.02             (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)))
% 6.74/7.02          | (r4_lattice3 @ sk_A @ 
% 6.74/7.02             (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_B)
% 6.74/7.02          | (v2_struct_0 @ sk_A)
% 6.74/7.02          | (r4_lattice3 @ sk_A @ 
% 6.74/7.02             (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_B))),
% 6.74/7.02      inference('demod', [status(thm)], ['129', '130'])).
% 6.74/7.02  thf('132', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         ((v2_struct_0 @ sk_A)
% 6.74/7.02          | (r4_lattice3 @ sk_A @ 
% 6.74/7.02             (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_B)
% 6.74/7.02          | ~ (r1_lattices @ sk_A @ 
% 6.74/7.02               (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 6.74/7.02               (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0))))),
% 6.74/7.02      inference('simplify', [status(thm)], ['131'])).
% 6.74/7.02  thf('133', plain, (~ (v2_struct_0 @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('134', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         (~ (r1_lattices @ sk_A @ 
% 6.74/7.02             (sk_D @ sk_B @ (k15_lattice3 @ sk_A @ X0) @ sk_A) @ 
% 6.74/7.02             (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)))
% 6.74/7.02          | (r4_lattice3 @ sk_A @ 
% 6.74/7.02             (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ X0)) @ sk_B))),
% 6.74/7.02      inference('clc', [status(thm)], ['132', '133'])).
% 6.74/7.02  thf('135', plain,
% 6.74/7.02      (((r4_lattice3 @ sk_A @ 
% 6.74/7.02         (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ sk_C)) @ sk_B)
% 6.74/7.02        | (r4_lattice3 @ sk_A @ 
% 6.74/7.02           (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ sk_C)) @ sk_B))),
% 6.74/7.02      inference('sup-', [status(thm)], ['96', '134'])).
% 6.74/7.02  thf('136', plain,
% 6.74/7.02      ((r4_lattice3 @ sk_A @ 
% 6.74/7.02        (k15_lattice3 @ sk_A @ (a_2_5_lattice3 @ sk_A @ sk_C)) @ sk_B)),
% 6.74/7.02      inference('simplify', [status(thm)], ['135'])).
% 6.74/7.02  thf('137', plain,
% 6.74/7.02      (((r4_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ sk_C) @ sk_B)
% 6.74/7.02        | (v2_struct_0 @ sk_A)
% 6.74/7.02        | ~ (v10_lattices @ sk_A)
% 6.74/7.02        | ~ (v4_lattice3 @ sk_A)
% 6.74/7.02        | ~ (l3_lattices @ sk_A))),
% 6.74/7.02      inference('sup+', [status(thm)], ['1', '136'])).
% 6.74/7.02  thf('138', plain, ((v10_lattices @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('139', plain, ((v4_lattice3 @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('140', plain, ((l3_lattices @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('141', plain,
% 6.74/7.02      (((r4_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ sk_C) @ sk_B)
% 6.74/7.02        | (v2_struct_0 @ sk_A))),
% 6.74/7.02      inference('demod', [status(thm)], ['137', '138', '139', '140'])).
% 6.74/7.02  thf('142', plain, (~ (v2_struct_0 @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('143', plain,
% 6.74/7.02      ((r4_lattice3 @ sk_A @ (k15_lattice3 @ sk_A @ sk_C) @ sk_B)),
% 6.74/7.02      inference('clc', [status(thm)], ['141', '142'])).
% 6.74/7.02  thf('144', plain,
% 6.74/7.02      (![X13 : $i, X14 : $i]:
% 6.74/7.02         (~ (l3_lattices @ X13)
% 6.74/7.02          | (v2_struct_0 @ X13)
% 6.74/7.02          | (m1_subset_1 @ (k15_lattice3 @ X13 @ X14) @ (u1_struct_0 @ X13)))),
% 6.74/7.02      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 6.74/7.02  thf('145', plain,
% 6.74/7.02      (![X13 : $i, X14 : $i]:
% 6.74/7.02         (~ (l3_lattices @ X13)
% 6.74/7.02          | (v2_struct_0 @ X13)
% 6.74/7.02          | (m1_subset_1 @ (k15_lattice3 @ X13 @ X14) @ (u1_struct_0 @ X13)))),
% 6.74/7.02      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 6.74/7.02  thf('146', plain,
% 6.74/7.02      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 6.74/7.02         ((v2_struct_0 @ X9)
% 6.74/7.02          | ~ (v10_lattices @ X9)
% 6.74/7.02          | ~ (v4_lattice3 @ X9)
% 6.74/7.02          | ~ (l3_lattices @ X9)
% 6.74/7.02          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 6.74/7.02          | ((X10) != (k15_lattice3 @ X9 @ X11))
% 6.74/7.02          | ~ (r4_lattice3 @ X9 @ X12 @ X11)
% 6.74/7.02          | (r1_lattices @ X9 @ X10 @ X12)
% 6.74/7.02          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X9))
% 6.74/7.02          | ~ (l3_lattices @ X9)
% 6.74/7.02          | (v2_struct_0 @ X9))),
% 6.74/7.02      inference('cnf', [status(esa)], [d21_lattice3])).
% 6.74/7.02  thf('147', plain,
% 6.74/7.02      (![X9 : $i, X11 : $i, X12 : $i]:
% 6.74/7.02         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X9))
% 6.74/7.02          | (r1_lattices @ X9 @ (k15_lattice3 @ X9 @ X11) @ X12)
% 6.74/7.02          | ~ (r4_lattice3 @ X9 @ X12 @ X11)
% 6.74/7.02          | ~ (m1_subset_1 @ (k15_lattice3 @ X9 @ X11) @ (u1_struct_0 @ X9))
% 6.74/7.02          | ~ (l3_lattices @ X9)
% 6.74/7.02          | ~ (v4_lattice3 @ X9)
% 6.74/7.02          | ~ (v10_lattices @ X9)
% 6.74/7.02          | (v2_struct_0 @ X9))),
% 6.74/7.02      inference('simplify', [status(thm)], ['146'])).
% 6.74/7.02  thf('148', plain,
% 6.74/7.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.74/7.02         ((v2_struct_0 @ X0)
% 6.74/7.02          | ~ (l3_lattices @ X0)
% 6.74/7.02          | (v2_struct_0 @ X0)
% 6.74/7.02          | ~ (v10_lattices @ X0)
% 6.74/7.02          | ~ (v4_lattice3 @ X0)
% 6.74/7.02          | ~ (l3_lattices @ X0)
% 6.74/7.02          | ~ (r4_lattice3 @ X0 @ X2 @ X1)
% 6.74/7.02          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 6.74/7.02          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0)))),
% 6.74/7.02      inference('sup-', [status(thm)], ['145', '147'])).
% 6.74/7.02  thf('149', plain,
% 6.74/7.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.74/7.02         (~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 6.74/7.02          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 6.74/7.02          | ~ (r4_lattice3 @ X0 @ X2 @ X1)
% 6.74/7.02          | ~ (v4_lattice3 @ X0)
% 6.74/7.02          | ~ (v10_lattices @ X0)
% 6.74/7.02          | ~ (l3_lattices @ X0)
% 6.74/7.02          | (v2_struct_0 @ X0))),
% 6.74/7.02      inference('simplify', [status(thm)], ['148'])).
% 6.74/7.02  thf('150', plain,
% 6.74/7.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.74/7.02         ((v2_struct_0 @ X0)
% 6.74/7.02          | ~ (l3_lattices @ X0)
% 6.74/7.02          | (v2_struct_0 @ X0)
% 6.74/7.02          | ~ (l3_lattices @ X0)
% 6.74/7.02          | ~ (v10_lattices @ X0)
% 6.74/7.02          | ~ (v4_lattice3 @ X0)
% 6.74/7.02          | ~ (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 6.74/7.02          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 6.74/7.02             (k15_lattice3 @ X0 @ X1)))),
% 6.74/7.02      inference('sup-', [status(thm)], ['144', '149'])).
% 6.74/7.02  thf('151', plain,
% 6.74/7.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.74/7.02         ((r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 6.74/7.02           (k15_lattice3 @ X0 @ X1))
% 6.74/7.02          | ~ (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 6.74/7.02          | ~ (v4_lattice3 @ X0)
% 6.74/7.02          | ~ (v10_lattices @ X0)
% 6.74/7.02          | ~ (l3_lattices @ X0)
% 6.74/7.02          | (v2_struct_0 @ X0))),
% 6.74/7.02      inference('simplify', [status(thm)], ['150'])).
% 6.74/7.02  thf('152', plain,
% 6.74/7.02      (((v2_struct_0 @ sk_A)
% 6.74/7.02        | ~ (l3_lattices @ sk_A)
% 6.74/7.02        | ~ (v10_lattices @ sk_A)
% 6.74/7.02        | ~ (v4_lattice3 @ sk_A)
% 6.74/7.02        | (r1_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 6.74/7.02           (k15_lattice3 @ sk_A @ sk_C)))),
% 6.74/7.02      inference('sup-', [status(thm)], ['143', '151'])).
% 6.74/7.02  thf('153', plain, ((l3_lattices @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('154', plain, ((v10_lattices @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('155', plain, ((v4_lattice3 @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('156', plain,
% 6.74/7.02      (((v2_struct_0 @ sk_A)
% 6.74/7.02        | (r1_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 6.74/7.02           (k15_lattice3 @ sk_A @ sk_C)))),
% 6.74/7.02      inference('demod', [status(thm)], ['152', '153', '154', '155'])).
% 6.74/7.02  thf('157', plain, (~ (v2_struct_0 @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('158', plain,
% 6.74/7.02      ((r1_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 6.74/7.02        (k15_lattice3 @ sk_A @ sk_C))),
% 6.74/7.02      inference('clc', [status(thm)], ['156', '157'])).
% 6.74/7.02  thf('159', plain,
% 6.74/7.02      (![X13 : $i, X14 : $i]:
% 6.74/7.02         (~ (l3_lattices @ X13)
% 6.74/7.02          | (v2_struct_0 @ X13)
% 6.74/7.02          | (m1_subset_1 @ (k15_lattice3 @ X13 @ X14) @ (u1_struct_0 @ X13)))),
% 6.74/7.02      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 6.74/7.02  thf('160', plain,
% 6.74/7.02      (![X13 : $i, X14 : $i]:
% 6.74/7.02         (~ (l3_lattices @ X13)
% 6.74/7.02          | (v2_struct_0 @ X13)
% 6.74/7.02          | (m1_subset_1 @ (k15_lattice3 @ X13 @ X14) @ (u1_struct_0 @ X13)))),
% 6.74/7.02      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 6.74/7.02  thf(redefinition_r3_lattices, axiom,
% 6.74/7.02    (![A:$i,B:$i,C:$i]:
% 6.74/7.02     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 6.74/7.02         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 6.74/7.02         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 6.74/7.02         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 6.74/7.02       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 6.74/7.02  thf('161', plain,
% 6.74/7.02      (![X1 : $i, X2 : $i, X3 : $i]:
% 6.74/7.02         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 6.74/7.02          | ~ (l3_lattices @ X2)
% 6.74/7.02          | ~ (v9_lattices @ X2)
% 6.74/7.02          | ~ (v8_lattices @ X2)
% 6.74/7.02          | ~ (v6_lattices @ X2)
% 6.74/7.02          | (v2_struct_0 @ X2)
% 6.74/7.02          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 6.74/7.02          | (r3_lattices @ X2 @ X1 @ X3)
% 6.74/7.02          | ~ (r1_lattices @ X2 @ X1 @ X3))),
% 6.74/7.02      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 6.74/7.02  thf('162', plain,
% 6.74/7.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.74/7.02         ((v2_struct_0 @ X0)
% 6.74/7.02          | ~ (l3_lattices @ X0)
% 6.74/7.02          | ~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 6.74/7.02          | (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 6.74/7.02          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 6.74/7.02          | (v2_struct_0 @ X0)
% 6.74/7.02          | ~ (v6_lattices @ X0)
% 6.74/7.02          | ~ (v8_lattices @ X0)
% 6.74/7.02          | ~ (v9_lattices @ X0)
% 6.74/7.02          | ~ (l3_lattices @ X0))),
% 6.74/7.02      inference('sup-', [status(thm)], ['160', '161'])).
% 6.74/7.02  thf('163', plain,
% 6.74/7.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.74/7.02         (~ (v9_lattices @ X0)
% 6.74/7.02          | ~ (v8_lattices @ X0)
% 6.74/7.02          | ~ (v6_lattices @ X0)
% 6.74/7.02          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 6.74/7.02          | (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 6.74/7.02          | ~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 6.74/7.02          | ~ (l3_lattices @ X0)
% 6.74/7.02          | (v2_struct_0 @ X0))),
% 6.74/7.02      inference('simplify', [status(thm)], ['162'])).
% 6.74/7.02  thf('164', plain,
% 6.74/7.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.74/7.02         ((v2_struct_0 @ X0)
% 6.74/7.02          | ~ (l3_lattices @ X0)
% 6.74/7.02          | (v2_struct_0 @ X0)
% 6.74/7.02          | ~ (l3_lattices @ X0)
% 6.74/7.02          | ~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 6.74/7.02               (k15_lattice3 @ X0 @ X1))
% 6.74/7.02          | (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 6.74/7.02             (k15_lattice3 @ X0 @ X1))
% 6.74/7.02          | ~ (v6_lattices @ X0)
% 6.74/7.02          | ~ (v8_lattices @ X0)
% 6.74/7.02          | ~ (v9_lattices @ X0))),
% 6.74/7.02      inference('sup-', [status(thm)], ['159', '163'])).
% 6.74/7.02  thf('165', plain,
% 6.74/7.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.74/7.02         (~ (v9_lattices @ X0)
% 6.74/7.02          | ~ (v8_lattices @ X0)
% 6.74/7.02          | ~ (v6_lattices @ X0)
% 6.74/7.02          | (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 6.74/7.02             (k15_lattice3 @ X0 @ X1))
% 6.74/7.02          | ~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 6.74/7.02               (k15_lattice3 @ X0 @ X1))
% 6.74/7.02          | ~ (l3_lattices @ X0)
% 6.74/7.02          | (v2_struct_0 @ X0))),
% 6.74/7.02      inference('simplify', [status(thm)], ['164'])).
% 6.74/7.02  thf('166', plain,
% 6.74/7.02      (((v2_struct_0 @ sk_A)
% 6.74/7.02        | ~ (l3_lattices @ sk_A)
% 6.74/7.02        | (r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 6.74/7.02           (k15_lattice3 @ sk_A @ sk_C))
% 6.74/7.02        | ~ (v6_lattices @ sk_A)
% 6.74/7.02        | ~ (v8_lattices @ sk_A)
% 6.74/7.02        | ~ (v9_lattices @ sk_A))),
% 6.74/7.02      inference('sup-', [status(thm)], ['158', '165'])).
% 6.74/7.02  thf('167', plain, ((l3_lattices @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf(cc1_lattices, axiom,
% 6.74/7.02    (![A:$i]:
% 6.74/7.02     ( ( l3_lattices @ A ) =>
% 6.74/7.02       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 6.74/7.02         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 6.74/7.02           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 6.74/7.02           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 6.74/7.02  thf('168', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         ((v2_struct_0 @ X0)
% 6.74/7.02          | ~ (v10_lattices @ X0)
% 6.74/7.02          | (v6_lattices @ X0)
% 6.74/7.02          | ~ (l3_lattices @ X0))),
% 6.74/7.02      inference('cnf', [status(esa)], [cc1_lattices])).
% 6.74/7.02  thf('169', plain, (~ (v2_struct_0 @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('170', plain,
% 6.74/7.02      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 6.74/7.02      inference('sup-', [status(thm)], ['168', '169'])).
% 6.74/7.02  thf('171', plain, ((l3_lattices @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('172', plain, ((v10_lattices @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('173', plain, ((v6_lattices @ sk_A)),
% 6.74/7.02      inference('demod', [status(thm)], ['170', '171', '172'])).
% 6.74/7.02  thf('174', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         ((v2_struct_0 @ X0)
% 6.74/7.02          | ~ (v10_lattices @ X0)
% 6.74/7.02          | (v8_lattices @ X0)
% 6.74/7.02          | ~ (l3_lattices @ X0))),
% 6.74/7.02      inference('cnf', [status(esa)], [cc1_lattices])).
% 6.74/7.02  thf('175', plain, (~ (v2_struct_0 @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('176', plain,
% 6.74/7.02      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 6.74/7.02      inference('sup-', [status(thm)], ['174', '175'])).
% 6.74/7.02  thf('177', plain, ((l3_lattices @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('178', plain, ((v10_lattices @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('179', plain, ((v8_lattices @ sk_A)),
% 6.74/7.02      inference('demod', [status(thm)], ['176', '177', '178'])).
% 6.74/7.02  thf('180', plain,
% 6.74/7.02      (![X0 : $i]:
% 6.74/7.02         ((v2_struct_0 @ X0)
% 6.74/7.02          | ~ (v10_lattices @ X0)
% 6.74/7.02          | (v9_lattices @ X0)
% 6.74/7.02          | ~ (l3_lattices @ X0))),
% 6.74/7.02      inference('cnf', [status(esa)], [cc1_lattices])).
% 6.74/7.02  thf('181', plain, (~ (v2_struct_0 @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('182', plain,
% 6.74/7.02      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 6.74/7.02      inference('sup-', [status(thm)], ['180', '181'])).
% 6.74/7.02  thf('183', plain, ((l3_lattices @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('184', plain, ((v10_lattices @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('185', plain, ((v9_lattices @ sk_A)),
% 6.74/7.02      inference('demod', [status(thm)], ['182', '183', '184'])).
% 6.74/7.02  thf('186', plain,
% 6.74/7.02      (((v2_struct_0 @ sk_A)
% 6.74/7.02        | (r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 6.74/7.02           (k15_lattice3 @ sk_A @ sk_C)))),
% 6.74/7.02      inference('demod', [status(thm)], ['166', '167', '173', '179', '185'])).
% 6.74/7.02  thf('187', plain, (~ (v2_struct_0 @ sk_A)),
% 6.74/7.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/7.02  thf('188', plain,
% 6.74/7.02      ((r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 6.74/7.02        (k15_lattice3 @ sk_A @ sk_C))),
% 6.74/7.02      inference('clc', [status(thm)], ['186', '187'])).
% 6.74/7.02  thf('189', plain, ($false), inference('demod', [status(thm)], ['0', '188'])).
% 6.74/7.02  
% 6.74/7.02  % SZS output end Refutation
% 6.74/7.02  
% 6.86/7.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
