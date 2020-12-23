%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NhJ4CPvElp

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:28 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 288 expanded)
%              Number of leaves         :   33 (  96 expanded)
%              Depth                    :   20
%              Number of atoms          : 1994 (4908 expanded)
%              Number of equality atoms :   29 (  31 expanded)
%              Maximal formula depth    :   21 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r3_lattice3_type,type,(
    r3_lattice3: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(r4_lattice3_type,type,(
    r4_lattice3: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i > $i )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t38_lattice3,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v4_lattice3 @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( r2_hidden @ B @ C )
               => ( ( r3_lattices @ A @ B @ ( k15_lattice3 @ A @ C ) )
                  & ( r3_lattices @ A @ ( k16_lattice3 @ A @ C ) @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_lattice3])).

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
      | ( r4_lattice3 @ X15 @ ( sk_C @ X16 @ X15 ) @ X16 )
      | ~ ( l3_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v4_lattice3 @ X15 )
      | ( m1_subset_1 @ ( sk_C @ X16 @ X15 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( l3_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v4_lattice3 @ X15 )
      | ( r4_lattice3 @ X15 @ ( sk_C @ X16 @ X15 ) @ X16 )
      | ~ ( l3_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('4',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v4_lattice3 @ X15 )
      | ( m1_subset_1 @ ( sk_C @ X16 @ X15 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( l3_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

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

thf('5',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v10_lattices @ X18 )
      | ~ ( v4_lattice3 @ X18 )
      | ~ ( l3_lattices @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ~ ( r4_lattice3 @ X18 @ X19 @ X20 )
      | ( r4_lattice3 @ X18 @ ( sk_D_3 @ X19 @ X20 @ X18 ) @ X20 )
      | ( X19
        = ( k15_lattice3 @ X18 @ X20 ) )
      | ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('6',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X19
        = ( k15_lattice3 @ X18 @ X20 ) )
      | ( r4_lattice3 @ X18 @ ( sk_D_3 @ X19 @ X20 @ X18 ) @ X20 )
      | ~ ( r4_lattice3 @ X18 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l3_lattices @ X18 )
      | ~ ( v4_lattice3 @ X18 )
      | ~ ( v10_lattices @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r4_lattice3 @ X0 @ ( sk_D_3 @ ( sk_C @ X1 @ X0 ) @ X2 @ X0 ) @ X2 )
      | ( ( sk_C @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X2 ) )
      | ( r4_lattice3 @ X0 @ ( sk_D_3 @ ( sk_C @ X1 @ X0 ) @ X2 @ X0 ) @ X2 )
      | ~ ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( r4_lattice3 @ X1 @ ( sk_D_3 @ ( sk_C @ X0 @ X1 ) @ X0 @ X1 ) @ X0 )
      | ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) )
      | ( r4_lattice3 @ X1 @ ( sk_D_3 @ ( sk_C @ X0 @ X1 ) @ X0 @ X1 ) @ X0 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v4_lattice3 @ X15 )
      | ( r4_lattice3 @ X15 @ ( sk_C @ X16 @ X15 ) @ X16 )
      | ~ ( l3_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('12',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v4_lattice3 @ X15 )
      | ( m1_subset_1 @ ( sk_C @ X16 @ X15 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( l3_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('13',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v10_lattices @ X18 )
      | ~ ( v4_lattice3 @ X18 )
      | ~ ( l3_lattices @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ~ ( r4_lattice3 @ X18 @ X19 @ X20 )
      | ( m1_subset_1 @ ( sk_D_3 @ X19 @ X20 @ X18 ) @ ( u1_struct_0 @ X18 ) )
      | ( X19
        = ( k15_lattice3 @ X18 @ X20 ) )
      | ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('14',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X19
        = ( k15_lattice3 @ X18 @ X20 ) )
      | ( m1_subset_1 @ ( sk_D_3 @ X19 @ X20 @ X18 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( r4_lattice3 @ X18 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l3_lattices @ X18 )
      | ~ ( v4_lattice3 @ X18 )
      | ~ ( v10_lattices @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( m1_subset_1 @ ( sk_D_3 @ ( sk_C @ X1 @ X0 ) @ X2 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( sk_C @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X2 ) )
      | ( m1_subset_1 @ ( sk_D_3 @ ( sk_C @ X1 @ X0 ) @ X2 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( m1_subset_1 @ ( sk_D_3 @ ( sk_C @ X0 @ X1 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( sk_D_3 @ ( sk_C @ X0 @ X1 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v4_lattice3 @ X15 )
      | ~ ( r4_lattice3 @ X15 @ X17 @ X16 )
      | ( r1_lattices @ X15 @ ( sk_C @ X16 @ X15 ) @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l3_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( ( sk_C @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r1_lattices @ X0 @ ( sk_C @ X2 @ X0 ) @ ( sk_D_3 @ ( sk_C @ X1 @ X0 ) @ X1 @ X0 ) )
      | ~ ( r4_lattice3 @ X0 @ ( sk_D_3 @ ( sk_C @ X1 @ X0 ) @ X1 @ X0 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r4_lattice3 @ X0 @ ( sk_D_3 @ ( sk_C @ X1 @ X0 ) @ X1 @ X0 ) @ X2 )
      | ( r1_lattices @ X0 @ ( sk_C @ X2 @ X0 ) @ ( sk_D_3 @ ( sk_C @ X1 @ X0 ) @ X1 @ X0 ) )
      | ( ( sk_C @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) )
      | ( r1_lattices @ X1 @ ( sk_C @ X0 @ X1 ) @ ( sk_D_3 @ ( sk_C @ X0 @ X1 ) @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['10','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattices @ X1 @ ( sk_C @ X0 @ X1 ) @ ( sk_D_3 @ ( sk_C @ X0 @ X1 ) @ X0 @ X1 ) )
      | ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v10_lattices @ X18 )
      | ~ ( v4_lattice3 @ X18 )
      | ~ ( l3_lattices @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ~ ( r4_lattice3 @ X18 @ X19 @ X20 )
      | ~ ( r1_lattices @ X18 @ X19 @ ( sk_D_3 @ X19 @ X20 @ X18 ) )
      | ( X19
        = ( k15_lattice3 @ X18 @ X20 ) )
      | ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('25',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X19
        = ( k15_lattice3 @ X18 @ X20 ) )
      | ~ ( r1_lattices @ X18 @ X19 @ ( sk_D_3 @ X19 @ X20 @ X18 ) )
      | ~ ( r4_lattice3 @ X18 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l3_lattices @ X18 )
      | ~ ( v4_lattice3 @ X18 )
      | ~ ( v10_lattices @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( ( sk_C @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ ( sk_C @ X1 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ ( sk_C @ X1 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( sk_C @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( ( sk_C @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v4_lattice3 @ X15 )
      | ( m1_subset_1 @ ( sk_C @ X16 @ X15 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( l3_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('33',plain,(
    r2_hidden @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v4_lattice3 @ X15 )
      | ( r4_lattice3 @ X15 @ ( sk_C @ X16 @ X15 ) @ X16 )
      | ~ ( l3_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('36',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v4_lattice3 @ X15 )
      | ( m1_subset_1 @ ( sk_C @ X16 @ X15 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( l3_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

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

thf('37',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( r4_lattice3 @ X10 @ X9 @ X11 )
      | ~ ( r2_hidden @ X12 @ X11 )
      | ( r1_lattices @ X10 @ X12 @ X9 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('38',plain,(
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
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r4_lattice3 @ X0 @ ( sk_C @ X1 @ X0 ) @ X3 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ( r1_lattices @ X0 @ X2 @ ( sk_C @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
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
    inference('sup-',[status(thm)],['35','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r1_lattices @ X1 @ X2 @ ( sk_C @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ( r1_lattices @ sk_A @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) )
      | ~ ( r2_hidden @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','41'])).

thf('43',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_lattices @ sk_A @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) )
      | ~ ( r2_hidden @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B_1 @ X0 )
      | ( r1_lattices @ sk_A @ sk_B_1 @ ( sk_C @ X0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    r1_lattices @ sk_A @ sk_B_1 @ ( sk_C @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('50',plain,(
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

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ sk_B_1 @ X0 )
      | ( r3_lattices @ sk_A @ sk_B_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

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

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ sk_B_1 @ X0 )
      | ( r3_lattices @ sk_A @ sk_B_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','57','63','69','70'])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r3_lattices @ sk_A @ sk_B_1 @ ( sk_C @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( r3_lattices @ sk_A @ sk_B_1 @ ( sk_C @ sk_C_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ( r3_lattices @ sk_A @ sk_B_1 @ ( sk_C @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','74'])).

thf('76',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_lattices @ sk_A @ sk_B_1 @ ( sk_C @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    r3_lattices @ sk_A @ sk_B_1 @ ( sk_C @ sk_C_1 @ sk_A ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( r3_lattices @ sk_A @ sk_B_1 @ ( k15_lattice3 @ sk_A @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup+',[status(thm)],['31','80'])).

thf('82',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( r3_lattices @ sk_A @ sk_B_1 @ ( k15_lattice3 @ sk_A @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('86',plain,
    ( ~ ( r3_lattices @ sk_A @ sk_B_1 @ ( k15_lattice3 @ sk_A @ sk_C_1 ) )
    | ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C_1 ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ~ ( r3_lattices @ sk_A @ sk_B_1 @ ( k15_lattice3 @ sk_A @ sk_C_1 ) )
   <= ~ ( r3_lattices @ sk_A @ sk_B_1 @ ( k15_lattice3 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['86'])).

thf('88',plain,(
    r2_hidden @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k16_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( m1_subset_1 @ ( k16_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('90',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l3_lattices @ X22 )
      | ( v2_struct_0 @ X22 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X22 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

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

thf('91',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) )
      | ( X24
       != ( k16_lattice3 @ X25 @ X26 ) )
      | ( r3_lattice3 @ X25 @ X24 @ X26 )
      | ~ ( l3_lattices @ X25 )
      | ~ ( v4_lattice3 @ X25 )
      | ~ ( v10_lattices @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('92',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v10_lattices @ X25 )
      | ~ ( v4_lattice3 @ X25 )
      | ~ ( l3_lattices @ X25 )
      | ( r3_lattice3 @ X25 @ ( k16_lattice3 @ X25 @ X26 ) @ X26 )
      | ~ ( m1_subset_1 @ ( k16_lattice3 @ X25 @ X26 ) @ ( u1_struct_0 @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l3_lattices @ X22 )
      | ( v2_struct_0 @ X22 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X22 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

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

thf('96',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r3_lattice3 @ X5 @ X4 @ X6 )
      | ~ ( r2_hidden @ X7 @ X6 )
      | ( r1_lattices @ X5 @ X4 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X3 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r1_lattices @ X1 @ ( k16_lattice3 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r1_lattices @ X1 @ ( k16_lattice3 @ X1 @ X0 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B_1 )
      | ~ ( r2_hidden @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','100'])).

thf('102',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B_1 )
      | ~ ( r2_hidden @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['101','102','103','104'])).

thf('106',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B_1 @ X0 )
      | ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,(
    r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['88','107'])).

thf('109',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l3_lattices @ X22 )
      | ( v2_struct_0 @ X22 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X22 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf('111',plain,(
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

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B_1 )
      | ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B_1 )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['109','113'])).

thf('115',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('117',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('118',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B_1 )
      | ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['114','115','116','117','118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B_1 )
      | ~ ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,(
    r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['108','121'])).

thf('123',plain,
    ( ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C_1 ) @ sk_B_1 )
   <= ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C_1 ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['86'])).

thf('124',plain,(
    r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ~ ( r3_lattices @ sk_A @ sk_B_1 @ ( k15_lattice3 @ sk_A @ sk_C_1 ) )
    | ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C_1 ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['86'])).

thf('126',plain,(
    ~ ( r3_lattices @ sk_A @ sk_B_1 @ ( k15_lattice3 @ sk_A @ sk_C_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['124','125'])).

thf('127',plain,(
    ~ ( r3_lattices @ sk_A @ sk_B_1 @ ( k15_lattice3 @ sk_A @ sk_C_1 ) ) ),
    inference(simpl_trail,[status(thm)],['87','126'])).

thf('128',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['85','127'])).

thf('129',plain,(
    $false ),
    inference(demod,[status(thm)],['0','128'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NhJ4CPvElp
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:48:38 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.68/0.91  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.68/0.91  % Solved by: fo/fo7.sh
% 0.68/0.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.91  % done 370 iterations in 0.450s
% 0.68/0.91  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.68/0.91  % SZS output start Refutation
% 0.68/0.91  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.68/0.91  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.91  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 0.68/0.91  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.68/0.91  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.68/0.91  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.68/0.91  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.68/0.91  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.68/0.91  thf(r3_lattice3_type, type, r3_lattice3: $i > $i > $i > $o).
% 0.68/0.91  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.68/0.91  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.68/0.91  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 0.68/0.91  thf(r4_lattice3_type, type, r4_lattice3: $i > $i > $i > $o).
% 0.68/0.91  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.68/0.91  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.68/0.91  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.68/0.91  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.68/0.91  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i > $i).
% 0.68/0.91  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 0.68/0.91  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 0.68/0.91  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.68/0.91  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.68/0.91  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.68/0.91  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.68/0.91  thf(t38_lattice3, conjecture,
% 0.68/0.91    (![A:$i]:
% 0.68/0.91     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.68/0.91         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.68/0.91       ( ![B:$i]:
% 0.68/0.91         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.91           ( ![C:$i]:
% 0.68/0.91             ( ( r2_hidden @ B @ C ) =>
% 0.68/0.91               ( ( r3_lattices @ A @ B @ ( k15_lattice3 @ A @ C ) ) & 
% 0.68/0.91                 ( r3_lattices @ A @ ( k16_lattice3 @ A @ C ) @ B ) ) ) ) ) ) ))).
% 0.68/0.91  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.91    (~( ![A:$i]:
% 0.68/0.91        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.68/0.91            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.68/0.91          ( ![B:$i]:
% 0.68/0.91            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.91              ( ![C:$i]:
% 0.68/0.91                ( ( r2_hidden @ B @ C ) =>
% 0.68/0.91                  ( ( r3_lattices @ A @ B @ ( k15_lattice3 @ A @ C ) ) & 
% 0.68/0.91                    ( r3_lattices @ A @ ( k16_lattice3 @ A @ C ) @ B ) ) ) ) ) ) ) )),
% 0.68/0.91    inference('cnf.neg', [status(esa)], [t38_lattice3])).
% 0.68/0.91  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.91  thf(d18_lattice3, axiom,
% 0.68/0.91    (![A:$i]:
% 0.68/0.91     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.68/0.91       ( ( v4_lattice3 @ A ) <=>
% 0.68/0.91         ( ![B:$i]:
% 0.68/0.91           ( ?[C:$i]:
% 0.68/0.91             ( ( ![D:$i]:
% 0.68/0.91                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.91                   ( ( r4_lattice3 @ A @ D @ B ) => ( r1_lattices @ A @ C @ D ) ) ) ) & 
% 0.68/0.91               ( r4_lattice3 @ A @ C @ B ) & 
% 0.68/0.91               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.68/0.91  thf('1', plain,
% 0.68/0.91      (![X15 : $i, X16 : $i]:
% 0.68/0.92         (~ (v4_lattice3 @ X15)
% 0.68/0.92          | (r4_lattice3 @ X15 @ (sk_C @ X16 @ X15) @ X16)
% 0.68/0.92          | ~ (l3_lattices @ X15)
% 0.68/0.92          | (v2_struct_0 @ X15))),
% 0.68/0.92      inference('cnf', [status(esa)], [d18_lattice3])).
% 0.68/0.92  thf('2', plain,
% 0.68/0.92      (![X15 : $i, X16 : $i]:
% 0.68/0.92         (~ (v4_lattice3 @ X15)
% 0.68/0.92          | (m1_subset_1 @ (sk_C @ X16 @ X15) @ (u1_struct_0 @ X15))
% 0.68/0.92          | ~ (l3_lattices @ X15)
% 0.68/0.92          | (v2_struct_0 @ X15))),
% 0.68/0.92      inference('cnf', [status(esa)], [d18_lattice3])).
% 0.68/0.92  thf('3', plain,
% 0.68/0.92      (![X15 : $i, X16 : $i]:
% 0.68/0.92         (~ (v4_lattice3 @ X15)
% 0.68/0.92          | (r4_lattice3 @ X15 @ (sk_C @ X16 @ X15) @ X16)
% 0.68/0.92          | ~ (l3_lattices @ X15)
% 0.68/0.92          | (v2_struct_0 @ X15))),
% 0.68/0.92      inference('cnf', [status(esa)], [d18_lattice3])).
% 0.68/0.92  thf('4', plain,
% 0.68/0.92      (![X15 : $i, X16 : $i]:
% 0.68/0.92         (~ (v4_lattice3 @ X15)
% 0.68/0.92          | (m1_subset_1 @ (sk_C @ X16 @ X15) @ (u1_struct_0 @ X15))
% 0.68/0.92          | ~ (l3_lattices @ X15)
% 0.68/0.92          | (v2_struct_0 @ X15))),
% 0.68/0.92      inference('cnf', [status(esa)], [d18_lattice3])).
% 0.68/0.92  thf(d21_lattice3, axiom,
% 0.68/0.92    (![A:$i]:
% 0.68/0.92     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.68/0.92       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.68/0.92           ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.68/0.92         ( ![B:$i,C:$i]:
% 0.68/0.92           ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.92             ( ( ( C ) = ( k15_lattice3 @ A @ B ) ) <=>
% 0.68/0.92               ( ( r4_lattice3 @ A @ C @ B ) & 
% 0.68/0.92                 ( ![D:$i]:
% 0.68/0.92                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.92                     ( ( r4_lattice3 @ A @ D @ B ) =>
% 0.68/0.92                       ( r1_lattices @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.68/0.92  thf('5', plain,
% 0.68/0.92      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.68/0.92         ((v2_struct_0 @ X18)
% 0.68/0.92          | ~ (v10_lattices @ X18)
% 0.68/0.92          | ~ (v4_lattice3 @ X18)
% 0.68/0.92          | ~ (l3_lattices @ X18)
% 0.68/0.92          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 0.68/0.92          | ~ (r4_lattice3 @ X18 @ X19 @ X20)
% 0.68/0.92          | (r4_lattice3 @ X18 @ (sk_D_3 @ X19 @ X20 @ X18) @ X20)
% 0.68/0.92          | ((X19) = (k15_lattice3 @ X18 @ X20))
% 0.68/0.92          | ~ (l3_lattices @ X18)
% 0.68/0.92          | (v2_struct_0 @ X18))),
% 0.68/0.92      inference('cnf', [status(esa)], [d21_lattice3])).
% 0.68/0.92  thf('6', plain,
% 0.68/0.92      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.68/0.92         (((X19) = (k15_lattice3 @ X18 @ X20))
% 0.68/0.92          | (r4_lattice3 @ X18 @ (sk_D_3 @ X19 @ X20 @ X18) @ X20)
% 0.68/0.92          | ~ (r4_lattice3 @ X18 @ X19 @ X20)
% 0.68/0.92          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 0.68/0.92          | ~ (l3_lattices @ X18)
% 0.68/0.92          | ~ (v4_lattice3 @ X18)
% 0.68/0.92          | ~ (v10_lattices @ X18)
% 0.68/0.92          | (v2_struct_0 @ X18))),
% 0.68/0.92      inference('simplify', [status(thm)], ['5'])).
% 0.68/0.92  thf('7', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.92         ((v2_struct_0 @ X0)
% 0.68/0.92          | ~ (l3_lattices @ X0)
% 0.68/0.92          | ~ (v4_lattice3 @ X0)
% 0.68/0.92          | (v2_struct_0 @ X0)
% 0.68/0.92          | ~ (v10_lattices @ X0)
% 0.68/0.92          | ~ (v4_lattice3 @ X0)
% 0.68/0.92          | ~ (l3_lattices @ X0)
% 0.68/0.92          | ~ (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 0.68/0.92          | (r4_lattice3 @ X0 @ (sk_D_3 @ (sk_C @ X1 @ X0) @ X2 @ X0) @ X2)
% 0.68/0.92          | ((sk_C @ X1 @ X0) = (k15_lattice3 @ X0 @ X2)))),
% 0.68/0.92      inference('sup-', [status(thm)], ['4', '6'])).
% 0.68/0.92  thf('8', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.92         (((sk_C @ X1 @ X0) = (k15_lattice3 @ X0 @ X2))
% 0.68/0.92          | (r4_lattice3 @ X0 @ (sk_D_3 @ (sk_C @ X1 @ X0) @ X2 @ X0) @ X2)
% 0.68/0.92          | ~ (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 0.68/0.92          | ~ (v10_lattices @ X0)
% 0.68/0.92          | ~ (v4_lattice3 @ X0)
% 0.68/0.92          | ~ (l3_lattices @ X0)
% 0.68/0.92          | (v2_struct_0 @ X0))),
% 0.68/0.92      inference('simplify', [status(thm)], ['7'])).
% 0.68/0.92  thf('9', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((v2_struct_0 @ X1)
% 0.68/0.92          | ~ (l3_lattices @ X1)
% 0.68/0.92          | ~ (v4_lattice3 @ X1)
% 0.68/0.92          | (v2_struct_0 @ X1)
% 0.68/0.92          | ~ (l3_lattices @ X1)
% 0.68/0.92          | ~ (v4_lattice3 @ X1)
% 0.68/0.92          | ~ (v10_lattices @ X1)
% 0.68/0.92          | (r4_lattice3 @ X1 @ (sk_D_3 @ (sk_C @ X0 @ X1) @ X0 @ X1) @ X0)
% 0.68/0.92          | ((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0)))),
% 0.68/0.92      inference('sup-', [status(thm)], ['3', '8'])).
% 0.68/0.92  thf('10', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0))
% 0.68/0.92          | (r4_lattice3 @ X1 @ (sk_D_3 @ (sk_C @ X0 @ X1) @ X0 @ X1) @ X0)
% 0.68/0.92          | ~ (v10_lattices @ X1)
% 0.68/0.92          | ~ (v4_lattice3 @ X1)
% 0.68/0.92          | ~ (l3_lattices @ X1)
% 0.68/0.92          | (v2_struct_0 @ X1))),
% 0.68/0.92      inference('simplify', [status(thm)], ['9'])).
% 0.68/0.92  thf('11', plain,
% 0.68/0.92      (![X15 : $i, X16 : $i]:
% 0.68/0.92         (~ (v4_lattice3 @ X15)
% 0.68/0.92          | (r4_lattice3 @ X15 @ (sk_C @ X16 @ X15) @ X16)
% 0.68/0.92          | ~ (l3_lattices @ X15)
% 0.68/0.92          | (v2_struct_0 @ X15))),
% 0.68/0.92      inference('cnf', [status(esa)], [d18_lattice3])).
% 0.68/0.92  thf('12', plain,
% 0.68/0.92      (![X15 : $i, X16 : $i]:
% 0.68/0.92         (~ (v4_lattice3 @ X15)
% 0.68/0.92          | (m1_subset_1 @ (sk_C @ X16 @ X15) @ (u1_struct_0 @ X15))
% 0.68/0.92          | ~ (l3_lattices @ X15)
% 0.68/0.92          | (v2_struct_0 @ X15))),
% 0.68/0.92      inference('cnf', [status(esa)], [d18_lattice3])).
% 0.68/0.92  thf('13', plain,
% 0.68/0.92      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.68/0.92         ((v2_struct_0 @ X18)
% 0.68/0.92          | ~ (v10_lattices @ X18)
% 0.68/0.92          | ~ (v4_lattice3 @ X18)
% 0.68/0.92          | ~ (l3_lattices @ X18)
% 0.68/0.92          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 0.68/0.92          | ~ (r4_lattice3 @ X18 @ X19 @ X20)
% 0.68/0.92          | (m1_subset_1 @ (sk_D_3 @ X19 @ X20 @ X18) @ (u1_struct_0 @ X18))
% 0.68/0.92          | ((X19) = (k15_lattice3 @ X18 @ X20))
% 0.68/0.92          | ~ (l3_lattices @ X18)
% 0.68/0.92          | (v2_struct_0 @ X18))),
% 0.68/0.92      inference('cnf', [status(esa)], [d21_lattice3])).
% 0.68/0.92  thf('14', plain,
% 0.68/0.92      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.68/0.92         (((X19) = (k15_lattice3 @ X18 @ X20))
% 0.68/0.92          | (m1_subset_1 @ (sk_D_3 @ X19 @ X20 @ X18) @ (u1_struct_0 @ X18))
% 0.68/0.92          | ~ (r4_lattice3 @ X18 @ X19 @ X20)
% 0.68/0.92          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 0.68/0.92          | ~ (l3_lattices @ X18)
% 0.68/0.92          | ~ (v4_lattice3 @ X18)
% 0.68/0.92          | ~ (v10_lattices @ X18)
% 0.68/0.92          | (v2_struct_0 @ X18))),
% 0.68/0.92      inference('simplify', [status(thm)], ['13'])).
% 0.68/0.92  thf('15', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.92         ((v2_struct_0 @ X0)
% 0.68/0.92          | ~ (l3_lattices @ X0)
% 0.68/0.92          | ~ (v4_lattice3 @ X0)
% 0.68/0.92          | (v2_struct_0 @ X0)
% 0.68/0.92          | ~ (v10_lattices @ X0)
% 0.68/0.92          | ~ (v4_lattice3 @ X0)
% 0.68/0.92          | ~ (l3_lattices @ X0)
% 0.68/0.92          | ~ (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 0.68/0.92          | (m1_subset_1 @ (sk_D_3 @ (sk_C @ X1 @ X0) @ X2 @ X0) @ 
% 0.68/0.92             (u1_struct_0 @ X0))
% 0.68/0.92          | ((sk_C @ X1 @ X0) = (k15_lattice3 @ X0 @ X2)))),
% 0.68/0.92      inference('sup-', [status(thm)], ['12', '14'])).
% 0.68/0.92  thf('16', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.92         (((sk_C @ X1 @ X0) = (k15_lattice3 @ X0 @ X2))
% 0.68/0.92          | (m1_subset_1 @ (sk_D_3 @ (sk_C @ X1 @ X0) @ X2 @ X0) @ 
% 0.68/0.92             (u1_struct_0 @ X0))
% 0.68/0.92          | ~ (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 0.68/0.92          | ~ (v10_lattices @ X0)
% 0.68/0.92          | ~ (v4_lattice3 @ X0)
% 0.68/0.92          | ~ (l3_lattices @ X0)
% 0.68/0.92          | (v2_struct_0 @ X0))),
% 0.68/0.92      inference('simplify', [status(thm)], ['15'])).
% 0.68/0.92  thf('17', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((v2_struct_0 @ X1)
% 0.68/0.92          | ~ (l3_lattices @ X1)
% 0.68/0.92          | ~ (v4_lattice3 @ X1)
% 0.68/0.92          | (v2_struct_0 @ X1)
% 0.68/0.92          | ~ (l3_lattices @ X1)
% 0.68/0.92          | ~ (v4_lattice3 @ X1)
% 0.68/0.92          | ~ (v10_lattices @ X1)
% 0.68/0.92          | (m1_subset_1 @ (sk_D_3 @ (sk_C @ X0 @ X1) @ X0 @ X1) @ 
% 0.68/0.92             (u1_struct_0 @ X1))
% 0.68/0.92          | ((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0)))),
% 0.68/0.92      inference('sup-', [status(thm)], ['11', '16'])).
% 0.68/0.92  thf('18', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0))
% 0.68/0.92          | (m1_subset_1 @ (sk_D_3 @ (sk_C @ X0 @ X1) @ X0 @ X1) @ 
% 0.68/0.92             (u1_struct_0 @ X1))
% 0.68/0.92          | ~ (v10_lattices @ X1)
% 0.68/0.92          | ~ (v4_lattice3 @ X1)
% 0.68/0.92          | ~ (l3_lattices @ X1)
% 0.68/0.92          | (v2_struct_0 @ X1))),
% 0.68/0.92      inference('simplify', [status(thm)], ['17'])).
% 0.68/0.92  thf('19', plain,
% 0.68/0.92      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.68/0.92         (~ (v4_lattice3 @ X15)
% 0.68/0.92          | ~ (r4_lattice3 @ X15 @ X17 @ X16)
% 0.68/0.92          | (r1_lattices @ X15 @ (sk_C @ X16 @ X15) @ X17)
% 0.68/0.92          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X15))
% 0.68/0.92          | ~ (l3_lattices @ X15)
% 0.68/0.92          | (v2_struct_0 @ X15))),
% 0.68/0.92      inference('cnf', [status(esa)], [d18_lattice3])).
% 0.68/0.92  thf('20', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.92         ((v2_struct_0 @ X0)
% 0.68/0.92          | ~ (l3_lattices @ X0)
% 0.68/0.92          | ~ (v4_lattice3 @ X0)
% 0.68/0.92          | ~ (v10_lattices @ X0)
% 0.68/0.92          | ((sk_C @ X1 @ X0) = (k15_lattice3 @ X0 @ X1))
% 0.68/0.92          | (v2_struct_0 @ X0)
% 0.68/0.92          | ~ (l3_lattices @ X0)
% 0.68/0.92          | (r1_lattices @ X0 @ (sk_C @ X2 @ X0) @ 
% 0.68/0.92             (sk_D_3 @ (sk_C @ X1 @ X0) @ X1 @ X0))
% 0.68/0.92          | ~ (r4_lattice3 @ X0 @ (sk_D_3 @ (sk_C @ X1 @ X0) @ X1 @ X0) @ X2)
% 0.68/0.92          | ~ (v4_lattice3 @ X0))),
% 0.68/0.92      inference('sup-', [status(thm)], ['18', '19'])).
% 0.68/0.92  thf('21', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.92         (~ (r4_lattice3 @ X0 @ (sk_D_3 @ (sk_C @ X1 @ X0) @ X1 @ X0) @ X2)
% 0.68/0.92          | (r1_lattices @ X0 @ (sk_C @ X2 @ X0) @ 
% 0.68/0.92             (sk_D_3 @ (sk_C @ X1 @ X0) @ X1 @ X0))
% 0.68/0.92          | ((sk_C @ X1 @ X0) = (k15_lattice3 @ X0 @ X1))
% 0.68/0.92          | ~ (v10_lattices @ X0)
% 0.68/0.92          | ~ (v4_lattice3 @ X0)
% 0.68/0.92          | ~ (l3_lattices @ X0)
% 0.68/0.92          | (v2_struct_0 @ X0))),
% 0.68/0.92      inference('simplify', [status(thm)], ['20'])).
% 0.68/0.92  thf('22', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((v2_struct_0 @ X1)
% 0.68/0.92          | ~ (l3_lattices @ X1)
% 0.68/0.92          | ~ (v4_lattice3 @ X1)
% 0.68/0.92          | ~ (v10_lattices @ X1)
% 0.68/0.92          | ((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0))
% 0.68/0.92          | (v2_struct_0 @ X1)
% 0.68/0.92          | ~ (l3_lattices @ X1)
% 0.68/0.92          | ~ (v4_lattice3 @ X1)
% 0.68/0.92          | ~ (v10_lattices @ X1)
% 0.68/0.92          | ((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0))
% 0.68/0.92          | (r1_lattices @ X1 @ (sk_C @ X0 @ X1) @ 
% 0.68/0.92             (sk_D_3 @ (sk_C @ X0 @ X1) @ X0 @ X1)))),
% 0.68/0.92      inference('sup-', [status(thm)], ['10', '21'])).
% 0.68/0.92  thf('23', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((r1_lattices @ X1 @ (sk_C @ X0 @ X1) @ 
% 0.68/0.92           (sk_D_3 @ (sk_C @ X0 @ X1) @ X0 @ X1))
% 0.68/0.92          | ((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0))
% 0.68/0.92          | ~ (v10_lattices @ X1)
% 0.68/0.92          | ~ (v4_lattice3 @ X1)
% 0.68/0.92          | ~ (l3_lattices @ X1)
% 0.68/0.92          | (v2_struct_0 @ X1))),
% 0.68/0.92      inference('simplify', [status(thm)], ['22'])).
% 0.68/0.92  thf('24', plain,
% 0.68/0.92      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.68/0.92         ((v2_struct_0 @ X18)
% 0.68/0.92          | ~ (v10_lattices @ X18)
% 0.68/0.92          | ~ (v4_lattice3 @ X18)
% 0.68/0.92          | ~ (l3_lattices @ X18)
% 0.68/0.92          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 0.68/0.92          | ~ (r4_lattice3 @ X18 @ X19 @ X20)
% 0.68/0.92          | ~ (r1_lattices @ X18 @ X19 @ (sk_D_3 @ X19 @ X20 @ X18))
% 0.68/0.92          | ((X19) = (k15_lattice3 @ X18 @ X20))
% 0.68/0.92          | ~ (l3_lattices @ X18)
% 0.68/0.92          | (v2_struct_0 @ X18))),
% 0.68/0.92      inference('cnf', [status(esa)], [d21_lattice3])).
% 0.68/0.92  thf('25', plain,
% 0.68/0.92      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.68/0.92         (((X19) = (k15_lattice3 @ X18 @ X20))
% 0.68/0.92          | ~ (r1_lattices @ X18 @ X19 @ (sk_D_3 @ X19 @ X20 @ X18))
% 0.68/0.92          | ~ (r4_lattice3 @ X18 @ X19 @ X20)
% 0.68/0.92          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 0.68/0.92          | ~ (l3_lattices @ X18)
% 0.68/0.92          | ~ (v4_lattice3 @ X18)
% 0.68/0.92          | ~ (v10_lattices @ X18)
% 0.68/0.92          | (v2_struct_0 @ X18))),
% 0.68/0.92      inference('simplify', [status(thm)], ['24'])).
% 0.68/0.92  thf('26', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((v2_struct_0 @ X0)
% 0.68/0.92          | ~ (l3_lattices @ X0)
% 0.68/0.92          | ~ (v4_lattice3 @ X0)
% 0.68/0.92          | ~ (v10_lattices @ X0)
% 0.68/0.92          | ((sk_C @ X1 @ X0) = (k15_lattice3 @ X0 @ X1))
% 0.68/0.92          | (v2_struct_0 @ X0)
% 0.68/0.92          | ~ (v10_lattices @ X0)
% 0.68/0.92          | ~ (v4_lattice3 @ X0)
% 0.68/0.92          | ~ (l3_lattices @ X0)
% 0.68/0.92          | ~ (m1_subset_1 @ (sk_C @ X1 @ X0) @ (u1_struct_0 @ X0))
% 0.68/0.92          | ~ (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X1)
% 0.68/0.92          | ((sk_C @ X1 @ X0) = (k15_lattice3 @ X0 @ X1)))),
% 0.68/0.92      inference('sup-', [status(thm)], ['23', '25'])).
% 0.68/0.92  thf('27', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (~ (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X1)
% 0.68/0.92          | ~ (m1_subset_1 @ (sk_C @ X1 @ X0) @ (u1_struct_0 @ X0))
% 0.68/0.92          | ((sk_C @ X1 @ X0) = (k15_lattice3 @ X0 @ X1))
% 0.68/0.92          | ~ (v10_lattices @ X0)
% 0.68/0.92          | ~ (v4_lattice3 @ X0)
% 0.68/0.92          | ~ (l3_lattices @ X0)
% 0.68/0.92          | (v2_struct_0 @ X0))),
% 0.68/0.92      inference('simplify', [status(thm)], ['26'])).
% 0.68/0.92  thf('28', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((v2_struct_0 @ X0)
% 0.68/0.92          | ~ (l3_lattices @ X0)
% 0.68/0.92          | ~ (v4_lattice3 @ X0)
% 0.68/0.92          | (v2_struct_0 @ X0)
% 0.68/0.92          | ~ (l3_lattices @ X0)
% 0.68/0.92          | ~ (v4_lattice3 @ X0)
% 0.68/0.92          | ~ (v10_lattices @ X0)
% 0.68/0.92          | ((sk_C @ X1 @ X0) = (k15_lattice3 @ X0 @ X1))
% 0.68/0.92          | ~ (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X1))),
% 0.68/0.92      inference('sup-', [status(thm)], ['2', '27'])).
% 0.68/0.92  thf('29', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (~ (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X1)
% 0.68/0.92          | ((sk_C @ X1 @ X0) = (k15_lattice3 @ X0 @ X1))
% 0.68/0.92          | ~ (v10_lattices @ X0)
% 0.68/0.92          | ~ (v4_lattice3 @ X0)
% 0.68/0.92          | ~ (l3_lattices @ X0)
% 0.68/0.92          | (v2_struct_0 @ X0))),
% 0.68/0.92      inference('simplify', [status(thm)], ['28'])).
% 0.68/0.92  thf('30', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((v2_struct_0 @ X1)
% 0.68/0.92          | ~ (l3_lattices @ X1)
% 0.68/0.92          | ~ (v4_lattice3 @ X1)
% 0.68/0.92          | (v2_struct_0 @ X1)
% 0.68/0.92          | ~ (l3_lattices @ X1)
% 0.68/0.92          | ~ (v4_lattice3 @ X1)
% 0.68/0.92          | ~ (v10_lattices @ X1)
% 0.68/0.92          | ((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0)))),
% 0.68/0.92      inference('sup-', [status(thm)], ['1', '29'])).
% 0.68/0.92  thf('31', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (((sk_C @ X0 @ X1) = (k15_lattice3 @ X1 @ X0))
% 0.68/0.92          | ~ (v10_lattices @ X1)
% 0.68/0.92          | ~ (v4_lattice3 @ X1)
% 0.68/0.92          | ~ (l3_lattices @ X1)
% 0.68/0.92          | (v2_struct_0 @ X1))),
% 0.68/0.92      inference('simplify', [status(thm)], ['30'])).
% 0.68/0.92  thf('32', plain,
% 0.68/0.92      (![X15 : $i, X16 : $i]:
% 0.68/0.92         (~ (v4_lattice3 @ X15)
% 0.68/0.92          | (m1_subset_1 @ (sk_C @ X16 @ X15) @ (u1_struct_0 @ X15))
% 0.68/0.92          | ~ (l3_lattices @ X15)
% 0.68/0.92          | (v2_struct_0 @ X15))),
% 0.68/0.92      inference('cnf', [status(esa)], [d18_lattice3])).
% 0.68/0.92  thf('33', plain, ((r2_hidden @ sk_B_1 @ sk_C_1)),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf('34', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf('35', plain,
% 0.68/0.92      (![X15 : $i, X16 : $i]:
% 0.68/0.92         (~ (v4_lattice3 @ X15)
% 0.68/0.92          | (r4_lattice3 @ X15 @ (sk_C @ X16 @ X15) @ X16)
% 0.68/0.92          | ~ (l3_lattices @ X15)
% 0.68/0.92          | (v2_struct_0 @ X15))),
% 0.68/0.92      inference('cnf', [status(esa)], [d18_lattice3])).
% 0.68/0.92  thf('36', plain,
% 0.68/0.92      (![X15 : $i, X16 : $i]:
% 0.68/0.92         (~ (v4_lattice3 @ X15)
% 0.68/0.92          | (m1_subset_1 @ (sk_C @ X16 @ X15) @ (u1_struct_0 @ X15))
% 0.68/0.92          | ~ (l3_lattices @ X15)
% 0.68/0.92          | (v2_struct_0 @ X15))),
% 0.68/0.92      inference('cnf', [status(esa)], [d18_lattice3])).
% 0.68/0.92  thf(d17_lattice3, axiom,
% 0.68/0.92    (![A:$i]:
% 0.68/0.92     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.68/0.92       ( ![B:$i]:
% 0.68/0.92         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.92           ( ![C:$i]:
% 0.68/0.92             ( ( r4_lattice3 @ A @ B @ C ) <=>
% 0.68/0.92               ( ![D:$i]:
% 0.68/0.92                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.92                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ))).
% 0.68/0.92  thf('37', plain,
% 0.68/0.92      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.68/0.92         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.68/0.92          | ~ (r4_lattice3 @ X10 @ X9 @ X11)
% 0.68/0.92          | ~ (r2_hidden @ X12 @ X11)
% 0.68/0.92          | (r1_lattices @ X10 @ X12 @ X9)
% 0.68/0.92          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X10))
% 0.68/0.92          | ~ (l3_lattices @ X10)
% 0.68/0.92          | (v2_struct_0 @ X10))),
% 0.68/0.92      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.68/0.92  thf('38', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.92         ((v2_struct_0 @ X0)
% 0.68/0.92          | ~ (l3_lattices @ X0)
% 0.68/0.92          | ~ (v4_lattice3 @ X0)
% 0.68/0.92          | (v2_struct_0 @ X0)
% 0.68/0.92          | ~ (l3_lattices @ X0)
% 0.68/0.92          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.68/0.92          | (r1_lattices @ X0 @ X2 @ (sk_C @ X1 @ X0))
% 0.68/0.92          | ~ (r2_hidden @ X2 @ X3)
% 0.68/0.92          | ~ (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X3))),
% 0.68/0.92      inference('sup-', [status(thm)], ['36', '37'])).
% 0.68/0.92  thf('39', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.92         (~ (r4_lattice3 @ X0 @ (sk_C @ X1 @ X0) @ X3)
% 0.68/0.92          | ~ (r2_hidden @ X2 @ X3)
% 0.68/0.92          | (r1_lattices @ X0 @ X2 @ (sk_C @ X1 @ X0))
% 0.68/0.92          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.68/0.92          | ~ (v4_lattice3 @ X0)
% 0.68/0.92          | ~ (l3_lattices @ X0)
% 0.68/0.92          | (v2_struct_0 @ X0))),
% 0.68/0.92      inference('simplify', [status(thm)], ['38'])).
% 0.68/0.92  thf('40', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.92         ((v2_struct_0 @ X1)
% 0.68/0.92          | ~ (l3_lattices @ X1)
% 0.68/0.92          | ~ (v4_lattice3 @ X1)
% 0.68/0.92          | (v2_struct_0 @ X1)
% 0.68/0.92          | ~ (l3_lattices @ X1)
% 0.68/0.92          | ~ (v4_lattice3 @ X1)
% 0.68/0.92          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.68/0.92          | (r1_lattices @ X1 @ X2 @ (sk_C @ X0 @ X1))
% 0.68/0.92          | ~ (r2_hidden @ X2 @ X0))),
% 0.68/0.92      inference('sup-', [status(thm)], ['35', '39'])).
% 0.68/0.92  thf('41', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.92         (~ (r2_hidden @ X2 @ X0)
% 0.68/0.92          | (r1_lattices @ X1 @ X2 @ (sk_C @ X0 @ X1))
% 0.68/0.92          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.68/0.92          | ~ (v4_lattice3 @ X1)
% 0.68/0.92          | ~ (l3_lattices @ X1)
% 0.68/0.92          | (v2_struct_0 @ X1))),
% 0.68/0.92      inference('simplify', [status(thm)], ['40'])).
% 0.68/0.92  thf('42', plain,
% 0.68/0.92      (![X0 : $i]:
% 0.68/0.92         ((v2_struct_0 @ sk_A)
% 0.68/0.92          | ~ (l3_lattices @ sk_A)
% 0.68/0.92          | ~ (v4_lattice3 @ sk_A)
% 0.68/0.92          | (r1_lattices @ sk_A @ sk_B_1 @ (sk_C @ X0 @ sk_A))
% 0.68/0.92          | ~ (r2_hidden @ sk_B_1 @ X0))),
% 0.68/0.92      inference('sup-', [status(thm)], ['34', '41'])).
% 0.68/0.92  thf('43', plain, ((l3_lattices @ sk_A)),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf('44', plain, ((v4_lattice3 @ sk_A)),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf('45', plain,
% 0.68/0.92      (![X0 : $i]:
% 0.68/0.92         ((v2_struct_0 @ sk_A)
% 0.68/0.92          | (r1_lattices @ sk_A @ sk_B_1 @ (sk_C @ X0 @ sk_A))
% 0.68/0.92          | ~ (r2_hidden @ sk_B_1 @ X0))),
% 0.68/0.92      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.68/0.92  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf('47', plain,
% 0.68/0.92      (![X0 : $i]:
% 0.68/0.92         (~ (r2_hidden @ sk_B_1 @ X0)
% 0.68/0.92          | (r1_lattices @ sk_A @ sk_B_1 @ (sk_C @ X0 @ sk_A)))),
% 0.68/0.92      inference('clc', [status(thm)], ['45', '46'])).
% 0.68/0.92  thf('48', plain, ((r1_lattices @ sk_A @ sk_B_1 @ (sk_C @ sk_C_1 @ sk_A))),
% 0.68/0.92      inference('sup-', [status(thm)], ['33', '47'])).
% 0.68/0.92  thf('49', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf(redefinition_r3_lattices, axiom,
% 0.68/0.92    (![A:$i,B:$i,C:$i]:
% 0.68/0.92     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.68/0.92         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 0.68/0.92         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.68/0.92         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.92       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 0.68/0.92  thf('50', plain,
% 0.68/0.92      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.92         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.68/0.92          | ~ (l3_lattices @ X2)
% 0.68/0.92          | ~ (v9_lattices @ X2)
% 0.68/0.92          | ~ (v8_lattices @ X2)
% 0.68/0.92          | ~ (v6_lattices @ X2)
% 0.68/0.92          | (v2_struct_0 @ X2)
% 0.68/0.92          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.68/0.92          | (r3_lattices @ X2 @ X1 @ X3)
% 0.68/0.92          | ~ (r1_lattices @ X2 @ X1 @ X3))),
% 0.68/0.92      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.68/0.92  thf('51', plain,
% 0.68/0.92      (![X0 : $i]:
% 0.68/0.92         (~ (r1_lattices @ sk_A @ sk_B_1 @ X0)
% 0.68/0.92          | (r3_lattices @ sk_A @ sk_B_1 @ X0)
% 0.68/0.92          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.68/0.92          | (v2_struct_0 @ sk_A)
% 0.68/0.92          | ~ (v6_lattices @ sk_A)
% 0.68/0.92          | ~ (v8_lattices @ sk_A)
% 0.68/0.92          | ~ (v9_lattices @ sk_A)
% 0.68/0.92          | ~ (l3_lattices @ sk_A))),
% 0.68/0.92      inference('sup-', [status(thm)], ['49', '50'])).
% 0.68/0.92  thf(cc1_lattices, axiom,
% 0.68/0.92    (![A:$i]:
% 0.68/0.92     ( ( l3_lattices @ A ) =>
% 0.68/0.92       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.68/0.92         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.68/0.92           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.68/0.92           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.68/0.92  thf('52', plain,
% 0.68/0.92      (![X0 : $i]:
% 0.68/0.92         ((v2_struct_0 @ X0)
% 0.68/0.92          | ~ (v10_lattices @ X0)
% 0.68/0.92          | (v6_lattices @ X0)
% 0.68/0.92          | ~ (l3_lattices @ X0))),
% 0.68/0.92      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.68/0.92  thf('53', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf('54', plain,
% 0.68/0.92      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.68/0.92      inference('sup-', [status(thm)], ['52', '53'])).
% 0.68/0.92  thf('55', plain, ((l3_lattices @ sk_A)),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf('56', plain, ((v10_lattices @ sk_A)),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf('57', plain, ((v6_lattices @ sk_A)),
% 0.68/0.92      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.68/0.92  thf('58', plain,
% 0.68/0.92      (![X0 : $i]:
% 0.68/0.92         ((v2_struct_0 @ X0)
% 0.68/0.92          | ~ (v10_lattices @ X0)
% 0.68/0.92          | (v8_lattices @ X0)
% 0.68/0.92          | ~ (l3_lattices @ X0))),
% 0.68/0.92      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.68/0.92  thf('59', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf('60', plain,
% 0.68/0.92      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.68/0.92      inference('sup-', [status(thm)], ['58', '59'])).
% 0.68/0.92  thf('61', plain, ((l3_lattices @ sk_A)),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf('62', plain, ((v10_lattices @ sk_A)),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf('63', plain, ((v8_lattices @ sk_A)),
% 0.68/0.92      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.68/0.92  thf('64', plain,
% 0.68/0.92      (![X0 : $i]:
% 0.68/0.92         ((v2_struct_0 @ X0)
% 0.68/0.92          | ~ (v10_lattices @ X0)
% 0.68/0.92          | (v9_lattices @ X0)
% 0.68/0.92          | ~ (l3_lattices @ X0))),
% 0.68/0.92      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.68/0.92  thf('65', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf('66', plain,
% 0.68/0.92      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.68/0.92      inference('sup-', [status(thm)], ['64', '65'])).
% 0.68/0.92  thf('67', plain, ((l3_lattices @ sk_A)),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf('68', plain, ((v10_lattices @ sk_A)),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf('69', plain, ((v9_lattices @ sk_A)),
% 0.68/0.92      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.68/0.92  thf('70', plain, ((l3_lattices @ sk_A)),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf('71', plain,
% 0.68/0.92      (![X0 : $i]:
% 0.68/0.92         (~ (r1_lattices @ sk_A @ sk_B_1 @ X0)
% 0.68/0.92          | (r3_lattices @ sk_A @ sk_B_1 @ X0)
% 0.68/0.92          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.68/0.92          | (v2_struct_0 @ sk_A))),
% 0.68/0.92      inference('demod', [status(thm)], ['51', '57', '63', '69', '70'])).
% 0.68/0.92  thf('72', plain,
% 0.68/0.92      (((v2_struct_0 @ sk_A)
% 0.68/0.92        | ~ (m1_subset_1 @ (sk_C @ sk_C_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.68/0.92        | (r3_lattices @ sk_A @ sk_B_1 @ (sk_C @ sk_C_1 @ sk_A)))),
% 0.68/0.92      inference('sup-', [status(thm)], ['48', '71'])).
% 0.68/0.92  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf('74', plain,
% 0.68/0.92      (((r3_lattices @ sk_A @ sk_B_1 @ (sk_C @ sk_C_1 @ sk_A))
% 0.68/0.92        | ~ (m1_subset_1 @ (sk_C @ sk_C_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.68/0.92      inference('clc', [status(thm)], ['72', '73'])).
% 0.68/0.92  thf('75', plain,
% 0.68/0.92      (((v2_struct_0 @ sk_A)
% 0.68/0.92        | ~ (l3_lattices @ sk_A)
% 0.68/0.92        | ~ (v4_lattice3 @ sk_A)
% 0.68/0.92        | (r3_lattices @ sk_A @ sk_B_1 @ (sk_C @ sk_C_1 @ sk_A)))),
% 0.68/0.92      inference('sup-', [status(thm)], ['32', '74'])).
% 0.68/0.92  thf('76', plain, ((l3_lattices @ sk_A)),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf('77', plain, ((v4_lattice3 @ sk_A)),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf('78', plain,
% 0.68/0.92      (((v2_struct_0 @ sk_A)
% 0.68/0.92        | (r3_lattices @ sk_A @ sk_B_1 @ (sk_C @ sk_C_1 @ sk_A)))),
% 0.68/0.92      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.68/0.92  thf('79', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf('80', plain, ((r3_lattices @ sk_A @ sk_B_1 @ (sk_C @ sk_C_1 @ sk_A))),
% 0.68/0.92      inference('clc', [status(thm)], ['78', '79'])).
% 0.68/0.92  thf('81', plain,
% 0.68/0.92      (((r3_lattices @ sk_A @ sk_B_1 @ (k15_lattice3 @ sk_A @ sk_C_1))
% 0.68/0.92        | (v2_struct_0 @ sk_A)
% 0.68/0.92        | ~ (l3_lattices @ sk_A)
% 0.68/0.92        | ~ (v4_lattice3 @ sk_A)
% 0.68/0.92        | ~ (v10_lattices @ sk_A))),
% 0.68/0.92      inference('sup+', [status(thm)], ['31', '80'])).
% 0.68/0.92  thf('82', plain, ((l3_lattices @ sk_A)),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf('83', plain, ((v4_lattice3 @ sk_A)),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf('84', plain, ((v10_lattices @ sk_A)),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf('85', plain,
% 0.68/0.92      (((r3_lattices @ sk_A @ sk_B_1 @ (k15_lattice3 @ sk_A @ sk_C_1))
% 0.68/0.92        | (v2_struct_0 @ sk_A))),
% 0.68/0.92      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 0.68/0.92  thf('86', plain,
% 0.68/0.92      ((~ (r3_lattices @ sk_A @ sk_B_1 @ (k15_lattice3 @ sk_A @ sk_C_1))
% 0.68/0.92        | ~ (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C_1) @ sk_B_1))),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf('87', plain,
% 0.68/0.92      ((~ (r3_lattices @ sk_A @ sk_B_1 @ (k15_lattice3 @ sk_A @ sk_C_1)))
% 0.68/0.92         <= (~ ((r3_lattices @ sk_A @ sk_B_1 @ (k15_lattice3 @ sk_A @ sk_C_1))))),
% 0.68/0.92      inference('split', [status(esa)], ['86'])).
% 0.68/0.92  thf('88', plain, ((r2_hidden @ sk_B_1 @ sk_C_1)),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf('89', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf(dt_k16_lattice3, axiom,
% 0.68/0.92    (![A:$i,B:$i]:
% 0.68/0.92     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.68/0.92       ( m1_subset_1 @ ( k16_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.68/0.92  thf('90', plain,
% 0.68/0.92      (![X22 : $i, X23 : $i]:
% 0.68/0.92         (~ (l3_lattices @ X22)
% 0.68/0.92          | (v2_struct_0 @ X22)
% 0.68/0.92          | (m1_subset_1 @ (k16_lattice3 @ X22 @ X23) @ (u1_struct_0 @ X22)))),
% 0.68/0.92      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.68/0.92  thf(t34_lattice3, axiom,
% 0.68/0.92    (![A:$i]:
% 0.68/0.92     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.68/0.92         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.68/0.92       ( ![B:$i]:
% 0.68/0.92         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.92           ( ![C:$i]:
% 0.68/0.92             ( ( ( B ) = ( k16_lattice3 @ A @ C ) ) <=>
% 0.68/0.92               ( ( r3_lattice3 @ A @ B @ C ) & 
% 0.68/0.92                 ( ![D:$i]:
% 0.68/0.92                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.92                     ( ( r3_lattice3 @ A @ D @ C ) =>
% 0.68/0.92                       ( r3_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.68/0.92  thf('91', plain,
% 0.68/0.92      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.68/0.92         (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X25))
% 0.68/0.92          | ((X24) != (k16_lattice3 @ X25 @ X26))
% 0.68/0.92          | (r3_lattice3 @ X25 @ X24 @ X26)
% 0.68/0.92          | ~ (l3_lattices @ X25)
% 0.68/0.92          | ~ (v4_lattice3 @ X25)
% 0.68/0.92          | ~ (v10_lattices @ X25)
% 0.68/0.92          | (v2_struct_0 @ X25))),
% 0.68/0.92      inference('cnf', [status(esa)], [t34_lattice3])).
% 0.68/0.92  thf('92', plain,
% 0.68/0.92      (![X25 : $i, X26 : $i]:
% 0.68/0.92         ((v2_struct_0 @ X25)
% 0.68/0.92          | ~ (v10_lattices @ X25)
% 0.68/0.92          | ~ (v4_lattice3 @ X25)
% 0.68/0.92          | ~ (l3_lattices @ X25)
% 0.68/0.92          | (r3_lattice3 @ X25 @ (k16_lattice3 @ X25 @ X26) @ X26)
% 0.68/0.92          | ~ (m1_subset_1 @ (k16_lattice3 @ X25 @ X26) @ (u1_struct_0 @ X25)))),
% 0.68/0.92      inference('simplify', [status(thm)], ['91'])).
% 0.68/0.92  thf('93', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         ((v2_struct_0 @ X0)
% 0.68/0.92          | ~ (l3_lattices @ X0)
% 0.68/0.92          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X1)
% 0.68/0.92          | ~ (l3_lattices @ X0)
% 0.68/0.92          | ~ (v4_lattice3 @ X0)
% 0.68/0.92          | ~ (v10_lattices @ X0)
% 0.68/0.92          | (v2_struct_0 @ X0))),
% 0.68/0.92      inference('sup-', [status(thm)], ['90', '92'])).
% 0.68/0.92  thf('94', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i]:
% 0.68/0.92         (~ (v10_lattices @ X0)
% 0.68/0.92          | ~ (v4_lattice3 @ X0)
% 0.68/0.92          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X1)
% 0.68/0.92          | ~ (l3_lattices @ X0)
% 0.68/0.92          | (v2_struct_0 @ X0))),
% 0.68/0.92      inference('simplify', [status(thm)], ['93'])).
% 0.68/0.92  thf('95', plain,
% 0.68/0.92      (![X22 : $i, X23 : $i]:
% 0.68/0.92         (~ (l3_lattices @ X22)
% 0.68/0.92          | (v2_struct_0 @ X22)
% 0.68/0.92          | (m1_subset_1 @ (k16_lattice3 @ X22 @ X23) @ (u1_struct_0 @ X22)))),
% 0.68/0.92      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.68/0.92  thf(d16_lattice3, axiom,
% 0.68/0.92    (![A:$i]:
% 0.68/0.92     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.68/0.92       ( ![B:$i]:
% 0.68/0.92         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.92           ( ![C:$i]:
% 0.68/0.92             ( ( r3_lattice3 @ A @ B @ C ) <=>
% 0.68/0.92               ( ![D:$i]:
% 0.68/0.92                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.92                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 0.68/0.92  thf('96', plain,
% 0.68/0.92      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.68/0.92         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.68/0.92          | ~ (r3_lattice3 @ X5 @ X4 @ X6)
% 0.68/0.92          | ~ (r2_hidden @ X7 @ X6)
% 0.68/0.92          | (r1_lattices @ X5 @ X4 @ X7)
% 0.68/0.92          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X5))
% 0.68/0.92          | ~ (l3_lattices @ X5)
% 0.68/0.92          | (v2_struct_0 @ X5))),
% 0.68/0.92      inference('cnf', [status(esa)], [d16_lattice3])).
% 0.68/0.92  thf('97', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.92         ((v2_struct_0 @ X0)
% 0.68/0.92          | ~ (l3_lattices @ X0)
% 0.68/0.92          | (v2_struct_0 @ X0)
% 0.68/0.92          | ~ (l3_lattices @ X0)
% 0.68/0.92          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.68/0.92          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.68/0.92          | ~ (r2_hidden @ X2 @ X3)
% 0.68/0.92          | ~ (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X3))),
% 0.68/0.92      inference('sup-', [status(thm)], ['95', '96'])).
% 0.68/0.92  thf('98', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.92         (~ (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X3)
% 0.68/0.92          | ~ (r2_hidden @ X2 @ X3)
% 0.68/0.92          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.68/0.92          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.68/0.92          | ~ (l3_lattices @ X0)
% 0.68/0.92          | (v2_struct_0 @ X0))),
% 0.68/0.92      inference('simplify', [status(thm)], ['97'])).
% 0.68/0.92  thf('99', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.92         ((v2_struct_0 @ X1)
% 0.68/0.92          | ~ (l3_lattices @ X1)
% 0.68/0.92          | ~ (v4_lattice3 @ X1)
% 0.68/0.92          | ~ (v10_lattices @ X1)
% 0.68/0.92          | (v2_struct_0 @ X1)
% 0.68/0.92          | ~ (l3_lattices @ X1)
% 0.68/0.92          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.68/0.92          | (r1_lattices @ X1 @ (k16_lattice3 @ X1 @ X0) @ X2)
% 0.68/0.92          | ~ (r2_hidden @ X2 @ X0))),
% 0.68/0.92      inference('sup-', [status(thm)], ['94', '98'])).
% 0.68/0.92  thf('100', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.92         (~ (r2_hidden @ X2 @ X0)
% 0.68/0.92          | (r1_lattices @ X1 @ (k16_lattice3 @ X1 @ X0) @ X2)
% 0.68/0.92          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.68/0.92          | ~ (v10_lattices @ X1)
% 0.68/0.92          | ~ (v4_lattice3 @ X1)
% 0.68/0.92          | ~ (l3_lattices @ X1)
% 0.68/0.92          | (v2_struct_0 @ X1))),
% 0.68/0.92      inference('simplify', [status(thm)], ['99'])).
% 0.68/0.92  thf('101', plain,
% 0.68/0.92      (![X0 : $i]:
% 0.68/0.92         ((v2_struct_0 @ sk_A)
% 0.68/0.92          | ~ (l3_lattices @ sk_A)
% 0.68/0.92          | ~ (v4_lattice3 @ sk_A)
% 0.68/0.92          | ~ (v10_lattices @ sk_A)
% 0.68/0.92          | (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B_1)
% 0.68/0.92          | ~ (r2_hidden @ sk_B_1 @ X0))),
% 0.68/0.92      inference('sup-', [status(thm)], ['89', '100'])).
% 0.68/0.92  thf('102', plain, ((l3_lattices @ sk_A)),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf('103', plain, ((v4_lattice3 @ sk_A)),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf('104', plain, ((v10_lattices @ sk_A)),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf('105', plain,
% 0.68/0.92      (![X0 : $i]:
% 0.68/0.92         ((v2_struct_0 @ sk_A)
% 0.68/0.92          | (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B_1)
% 0.68/0.92          | ~ (r2_hidden @ sk_B_1 @ X0))),
% 0.68/0.92      inference('demod', [status(thm)], ['101', '102', '103', '104'])).
% 0.68/0.92  thf('106', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf('107', plain,
% 0.68/0.92      (![X0 : $i]:
% 0.68/0.92         (~ (r2_hidden @ sk_B_1 @ X0)
% 0.68/0.92          | (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B_1))),
% 0.68/0.92      inference('clc', [status(thm)], ['105', '106'])).
% 0.68/0.92  thf('108', plain,
% 0.68/0.92      ((r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C_1) @ sk_B_1)),
% 0.68/0.92      inference('sup-', [status(thm)], ['88', '107'])).
% 0.68/0.92  thf('109', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf('110', plain,
% 0.68/0.92      (![X22 : $i, X23 : $i]:
% 0.68/0.92         (~ (l3_lattices @ X22)
% 0.68/0.92          | (v2_struct_0 @ X22)
% 0.68/0.92          | (m1_subset_1 @ (k16_lattice3 @ X22 @ X23) @ (u1_struct_0 @ X22)))),
% 0.68/0.92      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.68/0.92  thf('111', plain,
% 0.68/0.92      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.92         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.68/0.92          | ~ (l3_lattices @ X2)
% 0.68/0.92          | ~ (v9_lattices @ X2)
% 0.68/0.92          | ~ (v8_lattices @ X2)
% 0.68/0.92          | ~ (v6_lattices @ X2)
% 0.68/0.92          | (v2_struct_0 @ X2)
% 0.68/0.92          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.68/0.92          | (r3_lattices @ X2 @ X1 @ X3)
% 0.68/0.92          | ~ (r1_lattices @ X2 @ X1 @ X3))),
% 0.68/0.92      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.68/0.92  thf('112', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.92         ((v2_struct_0 @ X0)
% 0.68/0.92          | ~ (l3_lattices @ X0)
% 0.68/0.92          | ~ (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.68/0.92          | (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.68/0.92          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.68/0.92          | (v2_struct_0 @ X0)
% 0.68/0.92          | ~ (v6_lattices @ X0)
% 0.68/0.92          | ~ (v8_lattices @ X0)
% 0.68/0.92          | ~ (v9_lattices @ X0)
% 0.68/0.92          | ~ (l3_lattices @ X0))),
% 0.68/0.92      inference('sup-', [status(thm)], ['110', '111'])).
% 0.68/0.92  thf('113', plain,
% 0.68/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.92         (~ (v9_lattices @ X0)
% 0.68/0.92          | ~ (v8_lattices @ X0)
% 0.68/0.92          | ~ (v6_lattices @ X0)
% 0.68/0.92          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.68/0.92          | (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.68/0.92          | ~ (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.68/0.92          | ~ (l3_lattices @ X0)
% 0.68/0.92          | (v2_struct_0 @ X0))),
% 0.68/0.92      inference('simplify', [status(thm)], ['112'])).
% 0.68/0.92  thf('114', plain,
% 0.68/0.92      (![X0 : $i]:
% 0.68/0.92         ((v2_struct_0 @ sk_A)
% 0.68/0.92          | ~ (l3_lattices @ sk_A)
% 0.68/0.92          | ~ (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B_1)
% 0.68/0.92          | (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B_1)
% 0.68/0.92          | ~ (v6_lattices @ sk_A)
% 0.68/0.92          | ~ (v8_lattices @ sk_A)
% 0.68/0.92          | ~ (v9_lattices @ sk_A))),
% 0.68/0.92      inference('sup-', [status(thm)], ['109', '113'])).
% 0.68/0.92  thf('115', plain, ((l3_lattices @ sk_A)),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf('116', plain, ((v6_lattices @ sk_A)),
% 0.68/0.92      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.68/0.92  thf('117', plain, ((v8_lattices @ sk_A)),
% 0.68/0.92      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.68/0.92  thf('118', plain, ((v9_lattices @ sk_A)),
% 0.68/0.92      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.68/0.92  thf('119', plain,
% 0.68/0.92      (![X0 : $i]:
% 0.68/0.92         ((v2_struct_0 @ sk_A)
% 0.68/0.92          | ~ (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B_1)
% 0.68/0.92          | (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B_1))),
% 0.68/0.92      inference('demod', [status(thm)], ['114', '115', '116', '117', '118'])).
% 0.68/0.92  thf('120', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.92  thf('121', plain,
% 0.68/0.92      (![X0 : $i]:
% 0.68/0.92         ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B_1)
% 0.68/0.92          | ~ (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B_1))),
% 0.68/0.92      inference('clc', [status(thm)], ['119', '120'])).
% 0.68/0.92  thf('122', plain,
% 0.68/0.92      ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C_1) @ sk_B_1)),
% 0.68/0.92      inference('sup-', [status(thm)], ['108', '121'])).
% 0.68/0.92  thf('123', plain,
% 0.68/0.92      ((~ (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C_1) @ sk_B_1))
% 0.68/0.92         <= (~ ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C_1) @ sk_B_1)))),
% 0.68/0.92      inference('split', [status(esa)], ['86'])).
% 0.68/0.92  thf('124', plain,
% 0.68/0.92      (((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C_1) @ sk_B_1))),
% 0.68/0.92      inference('sup-', [status(thm)], ['122', '123'])).
% 0.68/0.92  thf('125', plain,
% 0.68/0.92      (~ ((r3_lattices @ sk_A @ sk_B_1 @ (k15_lattice3 @ sk_A @ sk_C_1))) | 
% 0.68/0.92       ~ ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C_1) @ sk_B_1))),
% 0.68/0.92      inference('split', [status(esa)], ['86'])).
% 0.68/0.92  thf('126', plain,
% 0.68/0.92      (~ ((r3_lattices @ sk_A @ sk_B_1 @ (k15_lattice3 @ sk_A @ sk_C_1)))),
% 0.68/0.92      inference('sat_resolution*', [status(thm)], ['124', '125'])).
% 0.68/0.92  thf('127', plain,
% 0.68/0.92      (~ (r3_lattices @ sk_A @ sk_B_1 @ (k15_lattice3 @ sk_A @ sk_C_1))),
% 0.68/0.92      inference('simpl_trail', [status(thm)], ['87', '126'])).
% 0.68/0.92  thf('128', plain, ((v2_struct_0 @ sk_A)),
% 0.68/0.92      inference('clc', [status(thm)], ['85', '127'])).
% 0.68/0.92  thf('129', plain, ($false), inference('demod', [status(thm)], ['0', '128'])).
% 0.68/0.92  
% 0.68/0.92  % SZS output end Refutation
% 0.68/0.92  
% 0.68/0.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
