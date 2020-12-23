%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6stqPF2LlF

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:33 EST 2020

% Result     : Theorem 0.84s
% Output     : Refutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 238 expanded)
%              Number of leaves         :   38 (  82 expanded)
%              Depth                    :   27
%              Number of atoms          : 2409 (4006 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :   20 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(r4_lattice3_type,type,(
    r4_lattice3: $i > $i > $i > $o )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(a_2_2_lattice3_type,type,(
    a_2_2_lattice3: $i > $i > $i )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(r3_lattice3_type,type,(
    r3_lattice3: $i > $i > $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(t46_lattice3,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v4_lattice3 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( r3_lattices @ A @ ( k15_lattice3 @ A @ B ) @ ( k15_lattice3 @ A @ C ) )
            & ( r3_lattices @ A @ ( k16_lattice3 @ A @ C ) @ ( k16_lattice3 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v4_lattice3 @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i,C: $i] :
            ( ( r1_tarski @ B @ C )
           => ( ( r3_lattices @ A @ ( k15_lattice3 @ A @ B ) @ ( k15_lattice3 @ A @ C ) )
              & ( r3_lattices @ A @ ( k16_lattice3 @ A @ C ) @ ( k16_lattice3 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t46_lattice3])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k16_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( m1_subset_1 @ ( k16_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) ),
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

thf('2',plain,(
    ! [X8: $i,X9: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ( r2_hidden @ ( sk_D @ X12 @ X8 @ X9 ) @ X12 )
      | ( r3_lattice3 @ X9 @ X8 @ X12 )
      | ~ ( l3_lattices @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ sk_B )
      | ( r2_hidden @ ( sk_D @ sk_B @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf('10',plain,(
    ! [X8: $i,X9: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ( m1_subset_1 @ ( sk_D @ X12 @ X8 @ X9 ) @ ( u1_struct_0 @ X9 ) )
      | ( r3_lattice3 @ X9 @ X8 @ X12 )
      | ~ ( l3_lattices @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ( m1_subset_1 @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) ),
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

thf('14',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ( X26
       != ( k16_lattice3 @ X27 @ X28 ) )
      | ( r3_lattice3 @ X27 @ X26 @ X28 )
      | ~ ( l3_lattices @ X27 )
      | ~ ( v4_lattice3 @ X27 )
      | ~ ( v10_lattices @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('15',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v10_lattices @ X27 )
      | ~ ( v4_lattice3 @ X27 )
      | ~ ( l3_lattices @ X27 )
      | ( r3_lattice3 @ X27 @ ( k16_lattice3 @ X27 @ X28 ) @ X28 )
      | ~ ( m1_subset_1 @ ( k16_lattice3 @ X27 @ X28 ) @ ( u1_struct_0 @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf('19',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( r3_lattice3 @ X9 @ X8 @ X10 )
      | ~ ( r2_hidden @ X11 @ X10 )
      | ( r1_lattices @ X9 @ X8 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l3_lattices @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X3 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
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
    inference('sup-',[status(thm)],['17','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r1_lattices @ X1 @ ( k16_lattice3 @ X1 @ X0 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X3 ) @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['12','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) @ X3 )
      | ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X3 ) @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ sk_B )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ sk_B )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ sk_C_1 ) @ ( sk_D @ sk_B @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ sk_C_1 ) @ ( sk_D @ sk_B @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf('29',plain,(
    ! [X8: $i,X9: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( r1_lattices @ X9 @ X8 @ ( sk_D @ X12 @ X8 @ X9 ) )
      | ( r3_lattice3 @ X9 @ X8 @ X12 )
      | ~ ( l3_lattices @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ sk_C_1 ) @ sk_B )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ sk_C_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ sk_C_1 ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf('35',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf('36',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ( X26
       != ( k16_lattice3 @ X27 @ X28 ) )
      | ~ ( r3_lattice3 @ X27 @ X29 @ X28 )
      | ( r3_lattices @ X27 @ X29 @ X26 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X27 ) )
      | ~ ( l3_lattices @ X27 )
      | ~ ( v4_lattice3 @ X27 )
      | ~ ( v10_lattices @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('37',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v10_lattices @ X27 )
      | ~ ( v4_lattice3 @ X27 )
      | ~ ( l3_lattices @ X27 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X27 ) )
      | ( r3_lattices @ X27 @ X29 @ ( k16_lattice3 @ X27 @ X28 ) )
      | ~ ( r3_lattice3 @ X27 @ X29 @ X28 )
      | ~ ( m1_subset_1 @ ( k16_lattice3 @ X27 @ X28 ) @ ( u1_struct_0 @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r3_lattice3 @ X0 @ X2 @ X1 )
      | ( r3_lattices @ X0 @ X2 @ ( k16_lattice3 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r3_lattices @ X0 @ X2 @ ( k16_lattice3 @ X0 @ X1 ) )
      | ~ ( r3_lattice3 @ X0 @ X2 @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( k16_lattice3 @ X0 @ X2 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( k16_lattice3 @ X0 @ X2 ) )
      | ~ ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ sk_C_1 ) @ ( k16_lattice3 @ X0 @ sk_B ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ sk_C_1 ) @ ( k16_lattice3 @ X0 @ sk_B ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ~ ( r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_C_1 ) )
    | ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C_1 ) @ ( k16_lattice3 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C_1 ) @ ( k16_lattice3 @ sk_A @ sk_B ) )
   <= ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C_1 ) @ ( k16_lattice3 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['44'])).

thf(t37_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v4_lattice3 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( k15_lattice3 @ A @ B )
          = ( k16_lattice3 @ A @ ( a_2_2_lattice3 @ A @ B ) ) ) ) )).

thf('46',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k15_lattice3 @ X31 @ X32 )
        = ( k16_lattice3 @ X31 @ ( a_2_2_lattice3 @ X31 @ X32 ) ) )
      | ~ ( l3_lattices @ X31 )
      | ~ ( v4_lattice3 @ X31 )
      | ~ ( v10_lattices @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t37_lattice3])).

thf(dt_k15_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('47',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('48',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) ),
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

thf('49',plain,(
    ! [X13: $i,X14: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ( r2_hidden @ ( sk_D_1 @ X17 @ X13 @ X14 ) @ X17 )
      | ( r4_lattice3 @ X14 @ X13 @ X17 )
      | ~ ( l3_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_B @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('55',plain,(
    ! [X13: $i,X14: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X17 @ X13 @ X14 ) @ ( u1_struct_0 @ X14 ) )
      | ( r4_lattice3 @ X14 @ X13 @ X17 )
      | ~ ( l3_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( m1_subset_1 @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

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

thf('58',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X34 ) )
      | ( r3_lattices @ X34 @ X33 @ ( k15_lattice3 @ X34 @ X35 ) )
      | ~ ( r2_hidden @ X33 @ X35 )
      | ~ ( l3_lattices @ X34 )
      | ~ ( v4_lattice3 @ X34 )
      | ~ ( v10_lattices @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t38_lattice3])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X3 )
      | ( r3_lattices @ X0 @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X3 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r3_lattices @ X0 @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X3 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X3 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ sk_B )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ sk_B )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r3_lattices @ X0 @ ( sk_D_1 @ sk_B @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['53','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattices @ X0 @ ( sk_D_1 @ sk_B @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ sk_C_1 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

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

thf('64',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l3_lattices @ X6 )
      | ~ ( v9_lattices @ X6 )
      | ~ ( v8_lattices @ X6 )
      | ~ ( v6_lattices @ X6 )
      | ( v2_struct_0 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ( r1_lattices @ X6 @ X5 @ X7 )
      | ~ ( r3_lattices @ X6 @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r3_lattices @ X0 @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X3 )
      | ( r1_lattices @ X0 @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X3 )
      | ~ ( r3_lattices @ X0 @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X3 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ sk_B )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ sk_B )
      | ( r1_lattices @ X0 @ ( sk_D_1 @ sk_B @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ ( k15_lattice3 @ X0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ ( k15_lattice3 @ X0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( sk_D_1 @ sk_B @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ sk_C_1 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ sk_B )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r1_lattices @ X0 @ ( sk_D_1 @ sk_B @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ sk_C_1 ) )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ( r1_lattices @ X0 @ ( sk_D_1 @ sk_B @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ sk_C_1 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ sk_B )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('72',plain,(
    ! [X13: $i,X14: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( r1_lattices @ X14 @ ( sk_D_1 @ X17 @ X13 @ X14 ) @ X13 )
      | ( r4_lattice3 @ X14 @ X13 @ X17 )
      | ~ ( l3_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_lattices @ X0 @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattices @ X0 @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ sk_C_1 ) @ sk_B )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ sk_C_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['70','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ sk_C_1 ) @ sk_B )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf(fraenkel_a_2_2_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( v10_lattices @ B )
        & ( v4_lattice3 @ B )
        & ( l3_lattices @ B ) )
     => ( ( r2_hidden @ A @ ( a_2_2_lattice3 @ B @ C ) )
      <=> ? [D: $i] :
            ( ( r4_lattice3 @ B @ D @ C )
            & ( A = D )
            & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('78',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( l3_lattices @ X22 )
      | ~ ( v4_lattice3 @ X22 )
      | ~ ( v10_lattices @ X22 )
      | ( v2_struct_0 @ X22 )
      | ( r2_hidden @ X24 @ ( a_2_2_lattice3 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X22 ) )
      | ( X24 != X25 )
      | ~ ( r4_lattice3 @ X22 @ X25 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_2_lattice3])).

thf('79',plain,(
    ! [X22: $i,X23: $i,X25: $i] :
      ( ~ ( r4_lattice3 @ X22 @ X25 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X22 ) )
      | ( r2_hidden @ X25 @ ( a_2_2_lattice3 @ X22 @ X23 ) )
      | ( v2_struct_0 @ X22 )
      | ~ ( v10_lattices @ X22 )
      | ~ ( v4_lattice3 @ X22 )
      | ~ ( l3_lattices @ X22 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r2_hidden @ ( k15_lattice3 @ X0 @ X1 ) @ ( a_2_2_lattice3 @ X0 @ X2 ) )
      | ~ ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['77','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( k15_lattice3 @ X0 @ X1 ) @ ( a_2_2_lattice3 @ X0 @ X2 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( r2_hidden @ ( k15_lattice3 @ X0 @ sk_C_1 ) @ ( a_2_2_lattice3 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['76','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k15_lattice3 @ X0 @ sk_C_1 ) @ ( a_2_2_lattice3 @ X0 @ sk_B ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('85',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X34 ) )
      | ( r3_lattices @ X34 @ ( k16_lattice3 @ X34 @ X35 ) @ X33 )
      | ~ ( r2_hidden @ X33 @ X35 )
      | ~ ( l3_lattices @ X34 )
      | ~ ( v4_lattice3 @ X34 )
      | ~ ( v10_lattices @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t38_lattice3])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r2_hidden @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ ( a_2_2_lattice3 @ X0 @ sk_B ) ) @ ( k15_lattice3 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['83','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ ( a_2_2_lattice3 @ X0 @ sk_B ) ) @ ( k15_lattice3 @ X0 @ sk_C_1 ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ sk_B ) @ ( k15_lattice3 @ X0 @ sk_C_1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ sk_B ) @ ( k15_lattice3 @ X0 @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ~ ( r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_C_1 ) )
   <= ~ ( r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['44'])).

thf('93',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A ) )
   <= ~ ( r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
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

thf('97',plain,(
    ! [X4: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( v10_lattices @ X4 )
      | ( v6_lattices @ X4 )
      | ~ ( l3_lattices @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,(
    ! [X4: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( v10_lattices @ X4 )
      | ( v8_lattices @ X4 )
      | ~ ( l3_lattices @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('104',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,(
    ! [X4: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( v10_lattices @ X4 )
      | ( v9_lattices @ X4 )
      | ~ ( l3_lattices @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('110',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ~ ( r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['93','94','95','96','102','108','114'])).

thf('116',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C_1 ) @ ( k16_lattice3 @ sk_A @ sk_B ) )
    | ~ ( r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['44'])).

thf('119',plain,(
    ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C_1 ) @ ( k16_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['117','118'])).

thf('120',plain,(
    ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C_1 ) @ ( k16_lattice3 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['45','119'])).

thf('121',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['43','120'])).

thf('122',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['121','122','123','124'])).

thf('126',plain,(
    $false ),
    inference(demod,[status(thm)],['0','125'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6stqPF2LlF
% 0.15/0.37  % Computer   : n020.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 10:07:52 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.84/1.08  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.84/1.08  % Solved by: fo/fo7.sh
% 0.84/1.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.84/1.08  % done 514 iterations in 0.593s
% 0.84/1.08  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.84/1.08  % SZS output start Refutation
% 0.84/1.08  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 0.84/1.08  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.84/1.08  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.84/1.08  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.84/1.08  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 0.84/1.08  thf(sk_B_type, type, sk_B: $i).
% 0.84/1.08  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.84/1.08  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.84/1.08  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.84/1.08  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.84/1.08  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.84/1.08  thf(r4_lattice3_type, type, r4_lattice3: $i > $i > $i > $o).
% 0.84/1.08  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 0.84/1.08  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.84/1.08  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.84/1.08  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.84/1.08  thf(sk_A_type, type, sk_A: $i).
% 0.84/1.08  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.84/1.08  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 0.84/1.08  thf(a_2_2_lattice3_type, type, a_2_2_lattice3: $i > $i > $i).
% 0.84/1.08  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.84/1.08  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.84/1.08  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.84/1.08  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.84/1.08  thf(r3_lattice3_type, type, r3_lattice3: $i > $i > $i > $o).
% 0.84/1.08  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.84/1.08  thf(t46_lattice3, conjecture,
% 0.84/1.08    (![A:$i]:
% 0.84/1.08     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.84/1.08         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.84/1.08       ( ![B:$i,C:$i]:
% 0.84/1.08         ( ( r1_tarski @ B @ C ) =>
% 0.84/1.08           ( ( r3_lattices @
% 0.84/1.08               A @ ( k15_lattice3 @ A @ B ) @ ( k15_lattice3 @ A @ C ) ) & 
% 0.84/1.08             ( r3_lattices @
% 0.84/1.08               A @ ( k16_lattice3 @ A @ C ) @ ( k16_lattice3 @ A @ B ) ) ) ) ) ))).
% 0.84/1.08  thf(zf_stmt_0, negated_conjecture,
% 0.84/1.08    (~( ![A:$i]:
% 0.84/1.08        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.84/1.08            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.84/1.08          ( ![B:$i,C:$i]:
% 0.84/1.08            ( ( r1_tarski @ B @ C ) =>
% 0.84/1.08              ( ( r3_lattices @
% 0.84/1.08                  A @ ( k15_lattice3 @ A @ B ) @ ( k15_lattice3 @ A @ C ) ) & 
% 0.84/1.08                ( r3_lattices @
% 0.84/1.08                  A @ ( k16_lattice3 @ A @ C ) @ ( k16_lattice3 @ A @ B ) ) ) ) ) ) )),
% 0.84/1.08    inference('cnf.neg', [status(esa)], [t46_lattice3])).
% 0.84/1.08  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.84/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.08  thf(dt_k16_lattice3, axiom,
% 0.84/1.08    (![A:$i,B:$i]:
% 0.84/1.08     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.84/1.08       ( m1_subset_1 @ ( k16_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.84/1.08  thf('1', plain,
% 0.84/1.08      (![X20 : $i, X21 : $i]:
% 0.84/1.08         (~ (l3_lattices @ X20)
% 0.84/1.08          | (v2_struct_0 @ X20)
% 0.84/1.08          | (m1_subset_1 @ (k16_lattice3 @ X20 @ X21) @ (u1_struct_0 @ X20)))),
% 0.84/1.08      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.84/1.08  thf(d16_lattice3, axiom,
% 0.84/1.08    (![A:$i]:
% 0.84/1.08     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.84/1.08       ( ![B:$i]:
% 0.84/1.08         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.84/1.08           ( ![C:$i]:
% 0.84/1.08             ( ( r3_lattice3 @ A @ B @ C ) <=>
% 0.84/1.08               ( ![D:$i]:
% 0.84/1.08                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.84/1.08                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 0.84/1.08  thf('2', plain,
% 0.84/1.08      (![X8 : $i, X9 : $i, X12 : $i]:
% 0.84/1.08         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.84/1.08          | (r2_hidden @ (sk_D @ X12 @ X8 @ X9) @ X12)
% 0.84/1.08          | (r3_lattice3 @ X9 @ X8 @ X12)
% 0.84/1.08          | ~ (l3_lattices @ X9)
% 0.84/1.08          | (v2_struct_0 @ X9))),
% 0.84/1.08      inference('cnf', [status(esa)], [d16_lattice3])).
% 0.84/1.08  thf('3', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.08         ((v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.84/1.08          | (r2_hidden @ (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0) @ X2))),
% 0.84/1.08      inference('sup-', [status(thm)], ['1', '2'])).
% 0.84/1.08  thf('4', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.08         ((r2_hidden @ (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0) @ X2)
% 0.84/1.08          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0))),
% 0.84/1.08      inference('simplify', [status(thm)], ['3'])).
% 0.84/1.08  thf('5', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.84/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.08  thf(d3_tarski, axiom,
% 0.84/1.08    (![A:$i,B:$i]:
% 0.84/1.08     ( ( r1_tarski @ A @ B ) <=>
% 0.84/1.08       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.84/1.08  thf('6', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.08         (~ (r2_hidden @ X0 @ X1)
% 0.84/1.08          | (r2_hidden @ X0 @ X2)
% 0.84/1.08          | ~ (r1_tarski @ X1 @ X2))),
% 0.84/1.08      inference('cnf', [status(esa)], [d3_tarski])).
% 0.84/1.08  thf('7', plain,
% 0.84/1.08      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.84/1.08      inference('sup-', [status(thm)], ['5', '6'])).
% 0.84/1.08  thf('8', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i]:
% 0.84/1.08         ((v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ sk_B)
% 0.84/1.08          | (r2_hidden @ (sk_D @ sk_B @ (k16_lattice3 @ X0 @ X1) @ X0) @ sk_C_1))),
% 0.84/1.08      inference('sup-', [status(thm)], ['4', '7'])).
% 0.84/1.08  thf('9', plain,
% 0.84/1.08      (![X20 : $i, X21 : $i]:
% 0.84/1.08         (~ (l3_lattices @ X20)
% 0.84/1.08          | (v2_struct_0 @ X20)
% 0.84/1.08          | (m1_subset_1 @ (k16_lattice3 @ X20 @ X21) @ (u1_struct_0 @ X20)))),
% 0.84/1.08      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.84/1.08  thf('10', plain,
% 0.84/1.08      (![X8 : $i, X9 : $i, X12 : $i]:
% 0.84/1.08         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.84/1.08          | (m1_subset_1 @ (sk_D @ X12 @ X8 @ X9) @ (u1_struct_0 @ X9))
% 0.84/1.08          | (r3_lattice3 @ X9 @ X8 @ X12)
% 0.84/1.08          | ~ (l3_lattices @ X9)
% 0.84/1.08          | (v2_struct_0 @ X9))),
% 0.84/1.08      inference('cnf', [status(esa)], [d16_lattice3])).
% 0.84/1.08  thf('11', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.08         ((v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.84/1.08          | (m1_subset_1 @ (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0) @ 
% 0.84/1.08             (u1_struct_0 @ X0)))),
% 0.84/1.08      inference('sup-', [status(thm)], ['9', '10'])).
% 0.84/1.08  thf('12', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.08         ((m1_subset_1 @ (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0) @ 
% 0.84/1.08           (u1_struct_0 @ X0))
% 0.84/1.08          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0))),
% 0.84/1.08      inference('simplify', [status(thm)], ['11'])).
% 0.84/1.08  thf('13', plain,
% 0.84/1.08      (![X20 : $i, X21 : $i]:
% 0.84/1.08         (~ (l3_lattices @ X20)
% 0.84/1.08          | (v2_struct_0 @ X20)
% 0.84/1.08          | (m1_subset_1 @ (k16_lattice3 @ X20 @ X21) @ (u1_struct_0 @ X20)))),
% 0.84/1.08      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.84/1.08  thf(t34_lattice3, axiom,
% 0.84/1.08    (![A:$i]:
% 0.84/1.08     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.84/1.08         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.84/1.08       ( ![B:$i]:
% 0.84/1.08         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.84/1.08           ( ![C:$i]:
% 0.84/1.08             ( ( ( B ) = ( k16_lattice3 @ A @ C ) ) <=>
% 0.84/1.08               ( ( r3_lattice3 @ A @ B @ C ) & 
% 0.84/1.08                 ( ![D:$i]:
% 0.84/1.08                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.84/1.08                     ( ( r3_lattice3 @ A @ D @ C ) =>
% 0.84/1.08                       ( r3_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.84/1.08  thf('14', plain,
% 0.84/1.08      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.84/1.08         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 0.84/1.08          | ((X26) != (k16_lattice3 @ X27 @ X28))
% 0.84/1.08          | (r3_lattice3 @ X27 @ X26 @ X28)
% 0.84/1.08          | ~ (l3_lattices @ X27)
% 0.84/1.08          | ~ (v4_lattice3 @ X27)
% 0.84/1.08          | ~ (v10_lattices @ X27)
% 0.84/1.08          | (v2_struct_0 @ X27))),
% 0.84/1.08      inference('cnf', [status(esa)], [t34_lattice3])).
% 0.84/1.08  thf('15', plain,
% 0.84/1.08      (![X27 : $i, X28 : $i]:
% 0.84/1.08         ((v2_struct_0 @ X27)
% 0.84/1.08          | ~ (v10_lattices @ X27)
% 0.84/1.08          | ~ (v4_lattice3 @ X27)
% 0.84/1.08          | ~ (l3_lattices @ X27)
% 0.84/1.08          | (r3_lattice3 @ X27 @ (k16_lattice3 @ X27 @ X28) @ X28)
% 0.84/1.08          | ~ (m1_subset_1 @ (k16_lattice3 @ X27 @ X28) @ (u1_struct_0 @ X27)))),
% 0.84/1.08      inference('simplify', [status(thm)], ['14'])).
% 0.84/1.08  thf('16', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i]:
% 0.84/1.08         ((v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X1)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | ~ (v4_lattice3 @ X0)
% 0.84/1.08          | ~ (v10_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0))),
% 0.84/1.08      inference('sup-', [status(thm)], ['13', '15'])).
% 0.84/1.08  thf('17', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i]:
% 0.84/1.08         (~ (v10_lattices @ X0)
% 0.84/1.08          | ~ (v4_lattice3 @ X0)
% 0.84/1.08          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X1)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0))),
% 0.84/1.08      inference('simplify', [status(thm)], ['16'])).
% 0.84/1.08  thf('18', plain,
% 0.84/1.08      (![X20 : $i, X21 : $i]:
% 0.84/1.08         (~ (l3_lattices @ X20)
% 0.84/1.08          | (v2_struct_0 @ X20)
% 0.84/1.08          | (m1_subset_1 @ (k16_lattice3 @ X20 @ X21) @ (u1_struct_0 @ X20)))),
% 0.84/1.08      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.84/1.08  thf('19', plain,
% 0.84/1.08      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.84/1.08         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.84/1.08          | ~ (r3_lattice3 @ X9 @ X8 @ X10)
% 0.84/1.08          | ~ (r2_hidden @ X11 @ X10)
% 0.84/1.08          | (r1_lattices @ X9 @ X8 @ X11)
% 0.84/1.08          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X9))
% 0.84/1.08          | ~ (l3_lattices @ X9)
% 0.84/1.08          | (v2_struct_0 @ X9))),
% 0.84/1.08      inference('cnf', [status(esa)], [d16_lattice3])).
% 0.84/1.08  thf('20', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.84/1.08         ((v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.84/1.08          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.84/1.08          | ~ (r2_hidden @ X2 @ X3)
% 0.84/1.08          | ~ (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X3))),
% 0.84/1.08      inference('sup-', [status(thm)], ['18', '19'])).
% 0.84/1.08  thf('21', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.84/1.08         (~ (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X3)
% 0.84/1.08          | ~ (r2_hidden @ X2 @ X3)
% 0.84/1.08          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.84/1.08          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0))),
% 0.84/1.08      inference('simplify', [status(thm)], ['20'])).
% 0.84/1.08  thf('22', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.08         ((v2_struct_0 @ X1)
% 0.84/1.08          | ~ (l3_lattices @ X1)
% 0.84/1.08          | ~ (v4_lattice3 @ X1)
% 0.84/1.08          | ~ (v10_lattices @ X1)
% 0.84/1.08          | (v2_struct_0 @ X1)
% 0.84/1.08          | ~ (l3_lattices @ X1)
% 0.84/1.08          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.84/1.08          | (r1_lattices @ X1 @ (k16_lattice3 @ X1 @ X0) @ X2)
% 0.84/1.08          | ~ (r2_hidden @ X2 @ X0))),
% 0.84/1.08      inference('sup-', [status(thm)], ['17', '21'])).
% 0.84/1.08  thf('23', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.08         (~ (r2_hidden @ X2 @ X0)
% 0.84/1.08          | (r1_lattices @ X1 @ (k16_lattice3 @ X1 @ X0) @ X2)
% 0.84/1.08          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.84/1.08          | ~ (v10_lattices @ X1)
% 0.84/1.08          | ~ (v4_lattice3 @ X1)
% 0.84/1.08          | ~ (l3_lattices @ X1)
% 0.84/1.08          | (v2_struct_0 @ X1))),
% 0.84/1.08      inference('simplify', [status(thm)], ['22'])).
% 0.84/1.08  thf('24', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.84/1.08         ((v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.84/1.08          | (v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | ~ (v4_lattice3 @ X0)
% 0.84/1.08          | ~ (v10_lattices @ X0)
% 0.84/1.08          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X3) @ 
% 0.84/1.08             (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0))
% 0.84/1.08          | ~ (r2_hidden @ (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0) @ X3))),
% 0.84/1.08      inference('sup-', [status(thm)], ['12', '23'])).
% 0.84/1.08  thf('25', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.84/1.08         (~ (r2_hidden @ (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0) @ X3)
% 0.84/1.08          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X3) @ 
% 0.84/1.08             (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0))
% 0.84/1.08          | ~ (v10_lattices @ X0)
% 0.84/1.08          | ~ (v4_lattice3 @ X0)
% 0.84/1.08          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0))),
% 0.84/1.08      inference('simplify', [status(thm)], ['24'])).
% 0.84/1.08  thf('26', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i]:
% 0.84/1.08         ((r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ sk_B)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ sk_B)
% 0.84/1.08          | ~ (v4_lattice3 @ X0)
% 0.84/1.08          | ~ (v10_lattices @ X0)
% 0.84/1.08          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ sk_C_1) @ 
% 0.84/1.08             (sk_D @ sk_B @ (k16_lattice3 @ X0 @ X1) @ X0)))),
% 0.84/1.08      inference('sup-', [status(thm)], ['8', '25'])).
% 0.84/1.08  thf('27', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i]:
% 0.84/1.08         ((r1_lattices @ X0 @ (k16_lattice3 @ X0 @ sk_C_1) @ 
% 0.84/1.08           (sk_D @ sk_B @ (k16_lattice3 @ X0 @ X1) @ X0))
% 0.84/1.08          | ~ (v10_lattices @ X0)
% 0.84/1.08          | ~ (v4_lattice3 @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ sk_B))),
% 0.84/1.08      inference('simplify', [status(thm)], ['26'])).
% 0.84/1.08  thf('28', plain,
% 0.84/1.08      (![X20 : $i, X21 : $i]:
% 0.84/1.08         (~ (l3_lattices @ X20)
% 0.84/1.08          | (v2_struct_0 @ X20)
% 0.84/1.08          | (m1_subset_1 @ (k16_lattice3 @ X20 @ X21) @ (u1_struct_0 @ X20)))),
% 0.84/1.08      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.84/1.08  thf('29', plain,
% 0.84/1.08      (![X8 : $i, X9 : $i, X12 : $i]:
% 0.84/1.08         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.84/1.08          | ~ (r1_lattices @ X9 @ X8 @ (sk_D @ X12 @ X8 @ X9))
% 0.84/1.08          | (r3_lattice3 @ X9 @ X8 @ X12)
% 0.84/1.08          | ~ (l3_lattices @ X9)
% 0.84/1.08          | (v2_struct_0 @ X9))),
% 0.84/1.08      inference('cnf', [status(esa)], [d16_lattice3])).
% 0.84/1.08  thf('30', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.08         ((v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.84/1.08          | ~ (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 0.84/1.08               (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0)))),
% 0.84/1.08      inference('sup-', [status(thm)], ['28', '29'])).
% 0.84/1.08  thf('31', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.08         (~ (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 0.84/1.08             (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0))
% 0.84/1.08          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0))),
% 0.84/1.08      inference('simplify', [status(thm)], ['30'])).
% 0.84/1.08  thf('32', plain,
% 0.84/1.08      (![X0 : $i]:
% 0.84/1.08         ((r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ sk_C_1) @ sk_B)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0)
% 0.84/1.08          | ~ (v4_lattice3 @ X0)
% 0.84/1.08          | ~ (v10_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ sk_C_1) @ sk_B))),
% 0.84/1.08      inference('sup-', [status(thm)], ['27', '31'])).
% 0.84/1.08  thf('33', plain,
% 0.84/1.08      (![X0 : $i]:
% 0.84/1.08         (~ (v10_lattices @ X0)
% 0.84/1.08          | ~ (v4_lattice3 @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ sk_C_1) @ sk_B))),
% 0.84/1.08      inference('simplify', [status(thm)], ['32'])).
% 0.84/1.08  thf('34', plain,
% 0.84/1.08      (![X20 : $i, X21 : $i]:
% 0.84/1.08         (~ (l3_lattices @ X20)
% 0.84/1.08          | (v2_struct_0 @ X20)
% 0.84/1.08          | (m1_subset_1 @ (k16_lattice3 @ X20 @ X21) @ (u1_struct_0 @ X20)))),
% 0.84/1.08      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.84/1.08  thf('35', plain,
% 0.84/1.08      (![X20 : $i, X21 : $i]:
% 0.84/1.08         (~ (l3_lattices @ X20)
% 0.84/1.08          | (v2_struct_0 @ X20)
% 0.84/1.08          | (m1_subset_1 @ (k16_lattice3 @ X20 @ X21) @ (u1_struct_0 @ X20)))),
% 0.84/1.08      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.84/1.08  thf('36', plain,
% 0.84/1.08      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.84/1.08         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 0.84/1.08          | ((X26) != (k16_lattice3 @ X27 @ X28))
% 0.84/1.08          | ~ (r3_lattice3 @ X27 @ X29 @ X28)
% 0.84/1.08          | (r3_lattices @ X27 @ X29 @ X26)
% 0.84/1.08          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X27))
% 0.84/1.08          | ~ (l3_lattices @ X27)
% 0.84/1.08          | ~ (v4_lattice3 @ X27)
% 0.84/1.08          | ~ (v10_lattices @ X27)
% 0.84/1.08          | (v2_struct_0 @ X27))),
% 0.84/1.08      inference('cnf', [status(esa)], [t34_lattice3])).
% 0.84/1.08  thf('37', plain,
% 0.84/1.08      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.84/1.08         ((v2_struct_0 @ X27)
% 0.84/1.08          | ~ (v10_lattices @ X27)
% 0.84/1.08          | ~ (v4_lattice3 @ X27)
% 0.84/1.08          | ~ (l3_lattices @ X27)
% 0.84/1.08          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X27))
% 0.84/1.08          | (r3_lattices @ X27 @ X29 @ (k16_lattice3 @ X27 @ X28))
% 0.84/1.08          | ~ (r3_lattice3 @ X27 @ X29 @ X28)
% 0.84/1.08          | ~ (m1_subset_1 @ (k16_lattice3 @ X27 @ X28) @ (u1_struct_0 @ X27)))),
% 0.84/1.08      inference('simplify', [status(thm)], ['36'])).
% 0.84/1.08  thf('38', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.08         ((v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | ~ (r3_lattice3 @ X0 @ X2 @ X1)
% 0.84/1.08          | (r3_lattices @ X0 @ X2 @ (k16_lattice3 @ X0 @ X1))
% 0.84/1.08          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | ~ (v4_lattice3 @ X0)
% 0.84/1.08          | ~ (v10_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0))),
% 0.84/1.08      inference('sup-', [status(thm)], ['35', '37'])).
% 0.84/1.08  thf('39', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.08         (~ (v10_lattices @ X0)
% 0.84/1.08          | ~ (v4_lattice3 @ X0)
% 0.84/1.08          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.84/1.08          | (r3_lattices @ X0 @ X2 @ (k16_lattice3 @ X0 @ X1))
% 0.84/1.08          | ~ (r3_lattice3 @ X0 @ X2 @ X1)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0))),
% 0.84/1.08      inference('simplify', [status(thm)], ['38'])).
% 0.84/1.08  thf('40', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.08         ((v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | ~ (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.84/1.08          | (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 0.84/1.08             (k16_lattice3 @ X0 @ X2))
% 0.84/1.08          | ~ (v4_lattice3 @ X0)
% 0.84/1.08          | ~ (v10_lattices @ X0))),
% 0.84/1.08      inference('sup-', [status(thm)], ['34', '39'])).
% 0.84/1.08  thf('41', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.08         (~ (v10_lattices @ X0)
% 0.84/1.08          | ~ (v4_lattice3 @ X0)
% 0.84/1.08          | (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 0.84/1.08             (k16_lattice3 @ X0 @ X2))
% 0.84/1.08          | ~ (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0))),
% 0.84/1.08      inference('simplify', [status(thm)], ['40'])).
% 0.84/1.08  thf('42', plain,
% 0.84/1.08      (![X0 : $i]:
% 0.84/1.08         (~ (l3_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0)
% 0.84/1.08          | ~ (v4_lattice3 @ X0)
% 0.84/1.08          | ~ (v10_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ sk_C_1) @ 
% 0.84/1.08             (k16_lattice3 @ X0 @ sk_B))
% 0.84/1.08          | ~ (v4_lattice3 @ X0)
% 0.84/1.08          | ~ (v10_lattices @ X0))),
% 0.84/1.08      inference('sup-', [status(thm)], ['33', '41'])).
% 0.84/1.08  thf('43', plain,
% 0.84/1.08      (![X0 : $i]:
% 0.84/1.08         ((r3_lattices @ X0 @ (k16_lattice3 @ X0 @ sk_C_1) @ 
% 0.84/1.08           (k16_lattice3 @ X0 @ sk_B))
% 0.84/1.08          | ~ (v10_lattices @ X0)
% 0.84/1.08          | ~ (v4_lattice3 @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0))),
% 0.84/1.08      inference('simplify', [status(thm)], ['42'])).
% 0.84/1.08  thf('44', plain,
% 0.84/1.08      ((~ (r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 0.84/1.08           (k15_lattice3 @ sk_A @ sk_C_1))
% 0.84/1.08        | ~ (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C_1) @ 
% 0.84/1.08             (k16_lattice3 @ sk_A @ sk_B)))),
% 0.84/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.08  thf('45', plain,
% 0.84/1.08      ((~ (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C_1) @ 
% 0.84/1.08           (k16_lattice3 @ sk_A @ sk_B)))
% 0.84/1.08         <= (~
% 0.84/1.08             ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C_1) @ 
% 0.84/1.08               (k16_lattice3 @ sk_A @ sk_B))))),
% 0.84/1.08      inference('split', [status(esa)], ['44'])).
% 0.84/1.08  thf(t37_lattice3, axiom,
% 0.84/1.08    (![A:$i]:
% 0.84/1.08     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.84/1.08         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.84/1.08       ( ![B:$i]:
% 0.84/1.08         ( ( k15_lattice3 @ A @ B ) =
% 0.84/1.08           ( k16_lattice3 @ A @ ( a_2_2_lattice3 @ A @ B ) ) ) ) ))).
% 0.84/1.08  thf('46', plain,
% 0.84/1.08      (![X31 : $i, X32 : $i]:
% 0.84/1.08         (((k15_lattice3 @ X31 @ X32)
% 0.84/1.08            = (k16_lattice3 @ X31 @ (a_2_2_lattice3 @ X31 @ X32)))
% 0.84/1.08          | ~ (l3_lattices @ X31)
% 0.84/1.08          | ~ (v4_lattice3 @ X31)
% 0.84/1.08          | ~ (v10_lattices @ X31)
% 0.84/1.08          | (v2_struct_0 @ X31))),
% 0.84/1.08      inference('cnf', [status(esa)], [t37_lattice3])).
% 0.84/1.08  thf(dt_k15_lattice3, axiom,
% 0.84/1.08    (![A:$i,B:$i]:
% 0.84/1.08     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.84/1.08       ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.84/1.08  thf('47', plain,
% 0.84/1.08      (![X18 : $i, X19 : $i]:
% 0.84/1.08         (~ (l3_lattices @ X18)
% 0.84/1.08          | (v2_struct_0 @ X18)
% 0.84/1.08          | (m1_subset_1 @ (k15_lattice3 @ X18 @ X19) @ (u1_struct_0 @ X18)))),
% 0.84/1.08      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.84/1.08  thf('48', plain,
% 0.84/1.08      (![X18 : $i, X19 : $i]:
% 0.84/1.08         (~ (l3_lattices @ X18)
% 0.84/1.08          | (v2_struct_0 @ X18)
% 0.84/1.08          | (m1_subset_1 @ (k15_lattice3 @ X18 @ X19) @ (u1_struct_0 @ X18)))),
% 0.84/1.08      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.84/1.08  thf(d17_lattice3, axiom,
% 0.84/1.08    (![A:$i]:
% 0.84/1.08     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.84/1.08       ( ![B:$i]:
% 0.84/1.08         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.84/1.08           ( ![C:$i]:
% 0.84/1.08             ( ( r4_lattice3 @ A @ B @ C ) <=>
% 0.84/1.08               ( ![D:$i]:
% 0.84/1.08                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.84/1.08                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ))).
% 0.84/1.08  thf('49', plain,
% 0.84/1.08      (![X13 : $i, X14 : $i, X17 : $i]:
% 0.84/1.08         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.84/1.08          | (r2_hidden @ (sk_D_1 @ X17 @ X13 @ X14) @ X17)
% 0.84/1.08          | (r4_lattice3 @ X14 @ X13 @ X17)
% 0.84/1.08          | ~ (l3_lattices @ X14)
% 0.84/1.08          | (v2_struct_0 @ X14))),
% 0.84/1.08      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.84/1.08  thf('50', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.08         ((v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.84/1.08          | (r2_hidden @ (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X2))),
% 0.84/1.08      inference('sup-', [status(thm)], ['48', '49'])).
% 0.84/1.08  thf('51', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.08         ((r2_hidden @ (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X2)
% 0.84/1.08          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0))),
% 0.84/1.08      inference('simplify', [status(thm)], ['50'])).
% 0.84/1.08  thf('52', plain,
% 0.84/1.08      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.84/1.08      inference('sup-', [status(thm)], ['5', '6'])).
% 0.84/1.08  thf('53', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i]:
% 0.84/1.08         ((v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ sk_B)
% 0.84/1.08          | (r2_hidden @ (sk_D_1 @ sk_B @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.84/1.08             sk_C_1))),
% 0.84/1.08      inference('sup-', [status(thm)], ['51', '52'])).
% 0.84/1.08  thf('54', plain,
% 0.84/1.08      (![X18 : $i, X19 : $i]:
% 0.84/1.08         (~ (l3_lattices @ X18)
% 0.84/1.08          | (v2_struct_0 @ X18)
% 0.84/1.08          | (m1_subset_1 @ (k15_lattice3 @ X18 @ X19) @ (u1_struct_0 @ X18)))),
% 0.84/1.08      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.84/1.08  thf('55', plain,
% 0.84/1.08      (![X13 : $i, X14 : $i, X17 : $i]:
% 0.84/1.08         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.84/1.08          | (m1_subset_1 @ (sk_D_1 @ X17 @ X13 @ X14) @ (u1_struct_0 @ X14))
% 0.84/1.08          | (r4_lattice3 @ X14 @ X13 @ X17)
% 0.84/1.08          | ~ (l3_lattices @ X14)
% 0.84/1.08          | (v2_struct_0 @ X14))),
% 0.84/1.08      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.84/1.08  thf('56', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.08         ((v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.84/1.08          | (m1_subset_1 @ (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.84/1.08             (u1_struct_0 @ X0)))),
% 0.84/1.08      inference('sup-', [status(thm)], ['54', '55'])).
% 0.84/1.08  thf('57', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.08         ((m1_subset_1 @ (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.84/1.08           (u1_struct_0 @ X0))
% 0.84/1.08          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0))),
% 0.84/1.08      inference('simplify', [status(thm)], ['56'])).
% 0.84/1.08  thf(t38_lattice3, axiom,
% 0.84/1.08    (![A:$i]:
% 0.84/1.08     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.84/1.08         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.84/1.08       ( ![B:$i]:
% 0.84/1.08         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.84/1.08           ( ![C:$i]:
% 0.84/1.08             ( ( r2_hidden @ B @ C ) =>
% 0.84/1.08               ( ( r3_lattices @ A @ B @ ( k15_lattice3 @ A @ C ) ) & 
% 0.84/1.08                 ( r3_lattices @ A @ ( k16_lattice3 @ A @ C ) @ B ) ) ) ) ) ) ))).
% 0.84/1.08  thf('58', plain,
% 0.84/1.08      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.84/1.08         (~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X34))
% 0.84/1.08          | (r3_lattices @ X34 @ X33 @ (k15_lattice3 @ X34 @ X35))
% 0.84/1.08          | ~ (r2_hidden @ X33 @ X35)
% 0.84/1.08          | ~ (l3_lattices @ X34)
% 0.84/1.08          | ~ (v4_lattice3 @ X34)
% 0.84/1.08          | ~ (v10_lattices @ X34)
% 0.84/1.08          | (v2_struct_0 @ X34))),
% 0.84/1.08      inference('cnf', [status(esa)], [t38_lattice3])).
% 0.84/1.08  thf('59', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.84/1.08         ((v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.84/1.08          | (v2_struct_0 @ X0)
% 0.84/1.08          | ~ (v10_lattices @ X0)
% 0.84/1.08          | ~ (v4_lattice3 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | ~ (r2_hidden @ (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X3)
% 0.84/1.08          | (r3_lattices @ X0 @ 
% 0.84/1.08             (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.84/1.08             (k15_lattice3 @ X0 @ X3)))),
% 0.84/1.08      inference('sup-', [status(thm)], ['57', '58'])).
% 0.84/1.08  thf('60', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.84/1.08         ((r3_lattices @ X0 @ (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.84/1.08           (k15_lattice3 @ X0 @ X3))
% 0.84/1.08          | ~ (r2_hidden @ (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X3)
% 0.84/1.08          | ~ (v4_lattice3 @ X0)
% 0.84/1.08          | ~ (v10_lattices @ X0)
% 0.84/1.08          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0))),
% 0.84/1.08      inference('simplify', [status(thm)], ['59'])).
% 0.84/1.08  thf('61', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i]:
% 0.84/1.08         ((r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ sk_B)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ sk_B)
% 0.84/1.08          | ~ (v10_lattices @ X0)
% 0.84/1.08          | ~ (v4_lattice3 @ X0)
% 0.84/1.08          | (r3_lattices @ X0 @ 
% 0.84/1.08             (sk_D_1 @ sk_B @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.84/1.08             (k15_lattice3 @ X0 @ sk_C_1)))),
% 0.84/1.08      inference('sup-', [status(thm)], ['53', '60'])).
% 0.84/1.08  thf('62', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i]:
% 0.84/1.08         ((r3_lattices @ X0 @ 
% 0.84/1.08           (sk_D_1 @ sk_B @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.84/1.08           (k15_lattice3 @ X0 @ sk_C_1))
% 0.84/1.08          | ~ (v4_lattice3 @ X0)
% 0.84/1.08          | ~ (v10_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ sk_B))),
% 0.84/1.08      inference('simplify', [status(thm)], ['61'])).
% 0.84/1.08  thf('63', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.08         ((m1_subset_1 @ (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.84/1.08           (u1_struct_0 @ X0))
% 0.84/1.08          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0))),
% 0.84/1.08      inference('simplify', [status(thm)], ['56'])).
% 0.84/1.08  thf(redefinition_r3_lattices, axiom,
% 0.84/1.08    (![A:$i,B:$i,C:$i]:
% 0.84/1.08     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.84/1.08         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 0.84/1.08         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.84/1.08         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.08       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 0.84/1.08  thf('64', plain,
% 0.84/1.08      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.84/1.08         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 0.84/1.08          | ~ (l3_lattices @ X6)
% 0.84/1.08          | ~ (v9_lattices @ X6)
% 0.84/1.08          | ~ (v8_lattices @ X6)
% 0.84/1.08          | ~ (v6_lattices @ X6)
% 0.84/1.08          | (v2_struct_0 @ X6)
% 0.84/1.08          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 0.84/1.08          | (r1_lattices @ X6 @ X5 @ X7)
% 0.84/1.08          | ~ (r3_lattices @ X6 @ X5 @ X7))),
% 0.84/1.08      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.84/1.08  thf('65', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.84/1.08         ((v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.84/1.08          | ~ (r3_lattices @ X0 @ 
% 0.84/1.08               (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X3)
% 0.84/1.08          | (r1_lattices @ X0 @ 
% 0.84/1.08             (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X3)
% 0.84/1.08          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X0))
% 0.84/1.08          | (v2_struct_0 @ X0)
% 0.84/1.08          | ~ (v6_lattices @ X0)
% 0.84/1.08          | ~ (v8_lattices @ X0)
% 0.84/1.08          | ~ (v9_lattices @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0))),
% 0.84/1.08      inference('sup-', [status(thm)], ['63', '64'])).
% 0.84/1.08  thf('66', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.84/1.08         (~ (v9_lattices @ X0)
% 0.84/1.08          | ~ (v8_lattices @ X0)
% 0.84/1.08          | ~ (v6_lattices @ X0)
% 0.84/1.08          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X0))
% 0.84/1.08          | (r1_lattices @ X0 @ 
% 0.84/1.08             (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X3)
% 0.84/1.08          | ~ (r3_lattices @ X0 @ 
% 0.84/1.08               (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X3)
% 0.84/1.08          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0))),
% 0.84/1.08      inference('simplify', [status(thm)], ['65'])).
% 0.84/1.08  thf('67', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i]:
% 0.84/1.08         ((r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ sk_B)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0)
% 0.84/1.08          | ~ (v10_lattices @ X0)
% 0.84/1.08          | ~ (v4_lattice3 @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ sk_B)
% 0.84/1.08          | (r1_lattices @ X0 @ 
% 0.84/1.08             (sk_D_1 @ sk_B @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.84/1.08             (k15_lattice3 @ X0 @ sk_C_1))
% 0.84/1.08          | ~ (m1_subset_1 @ (k15_lattice3 @ X0 @ sk_C_1) @ (u1_struct_0 @ X0))
% 0.84/1.08          | ~ (v6_lattices @ X0)
% 0.84/1.08          | ~ (v8_lattices @ X0)
% 0.84/1.08          | ~ (v9_lattices @ X0))),
% 0.84/1.08      inference('sup-', [status(thm)], ['62', '66'])).
% 0.84/1.08  thf('68', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i]:
% 0.84/1.08         (~ (v9_lattices @ X0)
% 0.84/1.08          | ~ (v8_lattices @ X0)
% 0.84/1.08          | ~ (v6_lattices @ X0)
% 0.84/1.08          | ~ (m1_subset_1 @ (k15_lattice3 @ X0 @ sk_C_1) @ (u1_struct_0 @ X0))
% 0.84/1.08          | (r1_lattices @ X0 @ 
% 0.84/1.08             (sk_D_1 @ sk_B @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.84/1.08             (k15_lattice3 @ X0 @ sk_C_1))
% 0.84/1.08          | ~ (v4_lattice3 @ X0)
% 0.84/1.08          | ~ (v10_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ sk_B))),
% 0.84/1.08      inference('simplify', [status(thm)], ['67'])).
% 0.84/1.08  thf('69', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i]:
% 0.84/1.08         ((v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ sk_B)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0)
% 0.84/1.08          | ~ (v10_lattices @ X0)
% 0.84/1.08          | ~ (v4_lattice3 @ X0)
% 0.84/1.08          | (r1_lattices @ X0 @ 
% 0.84/1.08             (sk_D_1 @ sk_B @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.84/1.08             (k15_lattice3 @ X0 @ sk_C_1))
% 0.84/1.08          | ~ (v6_lattices @ X0)
% 0.84/1.08          | ~ (v8_lattices @ X0)
% 0.84/1.08          | ~ (v9_lattices @ X0))),
% 0.84/1.08      inference('sup-', [status(thm)], ['47', '68'])).
% 0.84/1.08  thf('70', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i]:
% 0.84/1.08         (~ (v9_lattices @ X0)
% 0.84/1.08          | ~ (v8_lattices @ X0)
% 0.84/1.08          | ~ (v6_lattices @ X0)
% 0.84/1.08          | (r1_lattices @ X0 @ 
% 0.84/1.08             (sk_D_1 @ sk_B @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.84/1.08             (k15_lattice3 @ X0 @ sk_C_1))
% 0.84/1.08          | ~ (v4_lattice3 @ X0)
% 0.84/1.08          | ~ (v10_lattices @ X0)
% 0.84/1.08          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ sk_B)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0))),
% 0.84/1.08      inference('simplify', [status(thm)], ['69'])).
% 0.84/1.08  thf('71', plain,
% 0.84/1.08      (![X18 : $i, X19 : $i]:
% 0.84/1.08         (~ (l3_lattices @ X18)
% 0.84/1.08          | (v2_struct_0 @ X18)
% 0.84/1.08          | (m1_subset_1 @ (k15_lattice3 @ X18 @ X19) @ (u1_struct_0 @ X18)))),
% 0.84/1.08      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.84/1.08  thf('72', plain,
% 0.84/1.08      (![X13 : $i, X14 : $i, X17 : $i]:
% 0.84/1.08         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.84/1.08          | ~ (r1_lattices @ X14 @ (sk_D_1 @ X17 @ X13 @ X14) @ X13)
% 0.84/1.08          | (r4_lattice3 @ X14 @ X13 @ X17)
% 0.84/1.08          | ~ (l3_lattices @ X14)
% 0.84/1.08          | (v2_struct_0 @ X14))),
% 0.84/1.08      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.84/1.08  thf('73', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.08         ((v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.84/1.08          | ~ (r1_lattices @ X0 @ 
% 0.84/1.08               (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.84/1.08               (k15_lattice3 @ X0 @ X1)))),
% 0.84/1.08      inference('sup-', [status(thm)], ['71', '72'])).
% 0.84/1.08  thf('74', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.08         (~ (r1_lattices @ X0 @ 
% 0.84/1.08             (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.84/1.08             (k15_lattice3 @ X0 @ X1))
% 0.84/1.08          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0))),
% 0.84/1.08      inference('simplify', [status(thm)], ['73'])).
% 0.84/1.08  thf('75', plain,
% 0.84/1.08      (![X0 : $i]:
% 0.84/1.08         ((v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ sk_C_1) @ sk_B)
% 0.84/1.08          | ~ (v10_lattices @ X0)
% 0.84/1.08          | ~ (v4_lattice3 @ X0)
% 0.84/1.08          | ~ (v6_lattices @ X0)
% 0.84/1.08          | ~ (v8_lattices @ X0)
% 0.84/1.08          | ~ (v9_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ sk_C_1) @ sk_B))),
% 0.84/1.08      inference('sup-', [status(thm)], ['70', '74'])).
% 0.84/1.08  thf('76', plain,
% 0.84/1.08      (![X0 : $i]:
% 0.84/1.08         (~ (v9_lattices @ X0)
% 0.84/1.08          | ~ (v8_lattices @ X0)
% 0.84/1.08          | ~ (v6_lattices @ X0)
% 0.84/1.08          | ~ (v4_lattice3 @ X0)
% 0.84/1.08          | ~ (v10_lattices @ X0)
% 0.84/1.08          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ sk_C_1) @ sk_B)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0))),
% 0.84/1.08      inference('simplify', [status(thm)], ['75'])).
% 0.84/1.08  thf('77', plain,
% 0.84/1.08      (![X18 : $i, X19 : $i]:
% 0.84/1.08         (~ (l3_lattices @ X18)
% 0.84/1.08          | (v2_struct_0 @ X18)
% 0.84/1.08          | (m1_subset_1 @ (k15_lattice3 @ X18 @ X19) @ (u1_struct_0 @ X18)))),
% 0.84/1.08      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.84/1.08  thf(fraenkel_a_2_2_lattice3, axiom,
% 0.84/1.08    (![A:$i,B:$i,C:$i]:
% 0.84/1.08     ( ( ( ~( v2_struct_0 @ B ) ) & ( v10_lattices @ B ) & 
% 0.84/1.08         ( v4_lattice3 @ B ) & ( l3_lattices @ B ) ) =>
% 0.84/1.08       ( ( r2_hidden @ A @ ( a_2_2_lattice3 @ B @ C ) ) <=>
% 0.84/1.08         ( ?[D:$i]:
% 0.84/1.08           ( ( r4_lattice3 @ B @ D @ C ) & ( ( A ) = ( D ) ) & 
% 0.84/1.08             ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.84/1.08  thf('78', plain,
% 0.84/1.08      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.84/1.08         (~ (l3_lattices @ X22)
% 0.84/1.08          | ~ (v4_lattice3 @ X22)
% 0.84/1.08          | ~ (v10_lattices @ X22)
% 0.84/1.08          | (v2_struct_0 @ X22)
% 0.84/1.08          | (r2_hidden @ X24 @ (a_2_2_lattice3 @ X22 @ X23))
% 0.84/1.08          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X22))
% 0.84/1.08          | ((X24) != (X25))
% 0.84/1.08          | ~ (r4_lattice3 @ X22 @ X25 @ X23))),
% 0.84/1.08      inference('cnf', [status(esa)], [fraenkel_a_2_2_lattice3])).
% 0.84/1.08  thf('79', plain,
% 0.84/1.08      (![X22 : $i, X23 : $i, X25 : $i]:
% 0.84/1.08         (~ (r4_lattice3 @ X22 @ X25 @ X23)
% 0.84/1.08          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X22))
% 0.84/1.08          | (r2_hidden @ X25 @ (a_2_2_lattice3 @ X22 @ X23))
% 0.84/1.08          | (v2_struct_0 @ X22)
% 0.84/1.08          | ~ (v10_lattices @ X22)
% 0.84/1.08          | ~ (v4_lattice3 @ X22)
% 0.84/1.08          | ~ (l3_lattices @ X22))),
% 0.84/1.08      inference('simplify', [status(thm)], ['78'])).
% 0.84/1.08  thf('80', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.08         ((v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | ~ (v4_lattice3 @ X0)
% 0.84/1.08          | ~ (v10_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0)
% 0.84/1.08          | (r2_hidden @ (k15_lattice3 @ X0 @ X1) @ (a_2_2_lattice3 @ X0 @ X2))
% 0.84/1.08          | ~ (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))),
% 0.84/1.08      inference('sup-', [status(thm)], ['77', '79'])).
% 0.84/1.08  thf('81', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.08         (~ (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.84/1.08          | (r2_hidden @ (k15_lattice3 @ X0 @ X1) @ (a_2_2_lattice3 @ X0 @ X2))
% 0.84/1.08          | ~ (v10_lattices @ X0)
% 0.84/1.08          | ~ (v4_lattice3 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0))),
% 0.84/1.08      inference('simplify', [status(thm)], ['80'])).
% 0.84/1.08  thf('82', plain,
% 0.84/1.08      (![X0 : $i]:
% 0.84/1.08         ((v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | ~ (v10_lattices @ X0)
% 0.84/1.08          | ~ (v4_lattice3 @ X0)
% 0.84/1.08          | ~ (v6_lattices @ X0)
% 0.84/1.08          | ~ (v8_lattices @ X0)
% 0.84/1.08          | ~ (v9_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | ~ (v4_lattice3 @ X0)
% 0.84/1.08          | ~ (v10_lattices @ X0)
% 0.84/1.08          | (r2_hidden @ (k15_lattice3 @ X0 @ sk_C_1) @ 
% 0.84/1.08             (a_2_2_lattice3 @ X0 @ sk_B)))),
% 0.84/1.08      inference('sup-', [status(thm)], ['76', '81'])).
% 0.84/1.08  thf('83', plain,
% 0.84/1.08      (![X0 : $i]:
% 0.84/1.08         ((r2_hidden @ (k15_lattice3 @ X0 @ sk_C_1) @ 
% 0.84/1.08           (a_2_2_lattice3 @ X0 @ sk_B))
% 0.84/1.08          | ~ (v9_lattices @ X0)
% 0.84/1.08          | ~ (v8_lattices @ X0)
% 0.84/1.08          | ~ (v6_lattices @ X0)
% 0.84/1.08          | ~ (v4_lattice3 @ X0)
% 0.84/1.08          | ~ (v10_lattices @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0))),
% 0.84/1.08      inference('simplify', [status(thm)], ['82'])).
% 0.84/1.08  thf('84', plain,
% 0.84/1.08      (![X18 : $i, X19 : $i]:
% 0.84/1.08         (~ (l3_lattices @ X18)
% 0.84/1.08          | (v2_struct_0 @ X18)
% 0.84/1.08          | (m1_subset_1 @ (k15_lattice3 @ X18 @ X19) @ (u1_struct_0 @ X18)))),
% 0.84/1.08      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.84/1.08  thf('85', plain,
% 0.84/1.08      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.84/1.08         (~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X34))
% 0.84/1.08          | (r3_lattices @ X34 @ (k16_lattice3 @ X34 @ X35) @ X33)
% 0.84/1.08          | ~ (r2_hidden @ X33 @ X35)
% 0.84/1.08          | ~ (l3_lattices @ X34)
% 0.84/1.08          | ~ (v4_lattice3 @ X34)
% 0.84/1.08          | ~ (v10_lattices @ X34)
% 0.84/1.08          | (v2_struct_0 @ X34))),
% 0.84/1.08      inference('cnf', [status(esa)], [t38_lattice3])).
% 0.84/1.08  thf('86', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.08         ((v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0)
% 0.84/1.08          | ~ (v10_lattices @ X0)
% 0.84/1.08          | ~ (v4_lattice3 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | ~ (r2_hidden @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.84/1.08          | (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X2) @ 
% 0.84/1.08             (k15_lattice3 @ X0 @ X1)))),
% 0.84/1.08      inference('sup-', [status(thm)], ['84', '85'])).
% 0.84/1.08  thf('87', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.08         ((r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X2) @ 
% 0.84/1.08           (k15_lattice3 @ X0 @ X1))
% 0.84/1.08          | ~ (r2_hidden @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.84/1.08          | ~ (v4_lattice3 @ X0)
% 0.84/1.08          | ~ (v10_lattices @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0))),
% 0.84/1.08      inference('simplify', [status(thm)], ['86'])).
% 0.84/1.08  thf('88', plain,
% 0.84/1.08      (![X0 : $i]:
% 0.84/1.08         ((v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | ~ (v10_lattices @ X0)
% 0.84/1.08          | ~ (v4_lattice3 @ X0)
% 0.84/1.08          | ~ (v6_lattices @ X0)
% 0.84/1.08          | ~ (v8_lattices @ X0)
% 0.84/1.08          | ~ (v9_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | ~ (v10_lattices @ X0)
% 0.84/1.08          | ~ (v4_lattice3 @ X0)
% 0.84/1.08          | (r3_lattices @ X0 @ 
% 0.84/1.08             (k16_lattice3 @ X0 @ (a_2_2_lattice3 @ X0 @ sk_B)) @ 
% 0.84/1.08             (k15_lattice3 @ X0 @ sk_C_1)))),
% 0.84/1.08      inference('sup-', [status(thm)], ['83', '87'])).
% 0.84/1.08  thf('89', plain,
% 0.84/1.08      (![X0 : $i]:
% 0.84/1.08         ((r3_lattices @ X0 @ 
% 0.84/1.08           (k16_lattice3 @ X0 @ (a_2_2_lattice3 @ X0 @ sk_B)) @ 
% 0.84/1.08           (k15_lattice3 @ X0 @ sk_C_1))
% 0.84/1.08          | ~ (v9_lattices @ X0)
% 0.84/1.08          | ~ (v8_lattices @ X0)
% 0.84/1.08          | ~ (v6_lattices @ X0)
% 0.84/1.08          | ~ (v4_lattice3 @ X0)
% 0.84/1.08          | ~ (v10_lattices @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0))),
% 0.84/1.08      inference('simplify', [status(thm)], ['88'])).
% 0.84/1.08  thf('90', plain,
% 0.84/1.08      (![X0 : $i]:
% 0.84/1.08         ((r3_lattices @ X0 @ (k15_lattice3 @ X0 @ sk_B) @ 
% 0.84/1.08           (k15_lattice3 @ X0 @ sk_C_1))
% 0.84/1.08          | (v2_struct_0 @ X0)
% 0.84/1.08          | ~ (v10_lattices @ X0)
% 0.84/1.08          | ~ (v4_lattice3 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | ~ (v10_lattices @ X0)
% 0.84/1.08          | ~ (v4_lattice3 @ X0)
% 0.84/1.08          | ~ (v6_lattices @ X0)
% 0.84/1.08          | ~ (v8_lattices @ X0)
% 0.84/1.08          | ~ (v9_lattices @ X0))),
% 0.84/1.08      inference('sup+', [status(thm)], ['46', '89'])).
% 0.84/1.08  thf('91', plain,
% 0.84/1.08      (![X0 : $i]:
% 0.84/1.08         (~ (v9_lattices @ X0)
% 0.84/1.08          | ~ (v8_lattices @ X0)
% 0.84/1.08          | ~ (v6_lattices @ X0)
% 0.84/1.08          | ~ (l3_lattices @ X0)
% 0.84/1.08          | ~ (v4_lattice3 @ X0)
% 0.84/1.08          | ~ (v10_lattices @ X0)
% 0.84/1.08          | (v2_struct_0 @ X0)
% 0.84/1.08          | (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ sk_B) @ 
% 0.84/1.08             (k15_lattice3 @ X0 @ sk_C_1)))),
% 0.84/1.08      inference('simplify', [status(thm)], ['90'])).
% 0.84/1.08  thf('92', plain,
% 0.84/1.08      ((~ (r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 0.84/1.08           (k15_lattice3 @ sk_A @ sk_C_1)))
% 0.84/1.08         <= (~
% 0.84/1.08             ((r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 0.84/1.08               (k15_lattice3 @ sk_A @ sk_C_1))))),
% 0.84/1.08      inference('split', [status(esa)], ['44'])).
% 0.84/1.08  thf('93', plain,
% 0.84/1.08      ((((v2_struct_0 @ sk_A)
% 0.84/1.08         | ~ (v10_lattices @ sk_A)
% 0.84/1.08         | ~ (v4_lattice3 @ sk_A)
% 0.84/1.08         | ~ (l3_lattices @ sk_A)
% 0.84/1.08         | ~ (v6_lattices @ sk_A)
% 0.84/1.08         | ~ (v8_lattices @ sk_A)
% 0.84/1.08         | ~ (v9_lattices @ sk_A)))
% 0.84/1.08         <= (~
% 0.84/1.08             ((r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 0.84/1.08               (k15_lattice3 @ sk_A @ sk_C_1))))),
% 0.84/1.08      inference('sup-', [status(thm)], ['91', '92'])).
% 0.84/1.08  thf('94', plain, ((v10_lattices @ sk_A)),
% 0.84/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.08  thf('95', plain, ((v4_lattice3 @ sk_A)),
% 0.84/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.08  thf('96', plain, ((l3_lattices @ sk_A)),
% 0.84/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.08  thf(cc1_lattices, axiom,
% 0.84/1.08    (![A:$i]:
% 0.84/1.08     ( ( l3_lattices @ A ) =>
% 0.84/1.08       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.84/1.08         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.84/1.08           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.84/1.08           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.84/1.08  thf('97', plain,
% 0.84/1.08      (![X4 : $i]:
% 0.84/1.08         ((v2_struct_0 @ X4)
% 0.84/1.08          | ~ (v10_lattices @ X4)
% 0.84/1.08          | (v6_lattices @ X4)
% 0.84/1.08          | ~ (l3_lattices @ X4))),
% 0.84/1.08      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.84/1.08  thf('98', plain, (~ (v2_struct_0 @ sk_A)),
% 0.84/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.08  thf('99', plain,
% 0.84/1.08      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.84/1.08      inference('sup-', [status(thm)], ['97', '98'])).
% 0.84/1.08  thf('100', plain, ((l3_lattices @ sk_A)),
% 0.84/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.08  thf('101', plain, ((v10_lattices @ sk_A)),
% 0.84/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.08  thf('102', plain, ((v6_lattices @ sk_A)),
% 0.84/1.08      inference('demod', [status(thm)], ['99', '100', '101'])).
% 0.84/1.08  thf('103', plain,
% 0.84/1.08      (![X4 : $i]:
% 0.84/1.08         ((v2_struct_0 @ X4)
% 0.84/1.08          | ~ (v10_lattices @ X4)
% 0.84/1.08          | (v8_lattices @ X4)
% 0.84/1.08          | ~ (l3_lattices @ X4))),
% 0.84/1.08      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.84/1.08  thf('104', plain, (~ (v2_struct_0 @ sk_A)),
% 0.84/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.08  thf('105', plain,
% 0.84/1.08      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.84/1.08      inference('sup-', [status(thm)], ['103', '104'])).
% 0.84/1.08  thf('106', plain, ((l3_lattices @ sk_A)),
% 0.84/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.08  thf('107', plain, ((v10_lattices @ sk_A)),
% 0.84/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.08  thf('108', plain, ((v8_lattices @ sk_A)),
% 0.84/1.08      inference('demod', [status(thm)], ['105', '106', '107'])).
% 0.84/1.08  thf('109', plain,
% 0.84/1.08      (![X4 : $i]:
% 0.84/1.08         ((v2_struct_0 @ X4)
% 0.84/1.08          | ~ (v10_lattices @ X4)
% 0.84/1.08          | (v9_lattices @ X4)
% 0.84/1.08          | ~ (l3_lattices @ X4))),
% 0.84/1.08      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.84/1.08  thf('110', plain, (~ (v2_struct_0 @ sk_A)),
% 0.84/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.08  thf('111', plain,
% 0.84/1.08      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.84/1.08      inference('sup-', [status(thm)], ['109', '110'])).
% 0.84/1.08  thf('112', plain, ((l3_lattices @ sk_A)),
% 0.84/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.08  thf('113', plain, ((v10_lattices @ sk_A)),
% 0.84/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.08  thf('114', plain, ((v9_lattices @ sk_A)),
% 0.84/1.08      inference('demod', [status(thm)], ['111', '112', '113'])).
% 0.84/1.08  thf('115', plain,
% 0.84/1.08      (((v2_struct_0 @ sk_A))
% 0.84/1.08         <= (~
% 0.84/1.08             ((r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 0.84/1.08               (k15_lattice3 @ sk_A @ sk_C_1))))),
% 0.84/1.08      inference('demod', [status(thm)],
% 0.84/1.08                ['93', '94', '95', '96', '102', '108', '114'])).
% 0.84/1.08  thf('116', plain, (~ (v2_struct_0 @ sk_A)),
% 0.84/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.08  thf('117', plain,
% 0.84/1.08      (((r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 0.84/1.08         (k15_lattice3 @ sk_A @ sk_C_1)))),
% 0.84/1.08      inference('sup-', [status(thm)], ['115', '116'])).
% 0.84/1.08  thf('118', plain,
% 0.84/1.08      (~
% 0.84/1.08       ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C_1) @ 
% 0.84/1.08         (k16_lattice3 @ sk_A @ sk_B))) | 
% 0.84/1.08       ~
% 0.84/1.08       ((r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 0.84/1.08         (k15_lattice3 @ sk_A @ sk_C_1)))),
% 0.84/1.08      inference('split', [status(esa)], ['44'])).
% 0.84/1.08  thf('119', plain,
% 0.84/1.08      (~
% 0.84/1.08       ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C_1) @ 
% 0.84/1.08         (k16_lattice3 @ sk_A @ sk_B)))),
% 0.84/1.08      inference('sat_resolution*', [status(thm)], ['117', '118'])).
% 0.84/1.08  thf('120', plain,
% 0.84/1.08      (~ (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C_1) @ 
% 0.84/1.08          (k16_lattice3 @ sk_A @ sk_B))),
% 0.84/1.08      inference('simpl_trail', [status(thm)], ['45', '119'])).
% 0.84/1.08  thf('121', plain,
% 0.84/1.08      ((~ (l3_lattices @ sk_A)
% 0.84/1.08        | (v2_struct_0 @ sk_A)
% 0.84/1.08        | ~ (v4_lattice3 @ sk_A)
% 0.84/1.08        | ~ (v10_lattices @ sk_A))),
% 0.84/1.08      inference('sup-', [status(thm)], ['43', '120'])).
% 0.84/1.08  thf('122', plain, ((l3_lattices @ sk_A)),
% 0.84/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.08  thf('123', plain, ((v4_lattice3 @ sk_A)),
% 0.84/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.08  thf('124', plain, ((v10_lattices @ sk_A)),
% 0.84/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.08  thf('125', plain, ((v2_struct_0 @ sk_A)),
% 0.84/1.08      inference('demod', [status(thm)], ['121', '122', '123', '124'])).
% 0.84/1.08  thf('126', plain, ($false), inference('demod', [status(thm)], ['0', '125'])).
% 0.84/1.08  
% 0.84/1.08  % SZS output end Refutation
% 0.84/1.08  
% 0.84/1.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
