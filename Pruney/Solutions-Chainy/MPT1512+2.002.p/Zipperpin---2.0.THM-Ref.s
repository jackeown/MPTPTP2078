%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GXH8dOU9IS

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:33 EST 2020

% Result     : Theorem 0.56s
% Output     : Refutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 275 expanded)
%              Number of leaves         :   36 (  93 expanded)
%              Depth                    :   24
%              Number of atoms          : 2377 (4593 expanded)
%              Number of equality atoms :    3 (   4 expanded)
%              Maximal formula depth    :   20 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(r4_lattice3_type,type,(
    r4_lattice3: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X24: $i,X25: $i] :
      ( ~ ( l3_lattices @ X24 )
      | ( v2_struct_0 @ X24 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( ~ ( l3_lattices @ X24 )
      | ( v2_struct_0 @ X24 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ),
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

thf('13',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ( r3_lattices @ X27 @ ( k16_lattice3 @ X27 @ X28 ) @ X26 )
      | ~ ( r2_hidden @ X26 @ X28 )
      | ~ ( l3_lattices @ X27 )
      | ~ ( v4_lattice3 @ X27 )
      | ~ ( v10_lattices @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t38_lattice3])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) @ X3 )
      | ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X3 ) @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X3 ) @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) @ X3 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ sk_B )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ sk_B )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ sk_C_1 ) @ ( sk_D @ sk_B @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ sk_C_1 ) @ ( sk_D @ sk_B @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('19',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l3_lattices @ X24 )
      | ( v2_struct_0 @ X24 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

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

thf('20',plain,(
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

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X3 ) @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X3 ) @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X3 ) @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ~ ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X3 ) @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ sk_B )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ sk_B )
      | ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ sk_C_1 ) @ ( sk_D @ sk_B @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ sk_C_1 ) @ ( sk_D @ sk_B @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l3_lattices @ X24 )
      | ( v2_struct_0 @ X24 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf('28',plain,(
    ! [X8: $i,X9: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( r1_lattices @ X9 @ X8 @ ( sk_D @ X12 @ X8 @ X9 ) )
      | ( r3_lattice3 @ X9 @ X8 @ X12 )
      | ~ ( l3_lattices @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ sk_C_1 ) @ sk_B )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ sk_C_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ sk_C_1 ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l3_lattices @ X24 )
      | ( v2_struct_0 @ X24 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf(t40_lattice3,axiom,(
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

thf('34',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X30 ) )
      | ( r3_lattices @ X30 @ X29 @ ( k16_lattice3 @ X30 @ X31 ) )
      | ~ ( r3_lattice3 @ X30 @ X29 @ X31 )
      | ~ ( l3_lattices @ X30 )
      | ~ ( v4_lattice3 @ X30 )
      | ~ ( v10_lattices @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t40_lattice3])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( k16_lattice3 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( k16_lattice3 @ X0 @ X2 ) )
      | ~ ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ sk_C_1 ) @ ( k16_lattice3 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['32','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ sk_C_1 ) @ ( k16_lattice3 @ X0 @ sk_B ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ~ ( r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_C_1 ) )
    | ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C_1 ) @ ( k16_lattice3 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C_1 ) @ ( k16_lattice3 @ sk_A @ sk_B ) )
   <= ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C_1 ) @ ( k16_lattice3 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['39'])).

thf(dt_k15_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('41',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l3_lattices @ X22 )
      | ( v2_struct_0 @ X22 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X22 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) ),
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

thf('42',plain,(
    ! [X13: $i,X14: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ( r2_hidden @ ( sk_D_1 @ X17 @ X13 @ X14 ) @ X17 )
      | ( r4_lattice3 @ X14 @ X13 @ X17 )
      | ~ ( l3_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_B @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l3_lattices @ X22 )
      | ( v2_struct_0 @ X22 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X22 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('48',plain,(
    ! [X13: $i,X14: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X17 @ X13 @ X14 ) @ ( u1_struct_0 @ X14 ) )
      | ( r4_lattice3 @ X14 @ X13 @ X17 )
      | ~ ( l3_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( m1_subset_1 @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l3_lattices @ X22 )
      | ( v2_struct_0 @ X22 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X22 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) ),
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

thf('52',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v10_lattices @ X18 )
      | ~ ( v4_lattice3 @ X18 )
      | ~ ( l3_lattices @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ( X19
       != ( k15_lattice3 @ X18 @ X20 ) )
      | ( r4_lattice3 @ X18 @ X19 @ X20 )
      | ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('53',plain,(
    ! [X18: $i,X20: $i] :
      ( ( r4_lattice3 @ X18 @ ( k15_lattice3 @ X18 @ X20 ) @ X20 )
      | ~ ( m1_subset_1 @ ( k15_lattice3 @ X18 @ X20 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( l3_lattices @ X18 )
      | ~ ( v4_lattice3 @ X18 )
      | ~ ( v10_lattices @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X1 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l3_lattices @ X22 )
      | ( v2_struct_0 @ X22 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X22 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('57',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( r4_lattice3 @ X14 @ X13 @ X15 )
      | ~ ( r2_hidden @ X16 @ X15 )
      | ( r1_lattices @ X14 @ X16 @ X13 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l3_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X3 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ( r1_lattices @ X0 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
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
    inference('sup-',[status(thm)],['55','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r1_lattices @ X1 @ X2 @ ( k15_lattice3 @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r1_lattices @ X0 @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X3 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['50','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X3 )
      | ( r1_lattices @ X0 @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X3 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ sk_B )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ sk_B )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r1_lattices @ X0 @ ( sk_D_1 @ sk_B @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['46','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattices @ X0 @ ( sk_D_1 @ sk_B @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ sk_C_1 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l3_lattices @ X22 )
      | ( v2_struct_0 @ X22 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X22 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('67',plain,(
    ! [X13: $i,X14: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( r1_lattices @ X14 @ ( sk_D_1 @ X17 @ X13 @ X14 ) @ X13 )
      | ( r4_lattice3 @ X14 @ X13 @ X17 )
      | ~ ( l3_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_lattices @ X0 @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattices @ X0 @ ( sk_D_1 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ sk_C_1 ) @ sk_B )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ sk_C_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ sk_C_1 ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l3_lattices @ X22 )
      | ( v2_struct_0 @ X22 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X22 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('73',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l3_lattices @ X22 )
      | ( v2_struct_0 @ X22 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X22 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('74',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v10_lattices @ X18 )
      | ~ ( v4_lattice3 @ X18 )
      | ~ ( l3_lattices @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ( X19
       != ( k15_lattice3 @ X18 @ X20 ) )
      | ~ ( r4_lattice3 @ X18 @ X21 @ X20 )
      | ( r1_lattices @ X18 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('75',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X18 ) )
      | ( r1_lattices @ X18 @ ( k15_lattice3 @ X18 @ X20 ) @ X21 )
      | ~ ( r4_lattice3 @ X18 @ X21 @ X20 )
      | ~ ( m1_subset_1 @ ( k15_lattice3 @ X18 @ X20 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( l3_lattices @ X18 )
      | ~ ( v4_lattice3 @ X18 )
      | ~ ( v10_lattices @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
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
    inference('sup-',[status(thm)],['73','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r4_lattice3 @ X0 @ X2 @ X1 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['72','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ sk_B ) @ ( k15_lattice3 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['71','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ sk_B ) @ ( k15_lattice3 @ X0 @ sk_C_1 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l3_lattices @ X22 )
      | ( v2_struct_0 @ X22 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X22 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('83',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l3_lattices @ X22 )
      | ( v2_struct_0 @ X22 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X22 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('84',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l3_lattices @ X6 )
      | ~ ( v9_lattices @ X6 )
      | ~ ( v8_lattices @ X6 )
      | ~ ( v6_lattices @ X6 )
      | ( v2_struct_0 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ( r3_lattices @ X6 @ X5 @ X7 )
      | ~ ( r1_lattices @ X6 @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('85',plain,(
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
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
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
    inference('sup-',[status(thm)],['82','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ sk_B ) @ ( k15_lattice3 @ X0 @ sk_C_1 ) )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ sk_B ) @ ( k15_lattice3 @ X0 @ sk_C_1 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,
    ( ~ ( r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_C_1 ) )
   <= ~ ( r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['39'])).

thf('92',plain,
    ( ( ~ ( l3_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A ) )
   <= ~ ( r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v4_lattice3 @ sk_A ),
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

thf('96',plain,(
    ! [X4: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( v10_lattices @ X4 )
      | ( v6_lattices @ X4 )
      | ~ ( l3_lattices @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('97',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,(
    ! [X4: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( v10_lattices @ X4 )
      | ( v8_lattices @ X4 )
      | ~ ( l3_lattices @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,(
    ! [X4: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( v10_lattices @ X4 )
      | ( v9_lattices @ X4 )
      | ~ ( l3_lattices @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('114',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ~ ( r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['92','93','94','95','101','107','113'])).

thf('115',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C_1 ) @ ( k16_lattice3 @ sk_A @ sk_B ) )
    | ~ ( r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['39'])).

thf('118',plain,(
    ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C_1 ) @ ( k16_lattice3 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['116','117'])).

thf('119',plain,(
    ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C_1 ) @ ( k16_lattice3 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['40','118'])).

thf('120',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( v6_lattices @ sk_A )
    | ~ ( v8_lattices @ sk_A )
    | ~ ( v9_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['38','119'])).

thf('121',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('125',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('126',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('127',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['120','121','122','123','124','125','126'])).

thf('128',plain,(
    $false ),
    inference(demod,[status(thm)],['0','127'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GXH8dOU9IS
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:45:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.56/0.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.56/0.74  % Solved by: fo/fo7.sh
% 0.56/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.56/0.74  % done 288 iterations in 0.283s
% 0.56/0.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.56/0.74  % SZS output start Refutation
% 0.56/0.74  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 0.56/0.74  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 0.56/0.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.56/0.74  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 0.56/0.74  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.56/0.74  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.56/0.74  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.56/0.74  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.56/0.74  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.56/0.74  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 0.56/0.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.56/0.74  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.56/0.74  thf(r4_lattice3_type, type, r4_lattice3: $i > $i > $i > $o).
% 0.56/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.56/0.74  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.56/0.74  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.56/0.74  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.56/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.56/0.74  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.56/0.74  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.56/0.74  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.56/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.56/0.74  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.56/0.74  thf(r3_lattice3_type, type, r3_lattice3: $i > $i > $i > $o).
% 0.56/0.74  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.56/0.74  thf(t46_lattice3, conjecture,
% 0.56/0.74    (![A:$i]:
% 0.56/0.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.56/0.74         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.56/0.74       ( ![B:$i,C:$i]:
% 0.56/0.74         ( ( r1_tarski @ B @ C ) =>
% 0.56/0.74           ( ( r3_lattices @
% 0.56/0.74               A @ ( k15_lattice3 @ A @ B ) @ ( k15_lattice3 @ A @ C ) ) & 
% 0.56/0.74             ( r3_lattices @
% 0.56/0.74               A @ ( k16_lattice3 @ A @ C ) @ ( k16_lattice3 @ A @ B ) ) ) ) ) ))).
% 0.56/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.56/0.74    (~( ![A:$i]:
% 0.56/0.74        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.56/0.74            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.56/0.74          ( ![B:$i,C:$i]:
% 0.56/0.74            ( ( r1_tarski @ B @ C ) =>
% 0.56/0.74              ( ( r3_lattices @
% 0.56/0.74                  A @ ( k15_lattice3 @ A @ B ) @ ( k15_lattice3 @ A @ C ) ) & 
% 0.56/0.74                ( r3_lattices @
% 0.56/0.74                  A @ ( k16_lattice3 @ A @ C ) @ ( k16_lattice3 @ A @ B ) ) ) ) ) ) )),
% 0.56/0.74    inference('cnf.neg', [status(esa)], [t46_lattice3])).
% 0.56/0.74  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf(dt_k16_lattice3, axiom,
% 0.56/0.74    (![A:$i,B:$i]:
% 0.56/0.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.56/0.74       ( m1_subset_1 @ ( k16_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.56/0.74  thf('1', plain,
% 0.56/0.74      (![X24 : $i, X25 : $i]:
% 0.56/0.74         (~ (l3_lattices @ X24)
% 0.56/0.74          | (v2_struct_0 @ X24)
% 0.56/0.74          | (m1_subset_1 @ (k16_lattice3 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 0.56/0.74      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.56/0.74  thf(d16_lattice3, axiom,
% 0.56/0.74    (![A:$i]:
% 0.56/0.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.56/0.74       ( ![B:$i]:
% 0.56/0.74         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.56/0.74           ( ![C:$i]:
% 0.56/0.74             ( ( r3_lattice3 @ A @ B @ C ) <=>
% 0.56/0.74               ( ![D:$i]:
% 0.56/0.74                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.56/0.74                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 0.56/0.74  thf('2', plain,
% 0.56/0.74      (![X8 : $i, X9 : $i, X12 : $i]:
% 0.56/0.74         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.56/0.74          | (r2_hidden @ (sk_D @ X12 @ X8 @ X9) @ X12)
% 0.56/0.74          | (r3_lattice3 @ X9 @ X8 @ X12)
% 0.56/0.74          | ~ (l3_lattices @ X9)
% 0.56/0.74          | (v2_struct_0 @ X9))),
% 0.56/0.74      inference('cnf', [status(esa)], [d16_lattice3])).
% 0.56/0.74  thf('3', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.74         ((v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.56/0.74          | (r2_hidden @ (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0) @ X2))),
% 0.56/0.74      inference('sup-', [status(thm)], ['1', '2'])).
% 0.56/0.74  thf('4', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.74         ((r2_hidden @ (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0) @ X2)
% 0.56/0.74          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0))),
% 0.56/0.74      inference('simplify', [status(thm)], ['3'])).
% 0.56/0.74  thf('5', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf(d3_tarski, axiom,
% 0.56/0.74    (![A:$i,B:$i]:
% 0.56/0.74     ( ( r1_tarski @ A @ B ) <=>
% 0.56/0.74       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.56/0.74  thf('6', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.74         (~ (r2_hidden @ X0 @ X1)
% 0.56/0.74          | (r2_hidden @ X0 @ X2)
% 0.56/0.74          | ~ (r1_tarski @ X1 @ X2))),
% 0.56/0.74      inference('cnf', [status(esa)], [d3_tarski])).
% 0.56/0.74  thf('7', plain,
% 0.56/0.74      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.56/0.74      inference('sup-', [status(thm)], ['5', '6'])).
% 0.56/0.74  thf('8', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]:
% 0.56/0.74         ((v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ sk_B)
% 0.56/0.74          | (r2_hidden @ (sk_D @ sk_B @ (k16_lattice3 @ X0 @ X1) @ X0) @ sk_C_1))),
% 0.56/0.74      inference('sup-', [status(thm)], ['4', '7'])).
% 0.56/0.74  thf('9', plain,
% 0.56/0.74      (![X24 : $i, X25 : $i]:
% 0.56/0.74         (~ (l3_lattices @ X24)
% 0.56/0.74          | (v2_struct_0 @ X24)
% 0.56/0.74          | (m1_subset_1 @ (k16_lattice3 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 0.56/0.74      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.56/0.74  thf('10', plain,
% 0.56/0.74      (![X8 : $i, X9 : $i, X12 : $i]:
% 0.56/0.74         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.56/0.74          | (m1_subset_1 @ (sk_D @ X12 @ X8 @ X9) @ (u1_struct_0 @ X9))
% 0.56/0.74          | (r3_lattice3 @ X9 @ X8 @ X12)
% 0.56/0.74          | ~ (l3_lattices @ X9)
% 0.56/0.74          | (v2_struct_0 @ X9))),
% 0.56/0.74      inference('cnf', [status(esa)], [d16_lattice3])).
% 0.56/0.74  thf('11', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.74         ((v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.56/0.74          | (m1_subset_1 @ (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0) @ 
% 0.56/0.74             (u1_struct_0 @ X0)))),
% 0.56/0.74      inference('sup-', [status(thm)], ['9', '10'])).
% 0.56/0.74  thf('12', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.74         ((m1_subset_1 @ (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0) @ 
% 0.56/0.74           (u1_struct_0 @ X0))
% 0.56/0.74          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0))),
% 0.56/0.74      inference('simplify', [status(thm)], ['11'])).
% 0.56/0.74  thf(t38_lattice3, axiom,
% 0.56/0.74    (![A:$i]:
% 0.56/0.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.56/0.74         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.56/0.74       ( ![B:$i]:
% 0.56/0.74         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.56/0.74           ( ![C:$i]:
% 0.56/0.74             ( ( r2_hidden @ B @ C ) =>
% 0.56/0.74               ( ( r3_lattices @ A @ B @ ( k15_lattice3 @ A @ C ) ) & 
% 0.56/0.74                 ( r3_lattices @ A @ ( k16_lattice3 @ A @ C ) @ B ) ) ) ) ) ) ))).
% 0.56/0.74  thf('13', plain,
% 0.56/0.74      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.56/0.74         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 0.56/0.74          | (r3_lattices @ X27 @ (k16_lattice3 @ X27 @ X28) @ X26)
% 0.56/0.74          | ~ (r2_hidden @ X26 @ X28)
% 0.56/0.74          | ~ (l3_lattices @ X27)
% 0.56/0.74          | ~ (v4_lattice3 @ X27)
% 0.56/0.74          | ~ (v10_lattices @ X27)
% 0.56/0.74          | (v2_struct_0 @ X27))),
% 0.56/0.74      inference('cnf', [status(esa)], [t38_lattice3])).
% 0.56/0.74  thf('14', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.56/0.74         ((v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.56/0.74          | (v2_struct_0 @ X0)
% 0.56/0.74          | ~ (v10_lattices @ X0)
% 0.56/0.74          | ~ (v4_lattice3 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | ~ (r2_hidden @ (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0) @ X3)
% 0.56/0.74          | (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X3) @ 
% 0.56/0.74             (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0)))),
% 0.56/0.74      inference('sup-', [status(thm)], ['12', '13'])).
% 0.56/0.74  thf('15', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.56/0.74         ((r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X3) @ 
% 0.56/0.74           (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0))
% 0.56/0.74          | ~ (r2_hidden @ (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0) @ X3)
% 0.56/0.74          | ~ (v4_lattice3 @ X0)
% 0.56/0.74          | ~ (v10_lattices @ X0)
% 0.56/0.74          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0))),
% 0.56/0.74      inference('simplify', [status(thm)], ['14'])).
% 0.56/0.74  thf('16', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]:
% 0.56/0.74         ((r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ sk_B)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ sk_B)
% 0.56/0.74          | ~ (v10_lattices @ X0)
% 0.56/0.74          | ~ (v4_lattice3 @ X0)
% 0.56/0.74          | (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ sk_C_1) @ 
% 0.56/0.74             (sk_D @ sk_B @ (k16_lattice3 @ X0 @ X1) @ X0)))),
% 0.56/0.74      inference('sup-', [status(thm)], ['8', '15'])).
% 0.56/0.74  thf('17', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]:
% 0.56/0.74         ((r3_lattices @ X0 @ (k16_lattice3 @ X0 @ sk_C_1) @ 
% 0.56/0.74           (sk_D @ sk_B @ (k16_lattice3 @ X0 @ X1) @ X0))
% 0.56/0.74          | ~ (v4_lattice3 @ X0)
% 0.56/0.74          | ~ (v10_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ sk_B))),
% 0.56/0.74      inference('simplify', [status(thm)], ['16'])).
% 0.56/0.74  thf('18', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.74         ((m1_subset_1 @ (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0) @ 
% 0.56/0.74           (u1_struct_0 @ X0))
% 0.56/0.74          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0))),
% 0.56/0.74      inference('simplify', [status(thm)], ['11'])).
% 0.56/0.74  thf('19', plain,
% 0.56/0.74      (![X24 : $i, X25 : $i]:
% 0.56/0.74         (~ (l3_lattices @ X24)
% 0.56/0.74          | (v2_struct_0 @ X24)
% 0.56/0.74          | (m1_subset_1 @ (k16_lattice3 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 0.56/0.74      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.56/0.74  thf(redefinition_r3_lattices, axiom,
% 0.56/0.74    (![A:$i,B:$i,C:$i]:
% 0.56/0.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.56/0.74         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 0.56/0.74         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.56/0.74         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.56/0.74       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 0.56/0.74  thf('20', plain,
% 0.56/0.74      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.56/0.74         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 0.56/0.74          | ~ (l3_lattices @ X6)
% 0.56/0.74          | ~ (v9_lattices @ X6)
% 0.56/0.74          | ~ (v8_lattices @ X6)
% 0.56/0.74          | ~ (v6_lattices @ X6)
% 0.56/0.74          | (v2_struct_0 @ X6)
% 0.56/0.74          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 0.56/0.74          | (r1_lattices @ X6 @ X5 @ X7)
% 0.56/0.74          | ~ (r3_lattices @ X6 @ X5 @ X7))),
% 0.56/0.74      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.56/0.74  thf('21', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.74         ((v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | ~ (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.56/0.74          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.56/0.74          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.56/0.74          | (v2_struct_0 @ X0)
% 0.56/0.74          | ~ (v6_lattices @ X0)
% 0.56/0.74          | ~ (v8_lattices @ X0)
% 0.56/0.74          | ~ (v9_lattices @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0))),
% 0.56/0.74      inference('sup-', [status(thm)], ['19', '20'])).
% 0.56/0.74  thf('22', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.74         (~ (v9_lattices @ X0)
% 0.56/0.74          | ~ (v8_lattices @ X0)
% 0.56/0.74          | ~ (v6_lattices @ X0)
% 0.56/0.74          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.56/0.74          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.56/0.74          | ~ (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0))),
% 0.56/0.74      inference('simplify', [status(thm)], ['21'])).
% 0.56/0.74  thf('23', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.56/0.74         ((v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.56/0.74          | (v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | ~ (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X3) @ 
% 0.56/0.74               (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0))
% 0.56/0.74          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X3) @ 
% 0.56/0.74             (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0))
% 0.56/0.74          | ~ (v6_lattices @ X0)
% 0.56/0.74          | ~ (v8_lattices @ X0)
% 0.56/0.74          | ~ (v9_lattices @ X0))),
% 0.56/0.74      inference('sup-', [status(thm)], ['18', '22'])).
% 0.56/0.74  thf('24', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.56/0.74         (~ (v9_lattices @ X0)
% 0.56/0.74          | ~ (v8_lattices @ X0)
% 0.56/0.74          | ~ (v6_lattices @ X0)
% 0.56/0.74          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X3) @ 
% 0.56/0.74             (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0))
% 0.56/0.74          | ~ (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X3) @ 
% 0.56/0.74               (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0))
% 0.56/0.74          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0))),
% 0.56/0.74      inference('simplify', [status(thm)], ['23'])).
% 0.56/0.74  thf('25', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]:
% 0.56/0.74         ((r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ sk_B)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0)
% 0.56/0.74          | ~ (v10_lattices @ X0)
% 0.56/0.74          | ~ (v4_lattice3 @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ sk_B)
% 0.56/0.74          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ sk_C_1) @ 
% 0.56/0.74             (sk_D @ sk_B @ (k16_lattice3 @ X0 @ X1) @ X0))
% 0.56/0.74          | ~ (v6_lattices @ X0)
% 0.56/0.74          | ~ (v8_lattices @ X0)
% 0.56/0.74          | ~ (v9_lattices @ X0))),
% 0.56/0.74      inference('sup-', [status(thm)], ['17', '24'])).
% 0.56/0.74  thf('26', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]:
% 0.56/0.74         (~ (v9_lattices @ X0)
% 0.56/0.74          | ~ (v8_lattices @ X0)
% 0.56/0.74          | ~ (v6_lattices @ X0)
% 0.56/0.74          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ sk_C_1) @ 
% 0.56/0.74             (sk_D @ sk_B @ (k16_lattice3 @ X0 @ X1) @ X0))
% 0.56/0.74          | ~ (v4_lattice3 @ X0)
% 0.56/0.74          | ~ (v10_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ sk_B))),
% 0.56/0.74      inference('simplify', [status(thm)], ['25'])).
% 0.56/0.74  thf('27', plain,
% 0.56/0.74      (![X24 : $i, X25 : $i]:
% 0.56/0.74         (~ (l3_lattices @ X24)
% 0.56/0.74          | (v2_struct_0 @ X24)
% 0.56/0.74          | (m1_subset_1 @ (k16_lattice3 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 0.56/0.74      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.56/0.74  thf('28', plain,
% 0.56/0.74      (![X8 : $i, X9 : $i, X12 : $i]:
% 0.56/0.74         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.56/0.74          | ~ (r1_lattices @ X9 @ X8 @ (sk_D @ X12 @ X8 @ X9))
% 0.56/0.74          | (r3_lattice3 @ X9 @ X8 @ X12)
% 0.56/0.74          | ~ (l3_lattices @ X9)
% 0.56/0.74          | (v2_struct_0 @ X9))),
% 0.56/0.74      inference('cnf', [status(esa)], [d16_lattice3])).
% 0.56/0.74  thf('29', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.74         ((v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.56/0.74          | ~ (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 0.56/0.74               (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0)))),
% 0.56/0.74      inference('sup-', [status(thm)], ['27', '28'])).
% 0.56/0.74  thf('30', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.74         (~ (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 0.56/0.74             (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0))
% 0.56/0.74          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0))),
% 0.56/0.74      inference('simplify', [status(thm)], ['29'])).
% 0.56/0.74  thf('31', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         ((r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ sk_C_1) @ sk_B)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0)
% 0.56/0.74          | ~ (v10_lattices @ X0)
% 0.56/0.74          | ~ (v4_lattice3 @ X0)
% 0.56/0.74          | ~ (v6_lattices @ X0)
% 0.56/0.74          | ~ (v8_lattices @ X0)
% 0.56/0.74          | ~ (v9_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ sk_C_1) @ sk_B))),
% 0.56/0.74      inference('sup-', [status(thm)], ['26', '30'])).
% 0.56/0.74  thf('32', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         (~ (v9_lattices @ X0)
% 0.56/0.74          | ~ (v8_lattices @ X0)
% 0.56/0.74          | ~ (v6_lattices @ X0)
% 0.56/0.74          | ~ (v4_lattice3 @ X0)
% 0.56/0.74          | ~ (v10_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ sk_C_1) @ sk_B))),
% 0.56/0.74      inference('simplify', [status(thm)], ['31'])).
% 0.56/0.74  thf('33', plain,
% 0.56/0.74      (![X24 : $i, X25 : $i]:
% 0.56/0.74         (~ (l3_lattices @ X24)
% 0.56/0.74          | (v2_struct_0 @ X24)
% 0.56/0.74          | (m1_subset_1 @ (k16_lattice3 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 0.56/0.74      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.56/0.74  thf(t40_lattice3, axiom,
% 0.56/0.74    (![A:$i]:
% 0.56/0.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.56/0.74         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.56/0.74       ( ![B:$i]:
% 0.56/0.74         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.56/0.74           ( ![C:$i]:
% 0.56/0.74             ( ( r3_lattice3 @ A @ B @ C ) =>
% 0.56/0.74               ( r3_lattices @ A @ B @ ( k16_lattice3 @ A @ C ) ) ) ) ) ) ))).
% 0.56/0.74  thf('34', plain,
% 0.56/0.74      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.56/0.74         (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X30))
% 0.56/0.74          | (r3_lattices @ X30 @ X29 @ (k16_lattice3 @ X30 @ X31))
% 0.56/0.74          | ~ (r3_lattice3 @ X30 @ X29 @ X31)
% 0.56/0.74          | ~ (l3_lattices @ X30)
% 0.56/0.74          | ~ (v4_lattice3 @ X30)
% 0.56/0.74          | ~ (v10_lattices @ X30)
% 0.56/0.74          | (v2_struct_0 @ X30))),
% 0.56/0.74      inference('cnf', [status(esa)], [t40_lattice3])).
% 0.56/0.74  thf('35', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.74         ((v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0)
% 0.56/0.74          | ~ (v10_lattices @ X0)
% 0.56/0.74          | ~ (v4_lattice3 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | ~ (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.56/0.74          | (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 0.56/0.74             (k16_lattice3 @ X0 @ X2)))),
% 0.56/0.74      inference('sup-', [status(thm)], ['33', '34'])).
% 0.56/0.74  thf('36', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.74         ((r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 0.56/0.74           (k16_lattice3 @ X0 @ X2))
% 0.56/0.74          | ~ (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.56/0.74          | ~ (v4_lattice3 @ X0)
% 0.56/0.74          | ~ (v10_lattices @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0))),
% 0.56/0.74      inference('simplify', [status(thm)], ['35'])).
% 0.56/0.74  thf('37', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         (~ (l3_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0)
% 0.56/0.74          | ~ (v10_lattices @ X0)
% 0.56/0.74          | ~ (v4_lattice3 @ X0)
% 0.56/0.74          | ~ (v6_lattices @ X0)
% 0.56/0.74          | ~ (v8_lattices @ X0)
% 0.56/0.74          | ~ (v9_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | ~ (v10_lattices @ X0)
% 0.56/0.74          | ~ (v4_lattice3 @ X0)
% 0.56/0.74          | (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ sk_C_1) @ 
% 0.56/0.74             (k16_lattice3 @ X0 @ sk_B)))),
% 0.56/0.74      inference('sup-', [status(thm)], ['32', '36'])).
% 0.56/0.74  thf('38', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         ((r3_lattices @ X0 @ (k16_lattice3 @ X0 @ sk_C_1) @ 
% 0.56/0.74           (k16_lattice3 @ X0 @ sk_B))
% 0.56/0.74          | ~ (v9_lattices @ X0)
% 0.56/0.74          | ~ (v8_lattices @ X0)
% 0.56/0.74          | ~ (v6_lattices @ X0)
% 0.56/0.74          | ~ (v4_lattice3 @ X0)
% 0.56/0.74          | ~ (v10_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0))),
% 0.56/0.74      inference('simplify', [status(thm)], ['37'])).
% 0.56/0.74  thf('39', plain,
% 0.56/0.74      ((~ (r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 0.56/0.74           (k15_lattice3 @ sk_A @ sk_C_1))
% 0.56/0.74        | ~ (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C_1) @ 
% 0.56/0.74             (k16_lattice3 @ sk_A @ sk_B)))),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf('40', plain,
% 0.56/0.74      ((~ (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C_1) @ 
% 0.56/0.74           (k16_lattice3 @ sk_A @ sk_B)))
% 0.56/0.74         <= (~
% 0.56/0.74             ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C_1) @ 
% 0.56/0.74               (k16_lattice3 @ sk_A @ sk_B))))),
% 0.56/0.74      inference('split', [status(esa)], ['39'])).
% 0.56/0.74  thf(dt_k15_lattice3, axiom,
% 0.56/0.74    (![A:$i,B:$i]:
% 0.56/0.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.56/0.74       ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.56/0.74  thf('41', plain,
% 0.56/0.74      (![X22 : $i, X23 : $i]:
% 0.56/0.74         (~ (l3_lattices @ X22)
% 0.56/0.74          | (v2_struct_0 @ X22)
% 0.56/0.74          | (m1_subset_1 @ (k15_lattice3 @ X22 @ X23) @ (u1_struct_0 @ X22)))),
% 0.56/0.74      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.56/0.74  thf(d17_lattice3, axiom,
% 0.56/0.74    (![A:$i]:
% 0.56/0.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.56/0.74       ( ![B:$i]:
% 0.56/0.74         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.56/0.74           ( ![C:$i]:
% 0.56/0.74             ( ( r4_lattice3 @ A @ B @ C ) <=>
% 0.56/0.74               ( ![D:$i]:
% 0.56/0.74                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.56/0.74                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ))).
% 0.56/0.74  thf('42', plain,
% 0.56/0.74      (![X13 : $i, X14 : $i, X17 : $i]:
% 0.56/0.74         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.56/0.74          | (r2_hidden @ (sk_D_1 @ X17 @ X13 @ X14) @ X17)
% 0.56/0.74          | (r4_lattice3 @ X14 @ X13 @ X17)
% 0.56/0.74          | ~ (l3_lattices @ X14)
% 0.56/0.74          | (v2_struct_0 @ X14))),
% 0.56/0.74      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.56/0.74  thf('43', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.74         ((v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.56/0.74          | (r2_hidden @ (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X2))),
% 0.56/0.74      inference('sup-', [status(thm)], ['41', '42'])).
% 0.56/0.74  thf('44', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.74         ((r2_hidden @ (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X2)
% 0.56/0.74          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0))),
% 0.56/0.74      inference('simplify', [status(thm)], ['43'])).
% 0.56/0.74  thf('45', plain,
% 0.56/0.74      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.56/0.74      inference('sup-', [status(thm)], ['5', '6'])).
% 0.56/0.74  thf('46', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]:
% 0.56/0.74         ((v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ sk_B)
% 0.56/0.74          | (r2_hidden @ (sk_D_1 @ sk_B @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.56/0.74             sk_C_1))),
% 0.56/0.74      inference('sup-', [status(thm)], ['44', '45'])).
% 0.56/0.74  thf('47', plain,
% 0.56/0.74      (![X22 : $i, X23 : $i]:
% 0.56/0.74         (~ (l3_lattices @ X22)
% 0.56/0.74          | (v2_struct_0 @ X22)
% 0.56/0.74          | (m1_subset_1 @ (k15_lattice3 @ X22 @ X23) @ (u1_struct_0 @ X22)))),
% 0.56/0.74      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.56/0.74  thf('48', plain,
% 0.56/0.74      (![X13 : $i, X14 : $i, X17 : $i]:
% 0.56/0.74         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.56/0.74          | (m1_subset_1 @ (sk_D_1 @ X17 @ X13 @ X14) @ (u1_struct_0 @ X14))
% 0.56/0.74          | (r4_lattice3 @ X14 @ X13 @ X17)
% 0.56/0.74          | ~ (l3_lattices @ X14)
% 0.56/0.74          | (v2_struct_0 @ X14))),
% 0.56/0.74      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.56/0.74  thf('49', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.74         ((v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.56/0.74          | (m1_subset_1 @ (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.56/0.74             (u1_struct_0 @ X0)))),
% 0.56/0.74      inference('sup-', [status(thm)], ['47', '48'])).
% 0.56/0.74  thf('50', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.74         ((m1_subset_1 @ (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.56/0.74           (u1_struct_0 @ X0))
% 0.56/0.74          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0))),
% 0.56/0.74      inference('simplify', [status(thm)], ['49'])).
% 0.56/0.74  thf('51', plain,
% 0.56/0.74      (![X22 : $i, X23 : $i]:
% 0.56/0.74         (~ (l3_lattices @ X22)
% 0.56/0.74          | (v2_struct_0 @ X22)
% 0.56/0.74          | (m1_subset_1 @ (k15_lattice3 @ X22 @ X23) @ (u1_struct_0 @ X22)))),
% 0.56/0.74      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.56/0.74  thf(d21_lattice3, axiom,
% 0.56/0.74    (![A:$i]:
% 0.56/0.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.56/0.74       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.56/0.74           ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.56/0.74         ( ![B:$i,C:$i]:
% 0.56/0.74           ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.56/0.74             ( ( ( C ) = ( k15_lattice3 @ A @ B ) ) <=>
% 0.56/0.74               ( ( r4_lattice3 @ A @ C @ B ) & 
% 0.56/0.74                 ( ![D:$i]:
% 0.56/0.74                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.56/0.74                     ( ( r4_lattice3 @ A @ D @ B ) =>
% 0.56/0.74                       ( r1_lattices @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.56/0.74  thf('52', plain,
% 0.56/0.74      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.56/0.74         ((v2_struct_0 @ X18)
% 0.56/0.74          | ~ (v10_lattices @ X18)
% 0.56/0.74          | ~ (v4_lattice3 @ X18)
% 0.56/0.74          | ~ (l3_lattices @ X18)
% 0.56/0.74          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 0.56/0.74          | ((X19) != (k15_lattice3 @ X18 @ X20))
% 0.56/0.74          | (r4_lattice3 @ X18 @ X19 @ X20)
% 0.56/0.74          | ~ (l3_lattices @ X18)
% 0.56/0.74          | (v2_struct_0 @ X18))),
% 0.56/0.74      inference('cnf', [status(esa)], [d21_lattice3])).
% 0.56/0.74  thf('53', plain,
% 0.56/0.74      (![X18 : $i, X20 : $i]:
% 0.56/0.74         ((r4_lattice3 @ X18 @ (k15_lattice3 @ X18 @ X20) @ X20)
% 0.56/0.74          | ~ (m1_subset_1 @ (k15_lattice3 @ X18 @ X20) @ (u1_struct_0 @ X18))
% 0.56/0.74          | ~ (l3_lattices @ X18)
% 0.56/0.74          | ~ (v4_lattice3 @ X18)
% 0.56/0.74          | ~ (v10_lattices @ X18)
% 0.56/0.74          | (v2_struct_0 @ X18))),
% 0.56/0.74      inference('simplify', [status(thm)], ['52'])).
% 0.56/0.74  thf('54', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]:
% 0.56/0.74         ((v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0)
% 0.56/0.74          | ~ (v10_lattices @ X0)
% 0.56/0.74          | ~ (v4_lattice3 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X1))),
% 0.56/0.74      inference('sup-', [status(thm)], ['51', '53'])).
% 0.56/0.74  thf('55', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]:
% 0.56/0.74         ((r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X1)
% 0.56/0.74          | ~ (v4_lattice3 @ X0)
% 0.56/0.74          | ~ (v10_lattices @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0))),
% 0.56/0.74      inference('simplify', [status(thm)], ['54'])).
% 0.56/0.74  thf('56', plain,
% 0.56/0.74      (![X22 : $i, X23 : $i]:
% 0.56/0.74         (~ (l3_lattices @ X22)
% 0.56/0.74          | (v2_struct_0 @ X22)
% 0.56/0.74          | (m1_subset_1 @ (k15_lattice3 @ X22 @ X23) @ (u1_struct_0 @ X22)))),
% 0.56/0.74      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.56/0.74  thf('57', plain,
% 0.56/0.74      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.56/0.74         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.56/0.74          | ~ (r4_lattice3 @ X14 @ X13 @ X15)
% 0.56/0.74          | ~ (r2_hidden @ X16 @ X15)
% 0.56/0.74          | (r1_lattices @ X14 @ X16 @ X13)
% 0.56/0.74          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X14))
% 0.56/0.74          | ~ (l3_lattices @ X14)
% 0.56/0.74          | (v2_struct_0 @ X14))),
% 0.56/0.74      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.56/0.74  thf('58', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.56/0.74         ((v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.56/0.74          | (r1_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))
% 0.56/0.74          | ~ (r2_hidden @ X2 @ X3)
% 0.56/0.74          | ~ (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X3))),
% 0.56/0.74      inference('sup-', [status(thm)], ['56', '57'])).
% 0.56/0.74  thf('59', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.56/0.74         (~ (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X3)
% 0.56/0.74          | ~ (r2_hidden @ X2 @ X3)
% 0.56/0.74          | (r1_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))
% 0.56/0.74          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0))),
% 0.56/0.74      inference('simplify', [status(thm)], ['58'])).
% 0.56/0.74  thf('60', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.74         ((v2_struct_0 @ X1)
% 0.56/0.74          | ~ (l3_lattices @ X1)
% 0.56/0.74          | ~ (v10_lattices @ X1)
% 0.56/0.74          | ~ (v4_lattice3 @ X1)
% 0.56/0.74          | (v2_struct_0 @ X1)
% 0.56/0.74          | ~ (l3_lattices @ X1)
% 0.56/0.74          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.56/0.74          | (r1_lattices @ X1 @ X2 @ (k15_lattice3 @ X1 @ X0))
% 0.56/0.74          | ~ (r2_hidden @ X2 @ X0))),
% 0.56/0.74      inference('sup-', [status(thm)], ['55', '59'])).
% 0.56/0.74  thf('61', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.74         (~ (r2_hidden @ X2 @ X0)
% 0.56/0.74          | (r1_lattices @ X1 @ X2 @ (k15_lattice3 @ X1 @ X0))
% 0.56/0.74          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.56/0.74          | ~ (v4_lattice3 @ X1)
% 0.56/0.74          | ~ (v10_lattices @ X1)
% 0.56/0.74          | ~ (l3_lattices @ X1)
% 0.56/0.74          | (v2_struct_0 @ X1))),
% 0.56/0.74      inference('simplify', [status(thm)], ['60'])).
% 0.56/0.74  thf('62', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.56/0.74         ((v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.56/0.74          | (v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | ~ (v10_lattices @ X0)
% 0.56/0.74          | ~ (v4_lattice3 @ X0)
% 0.56/0.74          | (r1_lattices @ X0 @ 
% 0.56/0.74             (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.56/0.74             (k15_lattice3 @ X0 @ X3))
% 0.56/0.74          | ~ (r2_hidden @ (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X3))),
% 0.56/0.74      inference('sup-', [status(thm)], ['50', '61'])).
% 0.56/0.74  thf('63', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.56/0.74         (~ (r2_hidden @ (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X3)
% 0.56/0.74          | (r1_lattices @ X0 @ 
% 0.56/0.74             (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.56/0.74             (k15_lattice3 @ X0 @ X3))
% 0.56/0.74          | ~ (v4_lattice3 @ X0)
% 0.56/0.74          | ~ (v10_lattices @ X0)
% 0.56/0.74          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0))),
% 0.56/0.74      inference('simplify', [status(thm)], ['62'])).
% 0.56/0.74  thf('64', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]:
% 0.56/0.74         ((r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ sk_B)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ sk_B)
% 0.56/0.74          | ~ (v10_lattices @ X0)
% 0.56/0.74          | ~ (v4_lattice3 @ X0)
% 0.56/0.74          | (r1_lattices @ X0 @ 
% 0.56/0.74             (sk_D_1 @ sk_B @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.56/0.74             (k15_lattice3 @ X0 @ sk_C_1)))),
% 0.56/0.74      inference('sup-', [status(thm)], ['46', '63'])).
% 0.56/0.74  thf('65', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]:
% 0.56/0.74         ((r1_lattices @ X0 @ 
% 0.56/0.74           (sk_D_1 @ sk_B @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.56/0.74           (k15_lattice3 @ X0 @ sk_C_1))
% 0.56/0.74          | ~ (v4_lattice3 @ X0)
% 0.56/0.74          | ~ (v10_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ sk_B))),
% 0.56/0.74      inference('simplify', [status(thm)], ['64'])).
% 0.56/0.74  thf('66', plain,
% 0.56/0.74      (![X22 : $i, X23 : $i]:
% 0.56/0.74         (~ (l3_lattices @ X22)
% 0.56/0.74          | (v2_struct_0 @ X22)
% 0.56/0.74          | (m1_subset_1 @ (k15_lattice3 @ X22 @ X23) @ (u1_struct_0 @ X22)))),
% 0.56/0.74      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.56/0.74  thf('67', plain,
% 0.56/0.74      (![X13 : $i, X14 : $i, X17 : $i]:
% 0.56/0.74         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.56/0.74          | ~ (r1_lattices @ X14 @ (sk_D_1 @ X17 @ X13 @ X14) @ X13)
% 0.56/0.74          | (r4_lattice3 @ X14 @ X13 @ X17)
% 0.56/0.74          | ~ (l3_lattices @ X14)
% 0.56/0.74          | (v2_struct_0 @ X14))),
% 0.56/0.74      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.56/0.74  thf('68', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.74         ((v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.56/0.74          | ~ (r1_lattices @ X0 @ 
% 0.56/0.74               (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.56/0.74               (k15_lattice3 @ X0 @ X1)))),
% 0.56/0.74      inference('sup-', [status(thm)], ['66', '67'])).
% 0.56/0.74  thf('69', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.74         (~ (r1_lattices @ X0 @ 
% 0.56/0.74             (sk_D_1 @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 0.56/0.74             (k15_lattice3 @ X0 @ X1))
% 0.56/0.74          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0))),
% 0.56/0.74      inference('simplify', [status(thm)], ['68'])).
% 0.56/0.74  thf('70', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         ((r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ sk_C_1) @ sk_B)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0)
% 0.56/0.74          | ~ (v10_lattices @ X0)
% 0.56/0.74          | ~ (v4_lattice3 @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ sk_C_1) @ sk_B))),
% 0.56/0.74      inference('sup-', [status(thm)], ['65', '69'])).
% 0.56/0.74  thf('71', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         (~ (v4_lattice3 @ X0)
% 0.56/0.74          | ~ (v10_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ sk_C_1) @ sk_B))),
% 0.56/0.74      inference('simplify', [status(thm)], ['70'])).
% 0.56/0.74  thf('72', plain,
% 0.56/0.74      (![X22 : $i, X23 : $i]:
% 0.56/0.74         (~ (l3_lattices @ X22)
% 0.56/0.74          | (v2_struct_0 @ X22)
% 0.56/0.74          | (m1_subset_1 @ (k15_lattice3 @ X22 @ X23) @ (u1_struct_0 @ X22)))),
% 0.56/0.74      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.56/0.74  thf('73', plain,
% 0.56/0.74      (![X22 : $i, X23 : $i]:
% 0.56/0.74         (~ (l3_lattices @ X22)
% 0.56/0.74          | (v2_struct_0 @ X22)
% 0.56/0.74          | (m1_subset_1 @ (k15_lattice3 @ X22 @ X23) @ (u1_struct_0 @ X22)))),
% 0.56/0.74      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.56/0.74  thf('74', plain,
% 0.56/0.74      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.56/0.74         ((v2_struct_0 @ X18)
% 0.56/0.74          | ~ (v10_lattices @ X18)
% 0.56/0.74          | ~ (v4_lattice3 @ X18)
% 0.56/0.74          | ~ (l3_lattices @ X18)
% 0.56/0.74          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 0.56/0.74          | ((X19) != (k15_lattice3 @ X18 @ X20))
% 0.56/0.74          | ~ (r4_lattice3 @ X18 @ X21 @ X20)
% 0.56/0.74          | (r1_lattices @ X18 @ X19 @ X21)
% 0.56/0.74          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X18))
% 0.56/0.74          | ~ (l3_lattices @ X18)
% 0.56/0.74          | (v2_struct_0 @ X18))),
% 0.56/0.74      inference('cnf', [status(esa)], [d21_lattice3])).
% 0.56/0.74  thf('75', plain,
% 0.56/0.74      (![X18 : $i, X20 : $i, X21 : $i]:
% 0.56/0.74         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X18))
% 0.56/0.74          | (r1_lattices @ X18 @ (k15_lattice3 @ X18 @ X20) @ X21)
% 0.56/0.74          | ~ (r4_lattice3 @ X18 @ X21 @ X20)
% 0.56/0.74          | ~ (m1_subset_1 @ (k15_lattice3 @ X18 @ X20) @ (u1_struct_0 @ X18))
% 0.56/0.74          | ~ (l3_lattices @ X18)
% 0.56/0.74          | ~ (v4_lattice3 @ X18)
% 0.56/0.74          | ~ (v10_lattices @ X18)
% 0.56/0.74          | (v2_struct_0 @ X18))),
% 0.56/0.74      inference('simplify', [status(thm)], ['74'])).
% 0.56/0.74  thf('76', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.74         ((v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0)
% 0.56/0.74          | ~ (v10_lattices @ X0)
% 0.56/0.74          | ~ (v4_lattice3 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | ~ (r4_lattice3 @ X0 @ X2 @ X1)
% 0.56/0.74          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.56/0.74          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0)))),
% 0.56/0.74      inference('sup-', [status(thm)], ['73', '75'])).
% 0.56/0.74  thf('77', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.74         (~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.56/0.74          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.56/0.74          | ~ (r4_lattice3 @ X0 @ X2 @ X1)
% 0.56/0.74          | ~ (v4_lattice3 @ X0)
% 0.56/0.74          | ~ (v10_lattices @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0))),
% 0.56/0.74      inference('simplify', [status(thm)], ['76'])).
% 0.56/0.74  thf('78', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.74         ((v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | ~ (v10_lattices @ X0)
% 0.56/0.74          | ~ (v4_lattice3 @ X0)
% 0.56/0.74          | ~ (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.56/0.74          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 0.56/0.74             (k15_lattice3 @ X0 @ X1)))),
% 0.56/0.74      inference('sup-', [status(thm)], ['72', '77'])).
% 0.56/0.74  thf('79', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.74         ((r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 0.56/0.74           (k15_lattice3 @ X0 @ X1))
% 0.56/0.74          | ~ (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.56/0.74          | ~ (v4_lattice3 @ X0)
% 0.56/0.74          | ~ (v10_lattices @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0))),
% 0.56/0.74      inference('simplify', [status(thm)], ['78'])).
% 0.56/0.74  thf('80', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         (~ (l3_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0)
% 0.56/0.74          | ~ (v10_lattices @ X0)
% 0.56/0.74          | ~ (v4_lattice3 @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | ~ (v10_lattices @ X0)
% 0.56/0.74          | ~ (v4_lattice3 @ X0)
% 0.56/0.74          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ sk_B) @ 
% 0.56/0.74             (k15_lattice3 @ X0 @ sk_C_1)))),
% 0.56/0.74      inference('sup-', [status(thm)], ['71', '79'])).
% 0.56/0.74  thf('81', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         ((r1_lattices @ X0 @ (k15_lattice3 @ X0 @ sk_B) @ 
% 0.56/0.74           (k15_lattice3 @ X0 @ sk_C_1))
% 0.56/0.74          | ~ (v4_lattice3 @ X0)
% 0.56/0.74          | ~ (v10_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0))),
% 0.56/0.74      inference('simplify', [status(thm)], ['80'])).
% 0.56/0.74  thf('82', plain,
% 0.56/0.74      (![X22 : $i, X23 : $i]:
% 0.56/0.74         (~ (l3_lattices @ X22)
% 0.56/0.74          | (v2_struct_0 @ X22)
% 0.56/0.74          | (m1_subset_1 @ (k15_lattice3 @ X22 @ X23) @ (u1_struct_0 @ X22)))),
% 0.56/0.74      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.56/0.74  thf('83', plain,
% 0.56/0.74      (![X22 : $i, X23 : $i]:
% 0.56/0.74         (~ (l3_lattices @ X22)
% 0.56/0.74          | (v2_struct_0 @ X22)
% 0.56/0.74          | (m1_subset_1 @ (k15_lattice3 @ X22 @ X23) @ (u1_struct_0 @ X22)))),
% 0.56/0.74      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.56/0.74  thf('84', plain,
% 0.56/0.74      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.56/0.74         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 0.56/0.74          | ~ (l3_lattices @ X6)
% 0.56/0.74          | ~ (v9_lattices @ X6)
% 0.56/0.74          | ~ (v8_lattices @ X6)
% 0.56/0.74          | ~ (v6_lattices @ X6)
% 0.56/0.74          | (v2_struct_0 @ X6)
% 0.56/0.74          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 0.56/0.74          | (r3_lattices @ X6 @ X5 @ X7)
% 0.56/0.74          | ~ (r1_lattices @ X6 @ X5 @ X7))),
% 0.56/0.74      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.56/0.74  thf('85', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.74         ((v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | ~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.56/0.74          | (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.56/0.74          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.56/0.74          | (v2_struct_0 @ X0)
% 0.56/0.74          | ~ (v6_lattices @ X0)
% 0.56/0.74          | ~ (v8_lattices @ X0)
% 0.56/0.74          | ~ (v9_lattices @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0))),
% 0.56/0.74      inference('sup-', [status(thm)], ['83', '84'])).
% 0.56/0.74  thf('86', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.74         (~ (v9_lattices @ X0)
% 0.56/0.74          | ~ (v8_lattices @ X0)
% 0.56/0.74          | ~ (v6_lattices @ X0)
% 0.56/0.74          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.56/0.74          | (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.56/0.74          | ~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0))),
% 0.56/0.74      inference('simplify', [status(thm)], ['85'])).
% 0.56/0.74  thf('87', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.74         ((v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | ~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 0.56/0.74               (k15_lattice3 @ X0 @ X1))
% 0.56/0.74          | (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 0.56/0.74             (k15_lattice3 @ X0 @ X1))
% 0.56/0.74          | ~ (v6_lattices @ X0)
% 0.56/0.74          | ~ (v8_lattices @ X0)
% 0.56/0.74          | ~ (v9_lattices @ X0))),
% 0.56/0.74      inference('sup-', [status(thm)], ['82', '86'])).
% 0.56/0.74  thf('88', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.74         (~ (v9_lattices @ X0)
% 0.56/0.74          | ~ (v8_lattices @ X0)
% 0.56/0.74          | ~ (v6_lattices @ X0)
% 0.56/0.74          | (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 0.56/0.74             (k15_lattice3 @ X0 @ X1))
% 0.56/0.74          | ~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 0.56/0.74               (k15_lattice3 @ X0 @ X1))
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0))),
% 0.56/0.74      inference('simplify', [status(thm)], ['87'])).
% 0.56/0.74  thf('89', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         (~ (l3_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0)
% 0.56/0.74          | ~ (v10_lattices @ X0)
% 0.56/0.74          | ~ (v4_lattice3 @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0)
% 0.56/0.74          | (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ sk_B) @ 
% 0.56/0.74             (k15_lattice3 @ X0 @ sk_C_1))
% 0.56/0.74          | ~ (v6_lattices @ X0)
% 0.56/0.74          | ~ (v8_lattices @ X0)
% 0.56/0.74          | ~ (v9_lattices @ X0))),
% 0.56/0.74      inference('sup-', [status(thm)], ['81', '88'])).
% 0.56/0.74  thf('90', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         (~ (v9_lattices @ X0)
% 0.56/0.74          | ~ (v8_lattices @ X0)
% 0.56/0.74          | ~ (v6_lattices @ X0)
% 0.56/0.74          | (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ sk_B) @ 
% 0.56/0.74             (k15_lattice3 @ X0 @ sk_C_1))
% 0.56/0.74          | ~ (v4_lattice3 @ X0)
% 0.56/0.74          | ~ (v10_lattices @ X0)
% 0.56/0.74          | (v2_struct_0 @ X0)
% 0.56/0.74          | ~ (l3_lattices @ X0))),
% 0.56/0.74      inference('simplify', [status(thm)], ['89'])).
% 0.56/0.74  thf('91', plain,
% 0.56/0.74      ((~ (r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 0.56/0.74           (k15_lattice3 @ sk_A @ sk_C_1)))
% 0.56/0.74         <= (~
% 0.56/0.74             ((r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 0.56/0.74               (k15_lattice3 @ sk_A @ sk_C_1))))),
% 0.56/0.74      inference('split', [status(esa)], ['39'])).
% 0.56/0.74  thf('92', plain,
% 0.56/0.74      (((~ (l3_lattices @ sk_A)
% 0.56/0.74         | (v2_struct_0 @ sk_A)
% 0.56/0.74         | ~ (v10_lattices @ sk_A)
% 0.56/0.74         | ~ (v4_lattice3 @ sk_A)
% 0.56/0.74         | ~ (v6_lattices @ sk_A)
% 0.56/0.74         | ~ (v8_lattices @ sk_A)
% 0.56/0.74         | ~ (v9_lattices @ sk_A)))
% 0.56/0.74         <= (~
% 0.56/0.74             ((r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 0.56/0.74               (k15_lattice3 @ sk_A @ sk_C_1))))),
% 0.56/0.74      inference('sup-', [status(thm)], ['90', '91'])).
% 0.56/0.74  thf('93', plain, ((l3_lattices @ sk_A)),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf('94', plain, ((v10_lattices @ sk_A)),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf('95', plain, ((v4_lattice3 @ sk_A)),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf(cc1_lattices, axiom,
% 0.56/0.74    (![A:$i]:
% 0.56/0.74     ( ( l3_lattices @ A ) =>
% 0.56/0.74       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.56/0.74         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.56/0.74           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.56/0.74           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.56/0.74  thf('96', plain,
% 0.56/0.74      (![X4 : $i]:
% 0.56/0.74         ((v2_struct_0 @ X4)
% 0.56/0.74          | ~ (v10_lattices @ X4)
% 0.56/0.74          | (v6_lattices @ X4)
% 0.56/0.74          | ~ (l3_lattices @ X4))),
% 0.56/0.74      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.56/0.74  thf('97', plain, (~ (v2_struct_0 @ sk_A)),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf('98', plain,
% 0.56/0.74      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.56/0.74      inference('sup-', [status(thm)], ['96', '97'])).
% 0.56/0.74  thf('99', plain, ((l3_lattices @ sk_A)),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf('100', plain, ((v10_lattices @ sk_A)),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf('101', plain, ((v6_lattices @ sk_A)),
% 0.56/0.74      inference('demod', [status(thm)], ['98', '99', '100'])).
% 0.56/0.74  thf('102', plain,
% 0.56/0.74      (![X4 : $i]:
% 0.56/0.74         ((v2_struct_0 @ X4)
% 0.56/0.74          | ~ (v10_lattices @ X4)
% 0.56/0.74          | (v8_lattices @ X4)
% 0.56/0.74          | ~ (l3_lattices @ X4))),
% 0.56/0.74      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.56/0.74  thf('103', plain, (~ (v2_struct_0 @ sk_A)),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf('104', plain,
% 0.56/0.74      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.56/0.74      inference('sup-', [status(thm)], ['102', '103'])).
% 0.56/0.74  thf('105', plain, ((l3_lattices @ sk_A)),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf('106', plain, ((v10_lattices @ sk_A)),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf('107', plain, ((v8_lattices @ sk_A)),
% 0.56/0.74      inference('demod', [status(thm)], ['104', '105', '106'])).
% 0.56/0.74  thf('108', plain,
% 0.56/0.74      (![X4 : $i]:
% 0.56/0.74         ((v2_struct_0 @ X4)
% 0.56/0.74          | ~ (v10_lattices @ X4)
% 0.56/0.74          | (v9_lattices @ X4)
% 0.56/0.74          | ~ (l3_lattices @ X4))),
% 0.56/0.74      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.56/0.74  thf('109', plain, (~ (v2_struct_0 @ sk_A)),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf('110', plain,
% 0.56/0.74      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.56/0.74      inference('sup-', [status(thm)], ['108', '109'])).
% 0.56/0.74  thf('111', plain, ((l3_lattices @ sk_A)),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf('112', plain, ((v10_lattices @ sk_A)),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf('113', plain, ((v9_lattices @ sk_A)),
% 0.56/0.74      inference('demod', [status(thm)], ['110', '111', '112'])).
% 0.56/0.74  thf('114', plain,
% 0.56/0.74      (((v2_struct_0 @ sk_A))
% 0.56/0.74         <= (~
% 0.56/0.74             ((r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 0.56/0.74               (k15_lattice3 @ sk_A @ sk_C_1))))),
% 0.56/0.74      inference('demod', [status(thm)],
% 0.56/0.74                ['92', '93', '94', '95', '101', '107', '113'])).
% 0.56/0.74  thf('115', plain, (~ (v2_struct_0 @ sk_A)),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf('116', plain,
% 0.56/0.74      (((r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 0.56/0.74         (k15_lattice3 @ sk_A @ sk_C_1)))),
% 0.56/0.74      inference('sup-', [status(thm)], ['114', '115'])).
% 0.56/0.74  thf('117', plain,
% 0.56/0.74      (~
% 0.56/0.74       ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C_1) @ 
% 0.56/0.74         (k16_lattice3 @ sk_A @ sk_B))) | 
% 0.56/0.74       ~
% 0.56/0.74       ((r3_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_B) @ 
% 0.56/0.74         (k15_lattice3 @ sk_A @ sk_C_1)))),
% 0.56/0.74      inference('split', [status(esa)], ['39'])).
% 0.56/0.74  thf('118', plain,
% 0.56/0.74      (~
% 0.56/0.74       ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C_1) @ 
% 0.56/0.74         (k16_lattice3 @ sk_A @ sk_B)))),
% 0.56/0.74      inference('sat_resolution*', [status(thm)], ['116', '117'])).
% 0.56/0.74  thf('119', plain,
% 0.56/0.74      (~ (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C_1) @ 
% 0.56/0.74          (k16_lattice3 @ sk_A @ sk_B))),
% 0.56/0.74      inference('simpl_trail', [status(thm)], ['40', '118'])).
% 0.56/0.74  thf('120', plain,
% 0.56/0.74      ((~ (l3_lattices @ sk_A)
% 0.56/0.74        | (v2_struct_0 @ sk_A)
% 0.56/0.74        | ~ (v10_lattices @ sk_A)
% 0.56/0.74        | ~ (v4_lattice3 @ sk_A)
% 0.56/0.74        | ~ (v6_lattices @ sk_A)
% 0.56/0.74        | ~ (v8_lattices @ sk_A)
% 0.56/0.74        | ~ (v9_lattices @ sk_A))),
% 0.56/0.74      inference('sup-', [status(thm)], ['38', '119'])).
% 0.56/0.74  thf('121', plain, ((l3_lattices @ sk_A)),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf('122', plain, ((v10_lattices @ sk_A)),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf('123', plain, ((v4_lattice3 @ sk_A)),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf('124', plain, ((v6_lattices @ sk_A)),
% 0.56/0.74      inference('demod', [status(thm)], ['98', '99', '100'])).
% 0.56/0.74  thf('125', plain, ((v8_lattices @ sk_A)),
% 0.56/0.74      inference('demod', [status(thm)], ['104', '105', '106'])).
% 0.56/0.74  thf('126', plain, ((v9_lattices @ sk_A)),
% 0.56/0.74      inference('demod', [status(thm)], ['110', '111', '112'])).
% 0.56/0.74  thf('127', plain, ((v2_struct_0 @ sk_A)),
% 0.56/0.74      inference('demod', [status(thm)],
% 0.56/0.74                ['120', '121', '122', '123', '124', '125', '126'])).
% 0.56/0.74  thf('128', plain, ($false), inference('demod', [status(thm)], ['0', '127'])).
% 0.56/0.74  
% 0.56/0.74  % SZS output end Refutation
% 0.56/0.74  
% 0.56/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
