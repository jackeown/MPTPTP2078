%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wlbDQJIAWS

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:28 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 275 expanded)
%              Number of leaves         :   34 (  93 expanded)
%              Depth                    :   20
%              Number of atoms          : 1611 (4498 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(a_2_2_lattice3_type,type,(
    a_2_2_lattice3: $i > $i > $i )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

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

thf(t37_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v4_lattice3 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( k15_lattice3 @ A @ B )
          = ( k16_lattice3 @ A @ ( a_2_2_lattice3 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k15_lattice3 @ X25 @ X26 )
        = ( k16_lattice3 @ X25 @ ( a_2_2_lattice3 @ X25 @ X26 ) ) )
      | ~ ( l3_lattices @ X25 )
      | ~ ( v4_lattice3 @ X25 )
      | ~ ( v10_lattices @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t37_lattice3])).

thf('2',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X4 @ X5 ) @ X8 )
      | ( r3_lattice3 @ X5 @ X4 @ X8 )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['8','9'])).

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

thf('11',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( l3_lattices @ X16 )
      | ~ ( v4_lattice3 @ X16 )
      | ~ ( v10_lattices @ X16 )
      | ( v2_struct_0 @ X16 )
      | ( X18
        = ( sk_D_2 @ X17 @ X16 @ X18 ) )
      | ~ ( r2_hidden @ X18 @ ( a_2_2_lattice3 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_2_lattice3])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ sk_A @ sk_B @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ( ( sk_D @ ( a_2_2_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A )
        = ( sk_D_2 @ X0 @ X1 @ ( sk_D @ ( a_2_2_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('14',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( l3_lattices @ X16 )
      | ~ ( v4_lattice3 @ X16 )
      | ~ ( v10_lattices @ X16 )
      | ( v2_struct_0 @ X16 )
      | ( r4_lattice3 @ X16 @ ( sk_D_2 @ X17 @ X16 @ X18 ) @ X17 )
      | ~ ( r2_hidden @ X18 @ ( a_2_2_lattice3 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_2_lattice3])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ sk_A @ sk_B @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ( r4_lattice3 @ X1 @ ( sk_D_2 @ X0 @ X1 @ ( sk_D @ ( a_2_2_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A ) ) @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ X1 @ ( sk_D @ ( a_2_2_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A ) @ X0 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( r3_lattice3 @ sk_A @ sk_B @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( r3_lattice3 @ sk_A @ sk_B @ ( a_2_2_lattice3 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ sk_A @ sk_B @ ( a_2_2_lattice3 @ X1 @ X0 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( r4_lattice3 @ X1 @ ( sk_D @ ( a_2_2_lattice3 @ X1 @ X0 ) @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( m1_subset_1 @ ( sk_D @ X8 @ X4 @ X5 ) @ ( u1_struct_0 @ X5 ) )
      | ( r3_lattice3 @ X5 @ X4 @ X8 )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['22','23'])).

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

thf('25',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( r4_lattice3 @ X10 @ X9 @ X11 )
      | ~ ( r2_hidden @ X12 @ X11 )
      | ( r1_lattices @ X10 @ X12 @ X9 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ X1 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r4_lattice3 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ X1 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r4_lattice3 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X2 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ sk_B @ ( a_2_2_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r1_lattices @ sk_A @ X1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ X0 ) @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ sk_B @ ( a_2_2_lattice3 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','28'])).

thf('30',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ sk_B @ ( a_2_2_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r1_lattices @ sk_A @ X1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ X0 ) @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ sk_B @ ( a_2_2_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ X1 @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ X0 ) @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r3_lattice3 @ sk_A @ sk_B @ ( a_2_2_lattice3 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ sk_B @ ( a_2_2_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ sk_B @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ X0 ) @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','34'])).

thf('36',plain,
    ( ( r1_lattices @ sk_A @ sk_B @ ( sk_D @ ( a_2_2_lattice3 @ sk_A @ sk_C ) @ sk_B @ sk_A ) )
    | ( r3_lattice3 @ sk_A @ sk_B @ ( a_2_2_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r1_lattices @ X5 @ X4 @ ( sk_D @ X8 @ X4 @ X5 ) )
      | ( r3_lattice3 @ X5 @ X4 @ X8 )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_lattices @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_lattices @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_lattice3 @ sk_A @ sk_B @ ( a_2_2_lattice3 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['36','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    r3_lattice3 @ sk_A @ sk_B @ ( a_2_2_lattice3 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k16_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( m1_subset_1 @ ( k16_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('48',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l3_lattices @ X14 )
      | ( v2_struct_0 @ X14 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X14 @ X15 ) @ ( u1_struct_0 @ X14 ) ) ) ),
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

thf('49',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( X20
       != ( k16_lattice3 @ X21 @ X22 ) )
      | ~ ( r3_lattice3 @ X21 @ X23 @ X22 )
      | ( r3_lattices @ X21 @ X23 @ X20 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l3_lattices @ X21 )
      | ~ ( v4_lattice3 @ X21 )
      | ~ ( v10_lattices @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('50',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v10_lattices @ X21 )
      | ~ ( v4_lattice3 @ X21 )
      | ~ ( l3_lattices @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X21 ) )
      | ( r3_lattices @ X21 @ X23 @ ( k16_lattice3 @ X21 @ X22 ) )
      | ~ ( r3_lattice3 @ X21 @ X23 @ X22 )
      | ~ ( m1_subset_1 @ ( k16_lattice3 @ X21 @ X22 ) @ ( u1_struct_0 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
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
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r3_lattices @ X0 @ X2 @ ( k16_lattice3 @ X0 @ X1 ) )
      | ~ ( r3_lattice3 @ X0 @ X2 @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( v10_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','52'])).

thf('54',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    r3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ ( a_2_2_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['46','59'])).

thf('61',plain,
    ( ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup+',[status(thm)],['1','60'])).

thf('62',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','63','64'])).

thf('66',plain,
    ( ~ ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) )
    | ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ~ ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) )
   <= ~ ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['66'])).

thf('68',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l3_lattices @ X14 )
      | ( v2_struct_0 @ X14 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X14 @ X15 ) @ ( u1_struct_0 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf('71',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( X20
       != ( k16_lattice3 @ X21 @ X22 ) )
      | ( r3_lattice3 @ X21 @ X20 @ X22 )
      | ~ ( l3_lattices @ X21 )
      | ~ ( v4_lattice3 @ X21 )
      | ~ ( v10_lattices @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('72',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v10_lattices @ X21 )
      | ~ ( v4_lattice3 @ X21 )
      | ~ ( l3_lattices @ X21 )
      | ( r3_lattice3 @ X21 @ ( k16_lattice3 @ X21 @ X22 ) @ X22 )
      | ~ ( m1_subset_1 @ ( k16_lattice3 @ X21 @ X22 ) @ ( u1_struct_0 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l3_lattices @ X14 )
      | ( v2_struct_0 @ X14 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X14 @ X15 ) @ ( u1_struct_0 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf('76',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r3_lattice3 @ X5 @ X4 @ X6 )
      | ~ ( r2_hidden @ X7 @ X6 )
      | ( r1_lattices @ X5 @ X4 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X3 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
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
    inference('sup-',[status(thm)],['74','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r1_lattices @ X1 @ ( k16_lattice3 @ X1 @ X0 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','80'])).

thf('82',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['68','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l3_lattices @ X14 )
      | ( v2_struct_0 @ X14 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X14 @ X15 ) @ ( u1_struct_0 @ X14 ) ) ) ),
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

thf('91',plain,(
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

thf('92',plain,(
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
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','93'])).

thf('95',plain,(
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

thf('96',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
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
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
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
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
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

thf('114',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['94','95','101','107','113'])).

thf('115',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ~ ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['114','115'])).

thf('117',plain,(
    r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['88','116'])).

thf('118',plain,
    ( ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C ) @ sk_B )
   <= ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(split,[status(esa)],['66'])).

thf('119',plain,(
    r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,
    ( ~ ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) )
    | ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(split,[status(esa)],['66'])).

thf('121',plain,(
    ~ ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['119','120'])).

thf('122',plain,(
    ~ ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['67','121'])).

thf('123',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['65','122'])).

thf('124',plain,(
    $false ),
    inference(demod,[status(thm)],['0','123'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wlbDQJIAWS
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:29:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.59/0.86  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.86  % Solved by: fo/fo7.sh
% 0.59/0.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.86  % done 329 iterations in 0.438s
% 0.59/0.86  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.86  % SZS output start Refutation
% 0.59/0.86  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.59/0.86  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.86  thf(a_2_2_lattice3_type, type, a_2_2_lattice3: $i > $i > $i).
% 0.59/0.86  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.59/0.86  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.59/0.86  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.86  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.86  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.59/0.86  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.86  thf(r3_lattice3_type, type, r3_lattice3: $i > $i > $i > $o).
% 0.59/0.86  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.86  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.59/0.86  thf(r4_lattice3_type, type, r4_lattice3: $i > $i > $i > $o).
% 0.59/0.86  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 0.59/0.86  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 0.59/0.86  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.59/0.86  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.59/0.86  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.59/0.86  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 0.59/0.86  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 0.59/0.86  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 0.59/0.86  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.59/0.86  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.59/0.86  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.59/0.86  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.59/0.86  thf(t38_lattice3, conjecture,
% 0.59/0.86    (![A:$i]:
% 0.59/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.59/0.86         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.59/0.86       ( ![B:$i]:
% 0.59/0.86         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.86           ( ![C:$i]:
% 0.59/0.86             ( ( r2_hidden @ B @ C ) =>
% 0.59/0.86               ( ( r3_lattices @ A @ B @ ( k15_lattice3 @ A @ C ) ) & 
% 0.59/0.86                 ( r3_lattices @ A @ ( k16_lattice3 @ A @ C ) @ B ) ) ) ) ) ) ))).
% 0.59/0.86  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.86    (~( ![A:$i]:
% 0.59/0.86        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.59/0.86            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.59/0.86          ( ![B:$i]:
% 0.59/0.86            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.86              ( ![C:$i]:
% 0.59/0.86                ( ( r2_hidden @ B @ C ) =>
% 0.59/0.86                  ( ( r3_lattices @ A @ B @ ( k15_lattice3 @ A @ C ) ) & 
% 0.59/0.86                    ( r3_lattices @ A @ ( k16_lattice3 @ A @ C ) @ B ) ) ) ) ) ) ) )),
% 0.59/0.86    inference('cnf.neg', [status(esa)], [t38_lattice3])).
% 0.59/0.86  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.86  thf(t37_lattice3, axiom,
% 0.59/0.86    (![A:$i]:
% 0.59/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.59/0.86         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.59/0.86       ( ![B:$i]:
% 0.59/0.86         ( ( k15_lattice3 @ A @ B ) =
% 0.59/0.86           ( k16_lattice3 @ A @ ( a_2_2_lattice3 @ A @ B ) ) ) ) ))).
% 0.59/0.86  thf('1', plain,
% 0.59/0.86      (![X25 : $i, X26 : $i]:
% 0.59/0.86         (((k15_lattice3 @ X25 @ X26)
% 0.59/0.86            = (k16_lattice3 @ X25 @ (a_2_2_lattice3 @ X25 @ X26)))
% 0.59/0.86          | ~ (l3_lattices @ X25)
% 0.59/0.86          | ~ (v4_lattice3 @ X25)
% 0.59/0.86          | ~ (v10_lattices @ X25)
% 0.59/0.86          | (v2_struct_0 @ X25))),
% 0.59/0.86      inference('cnf', [status(esa)], [t37_lattice3])).
% 0.59/0.86  thf('2', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.59/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.86  thf('3', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.59/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.86  thf('4', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.59/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.86  thf(d16_lattice3, axiom,
% 0.59/0.86    (![A:$i]:
% 0.59/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.59/0.86       ( ![B:$i]:
% 0.59/0.86         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.86           ( ![C:$i]:
% 0.59/0.86             ( ( r3_lattice3 @ A @ B @ C ) <=>
% 0.59/0.86               ( ![D:$i]:
% 0.59/0.86                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.86                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 0.59/0.86  thf('5', plain,
% 0.59/0.86      (![X4 : $i, X5 : $i, X8 : $i]:
% 0.59/0.86         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.59/0.86          | (r2_hidden @ (sk_D @ X8 @ X4 @ X5) @ X8)
% 0.59/0.86          | (r3_lattice3 @ X5 @ X4 @ X8)
% 0.59/0.86          | ~ (l3_lattices @ X5)
% 0.59/0.86          | (v2_struct_0 @ X5))),
% 0.59/0.86      inference('cnf', [status(esa)], [d16_lattice3])).
% 0.59/0.86  thf('6', plain,
% 0.59/0.86      (![X0 : $i]:
% 0.59/0.86         ((v2_struct_0 @ sk_A)
% 0.59/0.86          | ~ (l3_lattices @ sk_A)
% 0.59/0.86          | (r3_lattice3 @ sk_A @ sk_B @ X0)
% 0.59/0.86          | (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ X0))),
% 0.59/0.86      inference('sup-', [status(thm)], ['4', '5'])).
% 0.59/0.86  thf('7', plain, ((l3_lattices @ sk_A)),
% 0.59/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.86  thf('8', plain,
% 0.59/0.86      (![X0 : $i]:
% 0.59/0.86         ((v2_struct_0 @ sk_A)
% 0.59/0.86          | (r3_lattice3 @ sk_A @ sk_B @ X0)
% 0.59/0.86          | (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ X0))),
% 0.59/0.86      inference('demod', [status(thm)], ['6', '7'])).
% 0.59/0.86  thf('9', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.86  thf('10', plain,
% 0.59/0.86      (![X0 : $i]:
% 0.59/0.86         ((r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ X0)
% 0.59/0.86          | (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.59/0.86      inference('clc', [status(thm)], ['8', '9'])).
% 0.59/0.86  thf(fraenkel_a_2_2_lattice3, axiom,
% 0.59/0.86    (![A:$i,B:$i,C:$i]:
% 0.59/0.86     ( ( ( ~( v2_struct_0 @ B ) ) & ( v10_lattices @ B ) & 
% 0.59/0.86         ( v4_lattice3 @ B ) & ( l3_lattices @ B ) ) =>
% 0.59/0.86       ( ( r2_hidden @ A @ ( a_2_2_lattice3 @ B @ C ) ) <=>
% 0.59/0.86         ( ?[D:$i]:
% 0.59/0.86           ( ( r4_lattice3 @ B @ D @ C ) & ( ( A ) = ( D ) ) & 
% 0.59/0.86             ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.59/0.86  thf('11', plain,
% 0.59/0.86      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.59/0.86         (~ (l3_lattices @ X16)
% 0.59/0.86          | ~ (v4_lattice3 @ X16)
% 0.59/0.86          | ~ (v10_lattices @ X16)
% 0.59/0.86          | (v2_struct_0 @ X16)
% 0.59/0.86          | ((X18) = (sk_D_2 @ X17 @ X16 @ X18))
% 0.59/0.86          | ~ (r2_hidden @ X18 @ (a_2_2_lattice3 @ X16 @ X17)))),
% 0.59/0.86      inference('cnf', [status(esa)], [fraenkel_a_2_2_lattice3])).
% 0.59/0.86  thf('12', plain,
% 0.59/0.86      (![X0 : $i, X1 : $i]:
% 0.59/0.86         ((r3_lattice3 @ sk_A @ sk_B @ (a_2_2_lattice3 @ X1 @ X0))
% 0.59/0.86          | ((sk_D @ (a_2_2_lattice3 @ X1 @ X0) @ sk_B @ sk_A)
% 0.59/0.86              = (sk_D_2 @ X0 @ X1 @ 
% 0.59/0.86                 (sk_D @ (a_2_2_lattice3 @ X1 @ X0) @ sk_B @ sk_A)))
% 0.59/0.86          | (v2_struct_0 @ X1)
% 0.59/0.86          | ~ (v10_lattices @ X1)
% 0.59/0.86          | ~ (v4_lattice3 @ X1)
% 0.59/0.86          | ~ (l3_lattices @ X1))),
% 0.59/0.86      inference('sup-', [status(thm)], ['10', '11'])).
% 0.59/0.86  thf('13', plain,
% 0.59/0.86      (![X0 : $i]:
% 0.59/0.86         ((r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ X0)
% 0.59/0.86          | (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.59/0.86      inference('clc', [status(thm)], ['8', '9'])).
% 0.59/0.86  thf('14', plain,
% 0.59/0.86      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.59/0.86         (~ (l3_lattices @ X16)
% 0.59/0.86          | ~ (v4_lattice3 @ X16)
% 0.59/0.86          | ~ (v10_lattices @ X16)
% 0.59/0.86          | (v2_struct_0 @ X16)
% 0.59/0.86          | (r4_lattice3 @ X16 @ (sk_D_2 @ X17 @ X16 @ X18) @ X17)
% 0.59/0.86          | ~ (r2_hidden @ X18 @ (a_2_2_lattice3 @ X16 @ X17)))),
% 0.59/0.86      inference('cnf', [status(esa)], [fraenkel_a_2_2_lattice3])).
% 0.59/0.86  thf('15', plain,
% 0.59/0.86      (![X0 : $i, X1 : $i]:
% 0.59/0.86         ((r3_lattice3 @ sk_A @ sk_B @ (a_2_2_lattice3 @ X1 @ X0))
% 0.59/0.86          | (r4_lattice3 @ X1 @ 
% 0.59/0.86             (sk_D_2 @ X0 @ X1 @ 
% 0.59/0.86              (sk_D @ (a_2_2_lattice3 @ X1 @ X0) @ sk_B @ sk_A)) @ 
% 0.59/0.86             X0)
% 0.59/0.86          | (v2_struct_0 @ X1)
% 0.59/0.86          | ~ (v10_lattices @ X1)
% 0.59/0.86          | ~ (v4_lattice3 @ X1)
% 0.59/0.86          | ~ (l3_lattices @ X1))),
% 0.59/0.86      inference('sup-', [status(thm)], ['13', '14'])).
% 0.59/0.86  thf('16', plain,
% 0.59/0.86      (![X0 : $i, X1 : $i]:
% 0.59/0.86         ((r4_lattice3 @ X1 @ 
% 0.59/0.86           (sk_D @ (a_2_2_lattice3 @ X1 @ X0) @ sk_B @ sk_A) @ X0)
% 0.59/0.86          | ~ (l3_lattices @ X1)
% 0.59/0.86          | ~ (v4_lattice3 @ X1)
% 0.59/0.86          | ~ (v10_lattices @ X1)
% 0.59/0.86          | (v2_struct_0 @ X1)
% 0.59/0.86          | (r3_lattice3 @ sk_A @ sk_B @ (a_2_2_lattice3 @ X1 @ X0))
% 0.59/0.86          | ~ (l3_lattices @ X1)
% 0.59/0.86          | ~ (v4_lattice3 @ X1)
% 0.59/0.86          | ~ (v10_lattices @ X1)
% 0.59/0.86          | (v2_struct_0 @ X1)
% 0.59/0.86          | (r3_lattice3 @ sk_A @ sk_B @ (a_2_2_lattice3 @ X1 @ X0)))),
% 0.59/0.86      inference('sup+', [status(thm)], ['12', '15'])).
% 0.59/0.86  thf('17', plain,
% 0.59/0.86      (![X0 : $i, X1 : $i]:
% 0.59/0.86         ((r3_lattice3 @ sk_A @ sk_B @ (a_2_2_lattice3 @ X1 @ X0))
% 0.59/0.86          | (v2_struct_0 @ X1)
% 0.59/0.86          | ~ (v10_lattices @ X1)
% 0.59/0.86          | ~ (v4_lattice3 @ X1)
% 0.59/0.86          | ~ (l3_lattices @ X1)
% 0.59/0.86          | (r4_lattice3 @ X1 @ 
% 0.59/0.86             (sk_D @ (a_2_2_lattice3 @ X1 @ X0) @ sk_B @ sk_A) @ X0))),
% 0.59/0.86      inference('simplify', [status(thm)], ['16'])).
% 0.59/0.86  thf('18', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.59/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.86  thf('19', plain,
% 0.59/0.86      (![X4 : $i, X5 : $i, X8 : $i]:
% 0.59/0.86         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.59/0.86          | (m1_subset_1 @ (sk_D @ X8 @ X4 @ X5) @ (u1_struct_0 @ X5))
% 0.59/0.86          | (r3_lattice3 @ X5 @ X4 @ X8)
% 0.59/0.86          | ~ (l3_lattices @ X5)
% 0.59/0.86          | (v2_struct_0 @ X5))),
% 0.59/0.86      inference('cnf', [status(esa)], [d16_lattice3])).
% 0.59/0.86  thf('20', plain,
% 0.59/0.86      (![X0 : $i]:
% 0.59/0.86         ((v2_struct_0 @ sk_A)
% 0.59/0.86          | ~ (l3_lattices @ sk_A)
% 0.59/0.86          | (r3_lattice3 @ sk_A @ sk_B @ X0)
% 0.59/0.86          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.59/0.86      inference('sup-', [status(thm)], ['18', '19'])).
% 0.59/0.86  thf('21', plain, ((l3_lattices @ sk_A)),
% 0.59/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.86  thf('22', plain,
% 0.59/0.86      (![X0 : $i]:
% 0.59/0.86         ((v2_struct_0 @ sk_A)
% 0.59/0.86          | (r3_lattice3 @ sk_A @ sk_B @ X0)
% 0.59/0.86          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.59/0.86      inference('demod', [status(thm)], ['20', '21'])).
% 0.59/0.86  thf('23', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.86  thf('24', plain,
% 0.59/0.86      (![X0 : $i]:
% 0.59/0.86         ((m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.59/0.86          | (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.59/0.86      inference('clc', [status(thm)], ['22', '23'])).
% 0.59/0.86  thf(d17_lattice3, axiom,
% 0.59/0.86    (![A:$i]:
% 0.59/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.59/0.86       ( ![B:$i]:
% 0.59/0.86         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.86           ( ![C:$i]:
% 0.59/0.86             ( ( r4_lattice3 @ A @ B @ C ) <=>
% 0.59/0.86               ( ![D:$i]:
% 0.59/0.86                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.86                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ))).
% 0.59/0.86  thf('25', plain,
% 0.59/0.86      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.59/0.86         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.59/0.86          | ~ (r4_lattice3 @ X10 @ X9 @ X11)
% 0.59/0.86          | ~ (r2_hidden @ X12 @ X11)
% 0.59/0.86          | (r1_lattices @ X10 @ X12 @ X9)
% 0.59/0.86          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X10))
% 0.59/0.86          | ~ (l3_lattices @ X10)
% 0.59/0.86          | (v2_struct_0 @ X10))),
% 0.59/0.86      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.59/0.86  thf('26', plain,
% 0.59/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.86         ((r3_lattice3 @ sk_A @ sk_B @ X0)
% 0.59/0.86          | (v2_struct_0 @ sk_A)
% 0.59/0.86          | ~ (l3_lattices @ sk_A)
% 0.59/0.86          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.59/0.86          | (r1_lattices @ sk_A @ X1 @ (sk_D @ X0 @ sk_B @ sk_A))
% 0.59/0.86          | ~ (r2_hidden @ X1 @ X2)
% 0.59/0.86          | ~ (r4_lattice3 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ X2))),
% 0.59/0.86      inference('sup-', [status(thm)], ['24', '25'])).
% 0.59/0.86  thf('27', plain, ((l3_lattices @ sk_A)),
% 0.59/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.86  thf('28', plain,
% 0.59/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.86         ((r3_lattice3 @ sk_A @ sk_B @ X0)
% 0.59/0.86          | (v2_struct_0 @ sk_A)
% 0.59/0.86          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.59/0.86          | (r1_lattices @ sk_A @ X1 @ (sk_D @ X0 @ sk_B @ sk_A))
% 0.59/0.86          | ~ (r2_hidden @ X1 @ X2)
% 0.59/0.86          | ~ (r4_lattice3 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ X2))),
% 0.59/0.86      inference('demod', [status(thm)], ['26', '27'])).
% 0.59/0.86  thf('29', plain,
% 0.59/0.86      (![X0 : $i, X1 : $i]:
% 0.59/0.86         (~ (l3_lattices @ sk_A)
% 0.59/0.86          | ~ (v4_lattice3 @ sk_A)
% 0.59/0.86          | ~ (v10_lattices @ sk_A)
% 0.59/0.86          | (v2_struct_0 @ sk_A)
% 0.59/0.86          | (r3_lattice3 @ sk_A @ sk_B @ (a_2_2_lattice3 @ sk_A @ X0))
% 0.59/0.86          | ~ (r2_hidden @ X1 @ X0)
% 0.59/0.86          | (r1_lattices @ sk_A @ X1 @ 
% 0.59/0.86             (sk_D @ (a_2_2_lattice3 @ sk_A @ X0) @ sk_B @ sk_A))
% 0.59/0.86          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.59/0.86          | (v2_struct_0 @ sk_A)
% 0.59/0.86          | (r3_lattice3 @ sk_A @ sk_B @ (a_2_2_lattice3 @ sk_A @ X0)))),
% 0.59/0.86      inference('sup-', [status(thm)], ['17', '28'])).
% 0.59/0.86  thf('30', plain, ((l3_lattices @ sk_A)),
% 0.59/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.86  thf('31', plain, ((v4_lattice3 @ sk_A)),
% 0.59/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.86  thf('32', plain, ((v10_lattices @ sk_A)),
% 0.59/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.86  thf('33', plain,
% 0.59/0.86      (![X0 : $i, X1 : $i]:
% 0.59/0.86         ((v2_struct_0 @ sk_A)
% 0.59/0.86          | (r3_lattice3 @ sk_A @ sk_B @ (a_2_2_lattice3 @ sk_A @ X0))
% 0.59/0.86          | ~ (r2_hidden @ X1 @ X0)
% 0.59/0.86          | (r1_lattices @ sk_A @ X1 @ 
% 0.59/0.86             (sk_D @ (a_2_2_lattice3 @ sk_A @ X0) @ sk_B @ sk_A))
% 0.59/0.86          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.59/0.86          | (v2_struct_0 @ sk_A)
% 0.59/0.86          | (r3_lattice3 @ sk_A @ sk_B @ (a_2_2_lattice3 @ sk_A @ X0)))),
% 0.59/0.86      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.59/0.86  thf('34', plain,
% 0.59/0.86      (![X0 : $i, X1 : $i]:
% 0.59/0.86         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.59/0.86          | (r1_lattices @ sk_A @ X1 @ 
% 0.59/0.86             (sk_D @ (a_2_2_lattice3 @ sk_A @ X0) @ sk_B @ sk_A))
% 0.59/0.86          | ~ (r2_hidden @ X1 @ X0)
% 0.59/0.86          | (r3_lattice3 @ sk_A @ sk_B @ (a_2_2_lattice3 @ sk_A @ X0))
% 0.59/0.86          | (v2_struct_0 @ sk_A))),
% 0.59/0.86      inference('simplify', [status(thm)], ['33'])).
% 0.59/0.86  thf('35', plain,
% 0.59/0.86      (![X0 : $i]:
% 0.59/0.86         ((v2_struct_0 @ sk_A)
% 0.59/0.86          | (r3_lattice3 @ sk_A @ sk_B @ (a_2_2_lattice3 @ sk_A @ X0))
% 0.59/0.86          | ~ (r2_hidden @ sk_B @ X0)
% 0.59/0.86          | (r1_lattices @ sk_A @ sk_B @ 
% 0.59/0.86             (sk_D @ (a_2_2_lattice3 @ sk_A @ X0) @ sk_B @ sk_A)))),
% 0.59/0.86      inference('sup-', [status(thm)], ['3', '34'])).
% 0.59/0.86  thf('36', plain,
% 0.59/0.86      (((r1_lattices @ sk_A @ sk_B @ 
% 0.59/0.86         (sk_D @ (a_2_2_lattice3 @ sk_A @ sk_C) @ sk_B @ sk_A))
% 0.59/0.86        | (r3_lattice3 @ sk_A @ sk_B @ (a_2_2_lattice3 @ sk_A @ sk_C))
% 0.59/0.86        | (v2_struct_0 @ sk_A))),
% 0.59/0.86      inference('sup-', [status(thm)], ['2', '35'])).
% 0.59/0.86  thf('37', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.59/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.86  thf('38', plain,
% 0.59/0.86      (![X4 : $i, X5 : $i, X8 : $i]:
% 0.59/0.86         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.59/0.86          | ~ (r1_lattices @ X5 @ X4 @ (sk_D @ X8 @ X4 @ X5))
% 0.59/0.86          | (r3_lattice3 @ X5 @ X4 @ X8)
% 0.59/0.86          | ~ (l3_lattices @ X5)
% 0.59/0.86          | (v2_struct_0 @ X5))),
% 0.59/0.86      inference('cnf', [status(esa)], [d16_lattice3])).
% 0.59/0.86  thf('39', plain,
% 0.59/0.86      (![X0 : $i]:
% 0.59/0.86         ((v2_struct_0 @ sk_A)
% 0.59/0.86          | ~ (l3_lattices @ sk_A)
% 0.59/0.86          | (r3_lattice3 @ sk_A @ sk_B @ X0)
% 0.59/0.86          | ~ (r1_lattices @ sk_A @ sk_B @ (sk_D @ X0 @ sk_B @ sk_A)))),
% 0.59/0.86      inference('sup-', [status(thm)], ['37', '38'])).
% 0.69/0.86  thf('40', plain, ((l3_lattices @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('41', plain,
% 0.69/0.86      (![X0 : $i]:
% 0.69/0.86         ((v2_struct_0 @ sk_A)
% 0.69/0.86          | (r3_lattice3 @ sk_A @ sk_B @ X0)
% 0.69/0.86          | ~ (r1_lattices @ sk_A @ sk_B @ (sk_D @ X0 @ sk_B @ sk_A)))),
% 0.69/0.86      inference('demod', [status(thm)], ['39', '40'])).
% 0.69/0.86  thf('42', plain, (~ (v2_struct_0 @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('43', plain,
% 0.69/0.86      (![X0 : $i]:
% 0.69/0.86         (~ (r1_lattices @ sk_A @ sk_B @ (sk_D @ X0 @ sk_B @ sk_A))
% 0.69/0.86          | (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.69/0.86      inference('clc', [status(thm)], ['41', '42'])).
% 0.69/0.86  thf('44', plain,
% 0.69/0.86      (((v2_struct_0 @ sk_A)
% 0.69/0.86        | (r3_lattice3 @ sk_A @ sk_B @ (a_2_2_lattice3 @ sk_A @ sk_C)))),
% 0.69/0.86      inference('clc', [status(thm)], ['36', '43'])).
% 0.69/0.86  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('46', plain,
% 0.69/0.86      ((r3_lattice3 @ sk_A @ sk_B @ (a_2_2_lattice3 @ sk_A @ sk_C))),
% 0.69/0.86      inference('clc', [status(thm)], ['44', '45'])).
% 0.69/0.86  thf('47', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf(dt_k16_lattice3, axiom,
% 0.69/0.86    (![A:$i,B:$i]:
% 0.69/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.69/0.86       ( m1_subset_1 @ ( k16_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.69/0.86  thf('48', plain,
% 0.69/0.86      (![X14 : $i, X15 : $i]:
% 0.69/0.86         (~ (l3_lattices @ X14)
% 0.69/0.86          | (v2_struct_0 @ X14)
% 0.69/0.86          | (m1_subset_1 @ (k16_lattice3 @ X14 @ X15) @ (u1_struct_0 @ X14)))),
% 0.69/0.86      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.69/0.86  thf(t34_lattice3, axiom,
% 0.69/0.86    (![A:$i]:
% 0.69/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.69/0.86         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.69/0.86       ( ![B:$i]:
% 0.69/0.86         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.69/0.86           ( ![C:$i]:
% 0.69/0.86             ( ( ( B ) = ( k16_lattice3 @ A @ C ) ) <=>
% 0.69/0.86               ( ( r3_lattice3 @ A @ B @ C ) & 
% 0.69/0.86                 ( ![D:$i]:
% 0.69/0.86                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.69/0.86                     ( ( r3_lattice3 @ A @ D @ C ) =>
% 0.69/0.86                       ( r3_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.69/0.86  thf('49', plain,
% 0.69/0.86      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.69/0.86         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.69/0.86          | ((X20) != (k16_lattice3 @ X21 @ X22))
% 0.69/0.86          | ~ (r3_lattice3 @ X21 @ X23 @ X22)
% 0.69/0.86          | (r3_lattices @ X21 @ X23 @ X20)
% 0.69/0.86          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X21))
% 0.69/0.86          | ~ (l3_lattices @ X21)
% 0.69/0.86          | ~ (v4_lattice3 @ X21)
% 0.69/0.86          | ~ (v10_lattices @ X21)
% 0.69/0.86          | (v2_struct_0 @ X21))),
% 0.69/0.86      inference('cnf', [status(esa)], [t34_lattice3])).
% 0.69/0.86  thf('50', plain,
% 0.69/0.86      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.69/0.86         ((v2_struct_0 @ X21)
% 0.69/0.86          | ~ (v10_lattices @ X21)
% 0.69/0.86          | ~ (v4_lattice3 @ X21)
% 0.69/0.86          | ~ (l3_lattices @ X21)
% 0.69/0.86          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X21))
% 0.69/0.86          | (r3_lattices @ X21 @ X23 @ (k16_lattice3 @ X21 @ X22))
% 0.69/0.86          | ~ (r3_lattice3 @ X21 @ X23 @ X22)
% 0.69/0.86          | ~ (m1_subset_1 @ (k16_lattice3 @ X21 @ X22) @ (u1_struct_0 @ X21)))),
% 0.69/0.86      inference('simplify', [status(thm)], ['49'])).
% 0.69/0.86  thf('51', plain,
% 0.69/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.86         ((v2_struct_0 @ X0)
% 0.69/0.86          | ~ (l3_lattices @ X0)
% 0.69/0.86          | ~ (r3_lattice3 @ X0 @ X2 @ X1)
% 0.69/0.86          | (r3_lattices @ X0 @ X2 @ (k16_lattice3 @ X0 @ X1))
% 0.69/0.86          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.69/0.86          | ~ (l3_lattices @ X0)
% 0.69/0.86          | ~ (v4_lattice3 @ X0)
% 0.69/0.86          | ~ (v10_lattices @ X0)
% 0.69/0.86          | (v2_struct_0 @ X0))),
% 0.69/0.86      inference('sup-', [status(thm)], ['48', '50'])).
% 0.69/0.86  thf('52', plain,
% 0.69/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.86         (~ (v10_lattices @ X0)
% 0.69/0.86          | ~ (v4_lattice3 @ X0)
% 0.69/0.86          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.69/0.86          | (r3_lattices @ X0 @ X2 @ (k16_lattice3 @ X0 @ X1))
% 0.69/0.86          | ~ (r3_lattice3 @ X0 @ X2 @ X1)
% 0.69/0.86          | ~ (l3_lattices @ X0)
% 0.69/0.86          | (v2_struct_0 @ X0))),
% 0.69/0.86      inference('simplify', [status(thm)], ['51'])).
% 0.69/0.86  thf('53', plain,
% 0.69/0.86      (![X0 : $i]:
% 0.69/0.86         ((v2_struct_0 @ sk_A)
% 0.69/0.86          | ~ (l3_lattices @ sk_A)
% 0.69/0.86          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0)
% 0.69/0.86          | (r3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0))
% 0.69/0.86          | ~ (v4_lattice3 @ sk_A)
% 0.69/0.86          | ~ (v10_lattices @ sk_A))),
% 0.69/0.86      inference('sup-', [status(thm)], ['47', '52'])).
% 0.69/0.86  thf('54', plain, ((l3_lattices @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('55', plain, ((v4_lattice3 @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('56', plain, ((v10_lattices @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('57', plain,
% 0.69/0.86      (![X0 : $i]:
% 0.69/0.86         ((v2_struct_0 @ sk_A)
% 0.69/0.86          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0)
% 0.69/0.86          | (r3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0)))),
% 0.69/0.86      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 0.69/0.86  thf('58', plain, (~ (v2_struct_0 @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('59', plain,
% 0.69/0.86      (![X0 : $i]:
% 0.69/0.86         ((r3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0))
% 0.69/0.86          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.69/0.86      inference('clc', [status(thm)], ['57', '58'])).
% 0.69/0.86  thf('60', plain,
% 0.69/0.86      ((r3_lattices @ sk_A @ sk_B @ 
% 0.69/0.86        (k16_lattice3 @ sk_A @ (a_2_2_lattice3 @ sk_A @ sk_C)))),
% 0.69/0.86      inference('sup-', [status(thm)], ['46', '59'])).
% 0.69/0.86  thf('61', plain,
% 0.69/0.86      (((r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C))
% 0.69/0.86        | (v2_struct_0 @ sk_A)
% 0.69/0.86        | ~ (v10_lattices @ sk_A)
% 0.69/0.86        | ~ (v4_lattice3 @ sk_A)
% 0.69/0.86        | ~ (l3_lattices @ sk_A))),
% 0.69/0.86      inference('sup+', [status(thm)], ['1', '60'])).
% 0.69/0.86  thf('62', plain, ((v10_lattices @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('63', plain, ((v4_lattice3 @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('64', plain, ((l3_lattices @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('65', plain,
% 0.69/0.86      (((r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C))
% 0.69/0.86        | (v2_struct_0 @ sk_A))),
% 0.69/0.86      inference('demod', [status(thm)], ['61', '62', '63', '64'])).
% 0.69/0.86  thf('66', plain,
% 0.69/0.86      ((~ (r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C))
% 0.69/0.86        | ~ (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C) @ sk_B))),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('67', plain,
% 0.69/0.86      ((~ (r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C)))
% 0.69/0.86         <= (~ ((r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C))))),
% 0.69/0.86      inference('split', [status(esa)], ['66'])).
% 0.69/0.86  thf('68', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('69', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('70', plain,
% 0.69/0.86      (![X14 : $i, X15 : $i]:
% 0.69/0.86         (~ (l3_lattices @ X14)
% 0.69/0.86          | (v2_struct_0 @ X14)
% 0.69/0.86          | (m1_subset_1 @ (k16_lattice3 @ X14 @ X15) @ (u1_struct_0 @ X14)))),
% 0.69/0.86      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.69/0.86  thf('71', plain,
% 0.69/0.86      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.69/0.86         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.69/0.86          | ((X20) != (k16_lattice3 @ X21 @ X22))
% 0.69/0.86          | (r3_lattice3 @ X21 @ X20 @ X22)
% 0.69/0.86          | ~ (l3_lattices @ X21)
% 0.69/0.86          | ~ (v4_lattice3 @ X21)
% 0.69/0.86          | ~ (v10_lattices @ X21)
% 0.69/0.86          | (v2_struct_0 @ X21))),
% 0.69/0.86      inference('cnf', [status(esa)], [t34_lattice3])).
% 0.69/0.86  thf('72', plain,
% 0.69/0.86      (![X21 : $i, X22 : $i]:
% 0.69/0.86         ((v2_struct_0 @ X21)
% 0.69/0.86          | ~ (v10_lattices @ X21)
% 0.69/0.86          | ~ (v4_lattice3 @ X21)
% 0.69/0.86          | ~ (l3_lattices @ X21)
% 0.69/0.86          | (r3_lattice3 @ X21 @ (k16_lattice3 @ X21 @ X22) @ X22)
% 0.69/0.86          | ~ (m1_subset_1 @ (k16_lattice3 @ X21 @ X22) @ (u1_struct_0 @ X21)))),
% 0.69/0.86      inference('simplify', [status(thm)], ['71'])).
% 0.69/0.86  thf('73', plain,
% 0.69/0.86      (![X0 : $i, X1 : $i]:
% 0.69/0.86         ((v2_struct_0 @ X0)
% 0.69/0.86          | ~ (l3_lattices @ X0)
% 0.69/0.86          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X1)
% 0.69/0.86          | ~ (l3_lattices @ X0)
% 0.69/0.86          | ~ (v4_lattice3 @ X0)
% 0.69/0.86          | ~ (v10_lattices @ X0)
% 0.69/0.86          | (v2_struct_0 @ X0))),
% 0.69/0.86      inference('sup-', [status(thm)], ['70', '72'])).
% 0.69/0.86  thf('74', plain,
% 0.69/0.86      (![X0 : $i, X1 : $i]:
% 0.69/0.86         (~ (v10_lattices @ X0)
% 0.69/0.86          | ~ (v4_lattice3 @ X0)
% 0.69/0.86          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X1)
% 0.69/0.86          | ~ (l3_lattices @ X0)
% 0.69/0.86          | (v2_struct_0 @ X0))),
% 0.69/0.86      inference('simplify', [status(thm)], ['73'])).
% 0.69/0.86  thf('75', plain,
% 0.69/0.86      (![X14 : $i, X15 : $i]:
% 0.69/0.86         (~ (l3_lattices @ X14)
% 0.69/0.86          | (v2_struct_0 @ X14)
% 0.69/0.86          | (m1_subset_1 @ (k16_lattice3 @ X14 @ X15) @ (u1_struct_0 @ X14)))),
% 0.69/0.86      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.69/0.86  thf('76', plain,
% 0.69/0.86      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.69/0.86         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.69/0.86          | ~ (r3_lattice3 @ X5 @ X4 @ X6)
% 0.69/0.86          | ~ (r2_hidden @ X7 @ X6)
% 0.69/0.86          | (r1_lattices @ X5 @ X4 @ X7)
% 0.69/0.86          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X5))
% 0.69/0.86          | ~ (l3_lattices @ X5)
% 0.69/0.86          | (v2_struct_0 @ X5))),
% 0.69/0.86      inference('cnf', [status(esa)], [d16_lattice3])).
% 0.69/0.86  thf('77', plain,
% 0.69/0.86      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.69/0.86         ((v2_struct_0 @ X0)
% 0.69/0.86          | ~ (l3_lattices @ X0)
% 0.69/0.86          | (v2_struct_0 @ X0)
% 0.69/0.86          | ~ (l3_lattices @ X0)
% 0.69/0.86          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.69/0.86          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.69/0.86          | ~ (r2_hidden @ X2 @ X3)
% 0.69/0.86          | ~ (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X3))),
% 0.69/0.86      inference('sup-', [status(thm)], ['75', '76'])).
% 0.69/0.86  thf('78', plain,
% 0.69/0.86      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.69/0.86         (~ (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X3)
% 0.69/0.86          | ~ (r2_hidden @ X2 @ X3)
% 0.69/0.86          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.69/0.86          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.69/0.86          | ~ (l3_lattices @ X0)
% 0.69/0.86          | (v2_struct_0 @ X0))),
% 0.69/0.86      inference('simplify', [status(thm)], ['77'])).
% 0.69/0.86  thf('79', plain,
% 0.69/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.86         ((v2_struct_0 @ X1)
% 0.69/0.86          | ~ (l3_lattices @ X1)
% 0.69/0.86          | ~ (v4_lattice3 @ X1)
% 0.69/0.86          | ~ (v10_lattices @ X1)
% 0.69/0.86          | (v2_struct_0 @ X1)
% 0.69/0.86          | ~ (l3_lattices @ X1)
% 0.69/0.86          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.69/0.86          | (r1_lattices @ X1 @ (k16_lattice3 @ X1 @ X0) @ X2)
% 0.69/0.86          | ~ (r2_hidden @ X2 @ X0))),
% 0.69/0.86      inference('sup-', [status(thm)], ['74', '78'])).
% 0.69/0.86  thf('80', plain,
% 0.69/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.86         (~ (r2_hidden @ X2 @ X0)
% 0.69/0.86          | (r1_lattices @ X1 @ (k16_lattice3 @ X1 @ X0) @ X2)
% 0.69/0.86          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.69/0.86          | ~ (v10_lattices @ X1)
% 0.69/0.86          | ~ (v4_lattice3 @ X1)
% 0.69/0.86          | ~ (l3_lattices @ X1)
% 0.69/0.86          | (v2_struct_0 @ X1))),
% 0.69/0.86      inference('simplify', [status(thm)], ['79'])).
% 0.69/0.86  thf('81', plain,
% 0.69/0.86      (![X0 : $i]:
% 0.69/0.86         ((v2_struct_0 @ sk_A)
% 0.69/0.86          | ~ (l3_lattices @ sk_A)
% 0.69/0.86          | ~ (v4_lattice3 @ sk_A)
% 0.69/0.86          | ~ (v10_lattices @ sk_A)
% 0.69/0.86          | (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.69/0.86          | ~ (r2_hidden @ sk_B @ X0))),
% 0.69/0.86      inference('sup-', [status(thm)], ['69', '80'])).
% 0.69/0.86  thf('82', plain, ((l3_lattices @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('83', plain, ((v4_lattice3 @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('84', plain, ((v10_lattices @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('85', plain,
% 0.69/0.86      (![X0 : $i]:
% 0.69/0.86         ((v2_struct_0 @ sk_A)
% 0.69/0.86          | (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.69/0.86          | ~ (r2_hidden @ sk_B @ X0))),
% 0.69/0.86      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 0.69/0.86  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('87', plain,
% 0.69/0.86      (![X0 : $i]:
% 0.69/0.86         (~ (r2_hidden @ sk_B @ X0)
% 0.69/0.86          | (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B))),
% 0.69/0.86      inference('clc', [status(thm)], ['85', '86'])).
% 0.69/0.86  thf('88', plain,
% 0.69/0.86      ((r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C) @ sk_B)),
% 0.69/0.86      inference('sup-', [status(thm)], ['68', '87'])).
% 0.69/0.86  thf('89', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('90', plain,
% 0.69/0.86      (![X14 : $i, X15 : $i]:
% 0.69/0.86         (~ (l3_lattices @ X14)
% 0.69/0.86          | (v2_struct_0 @ X14)
% 0.69/0.86          | (m1_subset_1 @ (k16_lattice3 @ X14 @ X15) @ (u1_struct_0 @ X14)))),
% 0.69/0.86      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.69/0.86  thf(redefinition_r3_lattices, axiom,
% 0.69/0.86    (![A:$i,B:$i,C:$i]:
% 0.69/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.69/0.86         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 0.69/0.86         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.69/0.86         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.86       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 0.69/0.86  thf('91', plain,
% 0.69/0.86      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.69/0.86         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.69/0.86          | ~ (l3_lattices @ X2)
% 0.69/0.86          | ~ (v9_lattices @ X2)
% 0.69/0.86          | ~ (v8_lattices @ X2)
% 0.69/0.86          | ~ (v6_lattices @ X2)
% 0.69/0.86          | (v2_struct_0 @ X2)
% 0.69/0.86          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.69/0.86          | (r3_lattices @ X2 @ X1 @ X3)
% 0.69/0.86          | ~ (r1_lattices @ X2 @ X1 @ X3))),
% 0.69/0.86      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.69/0.86  thf('92', plain,
% 0.69/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.86         ((v2_struct_0 @ X0)
% 0.69/0.86          | ~ (l3_lattices @ X0)
% 0.69/0.86          | ~ (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.69/0.86          | (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.69/0.86          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.69/0.86          | (v2_struct_0 @ X0)
% 0.69/0.86          | ~ (v6_lattices @ X0)
% 0.69/0.86          | ~ (v8_lattices @ X0)
% 0.69/0.86          | ~ (v9_lattices @ X0)
% 0.69/0.86          | ~ (l3_lattices @ X0))),
% 0.69/0.86      inference('sup-', [status(thm)], ['90', '91'])).
% 0.69/0.86  thf('93', plain,
% 0.69/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.86         (~ (v9_lattices @ X0)
% 0.69/0.86          | ~ (v8_lattices @ X0)
% 0.69/0.86          | ~ (v6_lattices @ X0)
% 0.69/0.86          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.69/0.86          | (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.69/0.86          | ~ (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.69/0.86          | ~ (l3_lattices @ X0)
% 0.69/0.86          | (v2_struct_0 @ X0))),
% 0.69/0.86      inference('simplify', [status(thm)], ['92'])).
% 0.69/0.86  thf('94', plain,
% 0.69/0.86      (![X0 : $i]:
% 0.69/0.86         ((v2_struct_0 @ sk_A)
% 0.69/0.86          | ~ (l3_lattices @ sk_A)
% 0.69/0.86          | ~ (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.69/0.86          | (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.69/0.86          | ~ (v6_lattices @ sk_A)
% 0.69/0.86          | ~ (v8_lattices @ sk_A)
% 0.69/0.86          | ~ (v9_lattices @ sk_A))),
% 0.69/0.86      inference('sup-', [status(thm)], ['89', '93'])).
% 0.69/0.86  thf('95', plain, ((l3_lattices @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf(cc1_lattices, axiom,
% 0.69/0.86    (![A:$i]:
% 0.69/0.86     ( ( l3_lattices @ A ) =>
% 0.69/0.86       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.69/0.86         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.69/0.86           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.69/0.86           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.69/0.86  thf('96', plain,
% 0.69/0.86      (![X0 : $i]:
% 0.69/0.86         ((v2_struct_0 @ X0)
% 0.69/0.86          | ~ (v10_lattices @ X0)
% 0.69/0.86          | (v6_lattices @ X0)
% 0.69/0.86          | ~ (l3_lattices @ X0))),
% 0.69/0.86      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.69/0.86  thf('97', plain, (~ (v2_struct_0 @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('98', plain,
% 0.69/0.86      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.69/0.86      inference('sup-', [status(thm)], ['96', '97'])).
% 0.69/0.86  thf('99', plain, ((l3_lattices @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('100', plain, ((v10_lattices @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('101', plain, ((v6_lattices @ sk_A)),
% 0.69/0.86      inference('demod', [status(thm)], ['98', '99', '100'])).
% 0.69/0.86  thf('102', plain,
% 0.69/0.86      (![X0 : $i]:
% 0.69/0.86         ((v2_struct_0 @ X0)
% 0.69/0.86          | ~ (v10_lattices @ X0)
% 0.69/0.86          | (v8_lattices @ X0)
% 0.69/0.86          | ~ (l3_lattices @ X0))),
% 0.69/0.86      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.69/0.86  thf('103', plain, (~ (v2_struct_0 @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('104', plain,
% 0.69/0.86      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.69/0.86      inference('sup-', [status(thm)], ['102', '103'])).
% 0.69/0.86  thf('105', plain, ((l3_lattices @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('106', plain, ((v10_lattices @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('107', plain, ((v8_lattices @ sk_A)),
% 0.69/0.86      inference('demod', [status(thm)], ['104', '105', '106'])).
% 0.69/0.86  thf('108', plain,
% 0.69/0.86      (![X0 : $i]:
% 0.69/0.86         ((v2_struct_0 @ X0)
% 0.69/0.86          | ~ (v10_lattices @ X0)
% 0.69/0.86          | (v9_lattices @ X0)
% 0.69/0.86          | ~ (l3_lattices @ X0))),
% 0.69/0.86      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.69/0.86  thf('109', plain, (~ (v2_struct_0 @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('110', plain,
% 0.69/0.86      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.69/0.86      inference('sup-', [status(thm)], ['108', '109'])).
% 0.69/0.86  thf('111', plain, ((l3_lattices @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('112', plain, ((v10_lattices @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('113', plain, ((v9_lattices @ sk_A)),
% 0.69/0.86      inference('demod', [status(thm)], ['110', '111', '112'])).
% 0.69/0.86  thf('114', plain,
% 0.69/0.86      (![X0 : $i]:
% 0.69/0.86         ((v2_struct_0 @ sk_A)
% 0.69/0.86          | ~ (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.69/0.86          | (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B))),
% 0.69/0.86      inference('demod', [status(thm)], ['94', '95', '101', '107', '113'])).
% 0.69/0.86  thf('115', plain, (~ (v2_struct_0 @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('116', plain,
% 0.69/0.86      (![X0 : $i]:
% 0.69/0.86         ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.69/0.86          | ~ (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B))),
% 0.69/0.86      inference('clc', [status(thm)], ['114', '115'])).
% 0.69/0.86  thf('117', plain,
% 0.69/0.86      ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C) @ sk_B)),
% 0.69/0.86      inference('sup-', [status(thm)], ['88', '116'])).
% 0.69/0.86  thf('118', plain,
% 0.69/0.86      ((~ (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C) @ sk_B))
% 0.69/0.86         <= (~ ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C) @ sk_B)))),
% 0.69/0.86      inference('split', [status(esa)], ['66'])).
% 0.69/0.86  thf('119', plain,
% 0.69/0.86      (((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C) @ sk_B))),
% 0.69/0.86      inference('sup-', [status(thm)], ['117', '118'])).
% 0.69/0.86  thf('120', plain,
% 0.69/0.86      (~ ((r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C))) | 
% 0.69/0.86       ~ ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C) @ sk_B))),
% 0.69/0.86      inference('split', [status(esa)], ['66'])).
% 0.69/0.86  thf('121', plain,
% 0.69/0.86      (~ ((r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C)))),
% 0.69/0.86      inference('sat_resolution*', [status(thm)], ['119', '120'])).
% 0.69/0.86  thf('122', plain,
% 0.69/0.86      (~ (r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ sk_C))),
% 0.69/0.86      inference('simpl_trail', [status(thm)], ['67', '121'])).
% 0.69/0.86  thf('123', plain, ((v2_struct_0 @ sk_A)),
% 0.69/0.86      inference('clc', [status(thm)], ['65', '122'])).
% 0.69/0.86  thf('124', plain, ($false), inference('demod', [status(thm)], ['0', '123'])).
% 0.69/0.86  
% 0.69/0.86  % SZS output end Refutation
% 0.69/0.86  
% 0.69/0.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
