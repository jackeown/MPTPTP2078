%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1514+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UddKAcJGCH

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:43 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  197 ( 422 expanded)
%              Number of leaves         :   32 ( 131 expanded)
%              Depth                    :   37
%              Number of atoms          : 2792 (8410 expanded)
%              Number of equality atoms :    3 (   4 expanded)
%              Maximal formula depth    :   22 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r4_lattice3_type,type,(
    r4_lattice3: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

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

thf(dt_k15_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X10 @ X11 ) @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X10 @ X11 ) @ ( u1_struct_0 @ X10 ) ) ) ),
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

thf('3',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X2 ) @ X5 )
      | ( r4_lattice3 @ X2 @ X1 @ X5 )
      | ~ ( l3_lattices @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X10 @ X11 ) @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('7',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ( m1_subset_1 @ ( sk_D @ X5 @ X1 @ X2 ) @ ( u1_struct_0 @ X2 ) )
      | ( r4_lattice3 @ X2 @ X1 @ X5 )
      | ~ ( l3_lattices @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( m1_subset_1 @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X23: $i] :
      ( ( r2_hidden @ ( sk_E @ X23 ) @ sk_C )
      | ~ ( r2_hidden @ X23 @ sk_B )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_E @ ( sk_D @ X1 @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_E @ ( sk_D @ X1 @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( r2_hidden @ ( sk_E @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ sk_C )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','13'])).

thf('15',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( r2_hidden @ ( sk_E @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ sk_C )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_E @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ sk_C )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( r2_hidden @ ( sk_E @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('22',plain,(
    ! [X23: $i] :
      ( ( m1_subset_1 @ ( sk_E @ X23 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X23 @ sk_B )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D @ X1 @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D @ X1 @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X10 @ X11 ) @ ( u1_struct_0 @ X10 ) ) ) ),
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

thf('33',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( v10_lattices @ X6 )
      | ~ ( v4_lattice3 @ X6 )
      | ~ ( l3_lattices @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ( X7
       != ( k15_lattice3 @ X6 @ X8 ) )
      | ( r4_lattice3 @ X6 @ X7 @ X8 )
      | ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('34',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r4_lattice3 @ X6 @ ( k15_lattice3 @ X6 @ X8 ) @ X8 )
      | ~ ( m1_subset_1 @ ( k15_lattice3 @ X6 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( l3_lattices @ X6 )
      | ~ ( v4_lattice3 @ X6 )
      | ~ ( v10_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X1 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X10 @ X11 ) @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('38',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( r4_lattice3 @ X2 @ X1 @ X3 )
      | ~ ( r2_hidden @ X4 @ X3 )
      | ( r1_lattices @ X2 @ X4 @ X1 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l3_lattices @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X3 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ( r1_lattices @ X0 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
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
    inference('sup-',[status(thm)],['36','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r1_lattices @ X1 @ X2 @ ( k15_lattice3 @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ( r1_lattices @ sk_A @ ( sk_E @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ ( k15_lattice3 @ sk_A @ X1 ) )
      | ~ ( r2_hidden @ ( sk_E @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','42'])).

thf('44',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_lattices @ sk_A @ ( sk_E @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ ( k15_lattice3 @ sk_A @ X1 ) )
      | ~ ( r2_hidden @ ( sk_E @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['43','44','45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( r1_lattices @ sk_A @ ( sk_E @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ ( k15_lattice3 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_lattices @ sk_A @ ( sk_E @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ ( k15_lattice3 @ sk_A @ sk_C ) )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( r1_lattices @ sk_A @ ( sk_E @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ ( k15_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('56',plain,(
    ! [X23: $i] :
      ( ( r3_lattices @ sk_A @ X23 @ ( sk_E @ X23 ) )
      | ~ ( r2_hidden @ X23 @ sk_B )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ sk_B )
      | ( r3_lattices @ sk_A @ ( sk_D @ X1 @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( sk_E @ ( sk_D @ X1 @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ sk_B )
      | ( r3_lattices @ sk_A @ ( sk_D @ X1 @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( sk_E @ ( sk_D @ X1 @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( r3_lattices @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( sk_E @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','59'])).

thf('61',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( r3_lattices @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( sk_E @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( sk_E @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( r3_lattices @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( sk_E @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

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

thf('67',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l3_lattices @ X14 )
      | ~ ( v9_lattices @ X14 )
      | ~ ( v8_lattices @ X14 )
      | ~ ( v6_lattices @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( r1_lattices @ X14 @ X13 @ X15 )
      | ~ ( r3_lattices @ X14 @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r3_lattices @ X0 @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X3 )
      | ( r1_lattices @ X0 @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X3 )
      | ~ ( r3_lattices @ X0 @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X3 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( r1_lattices @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( sk_E @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','69'])).

thf('71',plain,(
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

thf('72',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( r1_lattices @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( sk_E @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['70','71','77','83','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( sk_E @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_lattices @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( sk_E @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['53','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( r1_lattices @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( sk_E @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( r1_lattices @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( sk_E @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t25_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_lattices @ A )
        & ( l2_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( ( r1_lattices @ A @ B @ C )
                      & ( r1_lattices @ A @ C @ D ) )
                   => ( r1_lattices @ A @ B @ D ) ) ) ) ) ) )).

thf('97',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ( r1_lattices @ X17 @ X16 @ X18 )
      | ~ ( r1_lattices @ X17 @ X19 @ X18 )
      | ~ ( r1_lattices @ X17 @ X16 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l2_lattices @ X17 )
      | ~ ( v5_lattices @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t25_lattices])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v5_lattices @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_lattices @ X0 @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X3 )
      | ~ ( r1_lattices @ X0 @ X3 @ X4 )
      | ( r1_lattices @ X0 @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X4 )
      | ~ ( r1_lattices @ X0 @ X3 @ X4 )
      | ~ ( r1_lattices @ X0 @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l2_lattices @ X0 )
      | ~ ( v5_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ~ ( v5_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_lattices @ sk_A @ ( sk_E @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ X1 )
      | ( r1_lattices @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['95','99'])).

thf('101',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v5_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v5_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v5_lattices @ sk_A ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('109',plain,(
    ! [X12: $i] :
      ( ( l2_lattices @ X12 )
      | ~ ( l3_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('110',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_lattices @ sk_A @ ( sk_E @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ X1 )
      | ( r1_lattices @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['100','101','107','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ X1 )
      | ~ ( r1_lattices @ sk_A @ ( sk_E @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ X1 )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r1_lattices @ sk_A @ ( sk_E @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ X1 )
      | ( r1_lattices @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['52','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ X1 )
      | ~ ( r1_lattices @ sk_A @ ( sk_E @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) ) @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_lattices @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ ( k15_lattice3 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k15_lattice3 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_lattices @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['1','116'])).

thf('118',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_lattices @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( r1_lattices @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_C ) )
      | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( r1_lattices @ sk_A @ ( sk_D @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_A ) @ ( k15_lattice3 @ sk_A @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X10 @ X11 ) @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('124',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( r1_lattices @ X2 @ ( sk_D @ X5 @ X1 @ X2 ) @ X1 )
      | ( r4_lattice3 @ X2 @ X1 @ X5 )
      | ~ ( l3_lattices @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('125',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_lattices @ X0 @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattices @ X0 @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,
    ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ sk_C ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['122','126'])).

thf('128',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ sk_C ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    r4_lattice3 @ sk_A @ ( k15_lattice3 @ sk_A @ sk_C ) @ sk_B ),
    inference(clc,[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X10 @ X11 ) @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('134',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X10 @ X11 ) @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('135',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( v10_lattices @ X6 )
      | ~ ( v4_lattice3 @ X6 )
      | ~ ( l3_lattices @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ( X7
       != ( k15_lattice3 @ X6 @ X8 ) )
      | ~ ( r4_lattice3 @ X6 @ X9 @ X8 )
      | ( r1_lattices @ X6 @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('136',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X6 ) )
      | ( r1_lattices @ X6 @ ( k15_lattice3 @ X6 @ X8 ) @ X9 )
      | ~ ( r4_lattice3 @ X6 @ X9 @ X8 )
      | ~ ( m1_subset_1 @ ( k15_lattice3 @ X6 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( l3_lattices @ X6 )
      | ~ ( v4_lattice3 @ X6 )
      | ~ ( v10_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,(
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
    inference('sup-',[status(thm)],['134','136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r4_lattice3 @ X0 @ X2 @ X1 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['133','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ( r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['132','140'])).

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
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['141','142','143','144'])).

thf('146',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X10 @ X11 ) @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('149',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X10 @ X11 ) @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('150',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l3_lattices @ X14 )
      | ~ ( v9_lattices @ X14 )
      | ~ ( v8_lattices @ X14 )
      | ~ ( v6_lattices @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( r3_lattices @ X14 @ X13 @ X15 )
      | ~ ( r1_lattices @ X14 @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('151',plain,(
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
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,(
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
    inference('sup-',[status(thm)],['148','152'])).

thf('154',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_C ) )
    | ~ ( v6_lattices @ sk_A )
    | ~ ( v8_lattices @ sk_A )
    | ~ ( v9_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['147','154'])).

thf('156',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('158',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('159',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('160',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['155','156','157','158','159'])).

thf('161',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    r3_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_B ) @ ( k15_lattice3 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['160','161'])).

thf('163',plain,(
    $false ),
    inference(demod,[status(thm)],['0','162'])).


%------------------------------------------------------------------------------
