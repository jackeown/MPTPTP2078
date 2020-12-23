%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.u5c5S48qUj

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:27 EST 2020

% Result     : Theorem 29.93s
% Output     : Refutation 30.00s
% Verified   : 
% Statistics : Number of formulae       :  317 ( 797 expanded)
%              Number of leaves         :   38 ( 243 expanded)
%              Depth                    :   37
%              Number of atoms          : 4444 (14416 expanded)
%              Number of equality atoms :   17 (  30 expanded)
%              Maximal formula depth    :   24 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(k3_lattices_type,type,(
    k3_lattices: $i > $i > $i > $i )).

thf(a_3_4_lattice3_type,type,(
    a_3_4_lattice3: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(r3_lattice3_type,type,(
    r3_lattice3: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t35_lattice3,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v4_lattice3 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( r3_lattices @ A @ ( k3_lattices @ A @ B @ ( k16_lattice3 @ A @ C ) ) @ ( k16_lattice3 @ A @ ( a_3_4_lattice3 @ A @ B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v4_lattice3 @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( r3_lattices @ A @ ( k3_lattices @ A @ B @ ( k16_lattice3 @ A @ C ) ) @ ( k16_lattice3 @ A @ ( a_3_4_lattice3 @ A @ B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_lattice3])).

thf('0',plain,(
    ~ ( r3_lattices @ sk_A @ ( k3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ sk_C ) ) @ ( k16_lattice3 @ sk_A @ ( a_3_4_lattice3 @ sk_A @ sk_B @ sk_C ) ) ) ),
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

thf('2',plain,(
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

thf('3',plain,(
    ! [X19: $i,X20: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ( r2_hidden @ ( sk_D @ X23 @ X19 @ X20 ) @ X23 )
      | ( r3_lattice3 @ X20 @ X19 @ X23 )
      | ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fraenkel_a_3_4_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( v10_lattices @ B )
        & ( v4_lattice3 @ B )
        & ( l3_lattices @ B )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) )
     => ( ( r2_hidden @ A @ ( a_3_4_lattice3 @ B @ C @ D ) )
      <=> ? [E: $i] :
            ( ( r2_hidden @ E @ D )
            & ( A
              = ( k3_lattices @ B @ C @ E ) )
            & ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('7',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ~ ( l3_lattices @ X27 )
      | ~ ( v4_lattice3 @ X27 )
      | ~ ( v10_lattices @ X27 )
      | ( v2_struct_0 @ X27 )
      | ( X28
        = ( k3_lattices @ X27 @ X26 @ ( sk_E @ X29 @ X26 @ X27 @ X28 ) ) )
      | ~ ( r2_hidden @ X28 @ ( a_3_4_lattice3 @ X27 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_3_4_lattice3])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( X1
        = ( k3_lattices @ sk_A @ sk_B @ ( sk_E @ X0 @ sk_B @ sk_A @ X1 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( X1
        = ( k3_lattices @ sk_A @ sk_B @ ( sk_E @ X0 @ sk_B @ sk_A @ X1 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9','10','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k3_lattices @ sk_A @ sk_B @ ( sk_E @ X0 @ sk_B @ sk_A @ X1 ) ) )
      | ~ ( r2_hidden @ X1 @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( r3_lattice3 @ X1 @ ( k16_lattice3 @ X1 @ X2 ) @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) @ ( k16_lattice3 @ X1 @ X2 ) @ X1 )
        = ( k3_lattices @ sk_A @ sk_B @ ( sk_E @ X0 @ sk_B @ sk_A @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) @ ( k16_lattice3 @ X1 @ X2 ) @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('18',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ~ ( l3_lattices @ X27 )
      | ~ ( v4_lattice3 @ X27 )
      | ~ ( v10_lattices @ X27 )
      | ( v2_struct_0 @ X27 )
      | ( m1_subset_1 @ ( sk_E @ X29 @ X26 @ X27 @ X28 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( r2_hidden @ X28 @ ( a_3_4_lattice3 @ X27 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_3_4_lattice3])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( l3_lattices @ X3 )
      | ( r3_lattice3 @ X3 @ ( k16_lattice3 @ X3 @ X4 ) @ ( a_3_4_lattice3 @ X2 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( sk_E @ X0 @ X1 @ X2 @ ( sk_D @ ( a_3_4_lattice3 @ X2 @ X1 @ X0 ) @ ( k16_lattice3 @ X3 @ X4 ) @ X3 ) ) @ ( u1_struct_0 @ X2 ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( v10_lattices @ X2 )
      | ~ ( v4_lattice3 @ X2 )
      | ~ ( l3_lattices @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l3_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ X2 @ sk_B @ sk_A @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ X2 @ sk_B @ sk_A @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21','22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ~ ( l3_lattices @ X27 )
      | ~ ( v4_lattice3 @ X27 )
      | ~ ( v10_lattices @ X27 )
      | ( v2_struct_0 @ X27 )
      | ( r2_hidden @ ( sk_E @ X29 @ X26 @ X27 @ X28 ) @ X29 )
      | ~ ( r2_hidden @ X28 @ ( a_3_4_lattice3 @ X27 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_3_4_lattice3])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_B @ sk_A @ X1 ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_B @ sk_A @ X1 ) @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ sk_B @ sk_A @ X1 ) @ X0 )
      | ~ ( r2_hidden @ X1 @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( r3_lattice3 @ X1 @ ( k16_lattice3 @ X1 @ X2 ) @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_B @ sk_A @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) @ ( k16_lattice3 @ X1 @ X2 ) @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ X2 @ sk_B @ sk_A @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21','22','23'])).

thf('37',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l3_lattices @ X24 )
      | ( v2_struct_0 @ X24 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ),
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

thf('38',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ( X31
       != ( k16_lattice3 @ X32 @ X33 ) )
      | ( r3_lattice3 @ X32 @ X31 @ X33 )
      | ~ ( l3_lattices @ X32 )
      | ~ ( v4_lattice3 @ X32 )
      | ~ ( v10_lattices @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('39',plain,(
    ! [X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X32 )
      | ~ ( v10_lattices @ X32 )
      | ~ ( v4_lattice3 @ X32 )
      | ~ ( l3_lattices @ X32 )
      | ( r3_lattice3 @ X32 @ ( k16_lattice3 @ X32 @ X33 ) @ X33 )
      | ~ ( m1_subset_1 @ ( k16_lattice3 @ X32 @ X33 ) @ ( u1_struct_0 @ X32 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l3_lattices @ X24 )
      | ( v2_struct_0 @ X24 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf('43',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( r3_lattice3 @ X20 @ X19 @ X21 )
      | ~ ( r2_hidden @ X22 @ X21 )
      | ( r1_lattices @ X20 @ X19 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X3 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
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
    inference('sup-',[status(thm)],['41','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r1_lattices @ X1 @ ( k16_lattice3 @ X1 @ X0 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X3 ) @ ( sk_E @ X2 @ sk_B @ sk_A @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_E @ X2 @ sk_B @ sk_A @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['36','47'])).

thf('49',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X3 ) @ ( sk_E @ X2 @ sk_B @ sk_A @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_E @ X2 @ sk_B @ sk_A @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) ) @ X3 ) ) ),
    inference(demod,[status(thm)],['48','49','50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( sk_E @ X2 @ sk_B @ sk_A @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) ) @ X3 )
      | ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X3 ) @ ( sk_E @ X2 @ sk_B @ sk_A @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r3_lattice3 @ X1 @ ( k16_lattice3 @ X1 @ X2 ) @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( r3_lattice3 @ X1 @ ( k16_lattice3 @ X1 @ X2 ) @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ ( sk_E @ X0 @ sk_B @ sk_A @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) @ ( k16_lattice3 @ X1 @ X2 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['35','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ ( sk_E @ X0 @ sk_B @ sk_A @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) @ ( k16_lattice3 @ X1 @ X2 ) @ X1 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( r3_lattice3 @ X1 @ ( k16_lattice3 @ X1 @ X2 ) @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ X2 @ sk_B @ sk_A @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21','22','23'])).

thf('57',plain,(
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

thf('58',plain,(
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

thf('59',plain,(
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
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X3 ) @ ( sk_E @ X2 @ sk_B @ sk_A @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) ) )
      | ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X3 ) @ ( sk_E @ X2 @ sk_B @ sk_A @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) ) )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','60'])).

thf('62',plain,(
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

thf('63',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X3 ) @ ( sk_E @ X2 @ sk_B @ sk_A @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) ) )
      | ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X3 ) @ ( sk_E @ X2 @ sk_B @ sk_A @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['61','62','68','74','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X3 ) @ ( sk_E @ X2 @ sk_B @ sk_A @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) ) )
      | ~ ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X3 ) @ ( sk_E @ X2 @ sk_B @ sk_A @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X2 ) @ ( sk_E @ X2 @ sk_B @ sk_A @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['55','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X2 ) @ ( sk_E @ X2 @ sk_B @ sk_A @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l3_lattices @ X24 )
      | ( v2_struct_0 @ X24 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf(t3_filter_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( r3_lattices @ A @ B @ C )
                   => ( r3_lattices @ A @ B @ ( k3_lattices @ A @ D @ C ) ) ) ) ) ) ) )).

thf('87',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( r3_lattices @ X12 @ X11 @ ( k3_lattices @ X12 @ X13 @ X14 ) )
      | ~ ( r3_lattices @ X12 @ X11 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l3_lattices @ X12 )
      | ~ ( v10_lattices @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_filter_0])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( k3_lattices @ X0 @ X3 @ X2 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X0 ) )
      | ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( k3_lattices @ X0 @ X3 @ X2 ) )
      | ~ ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X1 ) @ X0 )
      | ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X1 ) @ ( k3_lattices @ sk_A @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['85','89'])).

thf('91',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X1 ) @ X0 )
      | ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X1 ) @ ( k3_lattices @ sk_A @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X2 ) @ ( k3_lattices @ sk_A @ sk_B @ ( sk_E @ X2 @ sk_B @ sk_A @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) ) ) )
      | ~ ( m1_subset_1 @ ( sk_E @ X2 @ sk_B @ sk_A @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( sk_E @ X2 @ sk_B @ sk_A @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X2 ) @ ( k3_lattices @ sk_A @ sk_B @ ( sk_E @ X2 @ sk_B @ sk_A @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X2 ) @ ( k3_lattices @ sk_A @ sk_B @ ( sk_E @ X2 @ sk_B @ sk_A @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['24','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X2 ) @ ( k3_lattices @ sk_A @ sk_B @ ( sk_E @ X2 @ sk_B @ sk_A @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X2 ) @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['15','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) )
      | ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X2 ) @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X2 ) @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l3_lattices @ X24 )
      | ( v2_struct_0 @ X24 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf('101',plain,(
    ! [X19: $i,X20: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ( m1_subset_1 @ ( sk_D @ X23 @ X19 @ X20 ) @ ( u1_struct_0 @ X20 ) )
      | ( r3_lattice3 @ X20 @ X19 @ X23 )
      | ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ( m1_subset_1 @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l3_lattices @ X24 )
      | ( v2_struct_0 @ X24 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf('105',plain,(
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

thf('106',plain,(
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
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
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
    inference('sup-',[status(thm)],['103','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X3 ) @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ~ ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X3 ) @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X1 ) )
      | ~ ( l3_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r3_lattice3 @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X1 ) )
      | ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X1 ) @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X1 ) @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_A ) )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['99','109'])).

thf('111',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('114',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('115',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X1 ) )
      | ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X1 ) @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X1 ) @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['110','111','112','113','114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X1 ) @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X1 ) @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattice3 @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X1 ) )
      | ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X1 ) @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X1 ) @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l3_lattices @ X24 )
      | ( v2_struct_0 @ X24 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf('121',plain,(
    ! [X19: $i,X20: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( r1_lattices @ X20 @ X19 @ ( sk_D @ X23 @ X19 @ X20 ) )
      | ( r3_lattice3 @ X20 @ X19 @ X23 )
      | ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( sk_D @ X2 @ ( k16_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( r3_lattice3 @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r3_lattice3 @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['119','123'])).

thf('125',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( r3_lattice3 @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X0: $i] :
      ( r3_lattice3 @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l3_lattices @ X24 )
      | ( v2_struct_0 @ X24 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf('131',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l3_lattices @ X24 )
      | ( v2_struct_0 @ X24 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf('132',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ( X31
       != ( k16_lattice3 @ X32 @ X33 ) )
      | ~ ( r3_lattice3 @ X32 @ X34 @ X33 )
      | ( r3_lattices @ X32 @ X34 @ X31 )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X32 ) )
      | ~ ( l3_lattices @ X32 )
      | ~ ( v4_lattice3 @ X32 )
      | ~ ( v10_lattices @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('133',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X32 )
      | ~ ( v10_lattices @ X32 )
      | ~ ( v4_lattice3 @ X32 )
      | ~ ( l3_lattices @ X32 )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X32 ) )
      | ( r3_lattices @ X32 @ X34 @ ( k16_lattice3 @ X32 @ X33 ) )
      | ~ ( r3_lattice3 @ X32 @ X34 @ X33 )
      | ~ ( m1_subset_1 @ ( k16_lattice3 @ X32 @ X33 ) @ ( u1_struct_0 @ X32 ) ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
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
    inference('sup-',[status(thm)],['131','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r3_lattices @ X0 @ X2 @ ( k16_lattice3 @ X0 @ X1 ) )
      | ~ ( r3_lattice3 @ X0 @ X2 @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( k16_lattice3 @ X0 @ X2 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['130','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ ( k16_lattice3 @ X0 @ X2 ) )
      | ~ ( r3_lattice3 @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ ( k16_lattice3 @ sk_A @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) ) )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( v10_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['129','137'])).

thf('139',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ ( k16_lattice3 @ sk_A @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['138','139','140','141'])).

thf('143',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X0: $i] :
      ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ ( k16_lattice3 @ sk_A @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) ) ) ),
    inference(clc,[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l3_lattices @ X24 )
      | ( v2_struct_0 @ X24 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf('146',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_filter_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v4_lattices @ A )
        & ( v5_lattices @ A )
        & ( v6_lattices @ A )
        & ( v8_lattices @ A )
        & ( v9_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( ( r3_lattices @ A @ B @ D )
                      & ( r3_lattices @ A @ C @ D ) )
                   => ( r3_lattices @ A @ ( k3_lattices @ A @ B @ C ) @ D ) ) ) ) ) ) )).

thf('147',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ( r3_lattices @ X16 @ ( k3_lattices @ X16 @ X15 @ X18 ) @ X17 )
      | ~ ( r3_lattices @ X16 @ X18 @ X17 )
      | ~ ( r3_lattices @ X16 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l3_lattices @ X16 )
      | ~ ( v9_lattices @ X16 )
      | ~ ( v8_lattices @ X16 )
      | ~ ( v6_lattices @ X16 )
      | ~ ( v5_lattices @ X16 )
      | ~ ( v4_lattices @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t6_filter_0])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( v5_lattices @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_lattices @ sk_A @ sk_B @ X1 )
      | ~ ( r3_lattices @ sk_A @ X0 @ X1 )
      | ( r3_lattices @ sk_A @ ( k3_lattices @ sk_A @ sk_B @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v4_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('150',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v4_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['151','152','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v5_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('156',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v5_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v5_lattices @ sk_A ),
    inference(demod,[status(thm)],['157','158','159'])).

thf('161',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('162',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('163',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('164',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_lattices @ sk_A @ sk_B @ X1 )
      | ~ ( r3_lattices @ sk_A @ X0 @ X1 )
      | ( r3_lattices @ sk_A @ ( k3_lattices @ sk_A @ sk_B @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['148','154','160','161','162','163','164'])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_lattices @ sk_A @ ( k3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) ) @ X1 )
      | ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ X1 )
      | ~ ( r3_lattices @ sk_A @ sk_B @ X1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['145','165'])).

thf('167',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_lattices @ sk_A @ ( k3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) ) @ X1 )
      | ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ X1 )
      | ~ ( r3_lattices @ sk_A @ sk_B @ X1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r3_lattices @ sk_A @ sk_B @ X1 )
      | ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ X1 )
      | ( r3_lattices @ sk_A @ ( k3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ ( k16_lattice3 @ sk_A @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_lattices @ sk_A @ ( k3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) ) @ ( k16_lattice3 @ sk_A @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) ) )
      | ~ ( r3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['144','169'])).

thf('171',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    ! [X19: $i,X20: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ( m1_subset_1 @ ( sk_D @ X23 @ X19 @ X20 ) @ ( u1_struct_0 @ X20 ) )
      | ( r3_lattice3 @ X20 @ X19 @ X23 )
      | ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('176',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['175','176'])).

thf('178',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    ! [X19: $i,X20: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ( r2_hidden @ ( sk_D @ X23 @ X19 @ X20 ) @ X23 )
      | ( r3_lattice3 @ X20 @ X19 @ X23 )
      | ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('183',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k3_lattices @ sk_A @ sk_B @ ( sk_E @ X0 @ sk_B @ sk_A @ X1 ) ) )
      | ~ ( r2_hidden @ X1 @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( r3_lattice3 @ sk_A @ sk_B @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) @ sk_B @ sk_A )
        = ( k3_lattices @ sk_A @ sk_B @ ( sk_E @ X0 @ sk_B @ sk_A @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) @ sk_B @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['182','183'])).

thf('189',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ~ ( l3_lattices @ X27 )
      | ~ ( v4_lattice3 @ X27 )
      | ~ ( v10_lattices @ X27 )
      | ( v2_struct_0 @ X27 )
      | ( m1_subset_1 @ ( sk_E @ X29 @ X26 @ X27 @ X28 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( r2_hidden @ X28 @ ( a_3_4_lattice3 @ X27 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_3_4_lattice3])).

thf('190',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r3_lattice3 @ sk_A @ sk_B @ ( a_3_4_lattice3 @ X2 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( sk_E @ X0 @ X1 @ X2 @ ( sk_D @ ( a_3_4_lattice3 @ X2 @ X1 @ X0 ) @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ X2 ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( v10_lattices @ X2 )
      | ~ ( v4_lattice3 @ X2 )
      | ~ ( l3_lattices @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ X0 @ sk_B @ sk_A @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_lattice3 @ sk_A @ sk_B @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['187','190'])).

thf('192',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ X0 @ sk_B @ sk_A @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_lattice3 @ sk_A @ sk_B @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['191','192','193','194'])).

thf('196',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    ! [X0: $i] :
      ( ( r3_lattice3 @ sk_A @ sk_B @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( m1_subset_1 @ ( sk_E @ X0 @ sk_B @ sk_A @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['195','196'])).

thf('198',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v4_lattices @ A )
        & ( l2_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k3_lattices @ A @ B @ C )
        = ( k3_lattices @ A @ C @ B ) ) ) )).

thf('199',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l2_lattices @ X2 )
      | ~ ( v4_lattices @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( ( k3_lattices @ X2 @ X1 @ X3 )
        = ( k3_lattices @ X2 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_lattices])).

thf('200',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['151','152','153'])).

thf('202',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('203',plain,(
    ! [X4: $i] :
      ( ( l2_lattices @ X4 )
      | ~ ( l3_lattices @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('204',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['200','201','204'])).

thf('206',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_B @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['205','206'])).

thf('208',plain,(
    ! [X0: $i] :
      ( ( r3_lattice3 @ sk_A @ sk_B @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( ( k3_lattices @ sk_A @ sk_B @ ( sk_E @ X0 @ sk_B @ sk_A @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) @ sk_B @ sk_A ) ) )
        = ( k3_lattices @ sk_A @ ( sk_E @ X0 @ sk_B @ sk_A @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) @ sk_B @ sk_A ) ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['197','207'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ( r3_lattice3 @ sk_A @ sk_B @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( m1_subset_1 @ ( sk_E @ X0 @ sk_B @ sk_A @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['195','196'])).

thf('210',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( r3_lattices @ X12 @ X11 @ ( k3_lattices @ X12 @ X13 @ X14 ) )
      | ~ ( r3_lattices @ X12 @ X11 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l3_lattices @ X12 )
      | ~ ( v10_lattices @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_filter_0])).

thf('213',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_lattices @ sk_A @ sk_B @ X0 )
      | ( r3_lattices @ sk_A @ sk_B @ ( k3_lattices @ sk_A @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_lattices @ sk_A @ sk_B @ X0 )
      | ( r3_lattices @ sk_A @ sk_B @ ( k3_lattices @ sk_A @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['213','214','215'])).

thf('217',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_lattices @ sk_A @ sk_B @ ( k3_lattices @ sk_A @ X0 @ sk_B ) )
      | ~ ( r3_lattices @ sk_A @ sk_B @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['210','216'])).

thf('218',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r3_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v6_lattices @ A )
        & ( v8_lattices @ A )
        & ( v9_lattices @ A )
        & ( l3_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( r3_lattices @ A @ B @ B ) ) )).

thf('220',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r3_lattices @ X8 @ X9 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l3_lattices @ X8 )
      | ~ ( v9_lattices @ X8 )
      | ~ ( v8_lattices @ X8 )
      | ~ ( v6_lattices @ X8 )
      | ( v2_struct_0 @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r3_lattices])).

thf('221',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r3_lattices @ sk_A @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['219','220'])).

thf('222',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('223',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('224',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('225',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r3_lattices @ sk_A @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['221','222','223','224','225'])).

thf('227',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_A @ sk_B @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['226','227'])).

thf('229',plain,(
    r3_lattices @ sk_A @ sk_B @ sk_B ),
    inference('sup-',[status(thm)],['218','228'])).

thf('230',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_lattices @ sk_A @ sk_B @ ( k3_lattices @ sk_A @ X0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['217','229'])).

thf('231',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_A @ sk_B @ ( k3_lattices @ sk_A @ X0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['230','231'])).

thf('233',plain,(
    ! [X0: $i] :
      ( ( r3_lattice3 @ sk_A @ sk_B @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( r3_lattices @ sk_A @ sk_B @ ( k3_lattices @ sk_A @ ( sk_E @ X0 @ sk_B @ sk_A @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) @ sk_B @ sk_A ) ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['209','232'])).

thf('234',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_A @ sk_B @ ( k3_lattices @ sk_A @ sk_B @ ( sk_E @ X0 @ sk_B @ sk_A @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) @ sk_B @ sk_A ) ) ) )
      | ( r3_lattice3 @ sk_A @ sk_B @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( r3_lattice3 @ sk_A @ sk_B @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['208','233'])).

thf('235',plain,(
    ! [X0: $i] :
      ( ( r3_lattice3 @ sk_A @ sk_B @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( r3_lattices @ sk_A @ sk_B @ ( k3_lattices @ sk_A @ sk_B @ ( sk_E @ X0 @ sk_B @ sk_A @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) @ sk_B @ sk_A ) ) ) ) ) ),
    inference(simplify,[status(thm)],['234'])).

thf('236',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_A @ sk_B @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) @ sk_B @ sk_A ) )
      | ( r3_lattice3 @ sk_A @ sk_B @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( r3_lattice3 @ sk_A @ sk_B @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['186','235'])).

thf('237',plain,(
    ! [X0: $i] :
      ( ( r3_lattice3 @ sk_A @ sk_B @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( r3_lattices @ sk_A @ sk_B @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['236'])).

thf('238',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,(
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

thf('240',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattices @ sk_A @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['238','239'])).

thf('241',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('242',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('243',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('244',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattices @ sk_A @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['240','241','242','243','244'])).

thf('246',plain,(
    ! [X0: $i] :
      ( ( r3_lattice3 @ sk_A @ sk_B @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ sk_B @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['237','245'])).

thf('247',plain,(
    ! [X0: $i] :
      ( ( r3_lattice3 @ sk_A @ sk_B @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( r1_lattices @ sk_A @ sk_B @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ sk_B @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['177','246'])).

thf('248',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_lattices @ sk_A @ sk_B @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) @ sk_B @ sk_A ) )
      | ( r3_lattice3 @ sk_A @ sk_B @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['247'])).

thf('249',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('250',plain,(
    ! [X0: $i] :
      ( ( r3_lattice3 @ sk_A @ sk_B @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( r1_lattices @ sk_A @ sk_B @ ( sk_D @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['248','249'])).

thf('251',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,(
    ! [X19: $i,X20: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( r1_lattices @ X20 @ X19 @ ( sk_D @ X23 @ X19 @ X20 ) )
      | ( r3_lattice3 @ X20 @ X19 @ X23 )
      | ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('253',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_lattices @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['251','252'])).

thf('254',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_lattices @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['253','254'])).

thf('256',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('257',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['255','256'])).

thf('258',plain,(
    ! [X0: $i] :
      ( r3_lattice3 @ sk_A @ sk_B @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['250','257'])).

thf('259',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('260',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r3_lattices @ X0 @ X2 @ ( k16_lattice3 @ X0 @ X1 ) )
      | ~ ( r3_lattice3 @ X0 @ X2 @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('261',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( v10_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['259','260'])).

thf('262',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['261','262','263','264'])).

thf('266',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['265','266'])).

thf('268',plain,(
    ! [X0: $i] :
      ( r3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['258','267'])).

thf('269',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ ( k16_lattice3 @ sk_A @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_lattices @ sk_A @ ( k3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) ) @ ( k16_lattice3 @ sk_A @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['170','268'])).

thf('270',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('271',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_A @ ( k3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) ) @ ( k16_lattice3 @ sk_A @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ ( k16_lattice3 @ sk_A @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['269','270'])).

thf('272',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r3_lattices @ sk_A @ ( k3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) ) @ ( k16_lattice3 @ sk_A @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','271'])).

thf('273',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('274',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r3_lattices @ sk_A @ ( k3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) ) @ ( k16_lattice3 @ sk_A @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['272','273'])).

thf('275',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,(
    ! [X0: $i] :
      ( r3_lattices @ sk_A @ ( k3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) ) @ ( k16_lattice3 @ sk_A @ ( a_3_4_lattice3 @ sk_A @ sk_B @ X0 ) ) ) ),
    inference(clc,[status(thm)],['274','275'])).

thf('277',plain,(
    $false ),
    inference(demod,[status(thm)],['0','276'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.u5c5S48qUj
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:17:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 29.93/30.16  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 29.93/30.16  % Solved by: fo/fo7.sh
% 29.93/30.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 29.93/30.16  % done 9316 iterations in 29.690s
% 29.93/30.16  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 29.93/30.16  % SZS output start Refutation
% 29.93/30.16  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 29.93/30.16  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 29.93/30.16  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 29.93/30.16  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 29.93/30.16  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 29.93/30.16  thf(k3_lattices_type, type, k3_lattices: $i > $i > $i > $i).
% 29.93/30.16  thf(a_3_4_lattice3_type, type, a_3_4_lattice3: $i > $i > $i > $i).
% 29.93/30.16  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 29.93/30.16  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 29.93/30.16  thf(sk_A_type, type, sk_A: $i).
% 29.93/30.16  thf(sk_B_type, type, sk_B: $i).
% 29.93/30.16  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 29.93/30.16  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 29.93/30.16  thf(r3_lattice3_type, type, r3_lattice3: $i > $i > $i > $o).
% 29.93/30.16  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 29.93/30.16  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 29.93/30.16  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 29.93/30.16  thf(sk_C_type, type, sk_C: $i).
% 29.93/30.16  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 29.93/30.16  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 29.93/30.16  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 29.93/30.16  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 29.93/30.16  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 29.93/30.16  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 29.93/30.16  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 29.93/30.16  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 29.93/30.16  thf(t35_lattice3, conjecture,
% 29.93/30.16    (![A:$i]:
% 29.93/30.16     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 29.93/30.16         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 29.93/30.16       ( ![B:$i]:
% 29.93/30.16         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 29.93/30.16           ( ![C:$i]:
% 29.93/30.16             ( r3_lattices @
% 29.93/30.16               A @ ( k3_lattices @ A @ B @ ( k16_lattice3 @ A @ C ) ) @ 
% 29.93/30.16               ( k16_lattice3 @ A @ ( a_3_4_lattice3 @ A @ B @ C ) ) ) ) ) ) ))).
% 29.93/30.16  thf(zf_stmt_0, negated_conjecture,
% 29.93/30.16    (~( ![A:$i]:
% 29.93/30.16        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 29.93/30.16            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 29.93/30.16          ( ![B:$i]:
% 29.93/30.16            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 29.93/30.16              ( ![C:$i]:
% 29.93/30.16                ( r3_lattices @
% 29.93/30.16                  A @ ( k3_lattices @ A @ B @ ( k16_lattice3 @ A @ C ) ) @ 
% 29.93/30.16                  ( k16_lattice3 @ A @ ( a_3_4_lattice3 @ A @ B @ C ) ) ) ) ) ) ) )),
% 29.93/30.16    inference('cnf.neg', [status(esa)], [t35_lattice3])).
% 29.93/30.16  thf('0', plain,
% 29.93/30.16      (~ (r3_lattices @ sk_A @ 
% 29.93/30.16          (k3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ sk_C)) @ 
% 29.93/30.16          (k16_lattice3 @ sk_A @ (a_3_4_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 29.93/30.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.16  thf(dt_k16_lattice3, axiom,
% 29.93/30.16    (![A:$i,B:$i]:
% 29.93/30.16     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 29.93/30.16       ( m1_subset_1 @ ( k16_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 29.93/30.16  thf('1', plain,
% 29.93/30.16      (![X24 : $i, X25 : $i]:
% 29.93/30.16         (~ (l3_lattices @ X24)
% 29.93/30.16          | (v2_struct_0 @ X24)
% 29.93/30.16          | (m1_subset_1 @ (k16_lattice3 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 29.93/30.16      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 29.93/30.16  thf('2', plain,
% 29.93/30.16      (![X24 : $i, X25 : $i]:
% 29.93/30.16         (~ (l3_lattices @ X24)
% 29.93/30.16          | (v2_struct_0 @ X24)
% 29.93/30.16          | (m1_subset_1 @ (k16_lattice3 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 29.93/30.16      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 29.93/30.16  thf(d16_lattice3, axiom,
% 29.93/30.16    (![A:$i]:
% 29.93/30.16     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 29.93/30.16       ( ![B:$i]:
% 29.93/30.16         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 29.93/30.16           ( ![C:$i]:
% 29.93/30.16             ( ( r3_lattice3 @ A @ B @ C ) <=>
% 29.93/30.16               ( ![D:$i]:
% 29.93/30.16                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 29.93/30.16                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 29.93/30.16  thf('3', plain,
% 29.93/30.16      (![X19 : $i, X20 : $i, X23 : $i]:
% 29.93/30.16         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 29.93/30.16          | (r2_hidden @ (sk_D @ X23 @ X19 @ X20) @ X23)
% 29.93/30.16          | (r3_lattice3 @ X20 @ X19 @ X23)
% 29.93/30.16          | ~ (l3_lattices @ X20)
% 29.93/30.16          | (v2_struct_0 @ X20))),
% 29.93/30.16      inference('cnf', [status(esa)], [d16_lattice3])).
% 29.93/30.16  thf('4', plain,
% 29.93/30.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.93/30.16         ((v2_struct_0 @ X0)
% 29.93/30.16          | ~ (l3_lattices @ X0)
% 29.93/30.16          | (v2_struct_0 @ X0)
% 29.93/30.16          | ~ (l3_lattices @ X0)
% 29.93/30.16          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 29.93/30.16          | (r2_hidden @ (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0) @ X2))),
% 29.93/30.16      inference('sup-', [status(thm)], ['2', '3'])).
% 29.93/30.16  thf('5', plain,
% 29.93/30.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.93/30.16         ((r2_hidden @ (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0) @ X2)
% 29.93/30.16          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 29.93/30.16          | ~ (l3_lattices @ X0)
% 29.93/30.16          | (v2_struct_0 @ X0))),
% 29.93/30.16      inference('simplify', [status(thm)], ['4'])).
% 29.93/30.16  thf('6', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 29.93/30.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.16  thf(fraenkel_a_3_4_lattice3, axiom,
% 29.93/30.16    (![A:$i,B:$i,C:$i,D:$i]:
% 29.93/30.16     ( ( ( ~( v2_struct_0 @ B ) ) & ( v10_lattices @ B ) & 
% 29.93/30.16         ( v4_lattice3 @ B ) & ( l3_lattices @ B ) & 
% 29.93/30.16         ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) ) =>
% 29.93/30.16       ( ( r2_hidden @ A @ ( a_3_4_lattice3 @ B @ C @ D ) ) <=>
% 29.93/30.16         ( ?[E:$i]:
% 29.93/30.16           ( ( r2_hidden @ E @ D ) & ( ( A ) = ( k3_lattices @ B @ C @ E ) ) & 
% 29.93/30.16             ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 29.93/30.16  thf('7', plain,
% 29.93/30.16      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 29.93/30.16         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 29.93/30.16          | ~ (l3_lattices @ X27)
% 29.93/30.16          | ~ (v4_lattice3 @ X27)
% 29.93/30.16          | ~ (v10_lattices @ X27)
% 29.93/30.16          | (v2_struct_0 @ X27)
% 29.93/30.16          | ((X28) = (k3_lattices @ X27 @ X26 @ (sk_E @ X29 @ X26 @ X27 @ X28)))
% 29.93/30.16          | ~ (r2_hidden @ X28 @ (a_3_4_lattice3 @ X27 @ X26 @ X29)))),
% 29.93/30.16      inference('cnf', [status(esa)], [fraenkel_a_3_4_lattice3])).
% 29.93/30.16  thf('8', plain,
% 29.93/30.16      (![X0 : $i, X1 : $i]:
% 29.93/30.16         (~ (r2_hidden @ X1 @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0))
% 29.93/30.16          | ((X1)
% 29.93/30.16              = (k3_lattices @ sk_A @ sk_B @ (sk_E @ X0 @ sk_B @ sk_A @ X1)))
% 29.93/30.16          | (v2_struct_0 @ sk_A)
% 29.93/30.16          | ~ (v10_lattices @ sk_A)
% 29.93/30.16          | ~ (v4_lattice3 @ sk_A)
% 29.93/30.16          | ~ (l3_lattices @ sk_A))),
% 29.93/30.16      inference('sup-', [status(thm)], ['6', '7'])).
% 29.93/30.16  thf('9', plain, ((v10_lattices @ sk_A)),
% 29.93/30.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.16  thf('10', plain, ((v4_lattice3 @ sk_A)),
% 29.93/30.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.16  thf('11', plain, ((l3_lattices @ sk_A)),
% 29.93/30.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.16  thf('12', plain,
% 29.93/30.16      (![X0 : $i, X1 : $i]:
% 29.93/30.16         (~ (r2_hidden @ X1 @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0))
% 29.93/30.16          | ((X1)
% 29.93/30.16              = (k3_lattices @ sk_A @ sk_B @ (sk_E @ X0 @ sk_B @ sk_A @ X1)))
% 29.93/30.16          | (v2_struct_0 @ sk_A))),
% 29.93/30.16      inference('demod', [status(thm)], ['8', '9', '10', '11'])).
% 29.93/30.16  thf('13', plain, (~ (v2_struct_0 @ sk_A)),
% 29.93/30.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.16  thf('14', plain,
% 29.93/30.16      (![X0 : $i, X1 : $i]:
% 29.93/30.16         (((X1) = (k3_lattices @ sk_A @ sk_B @ (sk_E @ X0 @ sk_B @ sk_A @ X1)))
% 29.93/30.16          | ~ (r2_hidden @ X1 @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0)))),
% 29.93/30.16      inference('clc', [status(thm)], ['12', '13'])).
% 29.93/30.17  thf('15', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.93/30.17         ((v2_struct_0 @ X1)
% 29.93/30.17          | ~ (l3_lattices @ X1)
% 29.93/30.17          | (r3_lattice3 @ X1 @ (k16_lattice3 @ X1 @ X2) @ 
% 29.93/30.17             (a_3_4_lattice3 @ sk_A @ sk_B @ X0))
% 29.93/30.17          | ((sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0) @ 
% 29.93/30.17              (k16_lattice3 @ X1 @ X2) @ X1)
% 29.93/30.17              = (k3_lattices @ sk_A @ sk_B @ 
% 29.93/30.17                 (sk_E @ X0 @ sk_B @ sk_A @ 
% 29.93/30.17                  (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0) @ 
% 29.93/30.17                   (k16_lattice3 @ X1 @ X2) @ X1)))))),
% 29.93/30.17      inference('sup-', [status(thm)], ['5', '14'])).
% 29.93/30.17  thf('16', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('17', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.93/30.17         ((r2_hidden @ (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0) @ X2)
% 29.93/30.17          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | (v2_struct_0 @ X0))),
% 29.93/30.17      inference('simplify', [status(thm)], ['4'])).
% 29.93/30.17  thf('18', plain,
% 29.93/30.17      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 29.93/30.17         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 29.93/30.17          | ~ (l3_lattices @ X27)
% 29.93/30.17          | ~ (v4_lattice3 @ X27)
% 29.93/30.17          | ~ (v10_lattices @ X27)
% 29.93/30.17          | (v2_struct_0 @ X27)
% 29.93/30.17          | (m1_subset_1 @ (sk_E @ X29 @ X26 @ X27 @ X28) @ (u1_struct_0 @ X27))
% 29.93/30.17          | ~ (r2_hidden @ X28 @ (a_3_4_lattice3 @ X27 @ X26 @ X29)))),
% 29.93/30.17      inference('cnf', [status(esa)], [fraenkel_a_3_4_lattice3])).
% 29.93/30.17  thf('19', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 29.93/30.17         ((v2_struct_0 @ X3)
% 29.93/30.17          | ~ (l3_lattices @ X3)
% 29.93/30.17          | (r3_lattice3 @ X3 @ (k16_lattice3 @ X3 @ X4) @ 
% 29.93/30.17             (a_3_4_lattice3 @ X2 @ X1 @ X0))
% 29.93/30.17          | (m1_subset_1 @ 
% 29.93/30.17             (sk_E @ X0 @ X1 @ X2 @ 
% 29.93/30.17              (sk_D @ (a_3_4_lattice3 @ X2 @ X1 @ X0) @ 
% 29.93/30.17               (k16_lattice3 @ X3 @ X4) @ X3)) @ 
% 29.93/30.17             (u1_struct_0 @ X2))
% 29.93/30.17          | (v2_struct_0 @ X2)
% 29.93/30.17          | ~ (v10_lattices @ X2)
% 29.93/30.17          | ~ (v4_lattice3 @ X2)
% 29.93/30.17          | ~ (l3_lattices @ X2)
% 29.93/30.17          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2)))),
% 29.93/30.17      inference('sup-', [status(thm)], ['17', '18'])).
% 29.93/30.17  thf('20', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.93/30.17         (~ (l3_lattices @ sk_A)
% 29.93/30.17          | ~ (v4_lattice3 @ sk_A)
% 29.93/30.17          | ~ (v10_lattices @ sk_A)
% 29.93/30.17          | (v2_struct_0 @ sk_A)
% 29.93/30.17          | (m1_subset_1 @ 
% 29.93/30.17             (sk_E @ X2 @ sk_B @ sk_A @ 
% 29.93/30.17              (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X2) @ 
% 29.93/30.17               (k16_lattice3 @ X0 @ X1) @ X0)) @ 
% 29.93/30.17             (u1_struct_0 @ sk_A))
% 29.93/30.17          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 29.93/30.17             (a_3_4_lattice3 @ sk_A @ sk_B @ X2))
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | (v2_struct_0 @ X0))),
% 29.93/30.17      inference('sup-', [status(thm)], ['16', '19'])).
% 29.93/30.17  thf('21', plain, ((l3_lattices @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('22', plain, ((v4_lattice3 @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('23', plain, ((v10_lattices @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('24', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.93/30.17         ((v2_struct_0 @ sk_A)
% 29.93/30.17          | (m1_subset_1 @ 
% 29.93/30.17             (sk_E @ X2 @ sk_B @ sk_A @ 
% 29.93/30.17              (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X2) @ 
% 29.93/30.17               (k16_lattice3 @ X0 @ X1) @ X0)) @ 
% 29.93/30.17             (u1_struct_0 @ sk_A))
% 29.93/30.17          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 29.93/30.17             (a_3_4_lattice3 @ sk_A @ sk_B @ X2))
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | (v2_struct_0 @ X0))),
% 29.93/30.17      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 29.93/30.17  thf('25', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.93/30.17         ((r2_hidden @ (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0) @ X2)
% 29.93/30.17          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | (v2_struct_0 @ X0))),
% 29.93/30.17      inference('simplify', [status(thm)], ['4'])).
% 29.93/30.17  thf('26', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('27', plain,
% 29.93/30.17      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 29.93/30.17         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 29.93/30.17          | ~ (l3_lattices @ X27)
% 29.93/30.17          | ~ (v4_lattice3 @ X27)
% 29.93/30.17          | ~ (v10_lattices @ X27)
% 29.93/30.17          | (v2_struct_0 @ X27)
% 29.93/30.17          | (r2_hidden @ (sk_E @ X29 @ X26 @ X27 @ X28) @ X29)
% 29.93/30.17          | ~ (r2_hidden @ X28 @ (a_3_4_lattice3 @ X27 @ X26 @ X29)))),
% 29.93/30.17      inference('cnf', [status(esa)], [fraenkel_a_3_4_lattice3])).
% 29.93/30.17  thf('28', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i]:
% 29.93/30.17         (~ (r2_hidden @ X1 @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0))
% 29.93/30.17          | (r2_hidden @ (sk_E @ X0 @ sk_B @ sk_A @ X1) @ X0)
% 29.93/30.17          | (v2_struct_0 @ sk_A)
% 29.93/30.17          | ~ (v10_lattices @ sk_A)
% 29.93/30.17          | ~ (v4_lattice3 @ sk_A)
% 29.93/30.17          | ~ (l3_lattices @ sk_A))),
% 29.93/30.17      inference('sup-', [status(thm)], ['26', '27'])).
% 29.93/30.17  thf('29', plain, ((v10_lattices @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('30', plain, ((v4_lattice3 @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('31', plain, ((l3_lattices @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('32', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i]:
% 29.93/30.17         (~ (r2_hidden @ X1 @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0))
% 29.93/30.17          | (r2_hidden @ (sk_E @ X0 @ sk_B @ sk_A @ X1) @ X0)
% 29.93/30.17          | (v2_struct_0 @ sk_A))),
% 29.93/30.17      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 29.93/30.17  thf('33', plain, (~ (v2_struct_0 @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('34', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i]:
% 29.93/30.17         ((r2_hidden @ (sk_E @ X0 @ sk_B @ sk_A @ X1) @ X0)
% 29.93/30.17          | ~ (r2_hidden @ X1 @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0)))),
% 29.93/30.17      inference('clc', [status(thm)], ['32', '33'])).
% 29.93/30.17  thf('35', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.93/30.17         ((v2_struct_0 @ X1)
% 29.93/30.17          | ~ (l3_lattices @ X1)
% 29.93/30.17          | (r3_lattice3 @ X1 @ (k16_lattice3 @ X1 @ X2) @ 
% 29.93/30.17             (a_3_4_lattice3 @ sk_A @ sk_B @ X0))
% 29.93/30.17          | (r2_hidden @ 
% 29.93/30.17             (sk_E @ X0 @ sk_B @ sk_A @ 
% 29.93/30.17              (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0) @ 
% 29.93/30.17               (k16_lattice3 @ X1 @ X2) @ X1)) @ 
% 29.93/30.17             X0))),
% 29.93/30.17      inference('sup-', [status(thm)], ['25', '34'])).
% 29.93/30.17  thf('36', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.93/30.17         ((v2_struct_0 @ sk_A)
% 29.93/30.17          | (m1_subset_1 @ 
% 29.93/30.17             (sk_E @ X2 @ sk_B @ sk_A @ 
% 29.93/30.17              (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X2) @ 
% 29.93/30.17               (k16_lattice3 @ X0 @ X1) @ X0)) @ 
% 29.93/30.17             (u1_struct_0 @ sk_A))
% 29.93/30.17          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 29.93/30.17             (a_3_4_lattice3 @ sk_A @ sk_B @ X2))
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | (v2_struct_0 @ X0))),
% 29.93/30.17      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 29.93/30.17  thf('37', plain,
% 29.93/30.17      (![X24 : $i, X25 : $i]:
% 29.93/30.17         (~ (l3_lattices @ X24)
% 29.93/30.17          | (v2_struct_0 @ X24)
% 29.93/30.17          | (m1_subset_1 @ (k16_lattice3 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 29.93/30.17      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 29.93/30.17  thf(t34_lattice3, axiom,
% 29.93/30.17    (![A:$i]:
% 29.93/30.17     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 29.93/30.17         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 29.93/30.17       ( ![B:$i]:
% 29.93/30.17         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 29.93/30.17           ( ![C:$i]:
% 29.93/30.17             ( ( ( B ) = ( k16_lattice3 @ A @ C ) ) <=>
% 29.93/30.17               ( ( r3_lattice3 @ A @ B @ C ) & 
% 29.93/30.17                 ( ![D:$i]:
% 29.93/30.17                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 29.93/30.17                     ( ( r3_lattice3 @ A @ D @ C ) =>
% 29.93/30.17                       ( r3_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 29.93/30.17  thf('38', plain,
% 29.93/30.17      (![X31 : $i, X32 : $i, X33 : $i]:
% 29.93/30.17         (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X32))
% 29.93/30.17          | ((X31) != (k16_lattice3 @ X32 @ X33))
% 29.93/30.17          | (r3_lattice3 @ X32 @ X31 @ X33)
% 29.93/30.17          | ~ (l3_lattices @ X32)
% 29.93/30.17          | ~ (v4_lattice3 @ X32)
% 29.93/30.17          | ~ (v10_lattices @ X32)
% 29.93/30.17          | (v2_struct_0 @ X32))),
% 29.93/30.17      inference('cnf', [status(esa)], [t34_lattice3])).
% 29.93/30.17  thf('39', plain,
% 29.93/30.17      (![X32 : $i, X33 : $i]:
% 29.93/30.17         ((v2_struct_0 @ X32)
% 29.93/30.17          | ~ (v10_lattices @ X32)
% 29.93/30.17          | ~ (v4_lattice3 @ X32)
% 29.93/30.17          | ~ (l3_lattices @ X32)
% 29.93/30.17          | (r3_lattice3 @ X32 @ (k16_lattice3 @ X32 @ X33) @ X33)
% 29.93/30.17          | ~ (m1_subset_1 @ (k16_lattice3 @ X32 @ X33) @ (u1_struct_0 @ X32)))),
% 29.93/30.17      inference('simplify', [status(thm)], ['38'])).
% 29.93/30.17  thf('40', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i]:
% 29.93/30.17         ((v2_struct_0 @ X0)
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X1)
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | ~ (v4_lattice3 @ X0)
% 29.93/30.17          | ~ (v10_lattices @ X0)
% 29.93/30.17          | (v2_struct_0 @ X0))),
% 29.93/30.17      inference('sup-', [status(thm)], ['37', '39'])).
% 29.93/30.17  thf('41', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i]:
% 29.93/30.17         (~ (v10_lattices @ X0)
% 29.93/30.17          | ~ (v4_lattice3 @ X0)
% 29.93/30.17          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X1)
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | (v2_struct_0 @ X0))),
% 29.93/30.17      inference('simplify', [status(thm)], ['40'])).
% 29.93/30.17  thf('42', plain,
% 29.93/30.17      (![X24 : $i, X25 : $i]:
% 29.93/30.17         (~ (l3_lattices @ X24)
% 29.93/30.17          | (v2_struct_0 @ X24)
% 29.93/30.17          | (m1_subset_1 @ (k16_lattice3 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 29.93/30.17      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 29.93/30.17  thf('43', plain,
% 29.93/30.17      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 29.93/30.17         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 29.93/30.17          | ~ (r3_lattice3 @ X20 @ X19 @ X21)
% 29.93/30.17          | ~ (r2_hidden @ X22 @ X21)
% 29.93/30.17          | (r1_lattices @ X20 @ X19 @ X22)
% 29.93/30.17          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X20))
% 29.93/30.17          | ~ (l3_lattices @ X20)
% 29.93/30.17          | (v2_struct_0 @ X20))),
% 29.93/30.17      inference('cnf', [status(esa)], [d16_lattice3])).
% 29.93/30.17  thf('44', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 29.93/30.17         ((v2_struct_0 @ X0)
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | (v2_struct_0 @ X0)
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 29.93/30.17          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 29.93/30.17          | ~ (r2_hidden @ X2 @ X3)
% 29.93/30.17          | ~ (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X3))),
% 29.93/30.17      inference('sup-', [status(thm)], ['42', '43'])).
% 29.93/30.17  thf('45', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 29.93/30.17         (~ (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X3)
% 29.93/30.17          | ~ (r2_hidden @ X2 @ X3)
% 29.93/30.17          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 29.93/30.17          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | (v2_struct_0 @ X0))),
% 29.93/30.17      inference('simplify', [status(thm)], ['44'])).
% 29.93/30.17  thf('46', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.93/30.17         ((v2_struct_0 @ X1)
% 29.93/30.17          | ~ (l3_lattices @ X1)
% 29.93/30.17          | ~ (v4_lattice3 @ X1)
% 29.93/30.17          | ~ (v10_lattices @ X1)
% 29.93/30.17          | (v2_struct_0 @ X1)
% 29.93/30.17          | ~ (l3_lattices @ X1)
% 29.93/30.17          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 29.93/30.17          | (r1_lattices @ X1 @ (k16_lattice3 @ X1 @ X0) @ X2)
% 29.93/30.17          | ~ (r2_hidden @ X2 @ X0))),
% 29.93/30.17      inference('sup-', [status(thm)], ['41', '45'])).
% 29.93/30.17  thf('47', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.93/30.17         (~ (r2_hidden @ X2 @ X0)
% 29.93/30.17          | (r1_lattices @ X1 @ (k16_lattice3 @ X1 @ X0) @ X2)
% 29.93/30.17          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 29.93/30.17          | ~ (v10_lattices @ X1)
% 29.93/30.17          | ~ (v4_lattice3 @ X1)
% 29.93/30.17          | ~ (l3_lattices @ X1)
% 29.93/30.17          | (v2_struct_0 @ X1))),
% 29.93/30.17      inference('simplify', [status(thm)], ['46'])).
% 29.93/30.17  thf('48', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 29.93/30.17         ((v2_struct_0 @ X0)
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 29.93/30.17             (a_3_4_lattice3 @ sk_A @ sk_B @ X2))
% 29.93/30.17          | (v2_struct_0 @ sk_A)
% 29.93/30.17          | (v2_struct_0 @ sk_A)
% 29.93/30.17          | ~ (l3_lattices @ sk_A)
% 29.93/30.17          | ~ (v4_lattice3 @ sk_A)
% 29.93/30.17          | ~ (v10_lattices @ sk_A)
% 29.93/30.17          | (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X3) @ 
% 29.93/30.17             (sk_E @ X2 @ sk_B @ sk_A @ 
% 29.93/30.17              (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X2) @ 
% 29.93/30.17               (k16_lattice3 @ X0 @ X1) @ X0)))
% 29.93/30.17          | ~ (r2_hidden @ 
% 29.93/30.17               (sk_E @ X2 @ sk_B @ sk_A @ 
% 29.93/30.17                (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X2) @ 
% 29.93/30.17                 (k16_lattice3 @ X0 @ X1) @ X0)) @ 
% 29.93/30.17               X3))),
% 29.93/30.17      inference('sup-', [status(thm)], ['36', '47'])).
% 29.93/30.17  thf('49', plain, ((l3_lattices @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('50', plain, ((v4_lattice3 @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('51', plain, ((v10_lattices @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('52', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 29.93/30.17         ((v2_struct_0 @ X0)
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 29.93/30.17             (a_3_4_lattice3 @ sk_A @ sk_B @ X2))
% 29.93/30.17          | (v2_struct_0 @ sk_A)
% 29.93/30.17          | (v2_struct_0 @ sk_A)
% 29.93/30.17          | (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X3) @ 
% 29.93/30.17             (sk_E @ X2 @ sk_B @ sk_A @ 
% 29.93/30.17              (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X2) @ 
% 29.93/30.17               (k16_lattice3 @ X0 @ X1) @ X0)))
% 29.93/30.17          | ~ (r2_hidden @ 
% 29.93/30.17               (sk_E @ X2 @ sk_B @ sk_A @ 
% 29.93/30.17                (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X2) @ 
% 29.93/30.17                 (k16_lattice3 @ X0 @ X1) @ X0)) @ 
% 29.93/30.17               X3))),
% 29.93/30.17      inference('demod', [status(thm)], ['48', '49', '50', '51'])).
% 29.93/30.17  thf('53', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 29.93/30.17         (~ (r2_hidden @ 
% 29.93/30.17             (sk_E @ X2 @ sk_B @ sk_A @ 
% 29.93/30.17              (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X2) @ 
% 29.93/30.17               (k16_lattice3 @ X0 @ X1) @ X0)) @ 
% 29.93/30.17             X3)
% 29.93/30.17          | (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X3) @ 
% 29.93/30.17             (sk_E @ X2 @ sk_B @ sk_A @ 
% 29.93/30.17              (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X2) @ 
% 29.93/30.17               (k16_lattice3 @ X0 @ X1) @ X0)))
% 29.93/30.17          | (v2_struct_0 @ sk_A)
% 29.93/30.17          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 29.93/30.17             (a_3_4_lattice3 @ sk_A @ sk_B @ X2))
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | (v2_struct_0 @ X0))),
% 29.93/30.17      inference('simplify', [status(thm)], ['52'])).
% 29.93/30.17  thf('54', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.93/30.17         ((r3_lattice3 @ X1 @ (k16_lattice3 @ X1 @ X2) @ 
% 29.93/30.17           (a_3_4_lattice3 @ sk_A @ sk_B @ X0))
% 29.93/30.17          | ~ (l3_lattices @ X1)
% 29.93/30.17          | (v2_struct_0 @ X1)
% 29.93/30.17          | (v2_struct_0 @ X1)
% 29.93/30.17          | ~ (l3_lattices @ X1)
% 29.93/30.17          | (r3_lattice3 @ X1 @ (k16_lattice3 @ X1 @ X2) @ 
% 29.93/30.17             (a_3_4_lattice3 @ sk_A @ sk_B @ X0))
% 29.93/30.17          | (v2_struct_0 @ sk_A)
% 29.93/30.17          | (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ 
% 29.93/30.17             (sk_E @ X0 @ sk_B @ sk_A @ 
% 29.93/30.17              (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0) @ 
% 29.93/30.17               (k16_lattice3 @ X1 @ X2) @ X1))))),
% 29.93/30.17      inference('sup-', [status(thm)], ['35', '53'])).
% 29.93/30.17  thf('55', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.93/30.17         ((r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ 
% 29.93/30.17           (sk_E @ X0 @ sk_B @ sk_A @ 
% 29.93/30.17            (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0) @ 
% 29.93/30.17             (k16_lattice3 @ X1 @ X2) @ X1)))
% 29.93/30.17          | (v2_struct_0 @ sk_A)
% 29.93/30.17          | (v2_struct_0 @ X1)
% 29.93/30.17          | ~ (l3_lattices @ X1)
% 29.93/30.17          | (r3_lattice3 @ X1 @ (k16_lattice3 @ X1 @ X2) @ 
% 29.93/30.17             (a_3_4_lattice3 @ sk_A @ sk_B @ X0)))),
% 29.93/30.17      inference('simplify', [status(thm)], ['54'])).
% 29.93/30.17  thf('56', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.93/30.17         ((v2_struct_0 @ sk_A)
% 29.93/30.17          | (m1_subset_1 @ 
% 29.93/30.17             (sk_E @ X2 @ sk_B @ sk_A @ 
% 29.93/30.17              (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X2) @ 
% 29.93/30.17               (k16_lattice3 @ X0 @ X1) @ X0)) @ 
% 29.93/30.17             (u1_struct_0 @ sk_A))
% 29.93/30.17          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 29.93/30.17             (a_3_4_lattice3 @ sk_A @ sk_B @ X2))
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | (v2_struct_0 @ X0))),
% 29.93/30.17      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 29.93/30.17  thf('57', plain,
% 29.93/30.17      (![X24 : $i, X25 : $i]:
% 29.93/30.17         (~ (l3_lattices @ X24)
% 29.93/30.17          | (v2_struct_0 @ X24)
% 29.93/30.17          | (m1_subset_1 @ (k16_lattice3 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 29.93/30.17      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 29.93/30.17  thf(redefinition_r3_lattices, axiom,
% 29.93/30.17    (![A:$i,B:$i,C:$i]:
% 29.93/30.17     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 29.93/30.17         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 29.93/30.17         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 29.93/30.17         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 29.93/30.17       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 29.93/30.17  thf('58', plain,
% 29.93/30.17      (![X5 : $i, X6 : $i, X7 : $i]:
% 29.93/30.17         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 29.93/30.17          | ~ (l3_lattices @ X6)
% 29.93/30.17          | ~ (v9_lattices @ X6)
% 29.93/30.17          | ~ (v8_lattices @ X6)
% 29.93/30.17          | ~ (v6_lattices @ X6)
% 29.93/30.17          | (v2_struct_0 @ X6)
% 29.93/30.17          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 29.93/30.17          | (r3_lattices @ X6 @ X5 @ X7)
% 29.93/30.17          | ~ (r1_lattices @ X6 @ X5 @ X7))),
% 29.93/30.17      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 29.93/30.17  thf('59', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.93/30.17         ((v2_struct_0 @ X0)
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | ~ (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 29.93/30.17          | (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 29.93/30.17          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 29.93/30.17          | (v2_struct_0 @ X0)
% 29.93/30.17          | ~ (v6_lattices @ X0)
% 29.93/30.17          | ~ (v8_lattices @ X0)
% 29.93/30.17          | ~ (v9_lattices @ X0)
% 29.93/30.17          | ~ (l3_lattices @ X0))),
% 29.93/30.17      inference('sup-', [status(thm)], ['57', '58'])).
% 29.93/30.17  thf('60', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.93/30.17         (~ (v9_lattices @ X0)
% 29.93/30.17          | ~ (v8_lattices @ X0)
% 29.93/30.17          | ~ (v6_lattices @ X0)
% 29.93/30.17          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 29.93/30.17          | (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 29.93/30.17          | ~ (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | (v2_struct_0 @ X0))),
% 29.93/30.17      inference('simplify', [status(thm)], ['59'])).
% 29.93/30.17  thf('61', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 29.93/30.17         ((v2_struct_0 @ X0)
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 29.93/30.17             (a_3_4_lattice3 @ sk_A @ sk_B @ X2))
% 29.93/30.17          | (v2_struct_0 @ sk_A)
% 29.93/30.17          | (v2_struct_0 @ sk_A)
% 29.93/30.17          | ~ (l3_lattices @ sk_A)
% 29.93/30.17          | ~ (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X3) @ 
% 29.93/30.17               (sk_E @ X2 @ sk_B @ sk_A @ 
% 29.93/30.17                (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X2) @ 
% 29.93/30.17                 (k16_lattice3 @ X0 @ X1) @ X0)))
% 29.93/30.17          | (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X3) @ 
% 29.93/30.17             (sk_E @ X2 @ sk_B @ sk_A @ 
% 29.93/30.17              (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X2) @ 
% 29.93/30.17               (k16_lattice3 @ X0 @ X1) @ X0)))
% 29.93/30.17          | ~ (v6_lattices @ sk_A)
% 29.93/30.17          | ~ (v8_lattices @ sk_A)
% 29.93/30.17          | ~ (v9_lattices @ sk_A))),
% 29.93/30.17      inference('sup-', [status(thm)], ['56', '60'])).
% 29.93/30.17  thf('62', plain, ((l3_lattices @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf(cc1_lattices, axiom,
% 29.93/30.17    (![A:$i]:
% 29.93/30.17     ( ( l3_lattices @ A ) =>
% 29.93/30.17       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 29.93/30.17         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 29.93/30.17           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 29.93/30.17           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 29.93/30.17  thf('63', plain,
% 29.93/30.17      (![X0 : $i]:
% 29.93/30.17         ((v2_struct_0 @ X0)
% 29.93/30.17          | ~ (v10_lattices @ X0)
% 29.93/30.17          | (v6_lattices @ X0)
% 29.93/30.17          | ~ (l3_lattices @ X0))),
% 29.93/30.17      inference('cnf', [status(esa)], [cc1_lattices])).
% 29.93/30.17  thf('64', plain, (~ (v2_struct_0 @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('65', plain,
% 29.93/30.17      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 29.93/30.17      inference('sup-', [status(thm)], ['63', '64'])).
% 29.93/30.17  thf('66', plain, ((l3_lattices @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('67', plain, ((v10_lattices @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('68', plain, ((v6_lattices @ sk_A)),
% 29.93/30.17      inference('demod', [status(thm)], ['65', '66', '67'])).
% 29.93/30.17  thf('69', plain,
% 29.93/30.17      (![X0 : $i]:
% 29.93/30.17         ((v2_struct_0 @ X0)
% 29.93/30.17          | ~ (v10_lattices @ X0)
% 29.93/30.17          | (v8_lattices @ X0)
% 29.93/30.17          | ~ (l3_lattices @ X0))),
% 29.93/30.17      inference('cnf', [status(esa)], [cc1_lattices])).
% 29.93/30.17  thf('70', plain, (~ (v2_struct_0 @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('71', plain,
% 29.93/30.17      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 29.93/30.17      inference('sup-', [status(thm)], ['69', '70'])).
% 29.93/30.17  thf('72', plain, ((l3_lattices @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('73', plain, ((v10_lattices @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('74', plain, ((v8_lattices @ sk_A)),
% 29.93/30.17      inference('demod', [status(thm)], ['71', '72', '73'])).
% 29.93/30.17  thf('75', plain,
% 29.93/30.17      (![X0 : $i]:
% 29.93/30.17         ((v2_struct_0 @ X0)
% 29.93/30.17          | ~ (v10_lattices @ X0)
% 29.93/30.17          | (v9_lattices @ X0)
% 29.93/30.17          | ~ (l3_lattices @ X0))),
% 29.93/30.17      inference('cnf', [status(esa)], [cc1_lattices])).
% 29.93/30.17  thf('76', plain, (~ (v2_struct_0 @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('77', plain,
% 29.93/30.17      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 29.93/30.17      inference('sup-', [status(thm)], ['75', '76'])).
% 29.93/30.17  thf('78', plain, ((l3_lattices @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('79', plain, ((v10_lattices @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('80', plain, ((v9_lattices @ sk_A)),
% 29.93/30.17      inference('demod', [status(thm)], ['77', '78', '79'])).
% 29.93/30.17  thf('81', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 29.93/30.17         ((v2_struct_0 @ X0)
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 29.93/30.17             (a_3_4_lattice3 @ sk_A @ sk_B @ X2))
% 29.93/30.17          | (v2_struct_0 @ sk_A)
% 29.93/30.17          | (v2_struct_0 @ sk_A)
% 29.93/30.17          | ~ (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X3) @ 
% 29.93/30.17               (sk_E @ X2 @ sk_B @ sk_A @ 
% 29.93/30.17                (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X2) @ 
% 29.93/30.17                 (k16_lattice3 @ X0 @ X1) @ X0)))
% 29.93/30.17          | (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X3) @ 
% 29.93/30.17             (sk_E @ X2 @ sk_B @ sk_A @ 
% 29.93/30.17              (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X2) @ 
% 29.93/30.17               (k16_lattice3 @ X0 @ X1) @ X0))))),
% 29.93/30.17      inference('demod', [status(thm)], ['61', '62', '68', '74', '80'])).
% 29.93/30.17  thf('82', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 29.93/30.17         ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X3) @ 
% 29.93/30.17           (sk_E @ X2 @ sk_B @ sk_A @ 
% 29.93/30.17            (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X2) @ 
% 29.93/30.17             (k16_lattice3 @ X0 @ X1) @ X0)))
% 29.93/30.17          | ~ (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X3) @ 
% 29.93/30.17               (sk_E @ X2 @ sk_B @ sk_A @ 
% 29.93/30.17                (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X2) @ 
% 29.93/30.17                 (k16_lattice3 @ X0 @ X1) @ X0)))
% 29.93/30.17          | (v2_struct_0 @ sk_A)
% 29.93/30.17          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 29.93/30.17             (a_3_4_lattice3 @ sk_A @ sk_B @ X2))
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | (v2_struct_0 @ X0))),
% 29.93/30.17      inference('simplify', [status(thm)], ['81'])).
% 29.93/30.17  thf('83', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.93/30.17         ((r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 29.93/30.17           (a_3_4_lattice3 @ sk_A @ sk_B @ X2))
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | (v2_struct_0 @ X0)
% 29.93/30.17          | (v2_struct_0 @ sk_A)
% 29.93/30.17          | (v2_struct_0 @ X0)
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 29.93/30.17             (a_3_4_lattice3 @ sk_A @ sk_B @ X2))
% 29.93/30.17          | (v2_struct_0 @ sk_A)
% 29.93/30.17          | (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X2) @ 
% 29.93/30.17             (sk_E @ X2 @ sk_B @ sk_A @ 
% 29.93/30.17              (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X2) @ 
% 29.93/30.17               (k16_lattice3 @ X0 @ X1) @ X0))))),
% 29.93/30.17      inference('sup-', [status(thm)], ['55', '82'])).
% 29.93/30.17  thf('84', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.93/30.17         ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X2) @ 
% 29.93/30.17           (sk_E @ X2 @ sk_B @ sk_A @ 
% 29.93/30.17            (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X2) @ 
% 29.93/30.17             (k16_lattice3 @ X0 @ X1) @ X0)))
% 29.93/30.17          | (v2_struct_0 @ sk_A)
% 29.93/30.17          | (v2_struct_0 @ X0)
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 29.93/30.17             (a_3_4_lattice3 @ sk_A @ sk_B @ X2)))),
% 29.93/30.17      inference('simplify', [status(thm)], ['83'])).
% 29.93/30.17  thf('85', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('86', plain,
% 29.93/30.17      (![X24 : $i, X25 : $i]:
% 29.93/30.17         (~ (l3_lattices @ X24)
% 29.93/30.17          | (v2_struct_0 @ X24)
% 29.93/30.17          | (m1_subset_1 @ (k16_lattice3 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 29.93/30.17      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 29.93/30.17  thf(t3_filter_0, axiom,
% 29.93/30.17    (![A:$i]:
% 29.93/30.17     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 29.93/30.17       ( ![B:$i]:
% 29.93/30.17         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 29.93/30.17           ( ![C:$i]:
% 29.93/30.17             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 29.93/30.17               ( ![D:$i]:
% 29.93/30.17                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 29.93/30.17                   ( ( r3_lattices @ A @ B @ C ) =>
% 29.93/30.17                     ( r3_lattices @ A @ B @ ( k3_lattices @ A @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 29.93/30.17  thf('87', plain,
% 29.93/30.17      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 29.93/30.17         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 29.93/30.17          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 29.93/30.17          | (r3_lattices @ X12 @ X11 @ (k3_lattices @ X12 @ X13 @ X14))
% 29.93/30.17          | ~ (r3_lattices @ X12 @ X11 @ X14)
% 29.93/30.17          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X12))
% 29.93/30.17          | ~ (l3_lattices @ X12)
% 29.93/30.17          | ~ (v10_lattices @ X12)
% 29.93/30.17          | (v2_struct_0 @ X12))),
% 29.93/30.17      inference('cnf', [status(esa)], [t3_filter_0])).
% 29.93/30.17  thf('88', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 29.93/30.17         ((v2_struct_0 @ X0)
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | (v2_struct_0 @ X0)
% 29.93/30.17          | ~ (v10_lattices @ X0)
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 29.93/30.17          | ~ (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 29.93/30.17          | (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 29.93/30.17             (k3_lattices @ X0 @ X3 @ X2))
% 29.93/30.17          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X0)))),
% 29.93/30.17      inference('sup-', [status(thm)], ['86', '87'])).
% 29.93/30.17  thf('89', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 29.93/30.17         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X0))
% 29.93/30.17          | (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 29.93/30.17             (k3_lattices @ X0 @ X3 @ X2))
% 29.93/30.17          | ~ (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 29.93/30.17          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 29.93/30.17          | ~ (v10_lattices @ X0)
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | (v2_struct_0 @ X0))),
% 29.93/30.17      inference('simplify', [status(thm)], ['88'])).
% 29.93/30.17  thf('90', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i]:
% 29.93/30.17         ((v2_struct_0 @ sk_A)
% 29.93/30.17          | ~ (l3_lattices @ sk_A)
% 29.93/30.17          | ~ (v10_lattices @ sk_A)
% 29.93/30.17          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 29.93/30.17          | ~ (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X1) @ X0)
% 29.93/30.17          | (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X1) @ 
% 29.93/30.17             (k3_lattices @ sk_A @ sk_B @ X0)))),
% 29.93/30.17      inference('sup-', [status(thm)], ['85', '89'])).
% 29.93/30.17  thf('91', plain, ((l3_lattices @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('92', plain, ((v10_lattices @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('93', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i]:
% 29.93/30.17         ((v2_struct_0 @ sk_A)
% 29.93/30.17          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 29.93/30.17          | ~ (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X1) @ X0)
% 29.93/30.17          | (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X1) @ 
% 29.93/30.17             (k3_lattices @ sk_A @ sk_B @ X0)))),
% 29.93/30.17      inference('demod', [status(thm)], ['90', '91', '92'])).
% 29.93/30.17  thf('94', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.93/30.17         ((r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 29.93/30.17           (a_3_4_lattice3 @ sk_A @ sk_B @ X2))
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | (v2_struct_0 @ X0)
% 29.93/30.17          | (v2_struct_0 @ sk_A)
% 29.93/30.17          | (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X2) @ 
% 29.93/30.17             (k3_lattices @ sk_A @ sk_B @ 
% 29.93/30.17              (sk_E @ X2 @ sk_B @ sk_A @ 
% 29.93/30.17               (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X2) @ 
% 29.93/30.17                (k16_lattice3 @ X0 @ X1) @ X0))))
% 29.93/30.17          | ~ (m1_subset_1 @ 
% 29.93/30.17               (sk_E @ X2 @ sk_B @ sk_A @ 
% 29.93/30.17                (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X2) @ 
% 29.93/30.17                 (k16_lattice3 @ X0 @ X1) @ X0)) @ 
% 29.93/30.17               (u1_struct_0 @ sk_A))
% 29.93/30.17          | (v2_struct_0 @ sk_A))),
% 29.93/30.17      inference('sup-', [status(thm)], ['84', '93'])).
% 29.93/30.17  thf('95', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.93/30.17         (~ (m1_subset_1 @ 
% 29.93/30.17             (sk_E @ X2 @ sk_B @ sk_A @ 
% 29.93/30.17              (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X2) @ 
% 29.93/30.17               (k16_lattice3 @ X0 @ X1) @ X0)) @ 
% 29.93/30.17             (u1_struct_0 @ sk_A))
% 29.93/30.17          | (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X2) @ 
% 29.93/30.17             (k3_lattices @ sk_A @ sk_B @ 
% 29.93/30.17              (sk_E @ X2 @ sk_B @ sk_A @ 
% 29.93/30.17               (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X2) @ 
% 29.93/30.17                (k16_lattice3 @ X0 @ X1) @ X0))))
% 29.93/30.17          | (v2_struct_0 @ sk_A)
% 29.93/30.17          | (v2_struct_0 @ X0)
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 29.93/30.17             (a_3_4_lattice3 @ sk_A @ sk_B @ X2)))),
% 29.93/30.17      inference('simplify', [status(thm)], ['94'])).
% 29.93/30.17  thf('96', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.93/30.17         ((v2_struct_0 @ X0)
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 29.93/30.17             (a_3_4_lattice3 @ sk_A @ sk_B @ X2))
% 29.93/30.17          | (v2_struct_0 @ sk_A)
% 29.93/30.17          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 29.93/30.17             (a_3_4_lattice3 @ sk_A @ sk_B @ X2))
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | (v2_struct_0 @ X0)
% 29.93/30.17          | (v2_struct_0 @ sk_A)
% 29.93/30.17          | (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X2) @ 
% 29.93/30.17             (k3_lattices @ sk_A @ sk_B @ 
% 29.93/30.17              (sk_E @ X2 @ sk_B @ sk_A @ 
% 29.93/30.17               (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X2) @ 
% 29.93/30.17                (k16_lattice3 @ X0 @ X1) @ X0)))))),
% 29.93/30.17      inference('sup-', [status(thm)], ['24', '95'])).
% 29.93/30.17  thf('97', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.93/30.17         ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X2) @ 
% 29.93/30.17           (k3_lattices @ sk_A @ sk_B @ 
% 29.93/30.17            (sk_E @ X2 @ sk_B @ sk_A @ 
% 29.93/30.17             (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X2) @ 
% 29.93/30.17              (k16_lattice3 @ X0 @ X1) @ X0))))
% 29.93/30.17          | (v2_struct_0 @ sk_A)
% 29.93/30.17          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 29.93/30.17             (a_3_4_lattice3 @ sk_A @ sk_B @ X2))
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | (v2_struct_0 @ X0))),
% 29.93/30.17      inference('simplify', [status(thm)], ['96'])).
% 29.93/30.17  thf('98', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.93/30.17         ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X2) @ 
% 29.93/30.17           (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X2) @ 
% 29.93/30.17            (k16_lattice3 @ X0 @ X1) @ X0))
% 29.93/30.17          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 29.93/30.17             (a_3_4_lattice3 @ sk_A @ sk_B @ X2))
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | (v2_struct_0 @ X0)
% 29.93/30.17          | (v2_struct_0 @ X0)
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 29.93/30.17             (a_3_4_lattice3 @ sk_A @ sk_B @ X2))
% 29.93/30.17          | (v2_struct_0 @ sk_A))),
% 29.93/30.17      inference('sup+', [status(thm)], ['15', '97'])).
% 29.93/30.17  thf('99', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.93/30.17         ((v2_struct_0 @ sk_A)
% 29.93/30.17          | (v2_struct_0 @ X0)
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 29.93/30.17             (a_3_4_lattice3 @ sk_A @ sk_B @ X2))
% 29.93/30.17          | (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X2) @ 
% 29.93/30.17             (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X2) @ 
% 29.93/30.17              (k16_lattice3 @ X0 @ X1) @ X0)))),
% 29.93/30.17      inference('simplify', [status(thm)], ['98'])).
% 29.93/30.17  thf('100', plain,
% 29.93/30.17      (![X24 : $i, X25 : $i]:
% 29.93/30.17         (~ (l3_lattices @ X24)
% 29.93/30.17          | (v2_struct_0 @ X24)
% 29.93/30.17          | (m1_subset_1 @ (k16_lattice3 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 29.93/30.17      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 29.93/30.17  thf('101', plain,
% 29.93/30.17      (![X19 : $i, X20 : $i, X23 : $i]:
% 29.93/30.17         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 29.93/30.17          | (m1_subset_1 @ (sk_D @ X23 @ X19 @ X20) @ (u1_struct_0 @ X20))
% 29.93/30.17          | (r3_lattice3 @ X20 @ X19 @ X23)
% 29.93/30.17          | ~ (l3_lattices @ X20)
% 29.93/30.17          | (v2_struct_0 @ X20))),
% 29.93/30.17      inference('cnf', [status(esa)], [d16_lattice3])).
% 29.93/30.17  thf('102', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.93/30.17         ((v2_struct_0 @ X0)
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | (v2_struct_0 @ X0)
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 29.93/30.17          | (m1_subset_1 @ (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0) @ 
% 29.93/30.17             (u1_struct_0 @ X0)))),
% 29.93/30.17      inference('sup-', [status(thm)], ['100', '101'])).
% 29.93/30.17  thf('103', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.93/30.17         ((m1_subset_1 @ (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0) @ 
% 29.93/30.17           (u1_struct_0 @ X0))
% 29.93/30.17          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | (v2_struct_0 @ X0))),
% 29.93/30.17      inference('simplify', [status(thm)], ['102'])).
% 29.93/30.17  thf('104', plain,
% 29.93/30.17      (![X24 : $i, X25 : $i]:
% 29.93/30.17         (~ (l3_lattices @ X24)
% 29.93/30.17          | (v2_struct_0 @ X24)
% 29.93/30.17          | (m1_subset_1 @ (k16_lattice3 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 29.93/30.17      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 29.93/30.17  thf('105', plain,
% 29.93/30.17      (![X5 : $i, X6 : $i, X7 : $i]:
% 29.93/30.17         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 29.93/30.17          | ~ (l3_lattices @ X6)
% 29.93/30.17          | ~ (v9_lattices @ X6)
% 29.93/30.17          | ~ (v8_lattices @ X6)
% 29.93/30.17          | ~ (v6_lattices @ X6)
% 29.93/30.17          | (v2_struct_0 @ X6)
% 29.93/30.17          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 29.93/30.17          | (r1_lattices @ X6 @ X5 @ X7)
% 29.93/30.17          | ~ (r3_lattices @ X6 @ X5 @ X7))),
% 29.93/30.17      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 29.93/30.17  thf('106', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.93/30.17         ((v2_struct_0 @ X0)
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | ~ (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 29.93/30.17          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 29.93/30.17          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 29.93/30.17          | (v2_struct_0 @ X0)
% 29.93/30.17          | ~ (v6_lattices @ X0)
% 29.93/30.17          | ~ (v8_lattices @ X0)
% 29.93/30.17          | ~ (v9_lattices @ X0)
% 29.93/30.17          | ~ (l3_lattices @ X0))),
% 29.93/30.17      inference('sup-', [status(thm)], ['104', '105'])).
% 29.93/30.17  thf('107', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.93/30.17         (~ (v9_lattices @ X0)
% 29.93/30.17          | ~ (v8_lattices @ X0)
% 29.93/30.17          | ~ (v6_lattices @ X0)
% 29.93/30.17          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 29.93/30.17          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 29.93/30.17          | ~ (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | (v2_struct_0 @ X0))),
% 29.93/30.17      inference('simplify', [status(thm)], ['106'])).
% 29.93/30.17  thf('108', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 29.93/30.17         ((v2_struct_0 @ X0)
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 29.93/30.17          | (v2_struct_0 @ X0)
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | ~ (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X3) @ 
% 29.93/30.17               (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0))
% 29.93/30.17          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X3) @ 
% 29.93/30.17             (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0))
% 29.93/30.17          | ~ (v6_lattices @ X0)
% 29.93/30.17          | ~ (v8_lattices @ X0)
% 29.93/30.17          | ~ (v9_lattices @ X0))),
% 29.93/30.17      inference('sup-', [status(thm)], ['103', '107'])).
% 29.93/30.17  thf('109', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 29.93/30.17         (~ (v9_lattices @ X0)
% 29.93/30.17          | ~ (v8_lattices @ X0)
% 29.93/30.17          | ~ (v6_lattices @ X0)
% 29.93/30.17          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X3) @ 
% 29.93/30.17             (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0))
% 29.93/30.17          | ~ (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X3) @ 
% 29.93/30.17               (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0))
% 29.93/30.17          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | (v2_struct_0 @ X0))),
% 29.93/30.17      inference('simplify', [status(thm)], ['108'])).
% 29.93/30.17  thf('110', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i]:
% 29.93/30.17         ((r3_lattice3 @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ 
% 29.93/30.17           (a_3_4_lattice3 @ sk_A @ sk_B @ X1))
% 29.93/30.17          | ~ (l3_lattices @ sk_A)
% 29.93/30.17          | (v2_struct_0 @ sk_A)
% 29.93/30.17          | (v2_struct_0 @ sk_A)
% 29.93/30.17          | (v2_struct_0 @ sk_A)
% 29.93/30.17          | ~ (l3_lattices @ sk_A)
% 29.93/30.17          | (r3_lattice3 @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ 
% 29.93/30.17             (a_3_4_lattice3 @ sk_A @ sk_B @ X1))
% 29.93/30.17          | (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X1) @ 
% 29.93/30.17             (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X1) @ 
% 29.93/30.17              (k16_lattice3 @ sk_A @ X0) @ sk_A))
% 29.93/30.17          | ~ (v6_lattices @ sk_A)
% 29.93/30.17          | ~ (v8_lattices @ sk_A)
% 29.93/30.17          | ~ (v9_lattices @ sk_A))),
% 29.93/30.17      inference('sup-', [status(thm)], ['99', '109'])).
% 29.93/30.17  thf('111', plain, ((l3_lattices @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('112', plain, ((l3_lattices @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('113', plain, ((v6_lattices @ sk_A)),
% 29.93/30.17      inference('demod', [status(thm)], ['65', '66', '67'])).
% 29.93/30.17  thf('114', plain, ((v8_lattices @ sk_A)),
% 29.93/30.17      inference('demod', [status(thm)], ['71', '72', '73'])).
% 29.93/30.17  thf('115', plain, ((v9_lattices @ sk_A)),
% 29.93/30.17      inference('demod', [status(thm)], ['77', '78', '79'])).
% 29.93/30.17  thf('116', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i]:
% 29.93/30.17         ((r3_lattice3 @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ 
% 29.93/30.17           (a_3_4_lattice3 @ sk_A @ sk_B @ X1))
% 29.93/30.17          | (v2_struct_0 @ sk_A)
% 29.93/30.17          | (v2_struct_0 @ sk_A)
% 29.93/30.17          | (v2_struct_0 @ sk_A)
% 29.93/30.17          | (r3_lattice3 @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ 
% 29.93/30.17             (a_3_4_lattice3 @ sk_A @ sk_B @ X1))
% 29.93/30.17          | (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X1) @ 
% 29.93/30.17             (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X1) @ 
% 29.93/30.17              (k16_lattice3 @ sk_A @ X0) @ sk_A)))),
% 29.93/30.17      inference('demod', [status(thm)],
% 29.93/30.17                ['110', '111', '112', '113', '114', '115'])).
% 29.93/30.17  thf('117', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i]:
% 29.93/30.17         ((r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X1) @ 
% 29.93/30.17           (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X1) @ 
% 29.93/30.17            (k16_lattice3 @ sk_A @ X0) @ sk_A))
% 29.93/30.17          | (v2_struct_0 @ sk_A)
% 29.93/30.17          | (r3_lattice3 @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ 
% 29.93/30.17             (a_3_4_lattice3 @ sk_A @ sk_B @ X1)))),
% 29.93/30.17      inference('simplify', [status(thm)], ['116'])).
% 29.93/30.17  thf('118', plain, (~ (v2_struct_0 @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('119', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i]:
% 29.93/30.17         ((r3_lattice3 @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ 
% 29.93/30.17           (a_3_4_lattice3 @ sk_A @ sk_B @ X1))
% 29.93/30.17          | (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X1) @ 
% 29.93/30.17             (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X1) @ 
% 29.93/30.17              (k16_lattice3 @ sk_A @ X0) @ sk_A)))),
% 29.93/30.17      inference('clc', [status(thm)], ['117', '118'])).
% 29.93/30.17  thf('120', plain,
% 29.93/30.17      (![X24 : $i, X25 : $i]:
% 29.93/30.17         (~ (l3_lattices @ X24)
% 29.93/30.17          | (v2_struct_0 @ X24)
% 29.93/30.17          | (m1_subset_1 @ (k16_lattice3 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 29.93/30.17      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 29.93/30.17  thf('121', plain,
% 29.93/30.17      (![X19 : $i, X20 : $i, X23 : $i]:
% 29.93/30.17         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 29.93/30.17          | ~ (r1_lattices @ X20 @ X19 @ (sk_D @ X23 @ X19 @ X20))
% 29.93/30.17          | (r3_lattice3 @ X20 @ X19 @ X23)
% 29.93/30.17          | ~ (l3_lattices @ X20)
% 29.93/30.17          | (v2_struct_0 @ X20))),
% 29.93/30.17      inference('cnf', [status(esa)], [d16_lattice3])).
% 29.93/30.17  thf('122', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.93/30.17         ((v2_struct_0 @ X0)
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | (v2_struct_0 @ X0)
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 29.93/30.17          | ~ (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 29.93/30.17               (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0)))),
% 29.93/30.17      inference('sup-', [status(thm)], ['120', '121'])).
% 29.93/30.17  thf('123', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.93/30.17         (~ (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 29.93/30.17             (sk_D @ X2 @ (k16_lattice3 @ X0 @ X1) @ X0))
% 29.93/30.17          | (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | (v2_struct_0 @ X0))),
% 29.93/30.17      inference('simplify', [status(thm)], ['122'])).
% 29.93/30.17  thf('124', plain,
% 29.93/30.17      (![X0 : $i]:
% 29.93/30.17         ((r3_lattice3 @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ 
% 29.93/30.17           (a_3_4_lattice3 @ sk_A @ sk_B @ X0))
% 29.93/30.17          | (v2_struct_0 @ sk_A)
% 29.93/30.17          | ~ (l3_lattices @ sk_A)
% 29.93/30.17          | (r3_lattice3 @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ 
% 29.93/30.17             (a_3_4_lattice3 @ sk_A @ sk_B @ X0)))),
% 29.93/30.17      inference('sup-', [status(thm)], ['119', '123'])).
% 29.93/30.17  thf('125', plain, ((l3_lattices @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('126', plain,
% 29.93/30.17      (![X0 : $i]:
% 29.93/30.17         ((r3_lattice3 @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ 
% 29.93/30.17           (a_3_4_lattice3 @ sk_A @ sk_B @ X0))
% 29.93/30.17          | (v2_struct_0 @ sk_A)
% 29.93/30.17          | (r3_lattice3 @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ 
% 29.93/30.17             (a_3_4_lattice3 @ sk_A @ sk_B @ X0)))),
% 29.93/30.17      inference('demod', [status(thm)], ['124', '125'])).
% 29.93/30.17  thf('127', plain,
% 29.93/30.17      (![X0 : $i]:
% 29.93/30.17         ((v2_struct_0 @ sk_A)
% 29.93/30.17          | (r3_lattice3 @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ 
% 29.93/30.17             (a_3_4_lattice3 @ sk_A @ sk_B @ X0)))),
% 29.93/30.17      inference('simplify', [status(thm)], ['126'])).
% 29.93/30.17  thf('128', plain, (~ (v2_struct_0 @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('129', plain,
% 29.93/30.17      (![X0 : $i]:
% 29.93/30.17         (r3_lattice3 @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ 
% 29.93/30.17          (a_3_4_lattice3 @ sk_A @ sk_B @ X0))),
% 29.93/30.17      inference('clc', [status(thm)], ['127', '128'])).
% 29.93/30.17  thf('130', plain,
% 29.93/30.17      (![X24 : $i, X25 : $i]:
% 29.93/30.17         (~ (l3_lattices @ X24)
% 29.93/30.17          | (v2_struct_0 @ X24)
% 29.93/30.17          | (m1_subset_1 @ (k16_lattice3 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 29.93/30.17      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 29.93/30.17  thf('131', plain,
% 29.93/30.17      (![X24 : $i, X25 : $i]:
% 29.93/30.17         (~ (l3_lattices @ X24)
% 29.93/30.17          | (v2_struct_0 @ X24)
% 29.93/30.17          | (m1_subset_1 @ (k16_lattice3 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 29.93/30.17      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 29.93/30.17  thf('132', plain,
% 29.93/30.17      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 29.93/30.17         (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X32))
% 29.93/30.17          | ((X31) != (k16_lattice3 @ X32 @ X33))
% 29.93/30.17          | ~ (r3_lattice3 @ X32 @ X34 @ X33)
% 29.93/30.17          | (r3_lattices @ X32 @ X34 @ X31)
% 29.93/30.17          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X32))
% 29.93/30.17          | ~ (l3_lattices @ X32)
% 29.93/30.17          | ~ (v4_lattice3 @ X32)
% 29.93/30.17          | ~ (v10_lattices @ X32)
% 29.93/30.17          | (v2_struct_0 @ X32))),
% 29.93/30.17      inference('cnf', [status(esa)], [t34_lattice3])).
% 29.93/30.17  thf('133', plain,
% 29.93/30.17      (![X32 : $i, X33 : $i, X34 : $i]:
% 29.93/30.17         ((v2_struct_0 @ X32)
% 29.93/30.17          | ~ (v10_lattices @ X32)
% 29.93/30.17          | ~ (v4_lattice3 @ X32)
% 29.93/30.17          | ~ (l3_lattices @ X32)
% 29.93/30.17          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X32))
% 29.93/30.17          | (r3_lattices @ X32 @ X34 @ (k16_lattice3 @ X32 @ X33))
% 29.93/30.17          | ~ (r3_lattice3 @ X32 @ X34 @ X33)
% 29.93/30.17          | ~ (m1_subset_1 @ (k16_lattice3 @ X32 @ X33) @ (u1_struct_0 @ X32)))),
% 29.93/30.17      inference('simplify', [status(thm)], ['132'])).
% 29.93/30.17  thf('134', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.93/30.17         ((v2_struct_0 @ X0)
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | ~ (r3_lattice3 @ X0 @ X2 @ X1)
% 29.93/30.17          | (r3_lattices @ X0 @ X2 @ (k16_lattice3 @ X0 @ X1))
% 29.93/30.17          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | ~ (v4_lattice3 @ X0)
% 29.93/30.17          | ~ (v10_lattices @ X0)
% 29.93/30.17          | (v2_struct_0 @ X0))),
% 29.93/30.17      inference('sup-', [status(thm)], ['131', '133'])).
% 29.93/30.17  thf('135', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.93/30.17         (~ (v10_lattices @ X0)
% 29.93/30.17          | ~ (v4_lattice3 @ X0)
% 29.93/30.17          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 29.93/30.17          | (r3_lattices @ X0 @ X2 @ (k16_lattice3 @ X0 @ X1))
% 29.93/30.17          | ~ (r3_lattice3 @ X0 @ X2 @ X1)
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | (v2_struct_0 @ X0))),
% 29.93/30.17      inference('simplify', [status(thm)], ['134'])).
% 29.93/30.17  thf('136', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.93/30.17         ((v2_struct_0 @ X0)
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | (v2_struct_0 @ X0)
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | ~ (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 29.93/30.17          | (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 29.93/30.17             (k16_lattice3 @ X0 @ X2))
% 29.93/30.17          | ~ (v4_lattice3 @ X0)
% 29.93/30.17          | ~ (v10_lattices @ X0))),
% 29.93/30.17      inference('sup-', [status(thm)], ['130', '135'])).
% 29.93/30.17  thf('137', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.93/30.17         (~ (v10_lattices @ X0)
% 29.93/30.17          | ~ (v4_lattice3 @ X0)
% 29.93/30.17          | (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ 
% 29.93/30.17             (k16_lattice3 @ X0 @ X2))
% 29.93/30.17          | ~ (r3_lattice3 @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 29.93/30.17          | ~ (l3_lattices @ X0)
% 29.93/30.17          | (v2_struct_0 @ X0))),
% 29.93/30.17      inference('simplify', [status(thm)], ['136'])).
% 29.93/30.17  thf('138', plain,
% 29.93/30.17      (![X0 : $i]:
% 29.93/30.17         ((v2_struct_0 @ sk_A)
% 29.93/30.17          | ~ (l3_lattices @ sk_A)
% 29.93/30.17          | (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ 
% 29.93/30.17             (k16_lattice3 @ sk_A @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0)))
% 29.93/30.17          | ~ (v4_lattice3 @ sk_A)
% 29.93/30.17          | ~ (v10_lattices @ sk_A))),
% 29.93/30.17      inference('sup-', [status(thm)], ['129', '137'])).
% 29.93/30.17  thf('139', plain, ((l3_lattices @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('140', plain, ((v4_lattice3 @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('141', plain, ((v10_lattices @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('142', plain,
% 29.93/30.17      (![X0 : $i]:
% 29.93/30.17         ((v2_struct_0 @ sk_A)
% 29.93/30.17          | (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ 
% 29.93/30.17             (k16_lattice3 @ sk_A @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0))))),
% 29.93/30.17      inference('demod', [status(thm)], ['138', '139', '140', '141'])).
% 29.93/30.17  thf('143', plain, (~ (v2_struct_0 @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('144', plain,
% 29.93/30.17      (![X0 : $i]:
% 29.93/30.17         (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ 
% 29.93/30.17          (k16_lattice3 @ sk_A @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0)))),
% 29.93/30.17      inference('clc', [status(thm)], ['142', '143'])).
% 29.93/30.17  thf('145', plain,
% 29.93/30.17      (![X24 : $i, X25 : $i]:
% 29.93/30.17         (~ (l3_lattices @ X24)
% 29.93/30.17          | (v2_struct_0 @ X24)
% 29.93/30.17          | (m1_subset_1 @ (k16_lattice3 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 29.93/30.17      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 29.93/30.17  thf('146', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf(t6_filter_0, axiom,
% 29.93/30.17    (![A:$i]:
% 29.93/30.17     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 29.93/30.17         ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v8_lattices @ A ) & 
% 29.93/30.17         ( v9_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 29.93/30.17       ( ![B:$i]:
% 29.93/30.17         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 29.93/30.17           ( ![C:$i]:
% 29.93/30.17             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 29.93/30.17               ( ![D:$i]:
% 29.93/30.17                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 29.93/30.17                   ( ( ( r3_lattices @ A @ B @ D ) & 
% 29.93/30.17                       ( r3_lattices @ A @ C @ D ) ) =>
% 29.93/30.17                     ( r3_lattices @ A @ ( k3_lattices @ A @ B @ C ) @ D ) ) ) ) ) ) ) ) ))).
% 29.93/30.17  thf('147', plain,
% 29.93/30.17      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 29.93/30.17         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 29.93/30.17          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 29.93/30.17          | (r3_lattices @ X16 @ (k3_lattices @ X16 @ X15 @ X18) @ X17)
% 29.93/30.17          | ~ (r3_lattices @ X16 @ X18 @ X17)
% 29.93/30.17          | ~ (r3_lattices @ X16 @ X15 @ X17)
% 29.93/30.17          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X16))
% 29.93/30.17          | ~ (l3_lattices @ X16)
% 29.93/30.17          | ~ (v9_lattices @ X16)
% 29.93/30.17          | ~ (v8_lattices @ X16)
% 29.93/30.17          | ~ (v6_lattices @ X16)
% 29.93/30.17          | ~ (v5_lattices @ X16)
% 29.93/30.17          | ~ (v4_lattices @ X16)
% 29.93/30.17          | (v2_struct_0 @ X16))),
% 29.93/30.17      inference('cnf', [status(esa)], [t6_filter_0])).
% 29.93/30.17  thf('148', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i]:
% 29.93/30.17         ((v2_struct_0 @ sk_A)
% 29.93/30.17          | ~ (v4_lattices @ sk_A)
% 29.93/30.17          | ~ (v5_lattices @ sk_A)
% 29.93/30.17          | ~ (v6_lattices @ sk_A)
% 29.93/30.17          | ~ (v8_lattices @ sk_A)
% 29.93/30.17          | ~ (v9_lattices @ sk_A)
% 29.93/30.17          | ~ (l3_lattices @ sk_A)
% 29.93/30.17          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 29.93/30.17          | ~ (r3_lattices @ sk_A @ sk_B @ X1)
% 29.93/30.17          | ~ (r3_lattices @ sk_A @ X0 @ X1)
% 29.93/30.17          | (r3_lattices @ sk_A @ (k3_lattices @ sk_A @ sk_B @ X0) @ X1)
% 29.93/30.17          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 29.93/30.17      inference('sup-', [status(thm)], ['146', '147'])).
% 29.93/30.17  thf('149', plain,
% 29.93/30.17      (![X0 : $i]:
% 29.93/30.17         ((v2_struct_0 @ X0)
% 29.93/30.17          | ~ (v10_lattices @ X0)
% 29.93/30.17          | (v4_lattices @ X0)
% 29.93/30.17          | ~ (l3_lattices @ X0))),
% 29.93/30.17      inference('cnf', [status(esa)], [cc1_lattices])).
% 29.93/30.17  thf('150', plain, (~ (v2_struct_0 @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('151', plain,
% 29.93/30.17      ((~ (l3_lattices @ sk_A) | (v4_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 29.93/30.17      inference('sup-', [status(thm)], ['149', '150'])).
% 29.93/30.17  thf('152', plain, ((l3_lattices @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('153', plain, ((v10_lattices @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('154', plain, ((v4_lattices @ sk_A)),
% 29.93/30.17      inference('demod', [status(thm)], ['151', '152', '153'])).
% 29.93/30.17  thf('155', plain,
% 29.93/30.17      (![X0 : $i]:
% 29.93/30.17         ((v2_struct_0 @ X0)
% 29.93/30.17          | ~ (v10_lattices @ X0)
% 29.93/30.17          | (v5_lattices @ X0)
% 29.93/30.17          | ~ (l3_lattices @ X0))),
% 29.93/30.17      inference('cnf', [status(esa)], [cc1_lattices])).
% 29.93/30.17  thf('156', plain, (~ (v2_struct_0 @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('157', plain,
% 29.93/30.17      ((~ (l3_lattices @ sk_A) | (v5_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 29.93/30.17      inference('sup-', [status(thm)], ['155', '156'])).
% 29.93/30.17  thf('158', plain, ((l3_lattices @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('159', plain, ((v10_lattices @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('160', plain, ((v5_lattices @ sk_A)),
% 29.93/30.17      inference('demod', [status(thm)], ['157', '158', '159'])).
% 29.93/30.17  thf('161', plain, ((v6_lattices @ sk_A)),
% 29.93/30.17      inference('demod', [status(thm)], ['65', '66', '67'])).
% 29.93/30.17  thf('162', plain, ((v8_lattices @ sk_A)),
% 29.93/30.17      inference('demod', [status(thm)], ['71', '72', '73'])).
% 29.93/30.17  thf('163', plain, ((v9_lattices @ sk_A)),
% 29.93/30.17      inference('demod', [status(thm)], ['77', '78', '79'])).
% 29.93/30.17  thf('164', plain, ((l3_lattices @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('165', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i]:
% 29.93/30.17         ((v2_struct_0 @ sk_A)
% 29.93/30.17          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 29.93/30.17          | ~ (r3_lattices @ sk_A @ sk_B @ X1)
% 29.93/30.17          | ~ (r3_lattices @ sk_A @ X0 @ X1)
% 29.93/30.17          | (r3_lattices @ sk_A @ (k3_lattices @ sk_A @ sk_B @ X0) @ X1)
% 29.93/30.17          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 29.93/30.17      inference('demod', [status(thm)],
% 29.93/30.17                ['148', '154', '160', '161', '162', '163', '164'])).
% 29.93/30.17  thf('166', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i]:
% 29.93/30.17         ((v2_struct_0 @ sk_A)
% 29.93/30.17          | ~ (l3_lattices @ sk_A)
% 29.93/30.17          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 29.93/30.17          | (r3_lattices @ sk_A @ 
% 29.93/30.17             (k3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0)) @ X1)
% 29.93/30.17          | ~ (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ X1)
% 29.93/30.17          | ~ (r3_lattices @ sk_A @ sk_B @ X1)
% 29.93/30.17          | (v2_struct_0 @ sk_A))),
% 29.93/30.17      inference('sup-', [status(thm)], ['145', '165'])).
% 29.93/30.17  thf('167', plain, ((l3_lattices @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('168', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i]:
% 29.93/30.17         ((v2_struct_0 @ sk_A)
% 29.93/30.17          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 29.93/30.17          | (r3_lattices @ sk_A @ 
% 29.93/30.17             (k3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0)) @ X1)
% 29.93/30.17          | ~ (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ X1)
% 29.93/30.17          | ~ (r3_lattices @ sk_A @ sk_B @ X1)
% 29.93/30.17          | (v2_struct_0 @ sk_A))),
% 29.93/30.17      inference('demod', [status(thm)], ['166', '167'])).
% 29.93/30.17  thf('169', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i]:
% 29.93/30.17         (~ (r3_lattices @ sk_A @ sk_B @ X1)
% 29.93/30.17          | ~ (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ X1)
% 29.93/30.17          | (r3_lattices @ sk_A @ 
% 29.93/30.17             (k3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0)) @ X1)
% 29.93/30.17          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 29.93/30.17          | (v2_struct_0 @ sk_A))),
% 29.93/30.17      inference('simplify', [status(thm)], ['168'])).
% 29.93/30.17  thf('170', plain,
% 29.93/30.17      (![X0 : $i]:
% 29.93/30.17         ((v2_struct_0 @ sk_A)
% 29.93/30.17          | ~ (m1_subset_1 @ 
% 29.93/30.17               (k16_lattice3 @ sk_A @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0)) @ 
% 29.93/30.17               (u1_struct_0 @ sk_A))
% 29.93/30.17          | (r3_lattices @ sk_A @ 
% 29.93/30.17             (k3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0)) @ 
% 29.93/30.17             (k16_lattice3 @ sk_A @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0)))
% 29.93/30.17          | ~ (r3_lattices @ sk_A @ sk_B @ 
% 29.93/30.17               (k16_lattice3 @ sk_A @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0))))),
% 29.93/30.17      inference('sup-', [status(thm)], ['144', '169'])).
% 29.93/30.17  thf('171', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('172', plain,
% 29.93/30.17      (![X19 : $i, X20 : $i, X23 : $i]:
% 29.93/30.17         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 29.93/30.17          | (m1_subset_1 @ (sk_D @ X23 @ X19 @ X20) @ (u1_struct_0 @ X20))
% 29.93/30.17          | (r3_lattice3 @ X20 @ X19 @ X23)
% 29.93/30.17          | ~ (l3_lattices @ X20)
% 29.93/30.17          | (v2_struct_0 @ X20))),
% 29.93/30.17      inference('cnf', [status(esa)], [d16_lattice3])).
% 29.93/30.17  thf('173', plain,
% 29.93/30.17      (![X0 : $i]:
% 29.93/30.17         ((v2_struct_0 @ sk_A)
% 29.93/30.17          | ~ (l3_lattices @ sk_A)
% 29.93/30.17          | (r3_lattice3 @ sk_A @ sk_B @ X0)
% 29.93/30.17          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 29.93/30.17      inference('sup-', [status(thm)], ['171', '172'])).
% 29.93/30.17  thf('174', plain, ((l3_lattices @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('175', plain,
% 29.93/30.17      (![X0 : $i]:
% 29.93/30.17         ((v2_struct_0 @ sk_A)
% 29.93/30.17          | (r3_lattice3 @ sk_A @ sk_B @ X0)
% 29.93/30.17          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 29.93/30.17      inference('demod', [status(thm)], ['173', '174'])).
% 29.93/30.17  thf('176', plain, (~ (v2_struct_0 @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('177', plain,
% 29.93/30.17      (![X0 : $i]:
% 29.93/30.17         ((m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 29.93/30.17          | (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 29.93/30.17      inference('clc', [status(thm)], ['175', '176'])).
% 29.93/30.17  thf('178', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('179', plain,
% 29.93/30.17      (![X19 : $i, X20 : $i, X23 : $i]:
% 29.93/30.17         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 29.93/30.17          | (r2_hidden @ (sk_D @ X23 @ X19 @ X20) @ X23)
% 29.93/30.17          | (r3_lattice3 @ X20 @ X19 @ X23)
% 29.93/30.17          | ~ (l3_lattices @ X20)
% 29.93/30.17          | (v2_struct_0 @ X20))),
% 29.93/30.17      inference('cnf', [status(esa)], [d16_lattice3])).
% 29.93/30.17  thf('180', plain,
% 29.93/30.17      (![X0 : $i]:
% 29.93/30.17         ((v2_struct_0 @ sk_A)
% 29.93/30.17          | ~ (l3_lattices @ sk_A)
% 29.93/30.17          | (r3_lattice3 @ sk_A @ sk_B @ X0)
% 29.93/30.17          | (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ X0))),
% 29.93/30.17      inference('sup-', [status(thm)], ['178', '179'])).
% 29.93/30.17  thf('181', plain, ((l3_lattices @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('182', plain,
% 29.93/30.17      (![X0 : $i]:
% 29.93/30.17         ((v2_struct_0 @ sk_A)
% 29.93/30.17          | (r3_lattice3 @ sk_A @ sk_B @ X0)
% 29.93/30.17          | (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ X0))),
% 29.93/30.17      inference('demod', [status(thm)], ['180', '181'])).
% 29.93/30.17  thf('183', plain, (~ (v2_struct_0 @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('184', plain,
% 29.93/30.17      (![X0 : $i]:
% 29.93/30.17         ((r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ X0)
% 29.93/30.17          | (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 29.93/30.17      inference('clc', [status(thm)], ['182', '183'])).
% 29.93/30.17  thf('185', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i]:
% 29.93/30.17         (((X1) = (k3_lattices @ sk_A @ sk_B @ (sk_E @ X0 @ sk_B @ sk_A @ X1)))
% 29.93/30.17          | ~ (r2_hidden @ X1 @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0)))),
% 29.93/30.17      inference('clc', [status(thm)], ['12', '13'])).
% 29.93/30.17  thf('186', plain,
% 29.93/30.17      (![X0 : $i]:
% 29.93/30.17         ((r3_lattice3 @ sk_A @ sk_B @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0))
% 29.93/30.17          | ((sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0) @ sk_B @ sk_A)
% 29.93/30.17              = (k3_lattices @ sk_A @ sk_B @ 
% 29.93/30.17                 (sk_E @ X0 @ sk_B @ sk_A @ 
% 29.93/30.17                  (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0) @ sk_B @ sk_A)))))),
% 29.93/30.17      inference('sup-', [status(thm)], ['184', '185'])).
% 29.93/30.17  thf('187', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('188', plain,
% 29.93/30.17      (![X0 : $i]:
% 29.93/30.17         ((r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ X0)
% 29.93/30.17          | (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 29.93/30.17      inference('clc', [status(thm)], ['182', '183'])).
% 29.93/30.17  thf('189', plain,
% 29.93/30.17      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 29.93/30.17         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 29.93/30.17          | ~ (l3_lattices @ X27)
% 29.93/30.17          | ~ (v4_lattice3 @ X27)
% 29.93/30.17          | ~ (v10_lattices @ X27)
% 29.93/30.17          | (v2_struct_0 @ X27)
% 29.93/30.17          | (m1_subset_1 @ (sk_E @ X29 @ X26 @ X27 @ X28) @ (u1_struct_0 @ X27))
% 29.93/30.17          | ~ (r2_hidden @ X28 @ (a_3_4_lattice3 @ X27 @ X26 @ X29)))),
% 29.93/30.17      inference('cnf', [status(esa)], [fraenkel_a_3_4_lattice3])).
% 29.93/30.17  thf('190', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.93/30.17         ((r3_lattice3 @ sk_A @ sk_B @ (a_3_4_lattice3 @ X2 @ X1 @ X0))
% 29.93/30.17          | (m1_subset_1 @ 
% 29.93/30.17             (sk_E @ X0 @ X1 @ X2 @ 
% 29.93/30.17              (sk_D @ (a_3_4_lattice3 @ X2 @ X1 @ X0) @ sk_B @ sk_A)) @ 
% 29.93/30.17             (u1_struct_0 @ X2))
% 29.93/30.17          | (v2_struct_0 @ X2)
% 29.93/30.17          | ~ (v10_lattices @ X2)
% 29.93/30.17          | ~ (v4_lattice3 @ X2)
% 29.93/30.17          | ~ (l3_lattices @ X2)
% 29.93/30.17          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2)))),
% 29.93/30.17      inference('sup-', [status(thm)], ['188', '189'])).
% 29.93/30.17  thf('191', plain,
% 29.93/30.17      (![X0 : $i]:
% 29.93/30.17         (~ (l3_lattices @ sk_A)
% 29.93/30.17          | ~ (v4_lattice3 @ sk_A)
% 29.93/30.17          | ~ (v10_lattices @ sk_A)
% 29.93/30.17          | (v2_struct_0 @ sk_A)
% 29.93/30.17          | (m1_subset_1 @ 
% 29.93/30.17             (sk_E @ X0 @ sk_B @ sk_A @ 
% 29.93/30.17              (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0) @ sk_B @ sk_A)) @ 
% 29.93/30.17             (u1_struct_0 @ sk_A))
% 29.93/30.17          | (r3_lattice3 @ sk_A @ sk_B @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0)))),
% 29.93/30.17      inference('sup-', [status(thm)], ['187', '190'])).
% 29.93/30.17  thf('192', plain, ((l3_lattices @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('193', plain, ((v4_lattice3 @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('194', plain, ((v10_lattices @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('195', plain,
% 29.93/30.17      (![X0 : $i]:
% 29.93/30.17         ((v2_struct_0 @ sk_A)
% 29.93/30.17          | (m1_subset_1 @ 
% 29.93/30.17             (sk_E @ X0 @ sk_B @ sk_A @ 
% 29.93/30.17              (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0) @ sk_B @ sk_A)) @ 
% 29.93/30.17             (u1_struct_0 @ sk_A))
% 29.93/30.17          | (r3_lattice3 @ sk_A @ sk_B @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0)))),
% 29.93/30.17      inference('demod', [status(thm)], ['191', '192', '193', '194'])).
% 29.93/30.17  thf('196', plain, (~ (v2_struct_0 @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('197', plain,
% 29.93/30.17      (![X0 : $i]:
% 29.93/30.17         ((r3_lattice3 @ sk_A @ sk_B @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0))
% 29.93/30.17          | (m1_subset_1 @ 
% 29.93/30.17             (sk_E @ X0 @ sk_B @ sk_A @ 
% 29.93/30.17              (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0) @ sk_B @ sk_A)) @ 
% 29.93/30.17             (u1_struct_0 @ sk_A)))),
% 29.93/30.17      inference('clc', [status(thm)], ['195', '196'])).
% 29.93/30.17  thf('198', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf(commutativity_k3_lattices, axiom,
% 29.93/30.17    (![A:$i,B:$i,C:$i]:
% 29.93/30.17     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 29.93/30.17         ( l2_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 29.93/30.17         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 29.93/30.17       ( ( k3_lattices @ A @ B @ C ) = ( k3_lattices @ A @ C @ B ) ) ))).
% 29.93/30.17  thf('199', plain,
% 29.93/30.17      (![X1 : $i, X2 : $i, X3 : $i]:
% 29.93/30.17         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 29.93/30.17          | ~ (l2_lattices @ X2)
% 29.93/30.17          | ~ (v4_lattices @ X2)
% 29.93/30.17          | (v2_struct_0 @ X2)
% 29.93/30.17          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 29.93/30.17          | ((k3_lattices @ X2 @ X1 @ X3) = (k3_lattices @ X2 @ X3 @ X1)))),
% 29.93/30.17      inference('cnf', [status(esa)], [commutativity_k3_lattices])).
% 29.93/30.17  thf('200', plain,
% 29.93/30.17      (![X0 : $i]:
% 29.93/30.17         (((k3_lattices @ sk_A @ sk_B @ X0) = (k3_lattices @ sk_A @ X0 @ sk_B))
% 29.93/30.17          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 29.93/30.17          | (v2_struct_0 @ sk_A)
% 29.93/30.17          | ~ (v4_lattices @ sk_A)
% 29.93/30.17          | ~ (l2_lattices @ sk_A))),
% 29.93/30.17      inference('sup-', [status(thm)], ['198', '199'])).
% 29.93/30.17  thf('201', plain, ((v4_lattices @ sk_A)),
% 29.93/30.17      inference('demod', [status(thm)], ['151', '152', '153'])).
% 29.93/30.17  thf('202', plain, ((l3_lattices @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf(dt_l3_lattices, axiom,
% 29.93/30.17    (![A:$i]:
% 29.93/30.17     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 29.93/30.17  thf('203', plain, (![X4 : $i]: ((l2_lattices @ X4) | ~ (l3_lattices @ X4))),
% 29.93/30.17      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 29.93/30.17  thf('204', plain, ((l2_lattices @ sk_A)),
% 29.93/30.17      inference('sup-', [status(thm)], ['202', '203'])).
% 29.93/30.17  thf('205', plain,
% 29.93/30.17      (![X0 : $i]:
% 29.93/30.17         (((k3_lattices @ sk_A @ sk_B @ X0) = (k3_lattices @ sk_A @ X0 @ sk_B))
% 29.93/30.17          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 29.93/30.17          | (v2_struct_0 @ sk_A))),
% 29.93/30.17      inference('demod', [status(thm)], ['200', '201', '204'])).
% 29.93/30.17  thf('206', plain, (~ (v2_struct_0 @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('207', plain,
% 29.93/30.17      (![X0 : $i]:
% 29.93/30.17         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 29.93/30.17          | ((k3_lattices @ sk_A @ sk_B @ X0)
% 29.93/30.17              = (k3_lattices @ sk_A @ X0 @ sk_B)))),
% 29.93/30.17      inference('clc', [status(thm)], ['205', '206'])).
% 29.93/30.17  thf('208', plain,
% 29.93/30.17      (![X0 : $i]:
% 29.93/30.17         ((r3_lattice3 @ sk_A @ sk_B @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0))
% 29.93/30.17          | ((k3_lattices @ sk_A @ sk_B @ 
% 29.93/30.17              (sk_E @ X0 @ sk_B @ sk_A @ 
% 29.93/30.17               (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0) @ sk_B @ sk_A)))
% 29.93/30.17              = (k3_lattices @ sk_A @ 
% 29.93/30.17                 (sk_E @ X0 @ sk_B @ sk_A @ 
% 29.93/30.17                  (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0) @ sk_B @ sk_A)) @ 
% 29.93/30.17                 sk_B)))),
% 29.93/30.17      inference('sup-', [status(thm)], ['197', '207'])).
% 29.93/30.17  thf('209', plain,
% 29.93/30.17      (![X0 : $i]:
% 29.93/30.17         ((r3_lattice3 @ sk_A @ sk_B @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0))
% 29.93/30.17          | (m1_subset_1 @ 
% 29.93/30.17             (sk_E @ X0 @ sk_B @ sk_A @ 
% 29.93/30.17              (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0) @ sk_B @ sk_A)) @ 
% 29.93/30.17             (u1_struct_0 @ sk_A)))),
% 29.93/30.17      inference('clc', [status(thm)], ['195', '196'])).
% 29.93/30.17  thf('210', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('211', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('212', plain,
% 29.93/30.17      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 29.93/30.17         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 29.93/30.17          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 29.93/30.17          | (r3_lattices @ X12 @ X11 @ (k3_lattices @ X12 @ X13 @ X14))
% 29.93/30.17          | ~ (r3_lattices @ X12 @ X11 @ X14)
% 29.93/30.17          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X12))
% 29.93/30.17          | ~ (l3_lattices @ X12)
% 29.93/30.17          | ~ (v10_lattices @ X12)
% 29.93/30.17          | (v2_struct_0 @ X12))),
% 29.93/30.17      inference('cnf', [status(esa)], [t3_filter_0])).
% 29.93/30.17  thf('213', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i]:
% 29.93/30.17         ((v2_struct_0 @ sk_A)
% 29.93/30.17          | ~ (v10_lattices @ sk_A)
% 29.93/30.17          | ~ (l3_lattices @ sk_A)
% 29.93/30.17          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 29.93/30.17          | ~ (r3_lattices @ sk_A @ sk_B @ X0)
% 29.93/30.17          | (r3_lattices @ sk_A @ sk_B @ (k3_lattices @ sk_A @ X1 @ X0))
% 29.93/30.17          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 29.93/30.17      inference('sup-', [status(thm)], ['211', '212'])).
% 29.93/30.17  thf('214', plain, ((v10_lattices @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('215', plain, ((l3_lattices @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('216', plain,
% 29.93/30.17      (![X0 : $i, X1 : $i]:
% 29.93/30.17         ((v2_struct_0 @ sk_A)
% 29.93/30.17          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 29.93/30.17          | ~ (r3_lattices @ sk_A @ sk_B @ X0)
% 29.93/30.17          | (r3_lattices @ sk_A @ sk_B @ (k3_lattices @ sk_A @ X1 @ X0))
% 29.93/30.17          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 29.93/30.17      inference('demod', [status(thm)], ['213', '214', '215'])).
% 29.93/30.17  thf('217', plain,
% 29.93/30.17      (![X0 : $i]:
% 29.93/30.17         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 29.93/30.17          | (r3_lattices @ sk_A @ sk_B @ (k3_lattices @ sk_A @ X0 @ sk_B))
% 29.93/30.17          | ~ (r3_lattices @ sk_A @ sk_B @ sk_B)
% 29.93/30.17          | (v2_struct_0 @ sk_A))),
% 29.93/30.17      inference('sup-', [status(thm)], ['210', '216'])).
% 29.93/30.17  thf('218', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('219', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf(reflexivity_r3_lattices, axiom,
% 29.93/30.17    (![A:$i,B:$i,C:$i]:
% 29.93/30.17     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 29.93/30.17         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 29.93/30.17         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 29.93/30.17         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 29.93/30.17       ( r3_lattices @ A @ B @ B ) ))).
% 29.93/30.17  thf('220', plain,
% 29.93/30.17      (![X8 : $i, X9 : $i, X10 : $i]:
% 29.93/30.17         ((r3_lattices @ X8 @ X9 @ X9)
% 29.93/30.17          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 29.93/30.17          | ~ (l3_lattices @ X8)
% 29.93/30.17          | ~ (v9_lattices @ X8)
% 29.93/30.17          | ~ (v8_lattices @ X8)
% 29.93/30.17          | ~ (v6_lattices @ X8)
% 29.93/30.17          | (v2_struct_0 @ X8)
% 29.93/30.17          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X8)))),
% 29.93/30.17      inference('cnf', [status(esa)], [reflexivity_r3_lattices])).
% 29.93/30.17  thf('221', plain,
% 29.93/30.17      (![X0 : $i]:
% 29.93/30.17         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 29.93/30.17          | (v2_struct_0 @ sk_A)
% 29.93/30.17          | ~ (v6_lattices @ sk_A)
% 29.93/30.17          | ~ (v8_lattices @ sk_A)
% 29.93/30.17          | ~ (v9_lattices @ sk_A)
% 29.93/30.17          | ~ (l3_lattices @ sk_A)
% 29.93/30.17          | (r3_lattices @ sk_A @ sk_B @ sk_B))),
% 29.93/30.17      inference('sup-', [status(thm)], ['219', '220'])).
% 29.93/30.17  thf('222', plain, ((v6_lattices @ sk_A)),
% 29.93/30.17      inference('demod', [status(thm)], ['65', '66', '67'])).
% 29.93/30.17  thf('223', plain, ((v8_lattices @ sk_A)),
% 29.93/30.17      inference('demod', [status(thm)], ['71', '72', '73'])).
% 29.93/30.17  thf('224', plain, ((v9_lattices @ sk_A)),
% 29.93/30.17      inference('demod', [status(thm)], ['77', '78', '79'])).
% 29.93/30.17  thf('225', plain, ((l3_lattices @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.93/30.17  thf('226', plain,
% 29.93/30.17      (![X0 : $i]:
% 29.93/30.17         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 29.93/30.17          | (v2_struct_0 @ sk_A)
% 29.93/30.17          | (r3_lattices @ sk_A @ sk_B @ sk_B))),
% 29.93/30.17      inference('demod', [status(thm)], ['221', '222', '223', '224', '225'])).
% 29.93/30.17  thf('227', plain, (~ (v2_struct_0 @ sk_A)),
% 29.93/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.00/30.17  thf('228', plain,
% 30.00/30.17      (![X0 : $i]:
% 30.00/30.17         ((r3_lattices @ sk_A @ sk_B @ sk_B)
% 30.00/30.17          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 30.00/30.17      inference('clc', [status(thm)], ['226', '227'])).
% 30.00/30.17  thf('229', plain, ((r3_lattices @ sk_A @ sk_B @ sk_B)),
% 30.00/30.17      inference('sup-', [status(thm)], ['218', '228'])).
% 30.00/30.17  thf('230', plain,
% 30.00/30.17      (![X0 : $i]:
% 30.00/30.17         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 30.00/30.17          | (r3_lattices @ sk_A @ sk_B @ (k3_lattices @ sk_A @ X0 @ sk_B))
% 30.00/30.17          | (v2_struct_0 @ sk_A))),
% 30.00/30.17      inference('demod', [status(thm)], ['217', '229'])).
% 30.00/30.17  thf('231', plain, (~ (v2_struct_0 @ sk_A)),
% 30.00/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.00/30.17  thf('232', plain,
% 30.00/30.17      (![X0 : $i]:
% 30.00/30.17         ((r3_lattices @ sk_A @ sk_B @ (k3_lattices @ sk_A @ X0 @ sk_B))
% 30.00/30.17          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 30.00/30.17      inference('clc', [status(thm)], ['230', '231'])).
% 30.00/30.17  thf('233', plain,
% 30.00/30.17      (![X0 : $i]:
% 30.00/30.17         ((r3_lattice3 @ sk_A @ sk_B @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0))
% 30.00/30.17          | (r3_lattices @ sk_A @ sk_B @ 
% 30.00/30.17             (k3_lattices @ sk_A @ 
% 30.00/30.17              (sk_E @ X0 @ sk_B @ sk_A @ 
% 30.00/30.17               (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0) @ sk_B @ sk_A)) @ 
% 30.00/30.17              sk_B)))),
% 30.00/30.17      inference('sup-', [status(thm)], ['209', '232'])).
% 30.00/30.17  thf('234', plain,
% 30.00/30.17      (![X0 : $i]:
% 30.00/30.17         ((r3_lattices @ sk_A @ sk_B @ 
% 30.00/30.17           (k3_lattices @ sk_A @ sk_B @ 
% 30.00/30.17            (sk_E @ X0 @ sk_B @ sk_A @ 
% 30.00/30.17             (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0) @ sk_B @ sk_A))))
% 30.00/30.17          | (r3_lattice3 @ sk_A @ sk_B @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0))
% 30.00/30.17          | (r3_lattice3 @ sk_A @ sk_B @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0)))),
% 30.00/30.17      inference('sup+', [status(thm)], ['208', '233'])).
% 30.00/30.17  thf('235', plain,
% 30.00/30.17      (![X0 : $i]:
% 30.00/30.17         ((r3_lattice3 @ sk_A @ sk_B @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0))
% 30.00/30.17          | (r3_lattices @ sk_A @ sk_B @ 
% 30.00/30.17             (k3_lattices @ sk_A @ sk_B @ 
% 30.00/30.17              (sk_E @ X0 @ sk_B @ sk_A @ 
% 30.00/30.17               (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0) @ sk_B @ sk_A)))))),
% 30.00/30.17      inference('simplify', [status(thm)], ['234'])).
% 30.00/30.17  thf('236', plain,
% 30.00/30.17      (![X0 : $i]:
% 30.00/30.17         ((r3_lattices @ sk_A @ sk_B @ 
% 30.00/30.17           (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0) @ sk_B @ sk_A))
% 30.00/30.17          | (r3_lattice3 @ sk_A @ sk_B @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0))
% 30.00/30.17          | (r3_lattice3 @ sk_A @ sk_B @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0)))),
% 30.00/30.17      inference('sup+', [status(thm)], ['186', '235'])).
% 30.00/30.17  thf('237', plain,
% 30.00/30.17      (![X0 : $i]:
% 30.00/30.17         ((r3_lattice3 @ sk_A @ sk_B @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0))
% 30.00/30.17          | (r3_lattices @ sk_A @ sk_B @ 
% 30.00/30.17             (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0) @ sk_B @ sk_A)))),
% 30.00/30.17      inference('simplify', [status(thm)], ['236'])).
% 30.00/30.17  thf('238', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 30.00/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.00/30.17  thf('239', plain,
% 30.00/30.17      (![X5 : $i, X6 : $i, X7 : $i]:
% 30.00/30.17         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 30.00/30.17          | ~ (l3_lattices @ X6)
% 30.00/30.17          | ~ (v9_lattices @ X6)
% 30.00/30.17          | ~ (v8_lattices @ X6)
% 30.00/30.17          | ~ (v6_lattices @ X6)
% 30.00/30.17          | (v2_struct_0 @ X6)
% 30.00/30.17          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 30.00/30.17          | (r1_lattices @ X6 @ X5 @ X7)
% 30.00/30.17          | ~ (r3_lattices @ X6 @ X5 @ X7))),
% 30.00/30.17      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 30.00/30.17  thf('240', plain,
% 30.00/30.17      (![X0 : $i]:
% 30.00/30.17         (~ (r3_lattices @ sk_A @ sk_B @ X0)
% 30.00/30.17          | (r1_lattices @ sk_A @ sk_B @ X0)
% 30.00/30.17          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 30.00/30.17          | (v2_struct_0 @ sk_A)
% 30.00/30.17          | ~ (v6_lattices @ sk_A)
% 30.00/30.17          | ~ (v8_lattices @ sk_A)
% 30.00/30.17          | ~ (v9_lattices @ sk_A)
% 30.00/30.17          | ~ (l3_lattices @ sk_A))),
% 30.00/30.17      inference('sup-', [status(thm)], ['238', '239'])).
% 30.00/30.17  thf('241', plain, ((v6_lattices @ sk_A)),
% 30.00/30.17      inference('demod', [status(thm)], ['65', '66', '67'])).
% 30.00/30.17  thf('242', plain, ((v8_lattices @ sk_A)),
% 30.00/30.17      inference('demod', [status(thm)], ['71', '72', '73'])).
% 30.00/30.17  thf('243', plain, ((v9_lattices @ sk_A)),
% 30.00/30.17      inference('demod', [status(thm)], ['77', '78', '79'])).
% 30.00/30.17  thf('244', plain, ((l3_lattices @ sk_A)),
% 30.00/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.00/30.17  thf('245', plain,
% 30.00/30.17      (![X0 : $i]:
% 30.00/30.17         (~ (r3_lattices @ sk_A @ sk_B @ X0)
% 30.00/30.17          | (r1_lattices @ sk_A @ sk_B @ X0)
% 30.00/30.17          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 30.00/30.17          | (v2_struct_0 @ sk_A))),
% 30.00/30.17      inference('demod', [status(thm)], ['240', '241', '242', '243', '244'])).
% 30.00/30.17  thf('246', plain,
% 30.00/30.17      (![X0 : $i]:
% 30.00/30.17         ((r3_lattice3 @ sk_A @ sk_B @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0))
% 30.00/30.17          | (v2_struct_0 @ sk_A)
% 30.00/30.17          | ~ (m1_subset_1 @ 
% 30.00/30.17               (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0) @ sk_B @ sk_A) @ 
% 30.00/30.17               (u1_struct_0 @ sk_A))
% 30.00/30.17          | (r1_lattices @ sk_A @ sk_B @ 
% 30.00/30.17             (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0) @ sk_B @ sk_A)))),
% 30.00/30.17      inference('sup-', [status(thm)], ['237', '245'])).
% 30.00/30.17  thf('247', plain,
% 30.00/30.17      (![X0 : $i]:
% 30.00/30.17         ((r3_lattice3 @ sk_A @ sk_B @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0))
% 30.00/30.17          | (r1_lattices @ sk_A @ sk_B @ 
% 30.00/30.17             (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0) @ sk_B @ sk_A))
% 30.00/30.17          | (v2_struct_0 @ sk_A)
% 30.00/30.17          | (r3_lattice3 @ sk_A @ sk_B @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0)))),
% 30.00/30.17      inference('sup-', [status(thm)], ['177', '246'])).
% 30.00/30.17  thf('248', plain,
% 30.00/30.17      (![X0 : $i]:
% 30.00/30.17         ((v2_struct_0 @ sk_A)
% 30.00/30.17          | (r1_lattices @ sk_A @ sk_B @ 
% 30.00/30.17             (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0) @ sk_B @ sk_A))
% 30.00/30.17          | (r3_lattice3 @ sk_A @ sk_B @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0)))),
% 30.00/30.17      inference('simplify', [status(thm)], ['247'])).
% 30.00/30.17  thf('249', plain, (~ (v2_struct_0 @ sk_A)),
% 30.00/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.00/30.17  thf('250', plain,
% 30.00/30.17      (![X0 : $i]:
% 30.00/30.17         ((r3_lattice3 @ sk_A @ sk_B @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0))
% 30.00/30.17          | (r1_lattices @ sk_A @ sk_B @ 
% 30.00/30.17             (sk_D @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0) @ sk_B @ sk_A)))),
% 30.00/30.17      inference('clc', [status(thm)], ['248', '249'])).
% 30.00/30.17  thf('251', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 30.00/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.00/30.17  thf('252', plain,
% 30.00/30.17      (![X19 : $i, X20 : $i, X23 : $i]:
% 30.00/30.17         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 30.00/30.17          | ~ (r1_lattices @ X20 @ X19 @ (sk_D @ X23 @ X19 @ X20))
% 30.00/30.17          | (r3_lattice3 @ X20 @ X19 @ X23)
% 30.00/30.17          | ~ (l3_lattices @ X20)
% 30.00/30.17          | (v2_struct_0 @ X20))),
% 30.00/30.17      inference('cnf', [status(esa)], [d16_lattice3])).
% 30.00/30.17  thf('253', plain,
% 30.00/30.17      (![X0 : $i]:
% 30.00/30.17         ((v2_struct_0 @ sk_A)
% 30.00/30.17          | ~ (l3_lattices @ sk_A)
% 30.00/30.17          | (r3_lattice3 @ sk_A @ sk_B @ X0)
% 30.00/30.17          | ~ (r1_lattices @ sk_A @ sk_B @ (sk_D @ X0 @ sk_B @ sk_A)))),
% 30.00/30.17      inference('sup-', [status(thm)], ['251', '252'])).
% 30.00/30.17  thf('254', plain, ((l3_lattices @ sk_A)),
% 30.00/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.00/30.17  thf('255', plain,
% 30.00/30.17      (![X0 : $i]:
% 30.00/30.17         ((v2_struct_0 @ sk_A)
% 30.00/30.17          | (r3_lattice3 @ sk_A @ sk_B @ X0)
% 30.00/30.17          | ~ (r1_lattices @ sk_A @ sk_B @ (sk_D @ X0 @ sk_B @ sk_A)))),
% 30.00/30.17      inference('demod', [status(thm)], ['253', '254'])).
% 30.00/30.17  thf('256', plain, (~ (v2_struct_0 @ sk_A)),
% 30.00/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.00/30.17  thf('257', plain,
% 30.00/30.17      (![X0 : $i]:
% 30.00/30.17         (~ (r1_lattices @ sk_A @ sk_B @ (sk_D @ X0 @ sk_B @ sk_A))
% 30.00/30.17          | (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 30.00/30.17      inference('clc', [status(thm)], ['255', '256'])).
% 30.00/30.17  thf('258', plain,
% 30.00/30.17      (![X0 : $i]:
% 30.00/30.17         (r3_lattice3 @ sk_A @ sk_B @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0))),
% 30.00/30.17      inference('clc', [status(thm)], ['250', '257'])).
% 30.00/30.17  thf('259', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 30.00/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.00/30.17  thf('260', plain,
% 30.00/30.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.00/30.17         (~ (v10_lattices @ X0)
% 30.00/30.17          | ~ (v4_lattice3 @ X0)
% 30.00/30.17          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 30.00/30.17          | (r3_lattices @ X0 @ X2 @ (k16_lattice3 @ X0 @ X1))
% 30.00/30.17          | ~ (r3_lattice3 @ X0 @ X2 @ X1)
% 30.00/30.17          | ~ (l3_lattices @ X0)
% 30.00/30.17          | (v2_struct_0 @ X0))),
% 30.00/30.17      inference('simplify', [status(thm)], ['134'])).
% 30.00/30.17  thf('261', plain,
% 30.00/30.17      (![X0 : $i]:
% 30.00/30.17         ((v2_struct_0 @ sk_A)
% 30.00/30.17          | ~ (l3_lattices @ sk_A)
% 30.00/30.17          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0)
% 30.00/30.17          | (r3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0))
% 30.00/30.17          | ~ (v4_lattice3 @ sk_A)
% 30.00/30.17          | ~ (v10_lattices @ sk_A))),
% 30.00/30.17      inference('sup-', [status(thm)], ['259', '260'])).
% 30.00/30.17  thf('262', plain, ((l3_lattices @ sk_A)),
% 30.00/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.00/30.17  thf('263', plain, ((v4_lattice3 @ sk_A)),
% 30.00/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.00/30.17  thf('264', plain, ((v10_lattices @ sk_A)),
% 30.00/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.00/30.17  thf('265', plain,
% 30.00/30.17      (![X0 : $i]:
% 30.00/30.17         ((v2_struct_0 @ sk_A)
% 30.00/30.17          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0)
% 30.00/30.17          | (r3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0)))),
% 30.00/30.17      inference('demod', [status(thm)], ['261', '262', '263', '264'])).
% 30.00/30.17  thf('266', plain, (~ (v2_struct_0 @ sk_A)),
% 30.00/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.00/30.17  thf('267', plain,
% 30.00/30.17      (![X0 : $i]:
% 30.00/30.17         ((r3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0))
% 30.00/30.17          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 30.00/30.17      inference('clc', [status(thm)], ['265', '266'])).
% 30.00/30.17  thf('268', plain,
% 30.00/30.17      (![X0 : $i]:
% 30.00/30.17         (r3_lattices @ sk_A @ sk_B @ 
% 30.00/30.17          (k16_lattice3 @ sk_A @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0)))),
% 30.00/30.17      inference('sup-', [status(thm)], ['258', '267'])).
% 30.00/30.17  thf('269', plain,
% 30.00/30.17      (![X0 : $i]:
% 30.00/30.17         ((v2_struct_0 @ sk_A)
% 30.00/30.17          | ~ (m1_subset_1 @ 
% 30.00/30.17               (k16_lattice3 @ sk_A @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0)) @ 
% 30.00/30.17               (u1_struct_0 @ sk_A))
% 30.00/30.17          | (r3_lattices @ sk_A @ 
% 30.00/30.17             (k3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0)) @ 
% 30.00/30.17             (k16_lattice3 @ sk_A @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0))))),
% 30.00/30.17      inference('demod', [status(thm)], ['170', '268'])).
% 30.00/30.17  thf('270', plain, (~ (v2_struct_0 @ sk_A)),
% 30.00/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.00/30.17  thf('271', plain,
% 30.00/30.17      (![X0 : $i]:
% 30.00/30.17         ((r3_lattices @ sk_A @ 
% 30.00/30.17           (k3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0)) @ 
% 30.00/30.17           (k16_lattice3 @ sk_A @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0)))
% 30.00/30.17          | ~ (m1_subset_1 @ 
% 30.00/30.17               (k16_lattice3 @ sk_A @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0)) @ 
% 30.00/30.17               (u1_struct_0 @ sk_A)))),
% 30.00/30.17      inference('clc', [status(thm)], ['269', '270'])).
% 30.00/30.17  thf('272', plain,
% 30.00/30.17      (![X0 : $i]:
% 30.00/30.17         ((v2_struct_0 @ sk_A)
% 30.00/30.17          | ~ (l3_lattices @ sk_A)
% 30.00/30.17          | (r3_lattices @ sk_A @ 
% 30.00/30.17             (k3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0)) @ 
% 30.00/30.17             (k16_lattice3 @ sk_A @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0))))),
% 30.00/30.17      inference('sup-', [status(thm)], ['1', '271'])).
% 30.00/30.17  thf('273', plain, ((l3_lattices @ sk_A)),
% 30.00/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.00/30.17  thf('274', plain,
% 30.00/30.17      (![X0 : $i]:
% 30.00/30.17         ((v2_struct_0 @ sk_A)
% 30.00/30.17          | (r3_lattices @ sk_A @ 
% 30.00/30.17             (k3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0)) @ 
% 30.00/30.17             (k16_lattice3 @ sk_A @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0))))),
% 30.00/30.17      inference('demod', [status(thm)], ['272', '273'])).
% 30.00/30.17  thf('275', plain, (~ (v2_struct_0 @ sk_A)),
% 30.00/30.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.00/30.17  thf('276', plain,
% 30.00/30.17      (![X0 : $i]:
% 30.00/30.17         (r3_lattices @ sk_A @ 
% 30.00/30.17          (k3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0)) @ 
% 30.00/30.17          (k16_lattice3 @ sk_A @ (a_3_4_lattice3 @ sk_A @ sk_B @ X0)))),
% 30.00/30.17      inference('clc', [status(thm)], ['274', '275'])).
% 30.00/30.17  thf('277', plain, ($false), inference('demod', [status(thm)], ['0', '276'])).
% 30.00/30.17  
% 30.00/30.17  % SZS output end Refutation
% 30.00/30.17  
% 30.00/30.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
