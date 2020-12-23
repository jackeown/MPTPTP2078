%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WXhPBxhebe

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 311 expanded)
%              Number of leaves         :   35 ( 106 expanded)
%              Depth                    :   15
%              Number of atoms          : 1457 (4428 expanded)
%              Number of equality atoms :   46 ( 160 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r4_lattice3_type,type,(
    r4_lattice3: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(k1_lattices_type,type,(
    k1_lattices: $i > $i > $i > $i )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(t41_lattice3,conjecture,(
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
                  & ( r4_lattice3 @ A @ B @ C ) )
               => ( ( k15_lattice3 @ A @ C )
                  = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t41_lattice3])).

thf('0',plain,(
    r4_lattice3 @ sk_A @ sk_B_2 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k15_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) ),
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

thf('3',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v10_lattices @ X11 )
      | ~ ( v4_lattice3 @ X11 )
      | ~ ( l3_lattices @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( X12
       != ( k15_lattice3 @ X11 @ X13 ) )
      | ~ ( r4_lattice3 @ X11 @ X14 @ X13 )
      | ( r1_lattices @ X11 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l3_lattices @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('4',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X11 ) )
      | ( r1_lattices @ X11 @ ( k15_lattice3 @ X11 @ X13 ) @ X14 )
      | ~ ( r4_lattice3 @ X11 @ X14 @ X13 )
      | ~ ( m1_subset_1 @ ( k15_lattice3 @ X11 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( l3_lattices @ X11 )
      | ~ ( v4_lattice3 @ X11 )
      | ~ ( v10_lattices @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
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
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r4_lattice3 @ X0 @ X2 @ X1 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( r4_lattice3 @ sk_A @ sk_B_2 @ X0 )
      | ( r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r4_lattice3 @ sk_A @ sk_B_2 @ X0 )
      | ( r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B_2 )
      | ~ ( r4_lattice3 @ sk_A @ sk_B_2 @ X0 ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_C_2 ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['0','13'])).

thf('15',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf(d3_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l2_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_lattices @ A @ B @ C )
              <=> ( ( k1_lattices @ A @ B @ C )
                  = C ) ) ) ) ) )).

thf('16',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( r1_lattices @ X2 @ X1 @ X3 )
      | ( ( k1_lattices @ X2 @ X1 @ X3 )
        = X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l2_lattices @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_lattices])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( ( k1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
        = X2 )
      | ~ ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( ( k1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l2_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_C_2 ) @ sk_B_2 )
      = sk_B_2 ) ),
    inference('sup-',[status(thm)],['14','18'])).

thf('20',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('22',plain,(
    ! [X7: $i] :
      ( ( l2_lattices @ X7 )
      | ~ ( l3_lattices @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('23',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_C_2 ) @ sk_B_2 )
      = sk_B_2 ) ),
    inference(demod,[status(thm)],['19','20','23','24'])).

thf('26',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_C_2 ) @ sk_B_2 )
    = sk_B_2 ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('29',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( ( v9_lattices @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( k2_lattices @ A @ B @ ( k1_lattices @ A @ B @ C ) )
                  = B ) ) ) ) ) )).

thf('30',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v9_lattices @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( ( k2_lattices @ X4 @ X6 @ ( k1_lattices @ X4 @ X6 @ X5 ) )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l3_lattices @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d9_lattices])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ X0 @ sk_B_2 ) )
        = X0 )
      | ~ ( v9_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
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

thf('33',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ X0 @ sk_B_2 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['31','32','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ X0 @ sk_B_2 ) )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( ( k2_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ ( k1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B_2 ) )
        = ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','41'])).

thf('43',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ ( k1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B_2 ) )
        = ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k2_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ ( k1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B_2 ) )
      = ( k15_lattice3 @ sk_A @ X0 ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k2_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ sk_C_2 ) @ sk_B_2 )
    = ( k15_lattice3 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['27','46'])).

thf('48',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('49',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_lattices @ A ) )
     => ( ( v6_lattices @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( k2_lattices @ A @ B @ C )
                  = ( k2_lattices @ A @ C @ B ) ) ) ) ) ) )).

thf('50',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v6_lattices @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ( ( k2_lattices @ X15 @ X17 @ X16 )
        = ( k2_lattices @ X15 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d6_lattices])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ sk_B_2 )
        = ( k2_lattices @ sk_A @ sk_B_2 @ X0 ) )
      | ~ ( v6_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X7: $i] :
      ( ( l1_lattices @ X7 )
      | ~ ( l3_lattices @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('54',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ sk_B_2 )
        = ( k2_lattices @ sk_A @ sk_B_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['51','54','60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ X0 @ sk_B_2 )
        = ( k2_lattices @ sk_A @ sk_B_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( ( k2_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B_2 )
        = ( k2_lattices @ sk_A @ sk_B_2 @ ( k15_lattice3 @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['48','63'])).

thf('65',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B_2 )
        = ( k2_lattices @ sk_A @ sk_B_2 @ ( k15_lattice3 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k2_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B_2 )
      = ( k2_lattices @ sk_A @ sk_B_2 @ ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k2_lattices @ sk_A @ sk_B_2 @ ( k15_lattice3 @ sk_A @ sk_C_2 ) )
    = ( k15_lattice3 @ sk_A @ sk_C_2 ) ),
    inference(demod,[status(thm)],['47','68'])).

thf('70',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('71',plain,(
    r2_hidden @ sk_B_2 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('73',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( r3_lattices @ X21 @ X20 @ ( k15_lattice3 @ X21 @ X22 ) )
      | ~ ( r2_hidden @ X20 @ X22 )
      | ~ ( l3_lattices @ X21 )
      | ~ ( v4_lattice3 @ X21 )
      | ~ ( v10_lattices @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t38_lattice3])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r2_hidden @ sk_B_2 @ X0 )
      | ( r3_lattices @ sk_A @ sk_B_2 @ ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ sk_B_2 @ X0 )
      | ( r3_lattices @ sk_A @ sk_B_2 @ ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['74','75','76','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_A @ sk_B_2 @ ( k15_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ sk_B_2 @ X0 ) ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,(
    r3_lattices @ sk_A @ sk_B_2 @ ( k15_lattice3 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['71','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
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

thf('83',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l3_lattices @ X9 )
      | ~ ( v9_lattices @ X9 )
      | ~ ( v8_lattices @ X9 )
      | ~ ( v6_lattices @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( r1_lattices @ X9 @ X8 @ X10 )
      | ~ ( r3_lattices @ X9 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattices @ sk_A @ sk_B_2 @ X0 )
      | ( r1_lattices @ sk_A @ sk_B_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('93',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattices @ sk_A @ sk_B_2 @ X0 )
      | ( r1_lattices @ sk_A @ sk_B_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['84','85','91','92','93'])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k15_lattice3 @ sk_A @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_lattices @ sk_A @ sk_B_2 @ ( k15_lattice3 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['81','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( r1_lattices @ sk_A @ sk_B_2 @ ( k15_lattice3 @ sk_A @ sk_C_2 ) )
    | ~ ( m1_subset_1 @ ( k15_lattice3 @ sk_A @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( r1_lattices @ sk_A @ sk_B_2 @ ( k15_lattice3 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['70','97'])).

thf('99',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ sk_B_2 @ ( k15_lattice3 @ sk_A @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    r1_lattices @ sk_A @ sk_B_2 @ ( k15_lattice3 @ sk_A @ sk_C_2 ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('104',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( r1_lattices @ X2 @ X1 @ X3 )
      | ( ( k1_lattices @ X2 @ X1 @ X3 )
        = X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l2_lattices @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_lattices])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l2_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ sk_B_2 @ X0 )
        = X0 )
      | ~ ( r1_lattices @ sk_A @ sk_B_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['21','22'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ sk_B_2 @ X0 )
        = X0 )
      | ~ ( r1_lattices @ sk_A @ sk_B_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r1_lattices @ sk_A @ sk_B_2 @ ( k15_lattice3 @ sk_A @ X0 ) )
      | ( ( k1_lattices @ sk_A @ sk_B_2 @ ( k15_lattice3 @ sk_A @ X0 ) )
        = ( k15_lattice3 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['103','108'])).

thf('110',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r1_lattices @ sk_A @ sk_B_2 @ ( k15_lattice3 @ sk_A @ X0 ) )
      | ( ( k1_lattices @ sk_A @ sk_B_2 @ ( k15_lattice3 @ sk_A @ X0 ) )
        = ( k15_lattice3 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( ( k1_lattices @ sk_A @ sk_B_2 @ ( k15_lattice3 @ sk_A @ X0 ) )
        = ( k15_lattice3 @ sk_A @ X0 ) )
      | ~ ( r1_lattices @ sk_A @ sk_B_2 @ ( k15_lattice3 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ sk_B_2 @ ( k15_lattice3 @ sk_A @ X0 ) )
      | ( ( k1_lattices @ sk_A @ sk_B_2 @ ( k15_lattice3 @ sk_A @ X0 ) )
        = ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( k1_lattices @ sk_A @ sk_B_2 @ ( k15_lattice3 @ sk_A @ sk_C_2 ) )
    = ( k15_lattice3 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['102','114'])).

thf('116',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('118',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v9_lattices @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( ( k2_lattices @ X4 @ X6 @ ( k1_lattices @ X4 @ X6 @ X5 ) )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l3_lattices @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d9_lattices])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ X2 @ ( k1_lattices @ X0 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) ) )
        = X2 )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ X2 @ ( k1_lattices @ X0 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) ) )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( ( k2_lattices @ sk_A @ sk_B_2 @ ( k1_lattices @ sk_A @ sk_B_2 @ ( k15_lattice3 @ sk_A @ X0 ) ) )
        = sk_B_2 )
      | ~ ( v9_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['116','120'])).

thf('122',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_lattices @ sk_A @ sk_B_2 @ ( k1_lattices @ sk_A @ sk_B_2 @ ( k15_lattice3 @ sk_A @ X0 ) ) )
        = sk_B_2 ) ) ),
    inference(demod,[status(thm)],['121','122','123'])).

thf('125',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( k2_lattices @ sk_A @ sk_B_2 @ ( k1_lattices @ sk_A @ sk_B_2 @ ( k15_lattice3 @ sk_A @ X0 ) ) )
      = sk_B_2 ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( k2_lattices @ sk_A @ sk_B_2 @ ( k15_lattice3 @ sk_A @ sk_C_2 ) )
    = sk_B_2 ),
    inference('sup+',[status(thm)],['115','126'])).

thf('128',plain,
    ( ( k15_lattice3 @ sk_A @ sk_C_2 )
    = sk_B_2 ),
    inference('sup+',[status(thm)],['69','127'])).

thf('129',plain,(
    ( k15_lattice3 @ sk_A @ sk_C_2 )
 != sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['128','129'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WXhPBxhebe
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:43:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 134 iterations in 0.084s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.21/0.56  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.21/0.56  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.21/0.56  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.21/0.56  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.21/0.56  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.21/0.56  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 0.21/0.56  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 0.21/0.56  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.21/0.56  thf(r4_lattice3_type, type, r4_lattice3: $i > $i > $i > $o).
% 0.21/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.56  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.21/0.56  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 0.21/0.56  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 0.21/0.56  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 0.21/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.56  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.21/0.56  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.21/0.56  thf(k1_lattices_type, type, k1_lattices: $i > $i > $i > $i).
% 0.21/0.56  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.21/0.56  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 0.21/0.56  thf(t41_lattice3, conjecture,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.56         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.56           ( ![C:$i]:
% 0.21/0.56             ( ( ( r2_hidden @ B @ C ) & ( r4_lattice3 @ A @ B @ C ) ) =>
% 0.21/0.56               ( ( k15_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.56    (~( ![A:$i]:
% 0.21/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.56            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.56          ( ![B:$i]:
% 0.21/0.56            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.56              ( ![C:$i]:
% 0.21/0.56                ( ( ( r2_hidden @ B @ C ) & ( r4_lattice3 @ A @ B @ C ) ) =>
% 0.21/0.56                  ( ( k15_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t41_lattice3])).
% 0.21/0.56  thf('0', plain, ((r4_lattice3 @ sk_A @ sk_B_2 @ sk_C_2)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('1', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(dt_k15_lattice3, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.21/0.56       ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.21/0.56  thf('2', plain,
% 0.21/0.56      (![X18 : $i, X19 : $i]:
% 0.21/0.56         (~ (l3_lattices @ X18)
% 0.21/0.56          | (v2_struct_0 @ X18)
% 0.21/0.56          | (m1_subset_1 @ (k15_lattice3 @ X18 @ X19) @ (u1_struct_0 @ X18)))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.21/0.56  thf(d21_lattice3, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.21/0.56       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.56           ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.56         ( ![B:$i,C:$i]:
% 0.21/0.56           ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.56             ( ( ( C ) = ( k15_lattice3 @ A @ B ) ) <=>
% 0.21/0.56               ( ( r4_lattice3 @ A @ C @ B ) & 
% 0.21/0.56                 ( ![D:$i]:
% 0.21/0.56                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.56                     ( ( r4_lattice3 @ A @ D @ B ) =>
% 0.21/0.56                       ( r1_lattices @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf('3', plain,
% 0.21/0.56      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.56         ((v2_struct_0 @ X11)
% 0.21/0.56          | ~ (v10_lattices @ X11)
% 0.21/0.56          | ~ (v4_lattice3 @ X11)
% 0.21/0.56          | ~ (l3_lattices @ X11)
% 0.21/0.56          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 0.21/0.56          | ((X12) != (k15_lattice3 @ X11 @ X13))
% 0.21/0.56          | ~ (r4_lattice3 @ X11 @ X14 @ X13)
% 0.21/0.56          | (r1_lattices @ X11 @ X12 @ X14)
% 0.21/0.56          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X11))
% 0.21/0.56          | ~ (l3_lattices @ X11)
% 0.21/0.56          | (v2_struct_0 @ X11))),
% 0.21/0.56      inference('cnf', [status(esa)], [d21_lattice3])).
% 0.21/0.56  thf('4', plain,
% 0.21/0.56      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X11))
% 0.21/0.56          | (r1_lattices @ X11 @ (k15_lattice3 @ X11 @ X13) @ X14)
% 0.21/0.56          | ~ (r4_lattice3 @ X11 @ X14 @ X13)
% 0.21/0.56          | ~ (m1_subset_1 @ (k15_lattice3 @ X11 @ X13) @ (u1_struct_0 @ X11))
% 0.21/0.56          | ~ (l3_lattices @ X11)
% 0.21/0.56          | ~ (v4_lattice3 @ X11)
% 0.21/0.56          | ~ (v10_lattices @ X11)
% 0.21/0.56          | (v2_struct_0 @ X11))),
% 0.21/0.56      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.56  thf('5', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         ((v2_struct_0 @ X0)
% 0.21/0.56          | ~ (l3_lattices @ X0)
% 0.21/0.56          | (v2_struct_0 @ X0)
% 0.21/0.56          | ~ (v10_lattices @ X0)
% 0.21/0.56          | ~ (v4_lattice3 @ X0)
% 0.21/0.56          | ~ (l3_lattices @ X0)
% 0.21/0.56          | ~ (r4_lattice3 @ X0 @ X2 @ X1)
% 0.21/0.56          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.21/0.56          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['2', '4'])).
% 0.21/0.56  thf('6', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.56          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.21/0.56          | ~ (r4_lattice3 @ X0 @ X2 @ X1)
% 0.21/0.56          | ~ (v4_lattice3 @ X0)
% 0.21/0.56          | ~ (v10_lattices @ X0)
% 0.21/0.56          | ~ (l3_lattices @ X0)
% 0.21/0.56          | (v2_struct_0 @ X0))),
% 0.21/0.56      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.56  thf('7', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | ~ (l3_lattices @ sk_A)
% 0.21/0.56          | ~ (v10_lattices @ sk_A)
% 0.21/0.56          | ~ (v4_lattice3 @ sk_A)
% 0.21/0.56          | ~ (r4_lattice3 @ sk_A @ sk_B_2 @ X0)
% 0.21/0.56          | (r1_lattices @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B_2))),
% 0.21/0.56      inference('sup-', [status(thm)], ['1', '6'])).
% 0.21/0.56  thf('8', plain, ((l3_lattices @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('9', plain, ((v10_lattices @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('10', plain, ((v4_lattice3 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('11', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | ~ (r4_lattice3 @ sk_A @ sk_B_2 @ X0)
% 0.21/0.56          | (r1_lattices @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B_2))),
% 0.21/0.56      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 0.21/0.56  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('13', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r1_lattices @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B_2)
% 0.21/0.56          | ~ (r4_lattice3 @ sk_A @ sk_B_2 @ X0))),
% 0.21/0.56      inference('clc', [status(thm)], ['11', '12'])).
% 0.21/0.56  thf('14', plain,
% 0.21/0.56      ((r1_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_C_2) @ sk_B_2)),
% 0.21/0.56      inference('sup-', [status(thm)], ['0', '13'])).
% 0.21/0.56  thf('15', plain,
% 0.21/0.56      (![X18 : $i, X19 : $i]:
% 0.21/0.56         (~ (l3_lattices @ X18)
% 0.21/0.56          | (v2_struct_0 @ X18)
% 0.21/0.56          | (m1_subset_1 @ (k15_lattice3 @ X18 @ X19) @ (u1_struct_0 @ X18)))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.21/0.56  thf(d3_lattices, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l2_lattices @ A ) ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.56           ( ![C:$i]:
% 0.21/0.56             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.56               ( ( r1_lattices @ A @ B @ C ) <=>
% 0.21/0.56                 ( ( k1_lattices @ A @ B @ C ) = ( C ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf('16', plain,
% 0.21/0.56      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.21/0.56          | ~ (r1_lattices @ X2 @ X1 @ X3)
% 0.21/0.56          | ((k1_lattices @ X2 @ X1 @ X3) = (X3))
% 0.21/0.56          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.21/0.56          | ~ (l2_lattices @ X2)
% 0.21/0.56          | (v2_struct_0 @ X2))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_lattices])).
% 0.21/0.56  thf('17', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         ((v2_struct_0 @ X0)
% 0.21/0.56          | ~ (l3_lattices @ X0)
% 0.21/0.56          | (v2_struct_0 @ X0)
% 0.21/0.56          | ~ (l2_lattices @ X0)
% 0.21/0.56          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.56          | ((k1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2) = (X2))
% 0.21/0.56          | ~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))),
% 0.21/0.56      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.56  thf('18', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         (~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.21/0.56          | ((k1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2) = (X2))
% 0.21/0.56          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.56          | ~ (l2_lattices @ X0)
% 0.21/0.56          | ~ (l3_lattices @ X0)
% 0.21/0.56          | (v2_struct_0 @ X0))),
% 0.21/0.56      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.56  thf('19', plain,
% 0.21/0.56      (((v2_struct_0 @ sk_A)
% 0.21/0.56        | ~ (l3_lattices @ sk_A)
% 0.21/0.56        | ~ (l2_lattices @ sk_A)
% 0.21/0.56        | ~ (m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.21/0.56        | ((k1_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_C_2) @ sk_B_2)
% 0.21/0.56            = (sk_B_2)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['14', '18'])).
% 0.21/0.56  thf('20', plain, ((l3_lattices @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('21', plain, ((l3_lattices @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(dt_l3_lattices, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 0.21/0.56  thf('22', plain, (![X7 : $i]: ((l2_lattices @ X7) | ~ (l3_lattices @ X7))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.21/0.56  thf('23', plain, ((l2_lattices @ sk_A)),
% 0.21/0.56      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.56  thf('24', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('25', plain,
% 0.21/0.56      (((v2_struct_0 @ sk_A)
% 0.21/0.56        | ((k1_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_C_2) @ sk_B_2)
% 0.21/0.56            = (sk_B_2)))),
% 0.21/0.56      inference('demod', [status(thm)], ['19', '20', '23', '24'])).
% 0.21/0.56  thf('26', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('27', plain,
% 0.21/0.56      (((k1_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_C_2) @ sk_B_2)
% 0.21/0.56         = (sk_B_2))),
% 0.21/0.56      inference('clc', [status(thm)], ['25', '26'])).
% 0.21/0.56  thf('28', plain,
% 0.21/0.56      (![X18 : $i, X19 : $i]:
% 0.21/0.56         (~ (l3_lattices @ X18)
% 0.21/0.56          | (v2_struct_0 @ X18)
% 0.21/0.56          | (m1_subset_1 @ (k15_lattice3 @ X18 @ X19) @ (u1_struct_0 @ X18)))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.21/0.56  thf('29', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(d9_lattices, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.21/0.56       ( ( v9_lattices @ A ) <=>
% 0.21/0.56         ( ![B:$i]:
% 0.21/0.56           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.56             ( ![C:$i]:
% 0.21/0.56               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.56                 ( ( k2_lattices @ A @ B @ ( k1_lattices @ A @ B @ C ) ) =
% 0.21/0.56                   ( B ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf('30', plain,
% 0.21/0.56      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.56         (~ (v9_lattices @ X4)
% 0.21/0.56          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.21/0.56          | ((k2_lattices @ X4 @ X6 @ (k1_lattices @ X4 @ X6 @ X5)) = (X6))
% 0.21/0.56          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X4))
% 0.21/0.56          | ~ (l3_lattices @ X4)
% 0.21/0.56          | (v2_struct_0 @ X4))),
% 0.21/0.56      inference('cnf', [status(esa)], [d9_lattices])).
% 0.21/0.56  thf('31', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | ~ (l3_lattices @ sk_A)
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.56          | ((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ X0 @ sk_B_2))
% 0.21/0.56              = (X0))
% 0.21/0.56          | ~ (v9_lattices @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.56  thf('32', plain, ((l3_lattices @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(cc1_lattices, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( l3_lattices @ A ) =>
% 0.21/0.56       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.21/0.56         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.21/0.56           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.21/0.56           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.21/0.56  thf('33', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ X0)
% 0.21/0.56          | ~ (v10_lattices @ X0)
% 0.21/0.56          | (v9_lattices @ X0)
% 0.21/0.56          | ~ (l3_lattices @ X0))),
% 0.21/0.56      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.56  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('35', plain,
% 0.21/0.56      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.56  thf('36', plain, ((l3_lattices @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('37', plain, ((v10_lattices @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('38', plain, ((v9_lattices @ sk_A)),
% 0.21/0.56      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.21/0.56  thf('39', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.56          | ((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ X0 @ sk_B_2))
% 0.21/0.56              = (X0)))),
% 0.21/0.56      inference('demod', [status(thm)], ['31', '32', '38'])).
% 0.21/0.56  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('41', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ X0 @ sk_B_2))
% 0.21/0.56            = (X0))
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('clc', [status(thm)], ['39', '40'])).
% 0.21/0.56  thf('42', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | ~ (l3_lattices @ sk_A)
% 0.21/0.56          | ((k2_lattices @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ 
% 0.21/0.56              (k1_lattices @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B_2))
% 0.21/0.56              = (k15_lattice3 @ sk_A @ X0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['28', '41'])).
% 0.21/0.56  thf('43', plain, ((l3_lattices @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('44', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | ((k2_lattices @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ 
% 0.21/0.56              (k1_lattices @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B_2))
% 0.21/0.56              = (k15_lattice3 @ sk_A @ X0)))),
% 0.21/0.56      inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.56  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('46', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((k2_lattices @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ 
% 0.21/0.56           (k1_lattices @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B_2))
% 0.21/0.56           = (k15_lattice3 @ sk_A @ X0))),
% 0.21/0.56      inference('clc', [status(thm)], ['44', '45'])).
% 0.21/0.56  thf('47', plain,
% 0.21/0.56      (((k2_lattices @ sk_A @ (k15_lattice3 @ sk_A @ sk_C_2) @ sk_B_2)
% 0.21/0.56         = (k15_lattice3 @ sk_A @ sk_C_2))),
% 0.21/0.56      inference('sup+', [status(thm)], ['27', '46'])).
% 0.21/0.56  thf('48', plain,
% 0.21/0.56      (![X18 : $i, X19 : $i]:
% 0.21/0.56         (~ (l3_lattices @ X18)
% 0.21/0.56          | (v2_struct_0 @ X18)
% 0.21/0.56          | (m1_subset_1 @ (k15_lattice3 @ X18 @ X19) @ (u1_struct_0 @ X18)))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.21/0.56  thf('49', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(d6_lattices, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 0.21/0.56       ( ( v6_lattices @ A ) <=>
% 0.21/0.56         ( ![B:$i]:
% 0.21/0.56           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.56             ( ![C:$i]:
% 0.21/0.56               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.56                 ( ( k2_lattices @ A @ B @ C ) = ( k2_lattices @ A @ C @ B ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf('50', plain,
% 0.21/0.56      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.56         (~ (v6_lattices @ X15)
% 0.21/0.56          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.21/0.56          | ((k2_lattices @ X15 @ X17 @ X16) = (k2_lattices @ X15 @ X16 @ X17))
% 0.21/0.56          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X15))
% 0.21/0.56          | ~ (l1_lattices @ X15)
% 0.21/0.56          | (v2_struct_0 @ X15))),
% 0.21/0.56      inference('cnf', [status(esa)], [d6_lattices])).
% 0.21/0.56  thf('51', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | ~ (l1_lattices @ sk_A)
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.56          | ((k2_lattices @ sk_A @ X0 @ sk_B_2)
% 0.21/0.56              = (k2_lattices @ sk_A @ sk_B_2 @ X0))
% 0.21/0.56          | ~ (v6_lattices @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.56  thf('52', plain, ((l3_lattices @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('53', plain, (![X7 : $i]: ((l1_lattices @ X7) | ~ (l3_lattices @ X7))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.21/0.56  thf('54', plain, ((l1_lattices @ sk_A)),
% 0.21/0.56      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.56  thf('55', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ X0)
% 0.21/0.56          | ~ (v10_lattices @ X0)
% 0.21/0.56          | (v6_lattices @ X0)
% 0.21/0.56          | ~ (l3_lattices @ X0))),
% 0.21/0.56      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.56  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('57', plain,
% 0.21/0.56      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.56  thf('58', plain, ((l3_lattices @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('59', plain, ((v10_lattices @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('60', plain, ((v6_lattices @ sk_A)),
% 0.21/0.56      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.21/0.56  thf('61', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.56          | ((k2_lattices @ sk_A @ X0 @ sk_B_2)
% 0.21/0.56              = (k2_lattices @ sk_A @ sk_B_2 @ X0)))),
% 0.21/0.56      inference('demod', [status(thm)], ['51', '54', '60'])).
% 0.21/0.56  thf('62', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('63', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((k2_lattices @ sk_A @ X0 @ sk_B_2)
% 0.21/0.56            = (k2_lattices @ sk_A @ sk_B_2 @ X0))
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('clc', [status(thm)], ['61', '62'])).
% 0.21/0.56  thf('64', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | ~ (l3_lattices @ sk_A)
% 0.21/0.56          | ((k2_lattices @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B_2)
% 0.21/0.56              = (k2_lattices @ sk_A @ sk_B_2 @ (k15_lattice3 @ sk_A @ X0))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['48', '63'])).
% 0.21/0.56  thf('65', plain, ((l3_lattices @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('66', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | ((k2_lattices @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B_2)
% 0.21/0.56              = (k2_lattices @ sk_A @ sk_B_2 @ (k15_lattice3 @ sk_A @ X0))))),
% 0.21/0.56      inference('demod', [status(thm)], ['64', '65'])).
% 0.21/0.56  thf('67', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('68', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((k2_lattices @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B_2)
% 0.21/0.56           = (k2_lattices @ sk_A @ sk_B_2 @ (k15_lattice3 @ sk_A @ X0)))),
% 0.21/0.56      inference('clc', [status(thm)], ['66', '67'])).
% 0.21/0.56  thf('69', plain,
% 0.21/0.56      (((k2_lattices @ sk_A @ sk_B_2 @ (k15_lattice3 @ sk_A @ sk_C_2))
% 0.21/0.56         = (k15_lattice3 @ sk_A @ sk_C_2))),
% 0.21/0.56      inference('demod', [status(thm)], ['47', '68'])).
% 0.21/0.56  thf('70', plain,
% 0.21/0.56      (![X18 : $i, X19 : $i]:
% 0.21/0.56         (~ (l3_lattices @ X18)
% 0.21/0.56          | (v2_struct_0 @ X18)
% 0.21/0.56          | (m1_subset_1 @ (k15_lattice3 @ X18 @ X19) @ (u1_struct_0 @ X18)))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.21/0.56  thf('71', plain, ((r2_hidden @ sk_B_2 @ sk_C_2)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('72', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(t38_lattice3, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.56         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.56           ( ![C:$i]:
% 0.21/0.56             ( ( r2_hidden @ B @ C ) =>
% 0.21/0.56               ( ( r3_lattices @ A @ B @ ( k15_lattice3 @ A @ C ) ) & 
% 0.21/0.56                 ( r3_lattices @ A @ ( k16_lattice3 @ A @ C ) @ B ) ) ) ) ) ) ))).
% 0.21/0.56  thf('73', plain,
% 0.21/0.56      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.21/0.56          | (r3_lattices @ X21 @ X20 @ (k15_lattice3 @ X21 @ X22))
% 0.21/0.56          | ~ (r2_hidden @ X20 @ X22)
% 0.21/0.56          | ~ (l3_lattices @ X21)
% 0.21/0.56          | ~ (v4_lattice3 @ X21)
% 0.21/0.56          | ~ (v10_lattices @ X21)
% 0.21/0.56          | (v2_struct_0 @ X21))),
% 0.21/0.56      inference('cnf', [status(esa)], [t38_lattice3])).
% 0.21/0.56  thf('74', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | ~ (v10_lattices @ sk_A)
% 0.21/0.56          | ~ (v4_lattice3 @ sk_A)
% 0.21/0.56          | ~ (l3_lattices @ sk_A)
% 0.21/0.56          | ~ (r2_hidden @ sk_B_2 @ X0)
% 0.21/0.56          | (r3_lattices @ sk_A @ sk_B_2 @ (k15_lattice3 @ sk_A @ X0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['72', '73'])).
% 0.21/0.56  thf('75', plain, ((v10_lattices @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('76', plain, ((v4_lattice3 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('77', plain, ((l3_lattices @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('78', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | ~ (r2_hidden @ sk_B_2 @ X0)
% 0.21/0.56          | (r3_lattices @ sk_A @ sk_B_2 @ (k15_lattice3 @ sk_A @ X0)))),
% 0.21/0.56      inference('demod', [status(thm)], ['74', '75', '76', '77'])).
% 0.21/0.56  thf('79', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('80', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r3_lattices @ sk_A @ sk_B_2 @ (k15_lattice3 @ sk_A @ X0))
% 0.21/0.56          | ~ (r2_hidden @ sk_B_2 @ X0))),
% 0.21/0.56      inference('clc', [status(thm)], ['78', '79'])).
% 0.21/0.56  thf('81', plain,
% 0.21/0.56      ((r3_lattices @ sk_A @ sk_B_2 @ (k15_lattice3 @ sk_A @ sk_C_2))),
% 0.21/0.56      inference('sup-', [status(thm)], ['71', '80'])).
% 0.21/0.56  thf('82', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(redefinition_r3_lattices, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.21/0.56         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 0.21/0.56         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.56         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 0.21/0.56  thf('83', plain,
% 0.21/0.56      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.21/0.56          | ~ (l3_lattices @ X9)
% 0.21/0.56          | ~ (v9_lattices @ X9)
% 0.21/0.56          | ~ (v8_lattices @ X9)
% 0.21/0.56          | ~ (v6_lattices @ X9)
% 0.21/0.56          | (v2_struct_0 @ X9)
% 0.21/0.56          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.21/0.56          | (r1_lattices @ X9 @ X8 @ X10)
% 0.21/0.56          | ~ (r3_lattices @ X9 @ X8 @ X10))),
% 0.21/0.56      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.21/0.56  thf('84', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (r3_lattices @ sk_A @ sk_B_2 @ X0)
% 0.21/0.56          | (r1_lattices @ sk_A @ sk_B_2 @ X0)
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.56          | (v2_struct_0 @ sk_A)
% 0.21/0.56          | ~ (v6_lattices @ sk_A)
% 0.21/0.56          | ~ (v8_lattices @ sk_A)
% 0.21/0.56          | ~ (v9_lattices @ sk_A)
% 0.21/0.56          | ~ (l3_lattices @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['82', '83'])).
% 0.21/0.56  thf('85', plain, ((v6_lattices @ sk_A)),
% 0.21/0.56      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.21/0.56  thf('86', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ X0)
% 0.21/0.56          | ~ (v10_lattices @ X0)
% 0.21/0.56          | (v8_lattices @ X0)
% 0.21/0.56          | ~ (l3_lattices @ X0))),
% 0.21/0.56      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.56  thf('87', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('88', plain,
% 0.21/0.56      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['86', '87'])).
% 0.21/0.56  thf('89', plain, ((l3_lattices @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('90', plain, ((v10_lattices @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('91', plain, ((v8_lattices @ sk_A)),
% 0.21/0.56      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.21/0.56  thf('92', plain, ((v9_lattices @ sk_A)),
% 0.21/0.56      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.21/0.56  thf('93', plain, ((l3_lattices @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('94', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (r3_lattices @ sk_A @ sk_B_2 @ X0)
% 0.21/0.56          | (r1_lattices @ sk_A @ sk_B_2 @ X0)
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.56          | (v2_struct_0 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['84', '85', '91', '92', '93'])).
% 0.21/0.56  thf('95', plain,
% 0.21/0.56      (((v2_struct_0 @ sk_A)
% 0.21/0.56        | ~ (m1_subset_1 @ (k15_lattice3 @ sk_A @ sk_C_2) @ 
% 0.21/0.56             (u1_struct_0 @ sk_A))
% 0.21/0.56        | (r1_lattices @ sk_A @ sk_B_2 @ (k15_lattice3 @ sk_A @ sk_C_2)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['81', '94'])).
% 0.21/0.56  thf('96', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('97', plain,
% 0.21/0.56      (((r1_lattices @ sk_A @ sk_B_2 @ (k15_lattice3 @ sk_A @ sk_C_2))
% 0.21/0.56        | ~ (m1_subset_1 @ (k15_lattice3 @ sk_A @ sk_C_2) @ 
% 0.21/0.56             (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('clc', [status(thm)], ['95', '96'])).
% 0.21/0.56  thf('98', plain,
% 0.21/0.56      (((v2_struct_0 @ sk_A)
% 0.21/0.56        | ~ (l3_lattices @ sk_A)
% 0.21/0.56        | (r1_lattices @ sk_A @ sk_B_2 @ (k15_lattice3 @ sk_A @ sk_C_2)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['70', '97'])).
% 0.21/0.56  thf('99', plain, ((l3_lattices @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('100', plain,
% 0.21/0.56      (((v2_struct_0 @ sk_A)
% 0.21/0.56        | (r1_lattices @ sk_A @ sk_B_2 @ (k15_lattice3 @ sk_A @ sk_C_2)))),
% 0.21/0.56      inference('demod', [status(thm)], ['98', '99'])).
% 0.21/0.56  thf('101', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('102', plain,
% 0.21/0.56      ((r1_lattices @ sk_A @ sk_B_2 @ (k15_lattice3 @ sk_A @ sk_C_2))),
% 0.21/0.56      inference('clc', [status(thm)], ['100', '101'])).
% 0.21/0.56  thf('103', plain,
% 0.21/0.56      (![X18 : $i, X19 : $i]:
% 0.21/0.56         (~ (l3_lattices @ X18)
% 0.21/0.56          | (v2_struct_0 @ X18)
% 0.21/0.56          | (m1_subset_1 @ (k15_lattice3 @ X18 @ X19) @ (u1_struct_0 @ X18)))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.21/0.56  thf('104', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('105', plain,
% 0.21/0.56      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.21/0.56          | ~ (r1_lattices @ X2 @ X1 @ X3)
% 0.21/0.56          | ((k1_lattices @ X2 @ X1 @ X3) = (X3))
% 0.21/0.56          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.21/0.56          | ~ (l2_lattices @ X2)
% 0.21/0.56          | (v2_struct_0 @ X2))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_lattices])).
% 0.21/0.56  thf('106', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | ~ (l2_lattices @ sk_A)
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.56          | ((k1_lattices @ sk_A @ sk_B_2 @ X0) = (X0))
% 0.21/0.56          | ~ (r1_lattices @ sk_A @ sk_B_2 @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['104', '105'])).
% 0.21/0.56  thf('107', plain, ((l2_lattices @ sk_A)),
% 0.21/0.56      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.56  thf('108', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.56          | ((k1_lattices @ sk_A @ sk_B_2 @ X0) = (X0))
% 0.21/0.56          | ~ (r1_lattices @ sk_A @ sk_B_2 @ X0))),
% 0.21/0.56      inference('demod', [status(thm)], ['106', '107'])).
% 0.21/0.56  thf('109', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | ~ (l3_lattices @ sk_A)
% 0.21/0.56          | ~ (r1_lattices @ sk_A @ sk_B_2 @ (k15_lattice3 @ sk_A @ X0))
% 0.21/0.56          | ((k1_lattices @ sk_A @ sk_B_2 @ (k15_lattice3 @ sk_A @ X0))
% 0.21/0.56              = (k15_lattice3 @ sk_A @ X0))
% 0.21/0.56          | (v2_struct_0 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['103', '108'])).
% 0.21/0.56  thf('110', plain, ((l3_lattices @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('111', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | ~ (r1_lattices @ sk_A @ sk_B_2 @ (k15_lattice3 @ sk_A @ X0))
% 0.21/0.56          | ((k1_lattices @ sk_A @ sk_B_2 @ (k15_lattice3 @ sk_A @ X0))
% 0.21/0.56              = (k15_lattice3 @ sk_A @ X0))
% 0.21/0.56          | (v2_struct_0 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['109', '110'])).
% 0.21/0.56  thf('112', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((k1_lattices @ sk_A @ sk_B_2 @ (k15_lattice3 @ sk_A @ X0))
% 0.21/0.56            = (k15_lattice3 @ sk_A @ X0))
% 0.21/0.56          | ~ (r1_lattices @ sk_A @ sk_B_2 @ (k15_lattice3 @ sk_A @ X0))
% 0.21/0.56          | (v2_struct_0 @ sk_A))),
% 0.21/0.56      inference('simplify', [status(thm)], ['111'])).
% 0.21/0.56  thf('113', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('114', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (r1_lattices @ sk_A @ sk_B_2 @ (k15_lattice3 @ sk_A @ X0))
% 0.21/0.56          | ((k1_lattices @ sk_A @ sk_B_2 @ (k15_lattice3 @ sk_A @ X0))
% 0.21/0.56              = (k15_lattice3 @ sk_A @ X0)))),
% 0.21/0.56      inference('clc', [status(thm)], ['112', '113'])).
% 0.21/0.56  thf('115', plain,
% 0.21/0.56      (((k1_lattices @ sk_A @ sk_B_2 @ (k15_lattice3 @ sk_A @ sk_C_2))
% 0.21/0.56         = (k15_lattice3 @ sk_A @ sk_C_2))),
% 0.21/0.56      inference('sup-', [status(thm)], ['102', '114'])).
% 0.21/0.56  thf('116', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('117', plain,
% 0.21/0.56      (![X18 : $i, X19 : $i]:
% 0.21/0.56         (~ (l3_lattices @ X18)
% 0.21/0.56          | (v2_struct_0 @ X18)
% 0.21/0.56          | (m1_subset_1 @ (k15_lattice3 @ X18 @ X19) @ (u1_struct_0 @ X18)))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.21/0.56  thf('118', plain,
% 0.21/0.56      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.56         (~ (v9_lattices @ X4)
% 0.21/0.56          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.21/0.56          | ((k2_lattices @ X4 @ X6 @ (k1_lattices @ X4 @ X6 @ X5)) = (X6))
% 0.21/0.56          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X4))
% 0.21/0.56          | ~ (l3_lattices @ X4)
% 0.21/0.56          | (v2_struct_0 @ X4))),
% 0.21/0.56      inference('cnf', [status(esa)], [d9_lattices])).
% 0.21/0.56  thf('119', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         ((v2_struct_0 @ X0)
% 0.21/0.56          | ~ (l3_lattices @ X0)
% 0.21/0.56          | (v2_struct_0 @ X0)
% 0.21/0.56          | ~ (l3_lattices @ X0)
% 0.21/0.56          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.56          | ((k2_lattices @ X0 @ X2 @ 
% 0.21/0.56              (k1_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))) = (X2))
% 0.21/0.56          | ~ (v9_lattices @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['117', '118'])).
% 0.21/0.56  thf('120', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         (~ (v9_lattices @ X0)
% 0.21/0.56          | ((k2_lattices @ X0 @ X2 @ 
% 0.21/0.56              (k1_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))) = (X2))
% 0.21/0.56          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.56          | ~ (l3_lattices @ X0)
% 0.21/0.56          | (v2_struct_0 @ X0))),
% 0.21/0.56      inference('simplify', [status(thm)], ['119'])).
% 0.21/0.56  thf('121', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | ~ (l3_lattices @ sk_A)
% 0.21/0.56          | ((k2_lattices @ sk_A @ sk_B_2 @ 
% 0.21/0.56              (k1_lattices @ sk_A @ sk_B_2 @ (k15_lattice3 @ sk_A @ X0)))
% 0.21/0.56              = (sk_B_2))
% 0.21/0.56          | ~ (v9_lattices @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['116', '120'])).
% 0.21/0.56  thf('122', plain, ((l3_lattices @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('123', plain, ((v9_lattices @ sk_A)),
% 0.21/0.56      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.21/0.56  thf('124', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | ((k2_lattices @ sk_A @ sk_B_2 @ 
% 0.21/0.56              (k1_lattices @ sk_A @ sk_B_2 @ (k15_lattice3 @ sk_A @ X0)))
% 0.21/0.56              = (sk_B_2)))),
% 0.21/0.56      inference('demod', [status(thm)], ['121', '122', '123'])).
% 0.21/0.56  thf('125', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('126', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((k2_lattices @ sk_A @ sk_B_2 @ 
% 0.21/0.56           (k1_lattices @ sk_A @ sk_B_2 @ (k15_lattice3 @ sk_A @ X0)))
% 0.21/0.56           = (sk_B_2))),
% 0.21/0.56      inference('clc', [status(thm)], ['124', '125'])).
% 0.21/0.56  thf('127', plain,
% 0.21/0.56      (((k2_lattices @ sk_A @ sk_B_2 @ (k15_lattice3 @ sk_A @ sk_C_2))
% 0.21/0.56         = (sk_B_2))),
% 0.21/0.56      inference('sup+', [status(thm)], ['115', '126'])).
% 0.21/0.56  thf('128', plain, (((k15_lattice3 @ sk_A @ sk_C_2) = (sk_B_2))),
% 0.21/0.56      inference('sup+', [status(thm)], ['69', '127'])).
% 0.21/0.56  thf('129', plain, (((k15_lattice3 @ sk_A @ sk_C_2) != (sk_B_2))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('130', plain, ($false),
% 0.21/0.56      inference('simplify_reflect-', [status(thm)], ['128', '129'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.21/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
