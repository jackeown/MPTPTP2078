%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OmNKCDU3rh

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 376 expanded)
%              Number of leaves         :   35 ( 126 expanded)
%              Depth                    :   16
%              Number of atoms          : 1621 (5382 expanded)
%              Number of equality atoms :   44 ( 184 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_lattices_type,type,(
    k3_lattices: $i > $i > $i > $i )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(k1_lattices_type,type,(
    k1_lattices: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(r3_lattice3_type,type,(
    r3_lattice3: $i > $i > $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    r2_hidden @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
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

thf('2',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ( r3_lattices @ X22 @ ( k16_lattice3 @ X22 @ X23 ) @ X21 )
      | ~ ( r2_hidden @ X21 @ X23 )
      | ~ ( l3_lattices @ X22 )
      | ~ ( v4_lattice3 @ X22 )
      | ~ ( v10_lattices @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t38_lattice3])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('8',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['0','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k16_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( m1_subset_1 @ ( k16_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('12',plain,(
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

thf('13',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l3_lattices @ X12 )
      | ~ ( v9_lattices @ X12 )
      | ~ ( v8_lattices @ X12 )
      | ~ ( v6_lattices @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( r1_lattices @ X12 @ X11 @ X13 )
      | ~ ( r3_lattices @ X12 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('14',plain,(
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
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf('17',plain,(
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

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17','23','29','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['10','38'])).

thf('40',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l3_lattices @ X14 )
      | ( v2_struct_0 @ X14 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X14 @ X15 ) @ ( u1_struct_0 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

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

thf('41',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r1_lattices @ X5 @ X4 @ X6 )
      | ( ( k1_lattices @ X5 @ X4 @ X6 )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l2_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_lattices])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( ( k1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
        = X2 )
      | ~ ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ( ( k1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l2_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C ) @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['39','43'])).

thf('45',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('47',plain,(
    ! [X7: $i] :
      ( ( l2_lattices @ X7 )
      | ~ ( l3_lattices @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('48',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l3_lattices @ X14 )
      | ( v2_struct_0 @ X14 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X14 @ X15 ) @ ( u1_struct_0 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf(redefinition_k3_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v4_lattices @ A )
        & ( l2_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k3_lattices @ A @ B @ C )
        = ( k1_lattices @ A @ B @ C ) ) ) )).

thf('52',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l2_lattices @ X9 )
      | ~ ( v4_lattices @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( ( k3_lattices @ X9 @ X8 @ X10 )
        = ( k1_lattices @ X9 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_lattices])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( ( k3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
        = ( k1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_lattices @ X0 )
      | ~ ( l2_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l2_lattices @ X0 )
      | ~ ( v4_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( ( k3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
        = ( k1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( ( k3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
        = ( k1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B ) )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','54'])).

thf('56',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l3_lattices @ X14 )
      | ( v2_struct_0 @ X14 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X14 @ X15 ) @ ( u1_struct_0 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf('58',plain,(
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

thf('59',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l2_lattices @ X2 )
      | ~ ( v4_lattices @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( ( k3_lattices @ X2 @ X1 @ X3 )
        = ( k3_lattices @ X2 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_lattices])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v4_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v4_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['46','47'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_B @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( ( k3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) )
        = ( k3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['57','70'])).

thf('72',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) )
        = ( k3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) )
      = ( k3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('77',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['46','47'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) )
        = ( k1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['55','56','75','76','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) )
      = ( k1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ sk_C ) )
      = sk_B ) ),
    inference(demod,[status(thm)],['44','45','48','49','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ sk_C ) )
    = sk_B ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l3_lattices @ X14 )
      | ( v2_struct_0 @ X14 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X14 @ X15 ) @ ( u1_struct_0 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf('85',plain,(
    r3_lattice3 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
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

thf('88',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ( X16
       != ( k16_lattice3 @ X17 @ X18 ) )
      | ~ ( r3_lattice3 @ X17 @ X19 @ X18 )
      | ( r3_lattices @ X17 @ X19 @ X16 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l3_lattices @ X17 )
      | ~ ( v4_lattice3 @ X17 )
      | ~ ( v10_lattices @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('89',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( v10_lattices @ X17 )
      | ~ ( v4_lattice3 @ X17 )
      | ~ ( l3_lattices @ X17 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ( r3_lattices @ X17 @ X19 @ ( k16_lattice3 @ X17 @ X18 ) )
      | ~ ( r3_lattice3 @ X17 @ X19 @ X18 )
      | ~ ( m1_subset_1 @ ( k16_lattice3 @ X17 @ X18 ) @ ( u1_struct_0 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
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
    inference('sup-',[status(thm)],['87','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r3_lattices @ X0 @ X2 @ ( k16_lattice3 @ X0 @ X1 ) )
      | ~ ( r3_lattice3 @ X0 @ X2 @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( v10_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','91'])).

thf('93',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['92','93','94','95'])).

thf('97',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    r3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['85','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l3_lattices @ X12 )
      | ~ ( v9_lattices @ X12 )
      | ~ ( v8_lattices @ X12 )
      | ~ ( v6_lattices @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( r1_lattices @ X12 @ X11 @ X13 )
      | ~ ( r3_lattices @ X12 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattices @ sk_A @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('104',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('105',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('106',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattices @ sk_A @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['102','103','104','105','106'])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k16_lattice3 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['99','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( r1_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ sk_C ) )
    | ~ ( m1_subset_1 @ ( k16_lattice3 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( r1_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['84','110'])).

thf('112',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    r1_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l3_lattices @ X14 )
      | ( v2_struct_0 @ X14 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X14 @ X15 ) @ ( u1_struct_0 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf('117',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r1_lattices @ X5 @ X4 @ X6 )
      | ( ( k1_lattices @ X5 @ X4 @ X6 )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l2_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_lattices])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l2_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ sk_B @ X0 )
        = X0 )
      | ~ ( r1_lattices @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['46','47'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ sk_B @ X0 )
        = X0 )
      | ~ ( r1_lattices @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r1_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) )
      | ( ( k1_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) )
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['116','121'])).

thf('123',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r1_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) )
      | ( ( k1_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) )
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( ( k1_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) )
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ~ ( r1_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) )
      | ( ( k1_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) )
        = ( k16_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l3_lattices @ X14 )
      | ( v2_struct_0 @ X14 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X14 @ X15 ) @ ( u1_struct_0 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf('129',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l2_lattices @ X9 )
      | ~ ( v4_lattices @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( ( k3_lattices @ X9 @ X8 @ X10 )
        = ( k1_lattices @ X9 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_lattices])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B @ X0 )
        = ( k1_lattices @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('133',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['46','47'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B @ X0 )
        = ( k1_lattices @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132','133'])).

thf('135',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_B @ X0 )
        = ( k1_lattices @ sk_A @ sk_B @ X0 ) ) ) ),
    inference(clc,[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( ( k3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) )
        = ( k1_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['128','136'])).

thf('138',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) )
        = ( k1_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( k3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) )
      = ( k1_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(clc,[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) )
      | ( ( k3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ X0 ) )
        = ( k16_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['127','141'])).

thf('143',plain,
    ( ( k3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ sk_C ) )
    = ( k16_lattice3 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['115','142'])).

thf('144',plain,
    ( sk_B
    = ( k16_lattice3 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['83','143'])).

thf('145',plain,(
    ( k16_lattice3 @ sk_A @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['144','145'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OmNKCDU3rh
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:05:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.57  % Solved by: fo/fo7.sh
% 0.21/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.57  % done 137 iterations in 0.110s
% 0.21/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.57  % SZS output start Refutation
% 0.21/0.57  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.21/0.57  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.21/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.57  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.21/0.57  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.21/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.57  thf(k3_lattices_type, type, k3_lattices: $i > $i > $i > $i).
% 0.21/0.57  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 0.21/0.57  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 0.21/0.57  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.21/0.57  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 0.21/0.57  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 0.21/0.57  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 0.21/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.57  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.21/0.57  thf(k1_lattices_type, type, k1_lattices: $i > $i > $i > $i).
% 0.21/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.57  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.21/0.57  thf(r3_lattice3_type, type, r3_lattice3: $i > $i > $i > $o).
% 0.21/0.57  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.21/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.57  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 0.21/0.57  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.21/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.57  thf(t42_lattice3, conjecture,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.57         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.57           ( ![C:$i]:
% 0.21/0.57             ( ( ( r2_hidden @ B @ C ) & ( r3_lattice3 @ A @ B @ C ) ) =>
% 0.21/0.57               ( ( k16_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ))).
% 0.21/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.57    (~( ![A:$i]:
% 0.21/0.57        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.57            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.57          ( ![B:$i]:
% 0.21/0.57            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.57              ( ![C:$i]:
% 0.21/0.57                ( ( ( r2_hidden @ B @ C ) & ( r3_lattice3 @ A @ B @ C ) ) =>
% 0.21/0.57                  ( ( k16_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ) )),
% 0.21/0.57    inference('cnf.neg', [status(esa)], [t42_lattice3])).
% 0.21/0.57  thf('0', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(t38_lattice3, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.57         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.57           ( ![C:$i]:
% 0.21/0.57             ( ( r2_hidden @ B @ C ) =>
% 0.21/0.57               ( ( r3_lattices @ A @ B @ ( k15_lattice3 @ A @ C ) ) & 
% 0.21/0.57                 ( r3_lattices @ A @ ( k16_lattice3 @ A @ C ) @ B ) ) ) ) ) ) ))).
% 0.21/0.57  thf('2', plain,
% 0.21/0.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 0.21/0.57          | (r3_lattices @ X22 @ (k16_lattice3 @ X22 @ X23) @ X21)
% 0.21/0.57          | ~ (r2_hidden @ X21 @ X23)
% 0.21/0.57          | ~ (l3_lattices @ X22)
% 0.21/0.57          | ~ (v4_lattice3 @ X22)
% 0.21/0.57          | ~ (v10_lattices @ X22)
% 0.21/0.57          | (v2_struct_0 @ X22))),
% 0.21/0.57      inference('cnf', [status(esa)], [t38_lattice3])).
% 0.21/0.57  thf('3', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v2_struct_0 @ sk_A)
% 0.21/0.57          | ~ (v10_lattices @ sk_A)
% 0.21/0.57          | ~ (v4_lattice3 @ sk_A)
% 0.21/0.57          | ~ (l3_lattices @ sk_A)
% 0.21/0.57          | ~ (r2_hidden @ sk_B @ X0)
% 0.21/0.57          | (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B))),
% 0.21/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.57  thf('4', plain, ((v10_lattices @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('5', plain, ((v4_lattice3 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('6', plain, ((l3_lattices @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('7', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v2_struct_0 @ sk_A)
% 0.21/0.57          | ~ (r2_hidden @ sk_B @ X0)
% 0.21/0.57          | (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.21/0.57  thf('8', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('9', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.21/0.57          | ~ (r2_hidden @ sk_B @ X0))),
% 0.21/0.57      inference('clc', [status(thm)], ['7', '8'])).
% 0.21/0.57  thf('10', plain,
% 0.21/0.57      ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C) @ sk_B)),
% 0.21/0.57      inference('sup-', [status(thm)], ['0', '9'])).
% 0.21/0.57  thf('11', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(dt_k16_lattice3, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.21/0.57       ( m1_subset_1 @ ( k16_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.21/0.57  thf('12', plain,
% 0.21/0.57      (![X14 : $i, X15 : $i]:
% 0.21/0.57         (~ (l3_lattices @ X14)
% 0.21/0.57          | (v2_struct_0 @ X14)
% 0.21/0.57          | (m1_subset_1 @ (k16_lattice3 @ X14 @ X15) @ (u1_struct_0 @ X14)))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.21/0.57  thf(redefinition_r3_lattices, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.21/0.57         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 0.21/0.57         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.57         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 0.21/0.57  thf('13', plain,
% 0.21/0.57      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 0.21/0.57          | ~ (l3_lattices @ X12)
% 0.21/0.57          | ~ (v9_lattices @ X12)
% 0.21/0.57          | ~ (v8_lattices @ X12)
% 0.21/0.57          | ~ (v6_lattices @ X12)
% 0.21/0.57          | (v2_struct_0 @ X12)
% 0.21/0.57          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.21/0.57          | (r1_lattices @ X12 @ X11 @ X13)
% 0.21/0.57          | ~ (r3_lattices @ X12 @ X11 @ X13))),
% 0.21/0.57      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.21/0.57  thf('14', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         ((v2_struct_0 @ X0)
% 0.21/0.57          | ~ (l3_lattices @ X0)
% 0.21/0.57          | ~ (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.21/0.57          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.21/0.57          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.57          | (v2_struct_0 @ X0)
% 0.21/0.57          | ~ (v6_lattices @ X0)
% 0.21/0.57          | ~ (v8_lattices @ X0)
% 0.21/0.57          | ~ (v9_lattices @ X0)
% 0.21/0.57          | ~ (l3_lattices @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.57  thf('15', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         (~ (v9_lattices @ X0)
% 0.21/0.57          | ~ (v8_lattices @ X0)
% 0.21/0.57          | ~ (v6_lattices @ X0)
% 0.21/0.57          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.57          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.21/0.57          | ~ (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.21/0.57          | ~ (l3_lattices @ X0)
% 0.21/0.57          | (v2_struct_0 @ X0))),
% 0.21/0.57      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.57  thf('16', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v2_struct_0 @ sk_A)
% 0.21/0.57          | ~ (l3_lattices @ sk_A)
% 0.21/0.57          | ~ (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.21/0.57          | (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.21/0.57          | ~ (v6_lattices @ sk_A)
% 0.21/0.57          | ~ (v8_lattices @ sk_A)
% 0.21/0.57          | ~ (v9_lattices @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['11', '15'])).
% 0.21/0.57  thf('17', plain, ((l3_lattices @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(cc1_lattices, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( l3_lattices @ A ) =>
% 0.21/0.57       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.21/0.57         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.21/0.57           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.21/0.57           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.21/0.57  thf('18', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v2_struct_0 @ X0)
% 0.21/0.57          | ~ (v10_lattices @ X0)
% 0.21/0.57          | (v6_lattices @ X0)
% 0.21/0.57          | ~ (l3_lattices @ X0))),
% 0.21/0.57      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.57  thf('19', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('20', plain,
% 0.21/0.57      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.57  thf('21', plain, ((l3_lattices @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('22', plain, ((v10_lattices @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('23', plain, ((v6_lattices @ sk_A)),
% 0.21/0.57      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.21/0.57  thf('24', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v2_struct_0 @ X0)
% 0.21/0.57          | ~ (v10_lattices @ X0)
% 0.21/0.57          | (v8_lattices @ X0)
% 0.21/0.57          | ~ (l3_lattices @ X0))),
% 0.21/0.57      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.57  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('26', plain,
% 0.21/0.57      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.57  thf('27', plain, ((l3_lattices @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('28', plain, ((v10_lattices @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('29', plain, ((v8_lattices @ sk_A)),
% 0.21/0.57      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.21/0.57  thf('30', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v2_struct_0 @ X0)
% 0.21/0.57          | ~ (v10_lattices @ X0)
% 0.21/0.57          | (v9_lattices @ X0)
% 0.21/0.57          | ~ (l3_lattices @ X0))),
% 0.21/0.57      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.57  thf('31', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('32', plain,
% 0.21/0.57      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.57  thf('33', plain, ((l3_lattices @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('34', plain, ((v10_lattices @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('35', plain, ((v9_lattices @ sk_A)),
% 0.21/0.57      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.21/0.57  thf('36', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v2_struct_0 @ sk_A)
% 0.21/0.57          | ~ (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.21/0.57          | (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['16', '17', '23', '29', '35'])).
% 0.21/0.57  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('38', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.21/0.57          | ~ (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B))),
% 0.21/0.57      inference('clc', [status(thm)], ['36', '37'])).
% 0.21/0.57  thf('39', plain,
% 0.21/0.57      ((r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C) @ sk_B)),
% 0.21/0.57      inference('sup-', [status(thm)], ['10', '38'])).
% 0.21/0.57  thf('40', plain,
% 0.21/0.57      (![X14 : $i, X15 : $i]:
% 0.21/0.57         (~ (l3_lattices @ X14)
% 0.21/0.57          | (v2_struct_0 @ X14)
% 0.21/0.57          | (m1_subset_1 @ (k16_lattice3 @ X14 @ X15) @ (u1_struct_0 @ X14)))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.21/0.57  thf(d3_lattices, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l2_lattices @ A ) ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.57           ( ![C:$i]:
% 0.21/0.57             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.57               ( ( r1_lattices @ A @ B @ C ) <=>
% 0.21/0.57                 ( ( k1_lattices @ A @ B @ C ) = ( C ) ) ) ) ) ) ) ))).
% 0.21/0.57  thf('41', plain,
% 0.21/0.57      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.21/0.57          | ~ (r1_lattices @ X5 @ X4 @ X6)
% 0.21/0.57          | ((k1_lattices @ X5 @ X4 @ X6) = (X6))
% 0.21/0.57          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.21/0.57          | ~ (l2_lattices @ X5)
% 0.21/0.57          | (v2_struct_0 @ X5))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_lattices])).
% 0.21/0.57  thf('42', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         ((v2_struct_0 @ X0)
% 0.21/0.57          | ~ (l3_lattices @ X0)
% 0.21/0.57          | (v2_struct_0 @ X0)
% 0.21/0.57          | ~ (l2_lattices @ X0)
% 0.21/0.57          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.57          | ((k1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2) = (X2))
% 0.21/0.57          | ~ (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2))),
% 0.21/0.57      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.57  thf('43', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         (~ (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.21/0.57          | ((k1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2) = (X2))
% 0.21/0.57          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.57          | ~ (l2_lattices @ X0)
% 0.21/0.57          | ~ (l3_lattices @ X0)
% 0.21/0.57          | (v2_struct_0 @ X0))),
% 0.21/0.57      inference('simplify', [status(thm)], ['42'])).
% 0.21/0.57  thf('44', plain,
% 0.21/0.57      (((v2_struct_0 @ sk_A)
% 0.21/0.57        | ~ (l3_lattices @ sk_A)
% 0.21/0.57        | ~ (l2_lattices @ sk_A)
% 0.21/0.57        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.57        | ((k1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C) @ sk_B) = (sk_B)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['39', '43'])).
% 0.21/0.57  thf('45', plain, ((l3_lattices @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('46', plain, ((l3_lattices @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(dt_l3_lattices, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 0.21/0.57  thf('47', plain, (![X7 : $i]: ((l2_lattices @ X7) | ~ (l3_lattices @ X7))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.21/0.57  thf('48', plain, ((l2_lattices @ sk_A)),
% 0.21/0.57      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.57  thf('49', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('50', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('51', plain,
% 0.21/0.57      (![X14 : $i, X15 : $i]:
% 0.21/0.57         (~ (l3_lattices @ X14)
% 0.21/0.57          | (v2_struct_0 @ X14)
% 0.21/0.57          | (m1_subset_1 @ (k16_lattice3 @ X14 @ X15) @ (u1_struct_0 @ X14)))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.21/0.57  thf(redefinition_k3_lattices, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.21/0.57         ( l2_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.57         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57       ( ( k3_lattices @ A @ B @ C ) = ( k1_lattices @ A @ B @ C ) ) ))).
% 0.21/0.57  thf('52', plain,
% 0.21/0.57      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.21/0.57          | ~ (l2_lattices @ X9)
% 0.21/0.57          | ~ (v4_lattices @ X9)
% 0.21/0.57          | (v2_struct_0 @ X9)
% 0.21/0.57          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.21/0.57          | ((k3_lattices @ X9 @ X8 @ X10) = (k1_lattices @ X9 @ X8 @ X10)))),
% 0.21/0.57      inference('cnf', [status(esa)], [redefinition_k3_lattices])).
% 0.21/0.57  thf('53', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         ((v2_struct_0 @ X0)
% 0.21/0.57          | ~ (l3_lattices @ X0)
% 0.21/0.57          | ((k3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.21/0.57              = (k1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2))
% 0.21/0.57          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.57          | (v2_struct_0 @ X0)
% 0.21/0.57          | ~ (v4_lattices @ X0)
% 0.21/0.57          | ~ (l2_lattices @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.57  thf('54', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         (~ (l2_lattices @ X0)
% 0.21/0.57          | ~ (v4_lattices @ X0)
% 0.21/0.57          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.57          | ((k3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.21/0.57              = (k1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2))
% 0.21/0.57          | ~ (l3_lattices @ X0)
% 0.21/0.57          | (v2_struct_0 @ X0))),
% 0.21/0.57      inference('simplify', [status(thm)], ['53'])).
% 0.21/0.57  thf('55', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v2_struct_0 @ sk_A)
% 0.21/0.57          | ~ (l3_lattices @ sk_A)
% 0.21/0.57          | ((k3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.21/0.57              = (k1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B))
% 0.21/0.57          | ~ (v4_lattices @ sk_A)
% 0.21/0.57          | ~ (l2_lattices @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['50', '54'])).
% 0.21/0.57  thf('56', plain, ((l3_lattices @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('57', plain,
% 0.21/0.57      (![X14 : $i, X15 : $i]:
% 0.21/0.57         (~ (l3_lattices @ X14)
% 0.21/0.57          | (v2_struct_0 @ X14)
% 0.21/0.57          | (m1_subset_1 @ (k16_lattice3 @ X14 @ X15) @ (u1_struct_0 @ X14)))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.21/0.57  thf('58', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(commutativity_k3_lattices, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.21/0.57         ( l2_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.57         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57       ( ( k3_lattices @ A @ B @ C ) = ( k3_lattices @ A @ C @ B ) ) ))).
% 0.21/0.57  thf('59', plain,
% 0.21/0.57      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.21/0.57          | ~ (l2_lattices @ X2)
% 0.21/0.57          | ~ (v4_lattices @ X2)
% 0.21/0.57          | (v2_struct_0 @ X2)
% 0.21/0.57          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.21/0.57          | ((k3_lattices @ X2 @ X1 @ X3) = (k3_lattices @ X2 @ X3 @ X1)))),
% 0.21/0.57      inference('cnf', [status(esa)], [commutativity_k3_lattices])).
% 0.21/0.57  thf('60', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((k3_lattices @ sk_A @ sk_B @ X0) = (k3_lattices @ sk_A @ X0 @ sk_B))
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.57          | (v2_struct_0 @ sk_A)
% 0.21/0.57          | ~ (v4_lattices @ sk_A)
% 0.21/0.57          | ~ (l2_lattices @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['58', '59'])).
% 0.21/0.57  thf('61', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v2_struct_0 @ X0)
% 0.21/0.57          | ~ (v10_lattices @ X0)
% 0.21/0.57          | (v4_lattices @ X0)
% 0.21/0.57          | ~ (l3_lattices @ X0))),
% 0.21/0.57      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.57  thf('62', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('63', plain,
% 0.21/0.57      ((~ (l3_lattices @ sk_A) | (v4_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['61', '62'])).
% 0.21/0.57  thf('64', plain, ((l3_lattices @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('65', plain, ((v10_lattices @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('66', plain, ((v4_lattices @ sk_A)),
% 0.21/0.57      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.21/0.57  thf('67', plain, ((l2_lattices @ sk_A)),
% 0.21/0.57      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.57  thf('68', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((k3_lattices @ sk_A @ sk_B @ X0) = (k3_lattices @ sk_A @ X0 @ sk_B))
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.57          | (v2_struct_0 @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['60', '66', '67'])).
% 0.21/0.57  thf('69', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('70', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.57          | ((k3_lattices @ sk_A @ sk_B @ X0)
% 0.21/0.57              = (k3_lattices @ sk_A @ X0 @ sk_B)))),
% 0.21/0.57      inference('clc', [status(thm)], ['68', '69'])).
% 0.21/0.57  thf('71', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v2_struct_0 @ sk_A)
% 0.21/0.57          | ~ (l3_lattices @ sk_A)
% 0.21/0.57          | ((k3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0))
% 0.21/0.57              = (k3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['57', '70'])).
% 0.21/0.57  thf('72', plain, ((l3_lattices @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('73', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v2_struct_0 @ sk_A)
% 0.21/0.57          | ((k3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0))
% 0.21/0.57              = (k3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)))),
% 0.21/0.57      inference('demod', [status(thm)], ['71', '72'])).
% 0.21/0.57  thf('74', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('75', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((k3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0))
% 0.21/0.57           = (k3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B))),
% 0.21/0.57      inference('clc', [status(thm)], ['73', '74'])).
% 0.21/0.57  thf('76', plain, ((v4_lattices @ sk_A)),
% 0.21/0.57      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.21/0.57  thf('77', plain, ((l2_lattices @ sk_A)),
% 0.21/0.57      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.57  thf('78', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v2_struct_0 @ sk_A)
% 0.21/0.57          | ((k3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0))
% 0.21/0.57              = (k1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)))),
% 0.21/0.57      inference('demod', [status(thm)], ['55', '56', '75', '76', '77'])).
% 0.21/0.57  thf('79', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('80', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((k3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0))
% 0.21/0.57           = (k1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B))),
% 0.21/0.57      inference('clc', [status(thm)], ['78', '79'])).
% 0.21/0.57  thf('81', plain,
% 0.21/0.57      (((v2_struct_0 @ sk_A)
% 0.21/0.57        | ((k3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ sk_C)) = (sk_B)))),
% 0.21/0.57      inference('demod', [status(thm)], ['44', '45', '48', '49', '80'])).
% 0.21/0.57  thf('82', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('83', plain,
% 0.21/0.57      (((k3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ sk_C)) = (sk_B))),
% 0.21/0.57      inference('clc', [status(thm)], ['81', '82'])).
% 0.21/0.57  thf('84', plain,
% 0.21/0.57      (![X14 : $i, X15 : $i]:
% 0.21/0.57         (~ (l3_lattices @ X14)
% 0.21/0.57          | (v2_struct_0 @ X14)
% 0.21/0.57          | (m1_subset_1 @ (k16_lattice3 @ X14 @ X15) @ (u1_struct_0 @ X14)))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.21/0.57  thf('85', plain, ((r3_lattice3 @ sk_A @ sk_B @ sk_C)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('86', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('87', plain,
% 0.21/0.57      (![X14 : $i, X15 : $i]:
% 0.21/0.57         (~ (l3_lattices @ X14)
% 0.21/0.57          | (v2_struct_0 @ X14)
% 0.21/0.57          | (m1_subset_1 @ (k16_lattice3 @ X14 @ X15) @ (u1_struct_0 @ X14)))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.21/0.57  thf(t34_lattice3, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.57         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.57           ( ![C:$i]:
% 0.21/0.57             ( ( ( B ) = ( k16_lattice3 @ A @ C ) ) <=>
% 0.21/0.57               ( ( r3_lattice3 @ A @ B @ C ) & 
% 0.21/0.57                 ( ![D:$i]:
% 0.21/0.57                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.57                     ( ( r3_lattice3 @ A @ D @ C ) =>
% 0.21/0.57                       ( r3_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.57  thf('88', plain,
% 0.21/0.57      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.21/0.57          | ((X16) != (k16_lattice3 @ X17 @ X18))
% 0.21/0.57          | ~ (r3_lattice3 @ X17 @ X19 @ X18)
% 0.21/0.57          | (r3_lattices @ X17 @ X19 @ X16)
% 0.21/0.57          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.21/0.57          | ~ (l3_lattices @ X17)
% 0.21/0.57          | ~ (v4_lattice3 @ X17)
% 0.21/0.57          | ~ (v10_lattices @ X17)
% 0.21/0.57          | (v2_struct_0 @ X17))),
% 0.21/0.57      inference('cnf', [status(esa)], [t34_lattice3])).
% 0.21/0.57  thf('89', plain,
% 0.21/0.57      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.57         ((v2_struct_0 @ X17)
% 0.21/0.57          | ~ (v10_lattices @ X17)
% 0.21/0.57          | ~ (v4_lattice3 @ X17)
% 0.21/0.57          | ~ (l3_lattices @ X17)
% 0.21/0.57          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.21/0.57          | (r3_lattices @ X17 @ X19 @ (k16_lattice3 @ X17 @ X18))
% 0.21/0.57          | ~ (r3_lattice3 @ X17 @ X19 @ X18)
% 0.21/0.57          | ~ (m1_subset_1 @ (k16_lattice3 @ X17 @ X18) @ (u1_struct_0 @ X17)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['88'])).
% 0.21/0.57  thf('90', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         ((v2_struct_0 @ X0)
% 0.21/0.57          | ~ (l3_lattices @ X0)
% 0.21/0.57          | ~ (r3_lattice3 @ X0 @ X2 @ X1)
% 0.21/0.57          | (r3_lattices @ X0 @ X2 @ (k16_lattice3 @ X0 @ X1))
% 0.21/0.57          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.57          | ~ (l3_lattices @ X0)
% 0.21/0.57          | ~ (v4_lattice3 @ X0)
% 0.21/0.57          | ~ (v10_lattices @ X0)
% 0.21/0.57          | (v2_struct_0 @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['87', '89'])).
% 0.21/0.57  thf('91', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         (~ (v10_lattices @ X0)
% 0.21/0.57          | ~ (v4_lattice3 @ X0)
% 0.21/0.57          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.57          | (r3_lattices @ X0 @ X2 @ (k16_lattice3 @ X0 @ X1))
% 0.21/0.57          | ~ (r3_lattice3 @ X0 @ X2 @ X1)
% 0.21/0.57          | ~ (l3_lattices @ X0)
% 0.21/0.57          | (v2_struct_0 @ X0))),
% 0.21/0.57      inference('simplify', [status(thm)], ['90'])).
% 0.21/0.57  thf('92', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v2_struct_0 @ sk_A)
% 0.21/0.57          | ~ (l3_lattices @ sk_A)
% 0.21/0.57          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0)
% 0.21/0.57          | (r3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0))
% 0.21/0.57          | ~ (v4_lattice3 @ sk_A)
% 0.21/0.57          | ~ (v10_lattices @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['86', '91'])).
% 0.21/0.57  thf('93', plain, ((l3_lattices @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('94', plain, ((v4_lattice3 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('95', plain, ((v10_lattices @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('96', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v2_struct_0 @ sk_A)
% 0.21/0.57          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0)
% 0.21/0.57          | (r3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0)))),
% 0.21/0.57      inference('demod', [status(thm)], ['92', '93', '94', '95'])).
% 0.21/0.57  thf('97', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('98', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((r3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0))
% 0.21/0.57          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.21/0.57      inference('clc', [status(thm)], ['96', '97'])).
% 0.21/0.57  thf('99', plain,
% 0.21/0.57      ((r3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ sk_C))),
% 0.21/0.57      inference('sup-', [status(thm)], ['85', '98'])).
% 0.21/0.57  thf('100', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('101', plain,
% 0.21/0.57      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 0.21/0.57          | ~ (l3_lattices @ X12)
% 0.21/0.57          | ~ (v9_lattices @ X12)
% 0.21/0.57          | ~ (v8_lattices @ X12)
% 0.21/0.57          | ~ (v6_lattices @ X12)
% 0.21/0.57          | (v2_struct_0 @ X12)
% 0.21/0.57          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.21/0.57          | (r1_lattices @ X12 @ X11 @ X13)
% 0.21/0.57          | ~ (r3_lattices @ X12 @ X11 @ X13))),
% 0.21/0.57      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.21/0.57  thf('102', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (r3_lattices @ sk_A @ sk_B @ X0)
% 0.21/0.57          | (r1_lattices @ sk_A @ sk_B @ X0)
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.57          | (v2_struct_0 @ sk_A)
% 0.21/0.57          | ~ (v6_lattices @ sk_A)
% 0.21/0.57          | ~ (v8_lattices @ sk_A)
% 0.21/0.57          | ~ (v9_lattices @ sk_A)
% 0.21/0.57          | ~ (l3_lattices @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['100', '101'])).
% 0.21/0.57  thf('103', plain, ((v6_lattices @ sk_A)),
% 0.21/0.57      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.21/0.57  thf('104', plain, ((v8_lattices @ sk_A)),
% 0.21/0.57      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.21/0.57  thf('105', plain, ((v9_lattices @ sk_A)),
% 0.21/0.57      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.21/0.57  thf('106', plain, ((l3_lattices @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('107', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (r3_lattices @ sk_A @ sk_B @ X0)
% 0.21/0.57          | (r1_lattices @ sk_A @ sk_B @ X0)
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.57          | (v2_struct_0 @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['102', '103', '104', '105', '106'])).
% 0.21/0.57  thf('108', plain,
% 0.21/0.57      (((v2_struct_0 @ sk_A)
% 0.21/0.57        | ~ (m1_subset_1 @ (k16_lattice3 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.21/0.57        | (r1_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ sk_C)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['99', '107'])).
% 0.21/0.57  thf('109', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('110', plain,
% 0.21/0.57      (((r1_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ sk_C))
% 0.21/0.57        | ~ (m1_subset_1 @ (k16_lattice3 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('clc', [status(thm)], ['108', '109'])).
% 0.21/0.57  thf('111', plain,
% 0.21/0.57      (((v2_struct_0 @ sk_A)
% 0.21/0.57        | ~ (l3_lattices @ sk_A)
% 0.21/0.57        | (r1_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ sk_C)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['84', '110'])).
% 0.21/0.57  thf('112', plain, ((l3_lattices @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('113', plain,
% 0.21/0.57      (((v2_struct_0 @ sk_A)
% 0.21/0.57        | (r1_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ sk_C)))),
% 0.21/0.57      inference('demod', [status(thm)], ['111', '112'])).
% 0.21/0.57  thf('114', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('115', plain,
% 0.21/0.57      ((r1_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ sk_C))),
% 0.21/0.57      inference('clc', [status(thm)], ['113', '114'])).
% 0.21/0.57  thf('116', plain,
% 0.21/0.57      (![X14 : $i, X15 : $i]:
% 0.21/0.57         (~ (l3_lattices @ X14)
% 0.21/0.57          | (v2_struct_0 @ X14)
% 0.21/0.57          | (m1_subset_1 @ (k16_lattice3 @ X14 @ X15) @ (u1_struct_0 @ X14)))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.21/0.57  thf('117', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('118', plain,
% 0.21/0.57      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.21/0.57          | ~ (r1_lattices @ X5 @ X4 @ X6)
% 0.21/0.57          | ((k1_lattices @ X5 @ X4 @ X6) = (X6))
% 0.21/0.57          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.21/0.57          | ~ (l2_lattices @ X5)
% 0.21/0.57          | (v2_struct_0 @ X5))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_lattices])).
% 0.21/0.57  thf('119', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v2_struct_0 @ sk_A)
% 0.21/0.57          | ~ (l2_lattices @ sk_A)
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.57          | ((k1_lattices @ sk_A @ sk_B @ X0) = (X0))
% 0.21/0.57          | ~ (r1_lattices @ sk_A @ sk_B @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['117', '118'])).
% 0.21/0.57  thf('120', plain, ((l2_lattices @ sk_A)),
% 0.21/0.57      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.57  thf('121', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v2_struct_0 @ sk_A)
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.57          | ((k1_lattices @ sk_A @ sk_B @ X0) = (X0))
% 0.21/0.57          | ~ (r1_lattices @ sk_A @ sk_B @ X0))),
% 0.21/0.57      inference('demod', [status(thm)], ['119', '120'])).
% 0.21/0.57  thf('122', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v2_struct_0 @ sk_A)
% 0.21/0.57          | ~ (l3_lattices @ sk_A)
% 0.21/0.57          | ~ (r1_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0))
% 0.21/0.57          | ((k1_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0))
% 0.21/0.57              = (k16_lattice3 @ sk_A @ X0))
% 0.21/0.57          | (v2_struct_0 @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['116', '121'])).
% 0.21/0.57  thf('123', plain, ((l3_lattices @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('124', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v2_struct_0 @ sk_A)
% 0.21/0.57          | ~ (r1_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0))
% 0.21/0.57          | ((k1_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0))
% 0.21/0.57              = (k16_lattice3 @ sk_A @ X0))
% 0.21/0.57          | (v2_struct_0 @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['122', '123'])).
% 0.21/0.57  thf('125', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((k1_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0))
% 0.21/0.57            = (k16_lattice3 @ sk_A @ X0))
% 0.21/0.57          | ~ (r1_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0))
% 0.21/0.57          | (v2_struct_0 @ sk_A))),
% 0.21/0.57      inference('simplify', [status(thm)], ['124'])).
% 0.21/0.57  thf('126', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('127', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (r1_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0))
% 0.21/0.57          | ((k1_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0))
% 0.21/0.57              = (k16_lattice3 @ sk_A @ X0)))),
% 0.21/0.57      inference('clc', [status(thm)], ['125', '126'])).
% 0.21/0.57  thf('128', plain,
% 0.21/0.57      (![X14 : $i, X15 : $i]:
% 0.21/0.57         (~ (l3_lattices @ X14)
% 0.21/0.57          | (v2_struct_0 @ X14)
% 0.21/0.57          | (m1_subset_1 @ (k16_lattice3 @ X14 @ X15) @ (u1_struct_0 @ X14)))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.21/0.57  thf('129', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('130', plain,
% 0.21/0.57      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.21/0.57          | ~ (l2_lattices @ X9)
% 0.21/0.57          | ~ (v4_lattices @ X9)
% 0.21/0.57          | (v2_struct_0 @ X9)
% 0.21/0.57          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.21/0.57          | ((k3_lattices @ X9 @ X8 @ X10) = (k1_lattices @ X9 @ X8 @ X10)))),
% 0.21/0.57      inference('cnf', [status(esa)], [redefinition_k3_lattices])).
% 0.21/0.57  thf('131', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((k3_lattices @ sk_A @ sk_B @ X0) = (k1_lattices @ sk_A @ sk_B @ X0))
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.57          | (v2_struct_0 @ sk_A)
% 0.21/0.57          | ~ (v4_lattices @ sk_A)
% 0.21/0.57          | ~ (l2_lattices @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['129', '130'])).
% 0.21/0.57  thf('132', plain, ((v4_lattices @ sk_A)),
% 0.21/0.57      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.21/0.57  thf('133', plain, ((l2_lattices @ sk_A)),
% 0.21/0.57      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.57  thf('134', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((k3_lattices @ sk_A @ sk_B @ X0) = (k1_lattices @ sk_A @ sk_B @ X0))
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.57          | (v2_struct_0 @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['131', '132', '133'])).
% 0.21/0.57  thf('135', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('136', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.57          | ((k3_lattices @ sk_A @ sk_B @ X0)
% 0.21/0.57              = (k1_lattices @ sk_A @ sk_B @ X0)))),
% 0.21/0.57      inference('clc', [status(thm)], ['134', '135'])).
% 0.21/0.57  thf('137', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v2_struct_0 @ sk_A)
% 0.21/0.57          | ~ (l3_lattices @ sk_A)
% 0.21/0.57          | ((k3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0))
% 0.21/0.57              = (k1_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['128', '136'])).
% 0.21/0.57  thf('138', plain, ((l3_lattices @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('139', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v2_struct_0 @ sk_A)
% 0.21/0.57          | ((k3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0))
% 0.21/0.57              = (k1_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0))))),
% 0.21/0.57      inference('demod', [status(thm)], ['137', '138'])).
% 0.21/0.57  thf('140', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('141', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((k3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0))
% 0.21/0.57           = (k1_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0)))),
% 0.21/0.57      inference('clc', [status(thm)], ['139', '140'])).
% 0.21/0.57  thf('142', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (r1_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0))
% 0.21/0.57          | ((k3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ X0))
% 0.21/0.57              = (k16_lattice3 @ sk_A @ X0)))),
% 0.21/0.57      inference('demod', [status(thm)], ['127', '141'])).
% 0.21/0.57  thf('143', plain,
% 0.21/0.57      (((k3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ sk_C))
% 0.21/0.57         = (k16_lattice3 @ sk_A @ sk_C))),
% 0.21/0.57      inference('sup-', [status(thm)], ['115', '142'])).
% 0.21/0.57  thf('144', plain, (((sk_B) = (k16_lattice3 @ sk_A @ sk_C))),
% 0.21/0.57      inference('sup+', [status(thm)], ['83', '143'])).
% 0.21/0.57  thf('145', plain, (((k16_lattice3 @ sk_A @ sk_C) != (sk_B))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('146', plain, ($false),
% 0.21/0.57      inference('simplify_reflect-', [status(thm)], ['144', '145'])).
% 0.21/0.57  
% 0.21/0.57  % SZS output end Refutation
% 0.21/0.57  
% 0.21/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
