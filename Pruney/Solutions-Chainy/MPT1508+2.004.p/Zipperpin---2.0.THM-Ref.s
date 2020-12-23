%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZyAYjF8F15

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 292 expanded)
%              Number of leaves         :   33 ( 101 expanded)
%              Depth                    :   14
%              Number of atoms          : 1201 (4085 expanded)
%              Number of equality atoms :   28 ( 137 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(r3_lattice3_type,type,(
    r3_lattice3: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(k1_lattices_type,type,(
    k1_lattices: $i > $i > $i > $i )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(dt_k16_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( m1_subset_1 @ ( k16_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l3_lattices @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X11 @ X12 ) @ ( u1_struct_0 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

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

thf('1',plain,(
    r3_lattice3 @ sk_A @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('3',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ( r3_lattices @ X17 @ X16 @ ( k16_lattice3 @ X17 @ X18 ) )
      | ~ ( r3_lattice3 @ X17 @ X16 @ X18 )
      | ~ ( l3_lattices @ X17 )
      | ~ ( v4_lattice3 @ X17 )
      | ~ ( v10_lattices @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t40_lattice3])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r3_lattice3 @ sk_A @ sk_B_1 @ X0 )
      | ( r3_lattices @ sk_A @ sk_B_1 @ ( k16_lattice3 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r3_lattice3 @ sk_A @ sk_B_1 @ X0 )
      | ( r3_lattices @ sk_A @ sk_B_1 @ ( k16_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_A @ sk_B_1 @ ( k16_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattice3 @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    r3_lattices @ sk_A @ sk_B_1 @ ( k16_lattice3 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','10'])).

thf('12',plain,(
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

thf('13',plain,(
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

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattices @ sk_A @ sk_B_1 @ X0 )
      | ( r1_lattices @ sk_A @ sk_B_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

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

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattices @ sk_A @ sk_B_1 @ X0 )
      | ( r1_lattices @ sk_A @ sk_B_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','20','26','32','33'])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k16_lattice3 @ sk_A @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_lattices @ sk_A @ sk_B_1 @ ( k16_lattice3 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['11','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( r1_lattices @ sk_A @ sk_B_1 @ ( k16_lattice3 @ sk_A @ sk_C_1 ) )
    | ~ ( m1_subset_1 @ ( k16_lattice3 @ sk_A @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( r1_lattices @ sk_A @ sk_B_1 @ ( k16_lattice3 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['0','37'])).

thf('39',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ sk_B_1 @ ( k16_lattice3 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    r1_lattices @ sk_A @ sk_B_1 @ ( k16_lattice3 @ sk_A @ sk_C_1 ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l3_lattices @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X11 @ X12 ) @ ( u1_struct_0 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf('44',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('45',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( r1_lattices @ X2 @ X1 @ X3 )
      | ( ( k1_lattices @ X2 @ X1 @ X3 )
        = X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l2_lattices @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_lattices])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l2_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ sk_B_1 @ X0 )
        = X0 )
      | ~ ( r1_lattices @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('48',plain,(
    ! [X4: $i] :
      ( ( l2_lattices @ X4 )
      | ~ ( l3_lattices @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('49',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ sk_B_1 @ X0 )
        = X0 )
      | ~ ( r1_lattices @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r1_lattices @ sk_A @ sk_B_1 @ ( k16_lattice3 @ sk_A @ X0 ) )
      | ( ( k1_lattices @ sk_A @ sk_B_1 @ ( k16_lattice3 @ sk_A @ X0 ) )
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','50'])).

thf('52',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r1_lattices @ sk_A @ sk_B_1 @ ( k16_lattice3 @ sk_A @ X0 ) )
      | ( ( k1_lattices @ sk_A @ sk_B_1 @ ( k16_lattice3 @ sk_A @ X0 ) )
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k1_lattices @ sk_A @ sk_B_1 @ ( k16_lattice3 @ sk_A @ X0 ) )
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ~ ( r1_lattices @ sk_A @ sk_B_1 @ ( k16_lattice3 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ sk_B_1 @ ( k16_lattice3 @ sk_A @ X0 ) )
      | ( ( k1_lattices @ sk_A @ sk_B_1 @ ( k16_lattice3 @ sk_A @ X0 ) )
        = ( k16_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k1_lattices @ sk_A @ sk_B_1 @ ( k16_lattice3 @ sk_A @ sk_C_1 ) )
    = ( k16_lattice3 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['42','56'])).

thf('58',plain,(
    r2_hidden @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
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

thf('60',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ( r3_lattices @ X14 @ ( k16_lattice3 @ X14 @ X15 ) @ X13 )
      | ~ ( r2_hidden @ X13 @ X15 )
      | ~ ( l3_lattices @ X14 )
      | ~ ( v4_lattice3 @ X14 )
      | ~ ( v10_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t38_lattice3])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r2_hidden @ sk_B_1 @ X0 )
      | ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ sk_B_1 @ X0 )
      | ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['61','62','63','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B_1 )
      | ~ ( r2_hidden @ sk_B_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['58','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l3_lattices @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X11 @ X12 ) @ ( u1_struct_0 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf('71',plain,(
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

thf('72',plain,(
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
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B_1 )
      | ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B_1 )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','73'])).

thf('75',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('77',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('78',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B_1 )
      | ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['74','75','76','77','78'])).

thf('80',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B_1 )
      | ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,(
    r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['68','81'])).

thf('83',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l3_lattices @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X11 @ X12 ) @ ( u1_struct_0 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf('84',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( r1_lattices @ X2 @ X1 @ X3 )
      | ( ( k1_lattices @ X2 @ X1 @ X3 )
        = X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l2_lattices @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_lattices])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( ( k1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
        = X2 )
      | ~ ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ( ( k1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l2_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C_1 ) @ sk_B_1 )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['82','86'])).

thf('88',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['47','48'])).

thf('90',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C_1 ) @ sk_B_1 )
      = sk_B_1 ) ),
    inference(demod,[status(thm)],['87','88','89','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( k1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C_1 ) @ sk_B_1 )
    = sk_B_1 ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l3_lattices @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X11 @ X12 ) @ ( u1_struct_0 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf('95',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l2_lattices @ A ) )
     => ( ( v4_lattices @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( k1_lattices @ A @ B @ C )
                  = ( k1_lattices @ A @ C @ B ) ) ) ) ) ) )).

thf('96',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v4_lattices @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ( ( k1_lattices @ X8 @ X10 @ X9 )
        = ( k1_lattices @ X8 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l2_lattices @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_lattices])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l2_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ X0 @ sk_B_1 )
        = ( k1_lattices @ sk_A @ sk_B_1 @ X0 ) )
      | ~ ( v4_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['47','48'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v4_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v4_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ X0 @ sk_B_1 )
        = ( k1_lattices @ sk_A @ sk_B_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['97','98','104'])).

thf('106',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( ( k1_lattices @ sk_A @ X0 @ sk_B_1 )
        = ( k1_lattices @ sk_A @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( ( k1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B_1 )
        = ( k1_lattices @ sk_A @ sk_B_1 @ ( k16_lattice3 @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['94','107'])).

thf('109',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B_1 )
        = ( k1_lattices @ sk_A @ sk_B_1 @ ( k16_lattice3 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B_1 )
      = ( k1_lattices @ sk_A @ sk_B_1 @ ( k16_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( k1_lattices @ sk_A @ sk_B_1 @ ( k16_lattice3 @ sk_A @ sk_C_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['93','112'])).

thf('114',plain,
    ( ( k16_lattice3 @ sk_A @ sk_C_1 )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['57','113'])).

thf('115',plain,(
    ( k16_lattice3 @ sk_A @ sk_C_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['114','115'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZyAYjF8F15
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:41:33 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 82 iterations in 0.056s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.21/0.51  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.21/0.51  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.21/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.51  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.21/0.51  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 0.21/0.51  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.21/0.51  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 0.21/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.51  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 0.21/0.51  thf(r3_lattice3_type, type, r3_lattice3: $i > $i > $i > $o).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 0.21/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.51  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 0.21/0.51  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.21/0.51  thf(k1_lattices_type, type, k1_lattices: $i > $i > $i > $i).
% 0.21/0.51  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.21/0.51  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 0.21/0.51  thf(dt_k16_lattice3, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.21/0.51       ( m1_subset_1 @ ( k16_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      (![X11 : $i, X12 : $i]:
% 0.21/0.51         (~ (l3_lattices @ X11)
% 0.21/0.51          | (v2_struct_0 @ X11)
% 0.21/0.51          | (m1_subset_1 @ (k16_lattice3 @ X11 @ X12) @ (u1_struct_0 @ X11)))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.21/0.51  thf(t42_lattice3, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.51         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( ( r2_hidden @ B @ C ) & ( r3_lattice3 @ A @ B @ C ) ) =>
% 0.21/0.51               ( ( k16_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.51            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.51          ( ![B:$i]:
% 0.21/0.51            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51              ( ![C:$i]:
% 0.21/0.51                ( ( ( r2_hidden @ B @ C ) & ( r3_lattice3 @ A @ B @ C ) ) =>
% 0.21/0.51                  ( ( k16_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t42_lattice3])).
% 0.21/0.51  thf('1', plain, ((r3_lattice3 @ sk_A @ sk_B_1 @ sk_C_1)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('2', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t40_lattice3, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.51         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( r3_lattice3 @ A @ B @ C ) =>
% 0.21/0.51               ( r3_lattices @ A @ B @ ( k16_lattice3 @ A @ C ) ) ) ) ) ) ))).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.21/0.51          | (r3_lattices @ X17 @ X16 @ (k16_lattice3 @ X17 @ X18))
% 0.21/0.51          | ~ (r3_lattice3 @ X17 @ X16 @ X18)
% 0.21/0.51          | ~ (l3_lattices @ X17)
% 0.21/0.51          | ~ (v4_lattice3 @ X17)
% 0.21/0.51          | ~ (v10_lattices @ X17)
% 0.21/0.51          | (v2_struct_0 @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [t40_lattice3])).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (v10_lattices @ sk_A)
% 0.21/0.51          | ~ (v4_lattice3 @ sk_A)
% 0.21/0.51          | ~ (l3_lattices @ sk_A)
% 0.21/0.51          | ~ (r3_lattice3 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.51          | (r3_lattices @ sk_A @ sk_B_1 @ (k16_lattice3 @ sk_A @ X0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.51  thf('5', plain, ((v10_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('6', plain, ((v4_lattice3 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('7', plain, ((l3_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (r3_lattice3 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.51          | (r3_lattices @ sk_A @ sk_B_1 @ (k16_lattice3 @ sk_A @ X0)))),
% 0.21/0.51      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.21/0.51  thf('9', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r3_lattices @ sk_A @ sk_B_1 @ (k16_lattice3 @ sk_A @ X0))
% 0.21/0.51          | ~ (r3_lattice3 @ sk_A @ sk_B_1 @ X0))),
% 0.21/0.51      inference('clc', [status(thm)], ['8', '9'])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      ((r3_lattices @ sk_A @ sk_B_1 @ (k16_lattice3 @ sk_A @ sk_C_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '10'])).
% 0.21/0.51  thf('12', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(redefinition_r3_lattices, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.21/0.51         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 0.21/0.51         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.51         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 0.21/0.51          | ~ (l3_lattices @ X6)
% 0.21/0.51          | ~ (v9_lattices @ X6)
% 0.21/0.51          | ~ (v8_lattices @ X6)
% 0.21/0.51          | ~ (v6_lattices @ X6)
% 0.21/0.51          | (v2_struct_0 @ X6)
% 0.21/0.51          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 0.21/0.51          | (r1_lattices @ X6 @ X5 @ X7)
% 0.21/0.51          | ~ (r3_lattices @ X6 @ X5 @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (r3_lattices @ sk_A @ sk_B_1 @ X0)
% 0.21/0.51          | (r1_lattices @ sk_A @ sk_B_1 @ X0)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | (v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (v6_lattices @ sk_A)
% 0.21/0.51          | ~ (v8_lattices @ sk_A)
% 0.21/0.51          | ~ (v9_lattices @ sk_A)
% 0.21/0.51          | ~ (l3_lattices @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf(cc1_lattices, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l3_lattices @ A ) =>
% 0.21/0.51       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.21/0.51         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.21/0.51           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.21/0.51           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X0)
% 0.21/0.51          | ~ (v10_lattices @ X0)
% 0.21/0.51          | (v6_lattices @ X0)
% 0.21/0.51          | ~ (l3_lattices @ X0))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.51  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.51  thf('18', plain, ((l3_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('19', plain, ((v10_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('20', plain, ((v6_lattices @ sk_A)),
% 0.21/0.51      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X0)
% 0.21/0.51          | ~ (v10_lattices @ X0)
% 0.21/0.51          | (v8_lattices @ X0)
% 0.21/0.51          | ~ (l3_lattices @ X0))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.51  thf('22', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.51  thf('24', plain, ((l3_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('25', plain, ((v10_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('26', plain, ((v8_lattices @ sk_A)),
% 0.21/0.51      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X0)
% 0.21/0.51          | ~ (v10_lattices @ X0)
% 0.21/0.51          | (v9_lattices @ X0)
% 0.21/0.51          | ~ (l3_lattices @ X0))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.51  thf('28', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.51  thf('30', plain, ((l3_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('31', plain, ((v10_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('32', plain, ((v9_lattices @ sk_A)),
% 0.21/0.51      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.21/0.51  thf('33', plain, ((l3_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (r3_lattices @ sk_A @ sk_B_1 @ X0)
% 0.21/0.51          | (r1_lattices @ sk_A @ sk_B_1 @ X0)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['14', '20', '26', '32', '33'])).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (m1_subset_1 @ (k16_lattice3 @ sk_A @ sk_C_1) @ 
% 0.21/0.51             (u1_struct_0 @ sk_A))
% 0.21/0.51        | (r1_lattices @ sk_A @ sk_B_1 @ (k16_lattice3 @ sk_A @ sk_C_1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['11', '34'])).
% 0.21/0.51  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      (((r1_lattices @ sk_A @ sk_B_1 @ (k16_lattice3 @ sk_A @ sk_C_1))
% 0.21/0.51        | ~ (m1_subset_1 @ (k16_lattice3 @ sk_A @ sk_C_1) @ 
% 0.21/0.51             (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('clc', [status(thm)], ['35', '36'])).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (l3_lattices @ sk_A)
% 0.21/0.51        | (r1_lattices @ sk_A @ sk_B_1 @ (k16_lattice3 @ sk_A @ sk_C_1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['0', '37'])).
% 0.21/0.51  thf('39', plain, ((l3_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('40', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | (r1_lattices @ sk_A @ sk_B_1 @ (k16_lattice3 @ sk_A @ sk_C_1)))),
% 0.21/0.51      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.51  thf('41', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      ((r1_lattices @ sk_A @ sk_B_1 @ (k16_lattice3 @ sk_A @ sk_C_1))),
% 0.21/0.51      inference('clc', [status(thm)], ['40', '41'])).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      (![X11 : $i, X12 : $i]:
% 0.21/0.51         (~ (l3_lattices @ X11)
% 0.21/0.51          | (v2_struct_0 @ X11)
% 0.21/0.51          | (m1_subset_1 @ (k16_lattice3 @ X11 @ X12) @ (u1_struct_0 @ X11)))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.21/0.51  thf('44', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(d3_lattices, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l2_lattices @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51               ( ( r1_lattices @ A @ B @ C ) <=>
% 0.21/0.51                 ( ( k1_lattices @ A @ B @ C ) = ( C ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.21/0.51          | ~ (r1_lattices @ X2 @ X1 @ X3)
% 0.21/0.51          | ((k1_lattices @ X2 @ X1 @ X3) = (X3))
% 0.21/0.51          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.21/0.51          | ~ (l2_lattices @ X2)
% 0.21/0.51          | (v2_struct_0 @ X2))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_lattices])).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (l2_lattices @ sk_A)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | ((k1_lattices @ sk_A @ sk_B_1 @ X0) = (X0))
% 0.21/0.51          | ~ (r1_lattices @ sk_A @ sk_B_1 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.51  thf('47', plain, ((l3_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_l3_lattices, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 0.21/0.51  thf('48', plain, (![X4 : $i]: ((l2_lattices @ X4) | ~ (l3_lattices @ X4))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.21/0.51  thf('49', plain, ((l2_lattices @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.51  thf('50', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | ((k1_lattices @ sk_A @ sk_B_1 @ X0) = (X0))
% 0.21/0.51          | ~ (r1_lattices @ sk_A @ sk_B_1 @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['46', '49'])).
% 0.21/0.51  thf('51', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (l3_lattices @ sk_A)
% 0.21/0.51          | ~ (r1_lattices @ sk_A @ sk_B_1 @ (k16_lattice3 @ sk_A @ X0))
% 0.21/0.51          | ((k1_lattices @ sk_A @ sk_B_1 @ (k16_lattice3 @ sk_A @ X0))
% 0.21/0.51              = (k16_lattice3 @ sk_A @ X0))
% 0.21/0.51          | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['43', '50'])).
% 0.21/0.51  thf('52', plain, ((l3_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('53', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (r1_lattices @ sk_A @ sk_B_1 @ (k16_lattice3 @ sk_A @ X0))
% 0.21/0.51          | ((k1_lattices @ sk_A @ sk_B_1 @ (k16_lattice3 @ sk_A @ X0))
% 0.21/0.51              = (k16_lattice3 @ sk_A @ X0))
% 0.21/0.51          | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['51', '52'])).
% 0.21/0.51  thf('54', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((k1_lattices @ sk_A @ sk_B_1 @ (k16_lattice3 @ sk_A @ X0))
% 0.21/0.51            = (k16_lattice3 @ sk_A @ X0))
% 0.21/0.51          | ~ (r1_lattices @ sk_A @ sk_B_1 @ (k16_lattice3 @ sk_A @ X0))
% 0.21/0.51          | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('simplify', [status(thm)], ['53'])).
% 0.21/0.51  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('56', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (r1_lattices @ sk_A @ sk_B_1 @ (k16_lattice3 @ sk_A @ X0))
% 0.21/0.51          | ((k1_lattices @ sk_A @ sk_B_1 @ (k16_lattice3 @ sk_A @ X0))
% 0.21/0.51              = (k16_lattice3 @ sk_A @ X0)))),
% 0.21/0.51      inference('clc', [status(thm)], ['54', '55'])).
% 0.21/0.51  thf('57', plain,
% 0.21/0.51      (((k1_lattices @ sk_A @ sk_B_1 @ (k16_lattice3 @ sk_A @ sk_C_1))
% 0.21/0.51         = (k16_lattice3 @ sk_A @ sk_C_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['42', '56'])).
% 0.21/0.51  thf('58', plain, ((r2_hidden @ sk_B_1 @ sk_C_1)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('59', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t38_lattice3, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.51         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( r2_hidden @ B @ C ) =>
% 0.21/0.51               ( ( r3_lattices @ A @ B @ ( k15_lattice3 @ A @ C ) ) & 
% 0.21/0.51                 ( r3_lattices @ A @ ( k16_lattice3 @ A @ C ) @ B ) ) ) ) ) ) ))).
% 0.21/0.51  thf('60', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.21/0.51          | (r3_lattices @ X14 @ (k16_lattice3 @ X14 @ X15) @ X13)
% 0.21/0.51          | ~ (r2_hidden @ X13 @ X15)
% 0.21/0.51          | ~ (l3_lattices @ X14)
% 0.21/0.51          | ~ (v4_lattice3 @ X14)
% 0.21/0.51          | ~ (v10_lattices @ X14)
% 0.21/0.51          | (v2_struct_0 @ X14))),
% 0.21/0.51      inference('cnf', [status(esa)], [t38_lattice3])).
% 0.21/0.51  thf('61', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (v10_lattices @ sk_A)
% 0.21/0.51          | ~ (v4_lattice3 @ sk_A)
% 0.21/0.51          | ~ (l3_lattices @ sk_A)
% 0.21/0.51          | ~ (r2_hidden @ sk_B_1 @ X0)
% 0.21/0.51          | (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.51  thf('62', plain, ((v10_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('63', plain, ((v4_lattice3 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('64', plain, ((l3_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('65', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (r2_hidden @ sk_B_1 @ X0)
% 0.21/0.51          | (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B_1))),
% 0.21/0.51      inference('demod', [status(thm)], ['61', '62', '63', '64'])).
% 0.21/0.51  thf('66', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('67', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B_1)
% 0.21/0.51          | ~ (r2_hidden @ sk_B_1 @ X0))),
% 0.21/0.51      inference('clc', [status(thm)], ['65', '66'])).
% 0.21/0.51  thf('68', plain,
% 0.21/0.51      ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C_1) @ sk_B_1)),
% 0.21/0.51      inference('sup-', [status(thm)], ['58', '67'])).
% 0.21/0.51  thf('69', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('70', plain,
% 0.21/0.51      (![X11 : $i, X12 : $i]:
% 0.21/0.51         (~ (l3_lattices @ X11)
% 0.21/0.51          | (v2_struct_0 @ X11)
% 0.21/0.51          | (m1_subset_1 @ (k16_lattice3 @ X11 @ X12) @ (u1_struct_0 @ X11)))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.21/0.51  thf('71', plain,
% 0.21/0.51      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 0.21/0.51          | ~ (l3_lattices @ X6)
% 0.21/0.51          | ~ (v9_lattices @ X6)
% 0.21/0.51          | ~ (v8_lattices @ X6)
% 0.21/0.51          | ~ (v6_lattices @ X6)
% 0.21/0.51          | (v2_struct_0 @ X6)
% 0.21/0.51          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 0.21/0.51          | (r1_lattices @ X6 @ X5 @ X7)
% 0.21/0.51          | ~ (r3_lattices @ X6 @ X5 @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.21/0.51  thf('72', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X0)
% 0.21/0.51          | ~ (l3_lattices @ X0)
% 0.21/0.51          | ~ (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.21/0.51          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.21/0.51          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.51          | (v2_struct_0 @ X0)
% 0.21/0.51          | ~ (v6_lattices @ X0)
% 0.21/0.51          | ~ (v8_lattices @ X0)
% 0.21/0.51          | ~ (v9_lattices @ X0)
% 0.21/0.51          | ~ (l3_lattices @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['70', '71'])).
% 0.21/0.51  thf('73', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (v9_lattices @ X0)
% 0.21/0.51          | ~ (v8_lattices @ X0)
% 0.21/0.51          | ~ (v6_lattices @ X0)
% 0.21/0.51          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.51          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.21/0.51          | ~ (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.21/0.51          | ~ (l3_lattices @ X0)
% 0.21/0.51          | (v2_struct_0 @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['72'])).
% 0.21/0.51  thf('74', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (l3_lattices @ sk_A)
% 0.21/0.51          | ~ (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B_1)
% 0.21/0.51          | (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B_1)
% 0.21/0.51          | ~ (v6_lattices @ sk_A)
% 0.21/0.51          | ~ (v8_lattices @ sk_A)
% 0.21/0.51          | ~ (v9_lattices @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['69', '73'])).
% 0.21/0.51  thf('75', plain, ((l3_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('76', plain, ((v6_lattices @ sk_A)),
% 0.21/0.51      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.21/0.51  thf('77', plain, ((v8_lattices @ sk_A)),
% 0.21/0.51      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.21/0.51  thf('78', plain, ((v9_lattices @ sk_A)),
% 0.21/0.51      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.21/0.51  thf('79', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B_1)
% 0.21/0.51          | (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B_1))),
% 0.21/0.51      inference('demod', [status(thm)], ['74', '75', '76', '77', '78'])).
% 0.21/0.51  thf('80', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('81', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B_1)
% 0.21/0.51          | ~ (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B_1))),
% 0.21/0.51      inference('clc', [status(thm)], ['79', '80'])).
% 0.21/0.51  thf('82', plain,
% 0.21/0.51      ((r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C_1) @ sk_B_1)),
% 0.21/0.51      inference('sup-', [status(thm)], ['68', '81'])).
% 0.21/0.51  thf('83', plain,
% 0.21/0.51      (![X11 : $i, X12 : $i]:
% 0.21/0.51         (~ (l3_lattices @ X11)
% 0.21/0.51          | (v2_struct_0 @ X11)
% 0.21/0.51          | (m1_subset_1 @ (k16_lattice3 @ X11 @ X12) @ (u1_struct_0 @ X11)))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.21/0.51  thf('84', plain,
% 0.21/0.51      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.21/0.51          | ~ (r1_lattices @ X2 @ X1 @ X3)
% 0.21/0.51          | ((k1_lattices @ X2 @ X1 @ X3) = (X3))
% 0.21/0.51          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.21/0.51          | ~ (l2_lattices @ X2)
% 0.21/0.51          | (v2_struct_0 @ X2))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_lattices])).
% 0.21/0.51  thf('85', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X0)
% 0.21/0.51          | ~ (l3_lattices @ X0)
% 0.21/0.51          | (v2_struct_0 @ X0)
% 0.21/0.51          | ~ (l2_lattices @ X0)
% 0.21/0.51          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.51          | ((k1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2) = (X2))
% 0.21/0.51          | ~ (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2))),
% 0.21/0.51      inference('sup-', [status(thm)], ['83', '84'])).
% 0.21/0.51  thf('86', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.21/0.51          | ((k1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2) = (X2))
% 0.21/0.51          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.51          | ~ (l2_lattices @ X0)
% 0.21/0.51          | ~ (l3_lattices @ X0)
% 0.21/0.51          | (v2_struct_0 @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['85'])).
% 0.21/0.51  thf('87', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (l3_lattices @ sk_A)
% 0.21/0.51        | ~ (l2_lattices @ sk_A)
% 0.21/0.51        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.51        | ((k1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C_1) @ sk_B_1)
% 0.21/0.51            = (sk_B_1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['82', '86'])).
% 0.21/0.51  thf('88', plain, ((l3_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('89', plain, ((l2_lattices @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.51  thf('90', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('91', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ((k1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C_1) @ sk_B_1)
% 0.21/0.51            = (sk_B_1)))),
% 0.21/0.51      inference('demod', [status(thm)], ['87', '88', '89', '90'])).
% 0.21/0.51  thf('92', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('93', plain,
% 0.21/0.51      (((k1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C_1) @ sk_B_1)
% 0.21/0.51         = (sk_B_1))),
% 0.21/0.51      inference('clc', [status(thm)], ['91', '92'])).
% 0.21/0.51  thf('94', plain,
% 0.21/0.51      (![X11 : $i, X12 : $i]:
% 0.21/0.51         (~ (l3_lattices @ X11)
% 0.21/0.51          | (v2_struct_0 @ X11)
% 0.21/0.51          | (m1_subset_1 @ (k16_lattice3 @ X11 @ X12) @ (u1_struct_0 @ X11)))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.21/0.51  thf('95', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(d4_lattices, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l2_lattices @ A ) ) =>
% 0.21/0.51       ( ( v4_lattices @ A ) <=>
% 0.21/0.51         ( ![B:$i]:
% 0.21/0.51           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51             ( ![C:$i]:
% 0.21/0.51               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51                 ( ( k1_lattices @ A @ B @ C ) = ( k1_lattices @ A @ C @ B ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('96', plain,
% 0.21/0.51      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.51         (~ (v4_lattices @ X8)
% 0.21/0.51          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.21/0.51          | ((k1_lattices @ X8 @ X10 @ X9) = (k1_lattices @ X8 @ X9 @ X10))
% 0.21/0.51          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X8))
% 0.21/0.51          | ~ (l2_lattices @ X8)
% 0.21/0.51          | (v2_struct_0 @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [d4_lattices])).
% 0.21/0.51  thf('97', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (l2_lattices @ sk_A)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | ((k1_lattices @ sk_A @ X0 @ sk_B_1)
% 0.21/0.51              = (k1_lattices @ sk_A @ sk_B_1 @ X0))
% 0.21/0.51          | ~ (v4_lattices @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['95', '96'])).
% 0.21/0.51  thf('98', plain, ((l2_lattices @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.51  thf('99', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X0)
% 0.21/0.51          | ~ (v10_lattices @ X0)
% 0.21/0.51          | (v4_lattices @ X0)
% 0.21/0.51          | ~ (l3_lattices @ X0))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.51  thf('100', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('101', plain,
% 0.21/0.51      ((~ (l3_lattices @ sk_A) | (v4_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['99', '100'])).
% 0.21/0.51  thf('102', plain, ((l3_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('103', plain, ((v10_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('104', plain, ((v4_lattices @ sk_A)),
% 0.21/0.51      inference('demod', [status(thm)], ['101', '102', '103'])).
% 0.21/0.51  thf('105', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | ((k1_lattices @ sk_A @ X0 @ sk_B_1)
% 0.21/0.51              = (k1_lattices @ sk_A @ sk_B_1 @ X0)))),
% 0.21/0.51      inference('demod', [status(thm)], ['97', '98', '104'])).
% 0.21/0.51  thf('106', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('107', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((k1_lattices @ sk_A @ X0 @ sk_B_1)
% 0.21/0.51            = (k1_lattices @ sk_A @ sk_B_1 @ X0))
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('clc', [status(thm)], ['105', '106'])).
% 0.21/0.51  thf('108', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (l3_lattices @ sk_A)
% 0.21/0.51          | ((k1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B_1)
% 0.21/0.51              = (k1_lattices @ sk_A @ sk_B_1 @ (k16_lattice3 @ sk_A @ X0))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['94', '107'])).
% 0.21/0.51  thf('109', plain, ((l3_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('110', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_A)
% 0.21/0.51          | ((k1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B_1)
% 0.21/0.51              = (k1_lattices @ sk_A @ sk_B_1 @ (k16_lattice3 @ sk_A @ X0))))),
% 0.21/0.51      inference('demod', [status(thm)], ['108', '109'])).
% 0.21/0.51  thf('111', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('112', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((k1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B_1)
% 0.21/0.51           = (k1_lattices @ sk_A @ sk_B_1 @ (k16_lattice3 @ sk_A @ X0)))),
% 0.21/0.51      inference('clc', [status(thm)], ['110', '111'])).
% 0.21/0.51  thf('113', plain,
% 0.21/0.51      (((k1_lattices @ sk_A @ sk_B_1 @ (k16_lattice3 @ sk_A @ sk_C_1))
% 0.21/0.51         = (sk_B_1))),
% 0.21/0.51      inference('demod', [status(thm)], ['93', '112'])).
% 0.21/0.51  thf('114', plain, (((k16_lattice3 @ sk_A @ sk_C_1) = (sk_B_1))),
% 0.21/0.51      inference('sup+', [status(thm)], ['57', '113'])).
% 0.21/0.51  thf('115', plain, (((k16_lattice3 @ sk_A @ sk_C_1) != (sk_B_1))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('116', plain, ($false),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['114', '115'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
