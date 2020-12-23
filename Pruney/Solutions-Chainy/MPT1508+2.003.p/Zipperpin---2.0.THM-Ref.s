%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VhGANHUcdZ

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 263 expanded)
%              Number of leaves         :   33 (  93 expanded)
%              Depth                    :   18
%              Number of atoms          : 1011 (3664 expanded)
%              Number of equality atoms :   13 ( 113 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r3_lattice3_type,type,(
    r3_lattice3: $i > $i > $i > $o )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(a_2_1_lattice3_type,type,(
    a_2_1_lattice3: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

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
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ( r3_lattices @ X17 @ ( k16_lattice3 @ X17 @ X18 ) @ X16 )
      | ~ ( r2_hidden @ X16 @ X18 )
      | ~ ( l3_lattices @ X17 )
      | ~ ( v4_lattice3 @ X17 )
      | ~ ( v10_lattices @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t38_lattice3])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
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
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['1','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k16_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( m1_subset_1 @ ( k16_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X10 @ X11 ) @ ( u1_struct_0 @ X10 ) ) ) ),
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

thf('14',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X3 ) )
      | ~ ( l3_lattices @ X3 )
      | ~ ( v9_lattices @ X3 )
      | ~ ( v8_lattices @ X3 )
      | ~ ( v6_lattices @ X3 )
      | ( v2_struct_0 @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ( r1_lattices @ X3 @ X2 @ X4 )
      | ~ ( r3_lattices @ X3 @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('15',plain,(
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
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r3_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
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

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('26',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','24','30','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B )
      | ~ ( r3_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    r1_lattices @ sk_A @ ( k16_lattice3 @ sk_A @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['11','39'])).

thf('41',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X10 @ X11 ) @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf(t26_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v4_lattices @ A )
        & ( l2_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( r1_lattices @ A @ B @ C )
                  & ( r1_lattices @ A @ C @ B ) )
               => ( B = C ) ) ) ) ) )).

thf('42',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ~ ( r1_lattices @ X6 @ X5 @ X7 )
      | ~ ( r1_lattices @ X6 @ X7 @ X5 )
      | ( X5 = X7 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l2_lattices @ X6 )
      | ~ ( v4_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t26_lattices])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_lattices @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( ( k16_lattice3 @ X0 @ X1 )
        = X2 )
      | ~ ( r1_lattices @ X0 @ X2 @ ( k16_lattice3 @ X0 @ X1 ) )
      | ~ ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattices @ X0 @ ( k16_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_lattices @ X0 @ X2 @ ( k16_lattice3 @ X0 @ X1 ) )
      | ( ( k16_lattice3 @ X0 @ X1 )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l2_lattices @ X0 )
      | ~ ( v4_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v4_lattices @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( ( k16_lattice3 @ sk_A @ sk_C )
      = sk_B )
    | ~ ( r1_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['40','44'])).

thf('46',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v4_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v4_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('54',plain,(
    ! [X1: $i] :
      ( ( l2_lattices @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('55',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( m1_subset_1 @ ( k16_lattice3 @ X10 @ X11 ) @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k16_lattice3])).

thf(d22_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( k16_lattice3 @ A @ B )
          = ( k15_lattice3 @ A @ ( a_2_1_lattice3 @ A @ B ) ) ) ) )).

thf('58',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k16_lattice3 @ X8 @ X9 )
        = ( k15_lattice3 @ X8 @ ( a_2_1_lattice3 @ X8 @ X9 ) ) )
      | ~ ( l3_lattices @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d22_lattice3])).

thf('59',plain,(
    r3_lattice3 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fraenkel_a_2_1_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( l3_lattices @ B ) )
     => ( ( r2_hidden @ A @ ( a_2_1_lattice3 @ B @ C ) )
      <=> ? [D: $i] :
            ( ( r3_lattice3 @ B @ D @ C )
            & ( A = D )
            & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('61',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( l3_lattices @ X12 )
      | ( v2_struct_0 @ X12 )
      | ( r2_hidden @ X14 @ ( a_2_1_lattice3 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X12 ) )
      | ( X14 != X15 )
      | ~ ( r3_lattice3 @ X12 @ X15 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_lattice3])).

thf('62',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ~ ( r3_lattice3 @ X12 @ X15 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X12 ) )
      | ( r2_hidden @ X15 @ ( a_2_1_lattice3 @ X12 @ X13 ) )
      | ( v2_struct_0 @ X12 )
      | ~ ( l3_lattices @ X12 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','62'])).

thf('64',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ ( a_2_1_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    r2_hidden @ sk_B @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['59','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ( r3_lattices @ X17 @ X16 @ ( k15_lattice3 @ X17 @ X18 ) )
      | ~ ( r2_hidden @ X16 @ X18 )
      | ~ ( l3_lattices @ X17 )
      | ~ ( v4_lattice3 @ X17 )
      | ~ ( v10_lattices @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t38_lattice3])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['71','72','73','74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    r3_lattices @ sk_A @ sk_B @ ( k15_lattice3 @ sk_A @ ( a_2_1_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['68','77'])).

thf('79',plain,
    ( ( r3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup+',[status(thm)],['58','78'])).

thf('80',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( r3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    r3_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X3 ) )
      | ~ ( l3_lattices @ X3 )
      | ~ ( v9_lattices @ X3 )
      | ~ ( v8_lattices @ X3 )
      | ~ ( v6_lattices @ X3 )
      | ( v2_struct_0 @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ( r1_lattices @ X3 @ X2 @ X4 )
      | ~ ( r3_lattices @ X3 @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattices @ sk_A @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('88',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('89',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('90',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattices @ sk_A @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['86','87','88','89','90'])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k16_lattice3 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['83','91'])).

thf('93',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( r1_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ sk_C ) )
    | ~ ( m1_subset_1 @ ( k16_lattice3 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( r1_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['57','94'])).

thf('96',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    r1_lattices @ sk_A @ sk_B @ ( k16_lattice3 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k16_lattice3 @ sk_A @ sk_C )
      = sk_B ) ),
    inference(demod,[status(thm)],['45','46','52','55','56','99'])).

thf('101',plain,(
    ( k16_lattice3 @ sk_A @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['100','101'])).

thf('103',plain,(
    $false ),
    inference(demod,[status(thm)],['0','102'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VhGANHUcdZ
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:42:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 71 iterations in 0.040s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(r3_lattice3_type, type, r3_lattice3: $i > $i > $i > $o).
% 0.20/0.50  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.20/0.50  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.50  thf(a_2_1_lattice3_type, type, a_2_1_lattice3: $i > $i > $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 0.20/0.50  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.20/0.50  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.50  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 0.20/0.50  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 0.20/0.50  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.20/0.50  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 0.20/0.50  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.20/0.50  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 0.20/0.50  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.20/0.50  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 0.20/0.50  thf(t42_lattice3, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.20/0.50         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( ( r2_hidden @ B @ C ) & ( r3_lattice3 @ A @ B @ C ) ) =>
% 0.20/0.50               ( ( k16_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.20/0.50            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.20/0.50          ( ![B:$i]:
% 0.20/0.50            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50              ( ![C:$i]:
% 0.20/0.50                ( ( ( r2_hidden @ B @ C ) & ( r3_lattice3 @ A @ B @ C ) ) =>
% 0.20/0.50                  ( ( k16_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t42_lattice3])).
% 0.20/0.50  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('1', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t38_lattice3, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.20/0.50         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( r2_hidden @ B @ C ) =>
% 0.20/0.50               ( ( r3_lattices @ A @ B @ ( k15_lattice3 @ A @ C ) ) & 
% 0.20/0.50                 ( r3_lattices @ A @ ( k16_lattice3 @ A @ C ) @ B ) ) ) ) ) ) ))).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.20/0.50          | (r3_lattices @ X17 @ (k16_lattice3 @ X17 @ X18) @ X16)
% 0.20/0.50          | ~ (r2_hidden @ X16 @ X18)
% 0.20/0.50          | ~ (l3_lattices @ X17)
% 0.20/0.50          | ~ (v4_lattice3 @ X17)
% 0.20/0.50          | ~ (v10_lattices @ X17)
% 0.20/0.50          | (v2_struct_0 @ X17))),
% 0.20/0.50      inference('cnf', [status(esa)], [t38_lattice3])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (v10_lattices @ sk_A)
% 0.20/0.50          | ~ (v4_lattice3 @ sk_A)
% 0.20/0.50          | ~ (l3_lattices @ sk_A)
% 0.20/0.50          | ~ (r2_hidden @ sk_B @ X0)
% 0.20/0.50          | (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.50  thf('5', plain, ((v10_lattices @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('6', plain, ((v4_lattice3 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('7', plain, ((l3_lattices @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (r2_hidden @ sk_B @ X0)
% 0.20/0.50          | (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.20/0.50  thf('9', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.20/0.50          | ~ (r2_hidden @ sk_B @ X0))),
% 0.20/0.50      inference('clc', [status(thm)], ['8', '9'])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      ((r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C) @ sk_B)),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '10'])).
% 0.20/0.50  thf('12', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(dt_k16_lattice3, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.20/0.50       ( m1_subset_1 @ ( k16_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X10 : $i, X11 : $i]:
% 0.20/0.50         (~ (l3_lattices @ X10)
% 0.20/0.50          | (v2_struct_0 @ X10)
% 0.20/0.50          | (m1_subset_1 @ (k16_lattice3 @ X10 @ X11) @ (u1_struct_0 @ X10)))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.20/0.50  thf(redefinition_r3_lattices, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.20/0.50         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 0.20/0.50         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.50         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X3))
% 0.20/0.50          | ~ (l3_lattices @ X3)
% 0.20/0.50          | ~ (v9_lattices @ X3)
% 0.20/0.50          | ~ (v8_lattices @ X3)
% 0.20/0.50          | ~ (v6_lattices @ X3)
% 0.20/0.50          | (v2_struct_0 @ X3)
% 0.20/0.50          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 0.20/0.50          | (r1_lattices @ X3 @ X2 @ X4)
% 0.20/0.50          | ~ (r3_lattices @ X3 @ X2 @ X4))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X0)
% 0.20/0.50          | ~ (l3_lattices @ X0)
% 0.20/0.50          | ~ (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.20/0.50          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.20/0.50          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.50          | (v2_struct_0 @ X0)
% 0.20/0.50          | ~ (v6_lattices @ X0)
% 0.20/0.50          | ~ (v8_lattices @ X0)
% 0.20/0.50          | ~ (v9_lattices @ X0)
% 0.20/0.50          | ~ (l3_lattices @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (v9_lattices @ X0)
% 0.20/0.50          | ~ (v8_lattices @ X0)
% 0.20/0.50          | ~ (v6_lattices @ X0)
% 0.20/0.50          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.50          | (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.20/0.50          | ~ (r3_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.20/0.50          | ~ (l3_lattices @ X0)
% 0.20/0.50          | (v2_struct_0 @ X0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (l3_lattices @ sk_A)
% 0.20/0.50          | ~ (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.20/0.50          | (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.20/0.50          | ~ (v6_lattices @ sk_A)
% 0.20/0.50          | ~ (v8_lattices @ sk_A)
% 0.20/0.50          | ~ (v9_lattices @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['12', '16'])).
% 0.20/0.50  thf('18', plain, ((l3_lattices @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(cc1_lattices, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l3_lattices @ A ) =>
% 0.20/0.50       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.20/0.50         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.20/0.50           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.20/0.50           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X0)
% 0.20/0.50          | ~ (v10_lattices @ X0)
% 0.20/0.50          | (v6_lattices @ X0)
% 0.20/0.50          | ~ (l3_lattices @ X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.20/0.50  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.50  thf('22', plain, ((l3_lattices @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('23', plain, ((v10_lattices @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('24', plain, ((v6_lattices @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X0)
% 0.20/0.50          | ~ (v10_lattices @ X0)
% 0.20/0.50          | (v8_lattices @ X0)
% 0.20/0.50          | ~ (l3_lattices @ X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.20/0.50  thf('26', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.50  thf('28', plain, ((l3_lattices @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('29', plain, ((v10_lattices @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('30', plain, ((v8_lattices @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X0)
% 0.20/0.50          | ~ (v10_lattices @ X0)
% 0.20/0.50          | (v9_lattices @ X0)
% 0.20/0.50          | ~ (l3_lattices @ X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.20/0.50  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.50  thf('34', plain, ((l3_lattices @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('35', plain, ((v10_lattices @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('36', plain, ((v9_lattices @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.20/0.50          | (r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['17', '18', '24', '30', '36'])).
% 0.20/0.50  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B)
% 0.20/0.50          | ~ (r3_lattices @ sk_A @ (k16_lattice3 @ sk_A @ X0) @ sk_B))),
% 0.20/0.50      inference('clc', [status(thm)], ['37', '38'])).
% 0.20/0.50  thf('40', plain,
% 0.20/0.50      ((r1_lattices @ sk_A @ (k16_lattice3 @ sk_A @ sk_C) @ sk_B)),
% 0.20/0.50      inference('sup-', [status(thm)], ['11', '39'])).
% 0.20/0.50  thf('41', plain,
% 0.20/0.50      (![X10 : $i, X11 : $i]:
% 0.20/0.50         (~ (l3_lattices @ X10)
% 0.20/0.50          | (v2_struct_0 @ X10)
% 0.20/0.50          | (m1_subset_1 @ (k16_lattice3 @ X10 @ X11) @ (u1_struct_0 @ X10)))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.20/0.50  thf(t26_lattices, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & ( l2_lattices @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50               ( ( ( r1_lattices @ A @ B @ C ) & ( r1_lattices @ A @ C @ B ) ) =>
% 0.20/0.50                 ( ( B ) = ( C ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 0.20/0.50          | ~ (r1_lattices @ X6 @ X5 @ X7)
% 0.20/0.50          | ~ (r1_lattices @ X6 @ X7 @ X5)
% 0.20/0.50          | ((X5) = (X7))
% 0.20/0.50          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 0.20/0.50          | ~ (l2_lattices @ X6)
% 0.20/0.50          | ~ (v4_lattices @ X6)
% 0.20/0.50          | (v2_struct_0 @ X6))),
% 0.20/0.50      inference('cnf', [status(esa)], [t26_lattices])).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X0)
% 0.20/0.50          | ~ (l3_lattices @ X0)
% 0.20/0.50          | (v2_struct_0 @ X0)
% 0.20/0.50          | ~ (v4_lattices @ X0)
% 0.20/0.50          | ~ (l2_lattices @ X0)
% 0.20/0.50          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.50          | ((k16_lattice3 @ X0 @ X1) = (X2))
% 0.20/0.50          | ~ (r1_lattices @ X0 @ X2 @ (k16_lattice3 @ X0 @ X1))
% 0.20/0.50          | ~ (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2))),
% 0.20/0.50      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.50  thf('44', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (r1_lattices @ X0 @ (k16_lattice3 @ X0 @ X1) @ X2)
% 0.20/0.50          | ~ (r1_lattices @ X0 @ X2 @ (k16_lattice3 @ X0 @ X1))
% 0.20/0.50          | ((k16_lattice3 @ X0 @ X1) = (X2))
% 0.20/0.50          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.50          | ~ (l2_lattices @ X0)
% 0.20/0.50          | ~ (v4_lattices @ X0)
% 0.20/0.50          | ~ (l3_lattices @ X0)
% 0.20/0.50          | (v2_struct_0 @ X0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['43'])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ~ (l3_lattices @ sk_A)
% 0.20/0.50        | ~ (v4_lattices @ sk_A)
% 0.20/0.50        | ~ (l2_lattices @ sk_A)
% 0.20/0.50        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.50        | ((k16_lattice3 @ sk_A @ sk_C) = (sk_B))
% 0.20/0.50        | ~ (r1_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['40', '44'])).
% 0.20/0.50  thf('46', plain, ((l3_lattices @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('47', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X0)
% 0.20/0.50          | ~ (v10_lattices @ X0)
% 0.20/0.50          | (v4_lattices @ X0)
% 0.20/0.50          | ~ (l3_lattices @ X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.20/0.50  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('49', plain,
% 0.20/0.50      ((~ (l3_lattices @ sk_A) | (v4_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.50  thf('50', plain, ((l3_lattices @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('51', plain, ((v10_lattices @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('52', plain, ((v4_lattices @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.20/0.50  thf('53', plain, ((l3_lattices @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(dt_l3_lattices, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 0.20/0.50  thf('54', plain, (![X1 : $i]: ((l2_lattices @ X1) | ~ (l3_lattices @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.20/0.50  thf('55', plain, ((l2_lattices @ sk_A)),
% 0.20/0.50      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.50  thf('56', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('57', plain,
% 0.20/0.50      (![X10 : $i, X11 : $i]:
% 0.20/0.50         (~ (l3_lattices @ X10)
% 0.20/0.50          | (v2_struct_0 @ X10)
% 0.20/0.50          | (m1_subset_1 @ (k16_lattice3 @ X10 @ X11) @ (u1_struct_0 @ X10)))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k16_lattice3])).
% 0.20/0.50  thf(d22_lattice3, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( k16_lattice3 @ A @ B ) =
% 0.20/0.50           ( k15_lattice3 @ A @ ( a_2_1_lattice3 @ A @ B ) ) ) ) ))).
% 0.20/0.50  thf('58', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i]:
% 0.20/0.50         (((k16_lattice3 @ X8 @ X9)
% 0.20/0.50            = (k15_lattice3 @ X8 @ (a_2_1_lattice3 @ X8 @ X9)))
% 0.20/0.50          | ~ (l3_lattices @ X8)
% 0.20/0.50          | (v2_struct_0 @ X8))),
% 0.20/0.50      inference('cnf', [status(esa)], [d22_lattice3])).
% 0.20/0.50  thf('59', plain, ((r3_lattice3 @ sk_A @ sk_B @ sk_C)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('60', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(fraenkel_a_2_1_lattice3, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ B ) ) & ( l3_lattices @ B ) ) =>
% 0.20/0.50       ( ( r2_hidden @ A @ ( a_2_1_lattice3 @ B @ C ) ) <=>
% 0.20/0.50         ( ?[D:$i]:
% 0.20/0.50           ( ( r3_lattice3 @ B @ D @ C ) & ( ( A ) = ( D ) ) & 
% 0.20/0.50             ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.20/0.50  thf('61', plain,
% 0.20/0.50      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.50         (~ (l3_lattices @ X12)
% 0.20/0.50          | (v2_struct_0 @ X12)
% 0.20/0.50          | (r2_hidden @ X14 @ (a_2_1_lattice3 @ X12 @ X13))
% 0.20/0.50          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X12))
% 0.20/0.50          | ((X14) != (X15))
% 0.20/0.50          | ~ (r3_lattice3 @ X12 @ X15 @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [fraenkel_a_2_1_lattice3])).
% 0.20/0.50  thf('62', plain,
% 0.20/0.50      (![X12 : $i, X13 : $i, X15 : $i]:
% 0.20/0.50         (~ (r3_lattice3 @ X12 @ X15 @ X13)
% 0.20/0.50          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X12))
% 0.20/0.50          | (r2_hidden @ X15 @ (a_2_1_lattice3 @ X12 @ X13))
% 0.20/0.50          | (v2_struct_0 @ X12)
% 0.20/0.50          | ~ (l3_lattices @ X12))),
% 0.20/0.50      inference('simplify', [status(thm)], ['61'])).
% 0.20/0.50  thf('63', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (l3_lattices @ sk_A)
% 0.20/0.50          | (v2_struct_0 @ sk_A)
% 0.20/0.50          | (r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 0.20/0.50          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['60', '62'])).
% 0.20/0.50  thf('64', plain, ((l3_lattices @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('65', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | (r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0))
% 0.20/0.50          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['63', '64'])).
% 0.20/0.50  thf('66', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('67', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (r3_lattice3 @ sk_A @ sk_B @ X0)
% 0.20/0.50          | (r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ X0)))),
% 0.20/0.50      inference('clc', [status(thm)], ['65', '66'])).
% 0.20/0.50  thf('68', plain, ((r2_hidden @ sk_B @ (a_2_1_lattice3 @ sk_A @ sk_C))),
% 0.20/0.50      inference('sup-', [status(thm)], ['59', '67'])).
% 0.20/0.50  thf('69', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('70', plain,
% 0.20/0.50      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.20/0.50          | (r3_lattices @ X17 @ X16 @ (k15_lattice3 @ X17 @ X18))
% 0.20/0.50          | ~ (r2_hidden @ X16 @ X18)
% 0.20/0.50          | ~ (l3_lattices @ X17)
% 0.20/0.50          | ~ (v4_lattice3 @ X17)
% 0.20/0.50          | ~ (v10_lattices @ X17)
% 0.20/0.50          | (v2_struct_0 @ X17))),
% 0.20/0.50      inference('cnf', [status(esa)], [t38_lattice3])).
% 0.20/0.50  thf('71', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (v10_lattices @ sk_A)
% 0.20/0.50          | ~ (v4_lattice3 @ sk_A)
% 0.20/0.50          | ~ (l3_lattices @ sk_A)
% 0.20/0.50          | ~ (r2_hidden @ sk_B @ X0)
% 0.20/0.50          | (r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['69', '70'])).
% 0.20/0.50  thf('72', plain, ((v10_lattices @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('73', plain, ((v4_lattice3 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('74', plain, ((l3_lattices @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('75', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (r2_hidden @ sk_B @ X0)
% 0.20/0.50          | (r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ X0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['71', '72', '73', '74'])).
% 0.20/0.50  thf('76', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('77', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r3_lattices @ sk_A @ sk_B @ (k15_lattice3 @ sk_A @ X0))
% 0.20/0.50          | ~ (r2_hidden @ sk_B @ X0))),
% 0.20/0.50      inference('clc', [status(thm)], ['75', '76'])).
% 0.20/0.50  thf('78', plain,
% 0.20/0.50      ((r3_lattices @ sk_A @ sk_B @ 
% 0.20/0.50        (k15_lattice3 @ sk_A @ (a_2_1_lattice3 @ sk_A @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['68', '77'])).
% 0.20/0.50  thf('79', plain,
% 0.20/0.50      (((r3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ sk_C))
% 0.20/0.50        | (v2_struct_0 @ sk_A)
% 0.20/0.50        | ~ (l3_lattices @ sk_A))),
% 0.20/0.50      inference('sup+', [status(thm)], ['58', '78'])).
% 0.20/0.50  thf('80', plain, ((l3_lattices @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('81', plain,
% 0.20/0.50      (((r3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ sk_C))
% 0.20/0.50        | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['79', '80'])).
% 0.20/0.50  thf('82', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('83', plain,
% 0.20/0.50      ((r3_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ sk_C))),
% 0.20/0.50      inference('clc', [status(thm)], ['81', '82'])).
% 0.20/0.50  thf('84', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('85', plain,
% 0.20/0.50      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X3))
% 0.20/0.50          | ~ (l3_lattices @ X3)
% 0.20/0.50          | ~ (v9_lattices @ X3)
% 0.20/0.50          | ~ (v8_lattices @ X3)
% 0.20/0.50          | ~ (v6_lattices @ X3)
% 0.20/0.50          | (v2_struct_0 @ X3)
% 0.20/0.50          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 0.20/0.50          | (r1_lattices @ X3 @ X2 @ X4)
% 0.20/0.50          | ~ (r3_lattices @ X3 @ X2 @ X4))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.20/0.50  thf('86', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (r3_lattices @ sk_A @ sk_B @ X0)
% 0.20/0.50          | (r1_lattices @ sk_A @ sk_B @ X0)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | (v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (v6_lattices @ sk_A)
% 0.20/0.50          | ~ (v8_lattices @ sk_A)
% 0.20/0.50          | ~ (v9_lattices @ sk_A)
% 0.20/0.50          | ~ (l3_lattices @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['84', '85'])).
% 0.20/0.50  thf('87', plain, ((v6_lattices @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.20/0.50  thf('88', plain, ((v8_lattices @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.20/0.50  thf('89', plain, ((v9_lattices @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.20/0.50  thf('90', plain, ((l3_lattices @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('91', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (r3_lattices @ sk_A @ sk_B @ X0)
% 0.20/0.50          | (r1_lattices @ sk_A @ sk_B @ X0)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['86', '87', '88', '89', '90'])).
% 0.20/0.50  thf('92', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ~ (m1_subset_1 @ (k16_lattice3 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.20/0.50        | (r1_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['83', '91'])).
% 0.20/0.50  thf('93', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('94', plain,
% 0.20/0.50      (((r1_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ sk_C))
% 0.20/0.50        | ~ (m1_subset_1 @ (k16_lattice3 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('clc', [status(thm)], ['92', '93'])).
% 0.20/0.50  thf('95', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ~ (l3_lattices @ sk_A)
% 0.20/0.50        | (r1_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['57', '94'])).
% 0.20/0.50  thf('96', plain, ((l3_lattices @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('97', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | (r1_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ sk_C)))),
% 0.20/0.50      inference('demod', [status(thm)], ['95', '96'])).
% 0.20/0.50  thf('98', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('99', plain,
% 0.20/0.50      ((r1_lattices @ sk_A @ sk_B @ (k16_lattice3 @ sk_A @ sk_C))),
% 0.20/0.50      inference('clc', [status(thm)], ['97', '98'])).
% 0.20/0.50  thf('100', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A) | ((k16_lattice3 @ sk_A @ sk_C) = (sk_B)))),
% 0.20/0.50      inference('demod', [status(thm)], ['45', '46', '52', '55', '56', '99'])).
% 0.20/0.50  thf('101', plain, (((k16_lattice3 @ sk_A @ sk_C) != (sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('102', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['100', '101'])).
% 0.20/0.50  thf('103', plain, ($false), inference('demod', [status(thm)], ['0', '102'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
