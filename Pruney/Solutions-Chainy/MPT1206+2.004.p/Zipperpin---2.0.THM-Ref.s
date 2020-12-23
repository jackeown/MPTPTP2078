%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.k0bWMB9Caz

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 199 expanded)
%              Number of leaves         :   31 (  74 expanded)
%              Depth                    :   15
%              Number of atoms          :  887 (2308 expanded)
%              Number of equality atoms :   36 ( 100 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(v13_lattices_type,type,(
    v13_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(k5_lattices_type,type,(
    k5_lattices: $i > $i )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(k3_lattices_type,type,(
    k3_lattices: $i > $i > $i > $i )).

thf(k4_lattices_type,type,(
    k4_lattices: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(k1_lattices_type,type,(
    k1_lattices: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(t40_lattices,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v13_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k4_lattices @ A @ ( k5_lattices @ A ) @ B )
            = ( k5_lattices @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v13_lattices @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( k4_lattices @ A @ ( k5_lattices @ A ) @ B )
              = ( k5_lattices @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t40_lattices])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_lattices @ A ) )
     => ( m1_subset_1 @ ( k5_lattices @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X4 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_lattices @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

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

thf('2',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ( ( k1_lattices @ X2 @ X1 @ X3 )
       != X3 )
      | ( r1_lattices @ X2 @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l2_lattices @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_lattices])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
      | ( ( k1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
       != X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
       != X1 )
      | ( r1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l2_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ( r1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
    | ( ( k1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
     != sk_B ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('7',plain,(
    ! [X5: $i] :
      ( ( l1_lattices @ X5 )
      | ~ ( l3_lattices @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('8',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X5: $i] :
      ( ( l2_lattices @ X5 )
      | ~ ( l3_lattices @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('11',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X4 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_lattices @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf(redefinition_k3_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v4_lattices @ A )
        & ( l2_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k3_lattices @ A @ B @ C )
        = ( k1_lattices @ A @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l2_lattices @ X7 )
      | ~ ( v4_lattices @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( ( k3_lattices @ X7 @ X6 @ X8 )
        = ( k1_lattices @ X7 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_lattices])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( ( k3_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
        = ( k1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_lattices @ X0 )
      | ~ ( l2_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l2_lattices @ X0 )
      | ~ ( v4_lattices @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k3_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
        = ( k1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 ) )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ( ( k3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
      = ( k1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) )
    | ~ ( v4_lattices @ sk_A )
    | ~ ( l2_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t39_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v13_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k3_lattices @ A @ ( k5_lattices @ A ) @ B )
            = B ) ) ) )).

thf('20',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ( ( k3_lattices @ X16 @ ( k5_lattices @ X16 ) @ X15 )
        = X15 )
      | ~ ( l3_lattices @ X16 )
      | ~ ( v13_lattices @ X16 )
      | ~ ( v10_lattices @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t39_lattices])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v13_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v13_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
      = sk_B ) ),
    inference(demod,[status(thm)],['21','22','23','24'])).

thf('26',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
    = sk_B ),
    inference(clc,[status(thm)],['25','26'])).

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

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v4_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v4_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','27','33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( sk_B
    = ( k1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['5','8','11','37'])).

thf('39',plain,
    ( ( r1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    r1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X4 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_lattices @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf(t21_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v8_lattices @ A )
        & ( v9_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_lattices @ A @ B @ C )
              <=> ( ( k2_lattices @ A @ B @ C )
                  = B ) ) ) ) ) )).

thf('43',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r1_lattices @ X13 @ X12 @ X14 )
      | ( ( k2_lattices @ X13 @ X12 @ X14 )
        = X12 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l3_lattices @ X13 )
      | ~ ( v9_lattices @ X13 )
      | ~ ( v8_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t21_lattices])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
        = ( k5_lattices @ X0 ) )
      | ~ ( r1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
      | ( ( k2_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
        = ( k5_lattices @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ~ ( v8_lattices @ sk_A )
    | ~ ( v9_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
      = ( k5_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','45'])).

thf('47',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
      = ( k5_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47','53','59','60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( k2_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
    = ( k5_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X4 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_lattices @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf(redefinition_k4_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v6_lattices @ A )
        & ( l1_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k4_lattices @ A @ B @ C )
        = ( k2_lattices @ A @ B @ C ) ) ) )).

thf('67',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_lattices @ X10 )
      | ~ ( v6_lattices @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( ( k4_lattices @ X10 @ X9 @ X11 )
        = ( k2_lattices @ X10 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_lattices])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
        = ( k2_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( l1_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
        = ( k2_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 ) )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ( ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
      = ( k2_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) )
    | ~ ( v6_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['65','69'])).

thf('71',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

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

thf('78',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
      = ( k2_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['70','71','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
    = ( k2_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
    = ( k5_lattices @ sk_A ) ),
    inference('sup+',[status(thm)],['64','80'])).

thf('82',plain,(
    ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
 != ( k5_lattices @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['81','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.k0bWMB9Caz
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:03:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 61 iterations in 0.044s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.21/0.53  thf(v13_lattices_type, type, v13_lattices: $i > $o).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.21/0.53  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.21/0.53  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.21/0.53  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.21/0.53  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 0.21/0.53  thf(k5_lattices_type, type, k5_lattices: $i > $i).
% 0.21/0.53  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 0.21/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.53  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.21/0.53  thf(k3_lattices_type, type, k3_lattices: $i > $i > $i > $i).
% 0.21/0.53  thf(k4_lattices_type, type, k4_lattices: $i > $i > $i > $i).
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.21/0.53  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.21/0.53  thf(k1_lattices_type, type, k1_lattices: $i > $i > $i > $i).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.21/0.53  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 0.21/0.53  thf(t40_lattices, conjecture,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.53         ( v13_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53           ( ( k4_lattices @ A @ ( k5_lattices @ A ) @ B ) =
% 0.21/0.53             ( k5_lattices @ A ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i]:
% 0.21/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.53            ( v13_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.53          ( ![B:$i]:
% 0.21/0.53            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53              ( ( k4_lattices @ A @ ( k5_lattices @ A ) @ B ) =
% 0.21/0.53                ( k5_lattices @ A ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t40_lattices])).
% 0.21/0.53  thf('0', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(dt_k5_lattices, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 0.21/0.53       ( m1_subset_1 @ ( k5_lattices @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X4 : $i]:
% 0.21/0.53         ((m1_subset_1 @ (k5_lattices @ X4) @ (u1_struct_0 @ X4))
% 0.21/0.53          | ~ (l1_lattices @ X4)
% 0.21/0.53          | (v2_struct_0 @ X4))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 0.21/0.53  thf(d3_lattices, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l2_lattices @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53               ( ( r1_lattices @ A @ B @ C ) <=>
% 0.21/0.53                 ( ( k1_lattices @ A @ B @ C ) = ( C ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.21/0.53          | ((k1_lattices @ X2 @ X1 @ X3) != (X3))
% 0.21/0.53          | (r1_lattices @ X2 @ X1 @ X3)
% 0.21/0.53          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.21/0.53          | ~ (l2_lattices @ X2)
% 0.21/0.53          | (v2_struct_0 @ X2))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_lattices])).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X0)
% 0.21/0.53          | ~ (l1_lattices @ X0)
% 0.21/0.53          | (v2_struct_0 @ X0)
% 0.21/0.53          | ~ (l2_lattices @ X0)
% 0.21/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.53          | (r1_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 0.21/0.53          | ((k1_lattices @ X0 @ (k5_lattices @ X0) @ X1) != (X1)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (((k1_lattices @ X0 @ (k5_lattices @ X0) @ X1) != (X1))
% 0.21/0.53          | (r1_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 0.21/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.53          | ~ (l2_lattices @ X0)
% 0.21/0.53          | ~ (l1_lattices @ X0)
% 0.21/0.53          | (v2_struct_0 @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_A)
% 0.21/0.53        | ~ (l1_lattices @ sk_A)
% 0.21/0.53        | ~ (l2_lattices @ sk_A)
% 0.21/0.53        | (r1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)
% 0.21/0.53        | ((k1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B) != (sk_B)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['0', '4'])).
% 0.21/0.53  thf('6', plain, ((l3_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(dt_l3_lattices, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 0.21/0.53  thf('7', plain, (![X5 : $i]: ((l1_lattices @ X5) | ~ (l3_lattices @ X5))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.21/0.53  thf('8', plain, ((l1_lattices @ sk_A)),
% 0.21/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.53  thf('9', plain, ((l3_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('10', plain, (![X5 : $i]: ((l2_lattices @ X5) | ~ (l3_lattices @ X5))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.21/0.53  thf('11', plain, ((l2_lattices @ sk_A)),
% 0.21/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.53  thf('12', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (![X4 : $i]:
% 0.21/0.53         ((m1_subset_1 @ (k5_lattices @ X4) @ (u1_struct_0 @ X4))
% 0.21/0.53          | ~ (l1_lattices @ X4)
% 0.21/0.53          | (v2_struct_0 @ X4))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 0.21/0.53  thf(redefinition_k3_lattices, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.21/0.53         ( l2_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.53         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53       ( ( k3_lattices @ A @ B @ C ) = ( k1_lattices @ A @ B @ C ) ) ))).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 0.21/0.53          | ~ (l2_lattices @ X7)
% 0.21/0.53          | ~ (v4_lattices @ X7)
% 0.21/0.53          | (v2_struct_0 @ X7)
% 0.21/0.53          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.21/0.53          | ((k3_lattices @ X7 @ X6 @ X8) = (k1_lattices @ X7 @ X6 @ X8)))),
% 0.21/0.53      inference('cnf', [status(esa)], [redefinition_k3_lattices])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X0)
% 0.21/0.53          | ~ (l1_lattices @ X0)
% 0.21/0.53          | ((k3_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 0.21/0.53              = (k1_lattices @ X0 @ (k5_lattices @ X0) @ X1))
% 0.21/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.53          | (v2_struct_0 @ X0)
% 0.21/0.53          | ~ (v4_lattices @ X0)
% 0.21/0.53          | ~ (l2_lattices @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (l2_lattices @ X0)
% 0.21/0.53          | ~ (v4_lattices @ X0)
% 0.21/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.53          | ((k3_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 0.21/0.53              = (k1_lattices @ X0 @ (k5_lattices @ X0) @ X1))
% 0.21/0.53          | ~ (l1_lattices @ X0)
% 0.21/0.53          | (v2_struct_0 @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_A)
% 0.21/0.53        | ~ (l1_lattices @ sk_A)
% 0.21/0.53        | ((k3_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)
% 0.21/0.53            = (k1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B))
% 0.21/0.53        | ~ (v4_lattices @ sk_A)
% 0.21/0.53        | ~ (l2_lattices @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['12', '16'])).
% 0.21/0.53  thf('18', plain, ((l1_lattices @ sk_A)),
% 0.21/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.53  thf('19', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t39_lattices, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.53         ( v13_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53           ( ( k3_lattices @ A @ ( k5_lattices @ A ) @ B ) = ( B ) ) ) ) ))).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (![X15 : $i, X16 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 0.21/0.53          | ((k3_lattices @ X16 @ (k5_lattices @ X16) @ X15) = (X15))
% 0.21/0.53          | ~ (l3_lattices @ X16)
% 0.21/0.53          | ~ (v13_lattices @ X16)
% 0.21/0.53          | ~ (v10_lattices @ X16)
% 0.21/0.53          | (v2_struct_0 @ X16))),
% 0.21/0.53      inference('cnf', [status(esa)], [t39_lattices])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_A)
% 0.21/0.53        | ~ (v10_lattices @ sk_A)
% 0.21/0.53        | ~ (v13_lattices @ sk_A)
% 0.21/0.53        | ~ (l3_lattices @ sk_A)
% 0.21/0.53        | ((k3_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B) = (sk_B)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.53  thf('22', plain, ((v10_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('23', plain, ((v13_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('24', plain, ((l3_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_A)
% 0.21/0.53        | ((k3_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B) = (sk_B)))),
% 0.21/0.53      inference('demod', [status(thm)], ['21', '22', '23', '24'])).
% 0.21/0.53  thf('26', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      (((k3_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B) = (sk_B))),
% 0.21/0.53      inference('clc', [status(thm)], ['25', '26'])).
% 0.21/0.53  thf(cc1_lattices, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l3_lattices @ A ) =>
% 0.21/0.53       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.21/0.53         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.21/0.53           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.21/0.53           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X0)
% 0.21/0.53          | ~ (v10_lattices @ X0)
% 0.21/0.53          | (v4_lattices @ X0)
% 0.21/0.53          | ~ (l3_lattices @ X0))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.53  thf('29', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      ((~ (l3_lattices @ sk_A) | (v4_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.53  thf('31', plain, ((l3_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('32', plain, ((v10_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('33', plain, ((v4_lattices @ sk_A)),
% 0.21/0.53      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.21/0.53  thf('34', plain, ((l2_lattices @ sk_A)),
% 0.21/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_A)
% 0.21/0.53        | ((sk_B) = (k1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)))),
% 0.21/0.53      inference('demod', [status(thm)], ['17', '18', '27', '33', '34'])).
% 0.21/0.53  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('37', plain,
% 0.21/0.53      (((sk_B) = (k1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B))),
% 0.21/0.53      inference('clc', [status(thm)], ['35', '36'])).
% 0.21/0.53  thf('38', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_A)
% 0.21/0.53        | (r1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)
% 0.21/0.53        | ((sk_B) != (sk_B)))),
% 0.21/0.53      inference('demod', [status(thm)], ['5', '8', '11', '37'])).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      (((r1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)
% 0.21/0.53        | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('simplify', [status(thm)], ['38'])).
% 0.21/0.53  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('41', plain, ((r1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)),
% 0.21/0.53      inference('clc', [status(thm)], ['39', '40'])).
% 0.21/0.53  thf('42', plain,
% 0.21/0.53      (![X4 : $i]:
% 0.21/0.53         ((m1_subset_1 @ (k5_lattices @ X4) @ (u1_struct_0 @ X4))
% 0.21/0.53          | ~ (l1_lattices @ X4)
% 0.21/0.53          | (v2_struct_0 @ X4))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 0.21/0.53  thf(t21_lattices, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v8_lattices @ A ) & 
% 0.21/0.53         ( v9_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53               ( ( r1_lattices @ A @ B @ C ) <=>
% 0.21/0.53                 ( ( k2_lattices @ A @ B @ C ) = ( B ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('43', plain,
% 0.21/0.53      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.21/0.53          | ~ (r1_lattices @ X13 @ X12 @ X14)
% 0.21/0.53          | ((k2_lattices @ X13 @ X12 @ X14) = (X12))
% 0.21/0.53          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.21/0.53          | ~ (l3_lattices @ X13)
% 0.21/0.53          | ~ (v9_lattices @ X13)
% 0.21/0.53          | ~ (v8_lattices @ X13)
% 0.21/0.53          | (v2_struct_0 @ X13))),
% 0.21/0.53      inference('cnf', [status(esa)], [t21_lattices])).
% 0.21/0.53  thf('44', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X0)
% 0.21/0.53          | ~ (l1_lattices @ X0)
% 0.21/0.53          | (v2_struct_0 @ X0)
% 0.21/0.53          | ~ (v8_lattices @ X0)
% 0.21/0.53          | ~ (v9_lattices @ X0)
% 0.21/0.53          | ~ (l3_lattices @ X0)
% 0.21/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.53          | ((k2_lattices @ X0 @ (k5_lattices @ X0) @ X1) = (k5_lattices @ X0))
% 0.21/0.53          | ~ (r1_lattices @ X0 @ (k5_lattices @ X0) @ X1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.53  thf('45', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (r1_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 0.21/0.53          | ((k2_lattices @ X0 @ (k5_lattices @ X0) @ X1) = (k5_lattices @ X0))
% 0.21/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.53          | ~ (l3_lattices @ X0)
% 0.21/0.53          | ~ (v9_lattices @ X0)
% 0.21/0.53          | ~ (v8_lattices @ X0)
% 0.21/0.53          | ~ (l1_lattices @ X0)
% 0.21/0.53          | (v2_struct_0 @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['44'])).
% 0.21/0.53  thf('46', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_A)
% 0.21/0.53        | ~ (l1_lattices @ sk_A)
% 0.21/0.53        | ~ (v8_lattices @ sk_A)
% 0.21/0.53        | ~ (v9_lattices @ sk_A)
% 0.21/0.53        | ~ (l3_lattices @ sk_A)
% 0.21/0.53        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.53        | ((k2_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)
% 0.21/0.53            = (k5_lattices @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['41', '45'])).
% 0.21/0.53  thf('47', plain, ((l1_lattices @ sk_A)),
% 0.21/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.53  thf('48', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X0)
% 0.21/0.53          | ~ (v10_lattices @ X0)
% 0.21/0.53          | (v8_lattices @ X0)
% 0.21/0.53          | ~ (l3_lattices @ X0))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.53  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('50', plain,
% 0.21/0.53      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.53  thf('51', plain, ((l3_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('52', plain, ((v10_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('53', plain, ((v8_lattices @ sk_A)),
% 0.21/0.53      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.21/0.53  thf('54', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X0)
% 0.21/0.53          | ~ (v10_lattices @ X0)
% 0.21/0.53          | (v9_lattices @ X0)
% 0.21/0.53          | ~ (l3_lattices @ X0))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.53  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('56', plain,
% 0.21/0.53      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.53  thf('57', plain, ((l3_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('58', plain, ((v10_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('59', plain, ((v9_lattices @ sk_A)),
% 0.21/0.53      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.21/0.53  thf('60', plain, ((l3_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('61', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('62', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_A)
% 0.21/0.53        | ((k2_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)
% 0.21/0.53            = (k5_lattices @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['46', '47', '53', '59', '60', '61'])).
% 0.21/0.53  thf('63', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('64', plain,
% 0.21/0.53      (((k2_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)
% 0.21/0.53         = (k5_lattices @ sk_A))),
% 0.21/0.53      inference('clc', [status(thm)], ['62', '63'])).
% 0.21/0.53  thf('65', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('66', plain,
% 0.21/0.53      (![X4 : $i]:
% 0.21/0.53         ((m1_subset_1 @ (k5_lattices @ X4) @ (u1_struct_0 @ X4))
% 0.21/0.53          | ~ (l1_lattices @ X4)
% 0.21/0.53          | (v2_struct_0 @ X4))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 0.21/0.53  thf(redefinition_k4_lattices, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.21/0.53         ( l1_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.53         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53       ( ( k4_lattices @ A @ B @ C ) = ( k2_lattices @ A @ B @ C ) ) ))).
% 0.21/0.53  thf('67', plain,
% 0.21/0.53      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.21/0.53          | ~ (l1_lattices @ X10)
% 0.21/0.53          | ~ (v6_lattices @ X10)
% 0.21/0.53          | (v2_struct_0 @ X10)
% 0.21/0.53          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.21/0.53          | ((k4_lattices @ X10 @ X9 @ X11) = (k2_lattices @ X10 @ X9 @ X11)))),
% 0.21/0.53      inference('cnf', [status(esa)], [redefinition_k4_lattices])).
% 0.21/0.53  thf('68', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X0)
% 0.21/0.53          | ~ (l1_lattices @ X0)
% 0.21/0.53          | ((k4_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 0.21/0.53              = (k2_lattices @ X0 @ (k5_lattices @ X0) @ X1))
% 0.21/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.53          | (v2_struct_0 @ X0)
% 0.21/0.53          | ~ (v6_lattices @ X0)
% 0.21/0.53          | ~ (l1_lattices @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['66', '67'])).
% 0.21/0.53  thf('69', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (v6_lattices @ X0)
% 0.21/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.53          | ((k4_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 0.21/0.53              = (k2_lattices @ X0 @ (k5_lattices @ X0) @ X1))
% 0.21/0.53          | ~ (l1_lattices @ X0)
% 0.21/0.53          | (v2_struct_0 @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['68'])).
% 0.21/0.53  thf('70', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_A)
% 0.21/0.53        | ~ (l1_lattices @ sk_A)
% 0.21/0.53        | ((k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)
% 0.21/0.53            = (k2_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B))
% 0.21/0.53        | ~ (v6_lattices @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['65', '69'])).
% 0.21/0.53  thf('71', plain, ((l1_lattices @ sk_A)),
% 0.21/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.53  thf('72', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X0)
% 0.21/0.53          | ~ (v10_lattices @ X0)
% 0.21/0.53          | (v6_lattices @ X0)
% 0.21/0.53          | ~ (l3_lattices @ X0))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.53  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('74', plain,
% 0.21/0.53      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['72', '73'])).
% 0.21/0.53  thf('75', plain, ((l3_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('76', plain, ((v10_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('77', plain, ((v6_lattices @ sk_A)),
% 0.21/0.53      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.21/0.53  thf('78', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_A)
% 0.21/0.53        | ((k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)
% 0.21/0.53            = (k2_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)))),
% 0.21/0.53      inference('demod', [status(thm)], ['70', '71', '77'])).
% 0.21/0.53  thf('79', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('80', plain,
% 0.21/0.53      (((k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)
% 0.21/0.53         = (k2_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B))),
% 0.21/0.53      inference('clc', [status(thm)], ['78', '79'])).
% 0.21/0.53  thf('81', plain,
% 0.21/0.53      (((k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)
% 0.21/0.53         = (k5_lattices @ sk_A))),
% 0.21/0.53      inference('sup+', [status(thm)], ['64', '80'])).
% 0.21/0.53  thf('82', plain,
% 0.21/0.53      (((k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)
% 0.21/0.53         != (k5_lattices @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('83', plain, ($false),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['81', '82'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
