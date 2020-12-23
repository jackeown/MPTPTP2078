%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.I8gqq1l2l8

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:37 EST 2020

% Result     : Theorem 33.10s
% Output     : Refutation 33.10s
% Verified   : 
% Statistics : Number of formulae       :  389 (1822 expanded)
%              Number of leaves         :   48 ( 536 expanded)
%              Depth                    :   23
%              Number of atoms          : 3994 (23297 expanded)
%              Number of equality atoms :  176 ( 952 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(k1_lattices_type,type,(
    k1_lattices: $i > $i > $i > $i )).

thf(k5_lattices_type,type,(
    k5_lattices: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(v16_lattices_type,type,(
    v16_lattices: $i > $o )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v11_lattices_type,type,(
    v11_lattices: $i > $o )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(v17_lattices_type,type,(
    v17_lattices: $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(k3_lattices_type,type,(
    k3_lattices: $i > $i > $i > $i )).

thf(k4_lattices_type,type,(
    k4_lattices: $i > $i > $i > $i )).

thf(v14_lattices_type,type,(
    v14_lattices: $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(k7_lattices_type,type,(
    k7_lattices: $i > $i > $i )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(v13_lattices_type,type,(
    v13_lattices: $i > $o )).

thf(k6_lattices_type,type,(
    k6_lattices: $i > $i )).

thf(v15_lattices_type,type,(
    v15_lattices: $i > $o )).

thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(dt_k5_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_lattices @ A ) )
     => ( m1_subset_1 @ ( k5_lattices @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X27: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X27 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_lattices @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf(t49_lattices,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v17_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k7_lattices @ A @ ( k7_lattices @ A @ B ) )
            = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v17_lattices @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( k7_lattices @ A @ ( k7_lattices @ A @ B ) )
              = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t49_lattices])).

thf('1',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v4_lattices @ A )
        & ( l2_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k3_lattices @ A @ B @ C )
        = ( k1_lattices @ A @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X33 ) )
      | ~ ( l2_lattices @ X33 )
      | ~ ( v4_lattices @ X33 )
      | ( v2_struct_0 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X33 ) )
      | ( ( k3_lattices @ X33 @ X32 @ X34 )
        = ( k1_lattices @ X33 @ X32 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_lattices])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k1_lattices @ sk_A @ sk_B_3 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

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

thf('4',plain,(
    ! [X2: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v10_lattices @ X2 )
      | ( v4_lattices @ X2 )
      | ~ ( l3_lattices @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('5',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v4_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('11',plain,(
    ! [X31: $i] :
      ( ( l2_lattices @ X31 )
      | ~ ( l3_lattices @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('12',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k1_lattices @ sk_A @ sk_B_3 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','9','12'])).

thf('14',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k1_lattices @ sk_A @ sk_B_3 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ( ( k3_lattices @ sk_A @ sk_B_3 @ ( k5_lattices @ sk_A ) )
      = ( k1_lattices @ sk_A @ sk_B_3 @ ( k5_lattices @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','15'])).

thf('17',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X31: $i] :
      ( ( l1_lattices @ X31 )
      | ~ ( l3_lattices @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('19',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_lattices @ sk_A @ sk_B_3 @ ( k5_lattices @ sk_A ) )
      = ( k1_lattices @ sk_A @ sk_B_3 @ ( k5_lattices @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k3_lattices @ sk_A @ sk_B_3 @ ( k5_lattices @ sk_A ) )
    = ( k1_lattices @ sk_A @ sk_B_3 @ ( k5_lattices @ sk_A ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
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

thf('24',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X41 ) )
      | ( ( k3_lattices @ X41 @ ( k5_lattices @ X41 ) @ X40 )
        = X40 )
      | ~ ( l3_lattices @ X41 )
      | ~ ( v13_lattices @ X41 )
      | ~ ( v10_lattices @ X41 )
      | ( v2_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t39_lattices])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v13_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_3 )
      = sk_B_3 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v15_lattices @ A ) )
       => ( ~ ( v2_struct_0 @ A )
          & ( v13_lattices @ A )
          & ( v14_lattices @ A ) ) ) ) )).

thf('27',plain,(
    ! [X3: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( v15_lattices @ X3 )
      | ( v13_lattices @ X3 )
      | ~ ( l3_lattices @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc4_lattices])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v13_lattices @ sk_A )
    | ~ ( v15_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v13_lattices @ sk_A )
    | ~ ( v15_lattices @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(cc5_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v17_lattices @ A ) )
       => ( ~ ( v2_struct_0 @ A )
          & ( v11_lattices @ A )
          & ( v15_lattices @ A )
          & ( v16_lattices @ A ) ) ) ) )).

thf('32',plain,(
    ! [X4: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( v17_lattices @ X4 )
      | ( v15_lattices @ X4 )
      | ~ ( l3_lattices @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc5_lattices])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v15_lattices @ sk_A )
    | ~ ( v17_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v17_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v15_lattices @ sk_A ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    v13_lattices @ sk_A ),
    inference(demod,[status(thm)],['31','37'])).

thf('39',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X27: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X27 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_lattices @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('41',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
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

thf('42',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l2_lattices @ X6 )
      | ~ ( v4_lattices @ X6 )
      | ( v2_struct_0 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ( ( k3_lattices @ X6 @ X5 @ X7 )
        = ( k3_lattices @ X6 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_lattices])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_B_3 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('45',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['10','11'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_B_3 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_B_3 ) ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ( ( k3_lattices @ sk_A @ sk_B_3 @ ( k5_lattices @ sk_A ) )
      = ( k3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['40','48'])).

thf('50',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_lattices @ sk_A @ sk_B_3 @ ( k5_lattices @ sk_A ) )
      = ( k3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_3 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( k3_lattices @ sk_A @ sk_B_3 @ ( k5_lattices @ sk_A ) )
    = ( k3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_3 ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_lattices @ sk_A @ sk_B_3 @ ( k5_lattices @ sk_A ) )
      = sk_B_3 ) ),
    inference(demod,[status(thm)],['25','26','38','39','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k3_lattices @ sk_A @ sk_B_3 @ ( k5_lattices @ sk_A ) )
    = sk_B_3 ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,
    ( sk_B_3
    = ( k1_lattices @ sk_A @ sk_B_3 @ ( k5_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_lattices,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k7_lattices @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('59',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l3_lattices @ X29 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X29 ) )
      | ( m1_subset_1 @ ( k7_lattices @ X29 @ X30 ) @ ( u1_struct_0 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattices])).

thf('60',plain,
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('66',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l3_lattices @ X29 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X29 ) )
      | ( m1_subset_1 @ ( k7_lattices @ X29 @ X30 ) @ ( u1_struct_0 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattices])).

thf('67',plain,
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d11_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( ( v11_lattices @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( k2_lattices @ A @ B @ ( k1_lattices @ A @ C @ D ) )
                      = ( k1_lattices @ A @ ( k2_lattices @ A @ B @ C ) @ ( k2_lattices @ A @ B @ D ) ) ) ) ) ) ) ) )).

thf('73',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( v11_lattices @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( ( k2_lattices @ X11 @ X13 @ ( k1_lattices @ X11 @ X12 @ X14 ) )
        = ( k1_lattices @ X11 @ ( k2_lattices @ X11 @ X13 @ X12 ) @ ( k2_lattices @ X11 @ X13 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l3_lattices @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d11_lattices])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ sk_B_3 @ X1 ) )
        = ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_B_3 ) @ ( k2_lattices @ sk_A @ X0 @ X1 ) ) )
      | ~ ( v11_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X4: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( v17_lattices @ X4 )
      | ( v11_lattices @ X4 )
      | ~ ( l3_lattices @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc5_lattices])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v11_lattices @ sk_A )
    | ~ ( v17_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v17_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v11_lattices @ sk_A ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ sk_B_3 @ X1 ) )
        = ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_B_3 ) @ ( k2_lattices @ sk_A @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['74','75','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ ( k1_lattices @ sk_A @ sk_B_3 @ X0 ) )
        = ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ sk_B_3 ) @ ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['69','70'])).

thf(redefinition_k4_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v6_lattices @ A )
        & ( l1_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k4_lattices @ A @ B @ C )
        = ( k2_lattices @ A @ B @ C ) ) ) )).

thf('86',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X36 ) )
      | ~ ( l1_lattices @ X36 )
      | ~ ( v6_lattices @ X36 )
      | ( v2_struct_0 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X36 ) )
      | ( ( k4_lattices @ X36 @ X35 @ X37 )
        = ( k2_lattices @ X36 @ X35 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_lattices])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ X0 )
        = ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X2: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v10_lattices @ X2 )
      | ( v6_lattices @ X2 )
      | ~ ( l3_lattices @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ X0 )
        = ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ X0 )
        = ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ sk_B_3 )
    = ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['84','97'])).

thf('99',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('100',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k4_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v6_lattices @ A )
        & ( l1_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k4_lattices @ A @ B @ C )
        = ( k4_lattices @ A @ C @ B ) ) ) )).

thf('101',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_lattices @ X9 )
      | ~ ( v6_lattices @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( ( k4_lattices @ X9 @ X8 @ X10 )
        = ( k4_lattices @ X9 @ X10 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k4_lattices])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B_3 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('104',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B_3 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B_3 ) ) ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( k4_lattices @ sk_A @ sk_B_3 @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) )
    = ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['99','107'])).

thf('109',plain,
    ( ( k4_lattices @ sk_A @ sk_B_3 @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) )
    = ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ sk_B_3 ) ),
    inference(demod,[status(thm)],['98','108'])).

thf('110',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('111',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('113',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( v11_lattices @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( ( k2_lattices @ X11 @ X13 @ ( k1_lattices @ X11 @ X12 @ X14 ) )
        = ( k1_lattices @ X11 @ ( k2_lattices @ X11 @ X13 @ X12 ) @ ( k2_lattices @ X11 @ X13 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l3_lattices @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d11_lattices])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) @ X1 ) )
        = ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ ( k2_lattices @ sk_A @ X0 @ X1 ) ) )
      | ~ ( v11_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v11_lattices @ sk_A ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) @ X1 ) )
        = ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ ( k2_lattices @ sk_A @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ sk_B_3 @ ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) @ X0 ) )
        = ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_3 @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ ( k2_lattices @ sk_A @ sk_B_3 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['111','117'])).

thf('119',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('120',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X36 ) )
      | ~ ( l1_lattices @ X36 )
      | ~ ( v6_lattices @ X36 )
      | ( v2_struct_0 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X36 ) )
      | ( ( k4_lattices @ X36 @ X35 @ X37 )
        = ( k2_lattices @ X36 @ X35 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_lattices])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k2_lattices @ sk_A @ sk_B_3 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('124',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k2_lattices @ sk_A @ sk_B_3 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['122','123','124'])).

thf('126',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k2_lattices @ sk_A @ sk_B_3 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( k4_lattices @ sk_A @ sk_B_3 @ ( k7_lattices @ sk_A @ sk_B_3 ) )
    = ( k2_lattices @ sk_A @ sk_B_3 @ ( k7_lattices @ sk_A @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['119','127'])).

thf('129',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t47_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v17_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k4_lattices @ A @ ( k7_lattices @ A @ B ) @ B )
            = ( k5_lattices @ A ) ) ) ) )).

thf('130',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( u1_struct_0 @ X47 ) )
      | ( ( k4_lattices @ X47 @ ( k7_lattices @ X47 @ X46 ) @ X46 )
        = ( k5_lattices @ X47 ) )
      | ~ ( l3_lattices @ X47 )
      | ~ ( v17_lattices @ X47 )
      | ~ ( v10_lattices @ X47 )
      | ( v2_struct_0 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t47_lattices])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v17_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) @ sk_B_3 )
      = ( k5_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v17_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B_3 ) ) ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('137',plain,
    ( ( k4_lattices @ sk_A @ sk_B_3 @ ( k7_lattices @ sk_A @ sk_B_3 ) )
    = ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_lattices @ sk_A @ sk_B_3 @ ( k7_lattices @ sk_A @ sk_B_3 ) )
      = ( k5_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132','133','134','137'])).

thf('139',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( k4_lattices @ sk_A @ sk_B_3 @ ( k7_lattices @ sk_A @ sk_B_3 ) )
    = ( k5_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['138','139'])).

thf('141',plain,
    ( ( k5_lattices @ sk_A )
    = ( k2_lattices @ sk_A @ sk_B_3 @ ( k7_lattices @ sk_A @ sk_B_3 ) ) ),
    inference(demod,[status(thm)],['128','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ sk_B_3 @ ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) @ X0 ) )
        = ( k1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k2_lattices @ sk_A @ sk_B_3 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['118','141'])).

thf('143',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ sk_B_3 @ ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) @ X0 ) )
        = ( k1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k2_lattices @ sk_A @ sk_B_3 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['142','143'])).

thf('145',plain,
    ( ( k2_lattices @ sk_A @ sk_B_3 @ ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) ) )
    = ( k1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k2_lattices @ sk_A @ sk_B_3 @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) ) ) ),
    inference('sup-',[status(thm)],['110','144'])).

thf('146',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('147',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('148',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X33 ) )
      | ~ ( l2_lattices @ X33 )
      | ~ ( v4_lattices @ X33 )
      | ( v2_struct_0 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X33 ) )
      | ( ( k3_lattices @ X33 @ X32 @ X34 )
        = ( k1_lattices @ X33 @ X32 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_lattices])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) @ X0 )
        = ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('151',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['10','11'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) @ X0 )
        = ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['149','150','151'])).

thf('153',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) @ X0 )
        = ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['152','153'])).

thf('155',plain,
    ( ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) )
    = ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) ) ),
    inference('sup-',[status(thm)],['146','154'])).

thf('156',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','63'])).

thf(t48_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v17_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k3_lattices @ A @ ( k7_lattices @ A @ B ) @ B )
            = ( k6_lattices @ A ) ) ) ) )).

thf('157',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( u1_struct_0 @ X49 ) )
      | ( ( k3_lattices @ X49 @ ( k7_lattices @ X49 @ X48 ) @ X48 )
        = ( k6_lattices @ X49 ) )
      | ~ ( l3_lattices @ X49 )
      | ~ ( v17_lattices @ X49 )
      | ~ ( v10_lattices @ X49 )
      | ( v2_struct_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t48_lattices])).

thf('158',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v17_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ ( k7_lattices @ sk_A @ sk_B_3 ) )
      = ( k6_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v17_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('163',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('164',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l2_lattices @ X6 )
      | ~ ( v4_lattices @ X6 )
      | ( v2_struct_0 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ( ( k3_lattices @ X6 @ X5 @ X7 )
        = ( k3_lattices @ X6 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_lattices])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ ( k7_lattices @ sk_A @ sk_B_3 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('167',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['10','11'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ ( k7_lattices @ sk_A @ sk_B_3 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['165','166','167'])).

thf('169',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ ( k7_lattices @ sk_A @ sk_B_3 ) ) ) ) ),
    inference(clc,[status(thm)],['168','169'])).

thf('171',plain,
    ( ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) )
    = ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ ( k7_lattices @ sk_A @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['162','170'])).

thf('172',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) )
      = ( k6_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['158','159','160','161','171'])).

thf('173',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) )
    = ( k6_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['172','173'])).

thf('175',plain,
    ( ( k6_lattices @ sk_A )
    = ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) ) ),
    inference(demod,[status(thm)],['155','174'])).

thf('176',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k2_lattices @ sk_A @ sk_B_3 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('178',plain,
    ( ( k4_lattices @ sk_A @ sk_B_3 @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) )
    = ( k2_lattices @ sk_A @ sk_B_3 @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('180',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    ! [X27: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X27 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_lattices @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('182',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( v11_lattices @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( ( k2_lattices @ X11 @ X13 @ ( k1_lattices @ X11 @ X12 @ X14 ) )
        = ( k1_lattices @ X11 @ ( k2_lattices @ X11 @ X13 @ X12 ) @ ( k2_lattices @ X11 @ X13 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l3_lattices @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d11_lattices])).

thf('183',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ X1 @ ( k1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X2 ) )
        = ( k1_lattices @ X0 @ ( k2_lattices @ X0 @ X1 @ ( k5_lattices @ X0 ) ) @ ( k2_lattices @ X0 @ X1 @ X2 ) ) )
      | ~ ( v11_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v11_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ X1 @ ( k1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X2 ) )
        = ( k1_lattices @ X0 @ ( k2_lattices @ X0 @ X1 @ ( k5_lattices @ X0 ) ) @ ( k2_lattices @ X0 @ X1 @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['183'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_3 ) )
        = ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ ( k5_lattices @ sk_A ) ) @ ( k2_lattices @ sk_A @ X0 @ sk_B_3 ) ) )
      | ~ ( v11_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['180','184'])).

thf('186',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('187',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    ! [X27: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X27 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_lattices @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('189',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( ( v8_lattices @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( k1_lattices @ A @ ( k2_lattices @ A @ B @ C ) @ C )
                  = C ) ) ) ) ) )).

thf('190',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v8_lattices @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ( ( k1_lattices @ X21 @ ( k2_lattices @ X21 @ X23 @ X22 ) @ X22 )
        = X22 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l3_lattices @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d8_lattices])).

thf('191',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_B_3 ) @ sk_B_3 )
        = sk_B_3 )
      | ~ ( v8_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    ! [X2: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v10_lattices @ X2 )
      | ( v8_lattices @ X2 )
      | ~ ( l3_lattices @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('194',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['195','196','197'])).

thf('199',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_B_3 ) @ sk_B_3 )
        = sk_B_3 ) ) ),
    inference(demod,[status(thm)],['191','192','198'])).

thf('200',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    ! [X0: $i] :
      ( ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_B_3 ) @ sk_B_3 )
        = sk_B_3 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['199','200'])).

thf('202',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_3 ) @ sk_B_3 )
      = sk_B_3 ) ),
    inference('sup-',[status(thm)],['188','201'])).

thf('203',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('204',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    ! [X27: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X27 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_lattices @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf(d16_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_lattices @ A ) )
     => ( ( v13_lattices @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( B
                = ( k5_lattices @ A ) )
            <=> ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                 => ( ( ( k2_lattices @ A @ B @ C )
                      = B )
                    & ( ( k2_lattices @ A @ C @ B )
                      = B ) ) ) ) ) ) ) )).

thf('206',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v13_lattices @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ( X16
       != ( k5_lattices @ X15 ) )
      | ( ( k2_lattices @ X15 @ X16 @ X17 )
        = X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d16_lattices])).

thf('207',plain,(
    ! [X15: $i,X17: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( l1_lattices @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X15 ) )
      | ( ( k2_lattices @ X15 @ ( k5_lattices @ X15 ) @ X17 )
        = ( k5_lattices @ X15 ) )
      | ~ ( m1_subset_1 @ ( k5_lattices @ X15 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( v13_lattices @ X15 ) ) ),
    inference(simplify,[status(thm)],['206'])).

thf('208',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
        = ( k5_lattices @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['205','207'])).

thf('209',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
        = ( k5_lattices @ X0 ) )
      | ~ ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['208'])).

thf('210',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ~ ( v13_lattices @ sk_A )
    | ( ( k2_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_3 )
      = ( k5_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['204','209'])).

thf('211',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('212',plain,(
    v13_lattices @ sk_A ),
    inference(demod,[status(thm)],['31','37'])).

thf('213',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_3 )
      = ( k5_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['210','211','212'])).

thf('214',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,
    ( ( k2_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_3 )
    = ( k5_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['213','214'])).

thf('216',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_3 )
      = sk_B_3 ) ),
    inference(demod,[status(thm)],['202','203','215'])).

thf('217',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,
    ( ( k1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_3 )
    = sk_B_3 ),
    inference(clc,[status(thm)],['216','217'])).

thf('219',plain,(
    v11_lattices @ sk_A ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('220',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ sk_B_3 )
        = ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ ( k5_lattices @ sk_A ) ) @ ( k2_lattices @ sk_A @ X0 @ sk_B_3 ) ) ) ) ),
    inference(demod,[status(thm)],['185','186','187','218','219'])).

thf('221',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ X0 @ sk_B_3 )
        = ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ ( k5_lattices @ sk_A ) ) @ ( k2_lattices @ sk_A @ X0 @ sk_B_3 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['220','221'])).

thf('223',plain,
    ( ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ sk_B_3 )
    = ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ ( k5_lattices @ sk_A ) ) @ ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['179','222'])).

thf('224',plain,
    ( ( k4_lattices @ sk_A @ sk_B_3 @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) )
    = ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ sk_B_3 ) ),
    inference(demod,[status(thm)],['98','108'])).

thf('225',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('226',plain,(
    ! [X27: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X27 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_lattices @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('227',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v13_lattices @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ( X16
       != ( k5_lattices @ X15 ) )
      | ( ( k2_lattices @ X15 @ X17 @ X16 )
        = X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d16_lattices])).

thf('228',plain,(
    ! [X15: $i,X17: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( l1_lattices @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X15 ) )
      | ( ( k2_lattices @ X15 @ X17 @ ( k5_lattices @ X15 ) )
        = ( k5_lattices @ X15 ) )
      | ~ ( m1_subset_1 @ ( k5_lattices @ X15 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( v13_lattices @ X15 ) ) ),
    inference(simplify,[status(thm)],['227'])).

thf('229',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ X1 @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['226','228'])).

thf('230',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ X1 @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) )
      | ~ ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['229'])).

thf('231',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ~ ( v13_lattices @ sk_A )
    | ( ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ ( k5_lattices @ sk_A ) )
      = ( k5_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['225','230'])).

thf('232',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('233',plain,(
    v13_lattices @ sk_A ),
    inference(demod,[status(thm)],['31','37'])).

thf('234',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ ( k5_lattices @ sk_A ) )
      = ( k5_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['231','232','233'])).

thf('235',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,
    ( ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ ( k5_lattices @ sk_A ) )
    = ( k5_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['234','235'])).

thf('237',plain,
    ( ( k4_lattices @ sk_A @ sk_B_3 @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) )
    = ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ sk_B_3 ) ),
    inference(demod,[status(thm)],['98','108'])).

thf('238',plain,
    ( ( k4_lattices @ sk_A @ sk_B_3 @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) )
    = ( k1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k4_lattices @ sk_A @ sk_B_3 @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) ) ) ),
    inference(demod,[status(thm)],['223','224','236','237'])).

thf('239',plain,
    ( ( k2_lattices @ sk_A @ sk_B_3 @ ( k6_lattices @ sk_A ) )
    = ( k4_lattices @ sk_A @ sk_B_3 @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) ) ),
    inference(demod,[status(thm)],['145','175','178','238'])).

thf('240',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','63'])).

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

thf('242',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v9_lattices @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ( ( k2_lattices @ X24 @ X26 @ ( k1_lattices @ X24 @ X26 @ X25 ) )
        = X26 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X24 ) )
      | ~ ( l3_lattices @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d9_lattices])).

thf('243',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ X0 @ ( k7_lattices @ sk_A @ sk_B_3 ) ) )
        = X0 )
      | ~ ( v9_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['241','242'])).

thf('244',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,(
    ! [X2: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v10_lattices @ X2 )
      | ( v9_lattices @ X2 )
      | ~ ( l3_lattices @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('246',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['245','246'])).

thf('248',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('250',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['247','248','249'])).

thf('251',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ X0 @ ( k7_lattices @ sk_A @ sk_B_3 ) ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['243','244','250'])).

thf('252',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ X0 @ ( k7_lattices @ sk_A @ sk_B_3 ) ) )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['251','252'])).

thf('254',plain,
    ( ( k2_lattices @ sk_A @ sk_B_3 @ ( k1_lattices @ sk_A @ sk_B_3 @ ( k7_lattices @ sk_A @ sk_B_3 ) ) )
    = sk_B_3 ),
    inference('sup-',[status(thm)],['240','253'])).

thf('255',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('256',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k1_lattices @ sk_A @ sk_B_3 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('257',plain,
    ( ( k3_lattices @ sk_A @ sk_B_3 @ ( k7_lattices @ sk_A @ sk_B_3 ) )
    = ( k1_lattices @ sk_A @ sk_B_3 @ ( k7_lattices @ sk_A @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['255','256'])).

thf('258',plain,
    ( ( k2_lattices @ sk_A @ sk_B_3 @ ( k3_lattices @ sk_A @ sk_B_3 @ ( k7_lattices @ sk_A @ sk_B_3 ) ) )
    = sk_B_3 ),
    inference(demod,[status(thm)],['254','257'])).

thf('259',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('260',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( u1_struct_0 @ X49 ) )
      | ( ( k3_lattices @ X49 @ ( k7_lattices @ X49 @ X48 ) @ X48 )
        = ( k6_lattices @ X49 ) )
      | ~ ( l3_lattices @ X49 )
      | ~ ( v17_lattices @ X49 )
      | ~ ( v10_lattices @ X49 )
      | ( v2_struct_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t48_lattices])).

thf('261',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v17_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) @ sk_B_3 )
      = ( k6_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['259','260'])).

thf('262',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,(
    v17_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('266',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_B_3 ) ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('267',plain,
    ( ( k3_lattices @ sk_A @ sk_B_3 @ ( k7_lattices @ sk_A @ sk_B_3 ) )
    = ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['265','266'])).

thf('268',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_lattices @ sk_A @ sk_B_3 @ ( k7_lattices @ sk_A @ sk_B_3 ) )
      = ( k6_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['261','262','263','264','267'])).

thf('269',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('270',plain,
    ( ( k3_lattices @ sk_A @ sk_B_3 @ ( k7_lattices @ sk_A @ sk_B_3 ) )
    = ( k6_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['268','269'])).

thf('271',plain,
    ( ( k2_lattices @ sk_A @ sk_B_3 @ ( k6_lattices @ sk_A ) )
    = sk_B_3 ),
    inference(demod,[status(thm)],['258','270'])).

thf('272',plain,
    ( sk_B_3
    = ( k4_lattices @ sk_A @ sk_B_3 @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) ) ),
    inference(demod,[status(thm)],['239','271'])).

thf('273',plain,
    ( sk_B_3
    = ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ sk_B_3 ) ),
    inference(demod,[status(thm)],['109','272'])).

thf('274',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ ( k1_lattices @ sk_A @ sk_B_3 @ X0 ) )
        = ( k1_lattices @ sk_A @ sk_B_3 @ ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['83','273'])).

thf('275',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ ( k1_lattices @ sk_A @ sk_B_3 @ X0 ) )
        = ( k1_lattices @ sk_A @ sk_B_3 @ ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['274','275'])).

thf('277',plain,
    ( ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ ( k1_lattices @ sk_A @ sk_B_3 @ ( k7_lattices @ sk_A @ sk_B_3 ) ) )
    = ( k1_lattices @ sk_A @ sk_B_3 @ ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ ( k7_lattices @ sk_A @ sk_B_3 ) ) ) ),
    inference('sup-',[status(thm)],['64','276'])).

thf('278',plain,
    ( ( k3_lattices @ sk_A @ sk_B_3 @ ( k7_lattices @ sk_A @ sk_B_3 ) )
    = ( k1_lattices @ sk_A @ sk_B_3 @ ( k7_lattices @ sk_A @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['255','256'])).

thf('279',plain,
    ( ( k3_lattices @ sk_A @ sk_B_3 @ ( k7_lattices @ sk_A @ sk_B_3 ) )
    = ( k6_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['268','269'])).

thf('280',plain,
    ( ( k6_lattices @ sk_A )
    = ( k1_lattices @ sk_A @ sk_B_3 @ ( k7_lattices @ sk_A @ sk_B_3 ) ) ),
    inference(demod,[status(thm)],['278','279'])).

thf('281',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['69','70'])).

thf(dt_k6_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l2_lattices @ A ) )
     => ( m1_subset_1 @ ( k6_lattices @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('282',plain,(
    ! [X28: $i] :
      ( ( m1_subset_1 @ ( k6_lattices @ X28 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( l2_lattices @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_lattices])).

thf('283',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v9_lattices @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ( ( k2_lattices @ X24 @ X26 @ ( k1_lattices @ X24 @ X26 @ X25 ) )
        = X26 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X24 ) )
      | ~ ( l3_lattices @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d9_lattices])).

thf('284',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ X1 @ ( k1_lattices @ X0 @ X1 @ ( k6_lattices @ X0 ) ) )
        = X1 )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['282','283'])).

thf('285',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ X1 @ ( k1_lattices @ X0 @ X1 @ ( k6_lattices @ X0 ) ) )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['284'])).

thf('286',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ ( k6_lattices @ sk_A ) ) )
      = ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) )
    | ~ ( v9_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['281','285'])).

thf('287',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['10','11'])).

thf('288',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('289',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('290',plain,(
    ! [X28: $i] :
      ( ( m1_subset_1 @ ( k6_lattices @ X28 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( l2_lattices @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_lattices])).

thf(d17_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l2_lattices @ A ) )
     => ( ( v14_lattices @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( B
                = ( k6_lattices @ A ) )
            <=> ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                 => ( ( ( k1_lattices @ A @ B @ C )
                      = B )
                    & ( ( k1_lattices @ A @ C @ B )
                      = B ) ) ) ) ) ) ) )).

thf('291',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v14_lattices @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ( X19
       != ( k6_lattices @ X18 ) )
      | ( ( k1_lattices @ X18 @ X20 @ X19 )
        = X19 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l2_lattices @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d17_lattices])).

thf('292',plain,(
    ! [X18: $i,X20: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( l2_lattices @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X18 ) )
      | ( ( k1_lattices @ X18 @ X20 @ ( k6_lattices @ X18 ) )
        = ( k6_lattices @ X18 ) )
      | ~ ( m1_subset_1 @ ( k6_lattices @ X18 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( v14_lattices @ X18 ) ) ),
    inference(simplify,[status(thm)],['291'])).

thf('293',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ~ ( v14_lattices @ X0 )
      | ( ( k1_lattices @ X0 @ X1 @ ( k6_lattices @ X0 ) )
        = ( k6_lattices @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l2_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['290','292'])).

thf('294',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k1_lattices @ X0 @ X1 @ ( k6_lattices @ X0 ) )
        = ( k6_lattices @ X0 ) )
      | ~ ( v14_lattices @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['293'])).

thf('295',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ~ ( v14_lattices @ sk_A )
    | ( ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ ( k6_lattices @ sk_A ) )
      = ( k6_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['289','294'])).

thf('296',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['10','11'])).

thf('297',plain,(
    ! [X3: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( v15_lattices @ X3 )
      | ( v14_lattices @ X3 )
      | ~ ( l3_lattices @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc4_lattices])).

thf('298',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('299',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v14_lattices @ sk_A )
    | ~ ( v15_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['297','298'])).

thf('300',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('301',plain,
    ( ( v14_lattices @ sk_A )
    | ~ ( v15_lattices @ sk_A ) ),
    inference(demod,[status(thm)],['299','300'])).

thf('302',plain,(
    v15_lattices @ sk_A ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('303',plain,(
    v14_lattices @ sk_A ),
    inference(demod,[status(thm)],['301','302'])).

thf('304',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ ( k6_lattices @ sk_A ) )
      = ( k6_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['295','296','303'])).

thf('305',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('306',plain,
    ( ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ ( k6_lattices @ sk_A ) )
    = ( k6_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['304','305'])).

thf('307',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['247','248','249'])).

thf('308',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ ( k6_lattices @ sk_A ) )
      = ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) ) ),
    inference(demod,[status(thm)],['286','287','288','306','307'])).

thf('309',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('310',plain,
    ( ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ ( k6_lattices @ sk_A ) )
    = ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) ),
    inference(clc,[status(thm)],['308','309'])).

thf('311',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('312',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ X0 )
        = ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('313',plain,
    ( ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ ( k7_lattices @ sk_A @ sk_B_3 ) )
    = ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ ( k7_lattices @ sk_A @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['311','312'])).

thf('314',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('315',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('316',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_lattices @ X9 )
      | ~ ( v6_lattices @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( ( k4_lattices @ X9 @ X8 @ X10 )
        = ( k4_lattices @ X9 @ X10 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k4_lattices])).

thf('317',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ ( k7_lattices @ sk_A @ sk_B_3 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['315','316'])).

thf('318',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('319',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('320',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ ( k7_lattices @ sk_A @ sk_B_3 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['317','318','319'])).

thf('321',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('322',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ ( k7_lattices @ sk_A @ sk_B_3 ) ) ) ) ),
    inference(clc,[status(thm)],['320','321'])).

thf('323',plain,
    ( ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) )
    = ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ ( k7_lattices @ sk_A @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['314','322'])).

thf('324',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('325',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( u1_struct_0 @ X47 ) )
      | ( ( k4_lattices @ X47 @ ( k7_lattices @ X47 @ X46 ) @ X46 )
        = ( k5_lattices @ X47 ) )
      | ~ ( l3_lattices @ X47 )
      | ~ ( v17_lattices @ X47 )
      | ~ ( v10_lattices @ X47 )
      | ( v2_struct_0 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t47_lattices])).

thf('326',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v17_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ ( k7_lattices @ sk_A @ sk_B_3 ) )
      = ( k5_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['324','325'])).

thf('327',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('328',plain,(
    v17_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('329',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('330',plain,
    ( ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) )
    = ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ ( k7_lattices @ sk_A @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['314','322'])).

thf('331',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) )
      = ( k5_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['326','327','328','329','330'])).

thf('332',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('333',plain,
    ( ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) )
    = ( k5_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['331','332'])).

thf('334',plain,
    ( ( k5_lattices @ sk_A )
    = ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ ( k7_lattices @ sk_A @ sk_B_3 ) ) ),
    inference(demod,[status(thm)],['323','333'])).

thf('335',plain,
    ( ( k5_lattices @ sk_A )
    = ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) ) @ ( k7_lattices @ sk_A @ sk_B_3 ) ) ),
    inference(demod,[status(thm)],['313','334'])).

thf('336',plain,
    ( ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) )
    = ( k1_lattices @ sk_A @ sk_B_3 @ ( k5_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['277','280','310','335'])).

thf('337',plain,
    ( ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) )
    = sk_B_3 ),
    inference('sup+',[status(thm)],['57','336'])).

thf('338',plain,(
    ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_3 ) )
 != sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('339',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['337','338'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.I8gqq1l2l8
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:23:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 33.10/33.33  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 33.10/33.33  % Solved by: fo/fo7.sh
% 33.10/33.33  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 33.10/33.33  % done 5340 iterations in 32.878s
% 33.10/33.33  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 33.10/33.33  % SZS output start Refutation
% 33.10/33.33  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 33.10/33.33  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 33.10/33.33  thf(sk_B_3_type, type, sk_B_3: $i).
% 33.10/33.33  thf(k1_lattices_type, type, k1_lattices: $i > $i > $i > $i).
% 33.10/33.33  thf(k5_lattices_type, type, k5_lattices: $i > $i).
% 33.10/33.33  thf(sk_A_type, type, sk_A: $i).
% 33.10/33.33  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 33.10/33.33  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 33.10/33.33  thf(v16_lattices_type, type, v16_lattices: $i > $o).
% 33.10/33.33  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 33.10/33.33  thf(v11_lattices_type, type, v11_lattices: $i > $o).
% 33.10/33.33  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 33.10/33.33  thf(v17_lattices_type, type, v17_lattices: $i > $o).
% 33.10/33.33  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 33.10/33.33  thf(k3_lattices_type, type, k3_lattices: $i > $i > $i > $i).
% 33.10/33.33  thf(k4_lattices_type, type, k4_lattices: $i > $i > $i > $i).
% 33.10/33.33  thf(v14_lattices_type, type, v14_lattices: $i > $o).
% 33.10/33.33  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 33.10/33.33  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 33.10/33.33  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 33.10/33.33  thf(k7_lattices_type, type, k7_lattices: $i > $i > $i).
% 33.10/33.33  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 33.10/33.33  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 33.10/33.33  thf(v13_lattices_type, type, v13_lattices: $i > $o).
% 33.10/33.33  thf(k6_lattices_type, type, k6_lattices: $i > $i).
% 33.10/33.33  thf(v15_lattices_type, type, v15_lattices: $i > $o).
% 33.10/33.33  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 33.10/33.33  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 33.10/33.33  thf(dt_k5_lattices, axiom,
% 33.10/33.33    (![A:$i]:
% 33.10/33.33     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 33.10/33.33       ( m1_subset_1 @ ( k5_lattices @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 33.10/33.33  thf('0', plain,
% 33.10/33.33      (![X27 : $i]:
% 33.10/33.33         ((m1_subset_1 @ (k5_lattices @ X27) @ (u1_struct_0 @ X27))
% 33.10/33.33          | ~ (l1_lattices @ X27)
% 33.10/33.33          | (v2_struct_0 @ X27))),
% 33.10/33.33      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 33.10/33.33  thf(t49_lattices, conjecture,
% 33.10/33.33    (![A:$i]:
% 33.10/33.33     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 33.10/33.33         ( v17_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 33.10/33.33       ( ![B:$i]:
% 33.10/33.33         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 33.10/33.33           ( ( k7_lattices @ A @ ( k7_lattices @ A @ B ) ) = ( B ) ) ) ) ))).
% 33.10/33.33  thf(zf_stmt_0, negated_conjecture,
% 33.10/33.33    (~( ![A:$i]:
% 33.10/33.33        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 33.10/33.33            ( v17_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 33.10/33.33          ( ![B:$i]:
% 33.10/33.33            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 33.10/33.33              ( ( k7_lattices @ A @ ( k7_lattices @ A @ B ) ) = ( B ) ) ) ) ) )),
% 33.10/33.33    inference('cnf.neg', [status(esa)], [t49_lattices])).
% 33.10/33.33  thf('1', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf(redefinition_k3_lattices, axiom,
% 33.10/33.33    (![A:$i,B:$i,C:$i]:
% 33.10/33.33     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 33.10/33.33         ( l2_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 33.10/33.33         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 33.10/33.33       ( ( k3_lattices @ A @ B @ C ) = ( k1_lattices @ A @ B @ C ) ) ))).
% 33.10/33.33  thf('2', plain,
% 33.10/33.33      (![X32 : $i, X33 : $i, X34 : $i]:
% 33.10/33.33         (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X33))
% 33.10/33.33          | ~ (l2_lattices @ X33)
% 33.10/33.33          | ~ (v4_lattices @ X33)
% 33.10/33.33          | (v2_struct_0 @ X33)
% 33.10/33.33          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X33))
% 33.10/33.33          | ((k3_lattices @ X33 @ X32 @ X34) = (k1_lattices @ X33 @ X32 @ X34)))),
% 33.10/33.33      inference('cnf', [status(esa)], [redefinition_k3_lattices])).
% 33.10/33.33  thf('3', plain,
% 33.10/33.33      (![X0 : $i]:
% 33.10/33.33         (((k3_lattices @ sk_A @ sk_B_3 @ X0)
% 33.10/33.33            = (k1_lattices @ sk_A @ sk_B_3 @ X0))
% 33.10/33.33          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | (v2_struct_0 @ sk_A)
% 33.10/33.33          | ~ (v4_lattices @ sk_A)
% 33.10/33.33          | ~ (l2_lattices @ sk_A))),
% 33.10/33.33      inference('sup-', [status(thm)], ['1', '2'])).
% 33.10/33.33  thf(cc1_lattices, axiom,
% 33.10/33.33    (![A:$i]:
% 33.10/33.33     ( ( l3_lattices @ A ) =>
% 33.10/33.33       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 33.10/33.33         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 33.10/33.33           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 33.10/33.33           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 33.10/33.33  thf('4', plain,
% 33.10/33.33      (![X2 : $i]:
% 33.10/33.33         ((v2_struct_0 @ X2)
% 33.10/33.33          | ~ (v10_lattices @ X2)
% 33.10/33.33          | (v4_lattices @ X2)
% 33.10/33.33          | ~ (l3_lattices @ X2))),
% 33.10/33.33      inference('cnf', [status(esa)], [cc1_lattices])).
% 33.10/33.33  thf('5', plain, (~ (v2_struct_0 @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('6', plain,
% 33.10/33.33      ((~ (l3_lattices @ sk_A) | (v4_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 33.10/33.33      inference('sup-', [status(thm)], ['4', '5'])).
% 33.10/33.33  thf('7', plain, ((l3_lattices @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('8', plain, ((v10_lattices @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('9', plain, ((v4_lattices @ sk_A)),
% 33.10/33.33      inference('demod', [status(thm)], ['6', '7', '8'])).
% 33.10/33.33  thf('10', plain, ((l3_lattices @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf(dt_l3_lattices, axiom,
% 33.10/33.33    (![A:$i]:
% 33.10/33.33     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 33.10/33.33  thf('11', plain,
% 33.10/33.33      (![X31 : $i]: ((l2_lattices @ X31) | ~ (l3_lattices @ X31))),
% 33.10/33.33      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 33.10/33.33  thf('12', plain, ((l2_lattices @ sk_A)),
% 33.10/33.33      inference('sup-', [status(thm)], ['10', '11'])).
% 33.10/33.33  thf('13', plain,
% 33.10/33.33      (![X0 : $i]:
% 33.10/33.33         (((k3_lattices @ sk_A @ sk_B_3 @ X0)
% 33.10/33.33            = (k1_lattices @ sk_A @ sk_B_3 @ X0))
% 33.10/33.33          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | (v2_struct_0 @ sk_A))),
% 33.10/33.33      inference('demod', [status(thm)], ['3', '9', '12'])).
% 33.10/33.33  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('15', plain,
% 33.10/33.33      (![X0 : $i]:
% 33.10/33.33         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | ((k3_lattices @ sk_A @ sk_B_3 @ X0)
% 33.10/33.33              = (k1_lattices @ sk_A @ sk_B_3 @ X0)))),
% 33.10/33.33      inference('clc', [status(thm)], ['13', '14'])).
% 33.10/33.33  thf('16', plain,
% 33.10/33.33      (((v2_struct_0 @ sk_A)
% 33.10/33.33        | ~ (l1_lattices @ sk_A)
% 33.10/33.33        | ((k3_lattices @ sk_A @ sk_B_3 @ (k5_lattices @ sk_A))
% 33.10/33.33            = (k1_lattices @ sk_A @ sk_B_3 @ (k5_lattices @ sk_A))))),
% 33.10/33.33      inference('sup-', [status(thm)], ['0', '15'])).
% 33.10/33.33  thf('17', plain, ((l3_lattices @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('18', plain,
% 33.10/33.33      (![X31 : $i]: ((l1_lattices @ X31) | ~ (l3_lattices @ X31))),
% 33.10/33.33      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 33.10/33.33  thf('19', plain, ((l1_lattices @ sk_A)),
% 33.10/33.33      inference('sup-', [status(thm)], ['17', '18'])).
% 33.10/33.33  thf('20', plain,
% 33.10/33.33      (((v2_struct_0 @ sk_A)
% 33.10/33.33        | ((k3_lattices @ sk_A @ sk_B_3 @ (k5_lattices @ sk_A))
% 33.10/33.33            = (k1_lattices @ sk_A @ sk_B_3 @ (k5_lattices @ sk_A))))),
% 33.10/33.33      inference('demod', [status(thm)], ['16', '19'])).
% 33.10/33.33  thf('21', plain, (~ (v2_struct_0 @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('22', plain,
% 33.10/33.33      (((k3_lattices @ sk_A @ sk_B_3 @ (k5_lattices @ sk_A))
% 33.10/33.33         = (k1_lattices @ sk_A @ sk_B_3 @ (k5_lattices @ sk_A)))),
% 33.10/33.33      inference('clc', [status(thm)], ['20', '21'])).
% 33.10/33.33  thf('23', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf(t39_lattices, axiom,
% 33.10/33.33    (![A:$i]:
% 33.10/33.33     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 33.10/33.33         ( v13_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 33.10/33.33       ( ![B:$i]:
% 33.10/33.33         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 33.10/33.33           ( ( k3_lattices @ A @ ( k5_lattices @ A ) @ B ) = ( B ) ) ) ) ))).
% 33.10/33.33  thf('24', plain,
% 33.10/33.33      (![X40 : $i, X41 : $i]:
% 33.10/33.33         (~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X41))
% 33.10/33.33          | ((k3_lattices @ X41 @ (k5_lattices @ X41) @ X40) = (X40))
% 33.10/33.33          | ~ (l3_lattices @ X41)
% 33.10/33.33          | ~ (v13_lattices @ X41)
% 33.10/33.33          | ~ (v10_lattices @ X41)
% 33.10/33.33          | (v2_struct_0 @ X41))),
% 33.10/33.33      inference('cnf', [status(esa)], [t39_lattices])).
% 33.10/33.33  thf('25', plain,
% 33.10/33.33      (((v2_struct_0 @ sk_A)
% 33.10/33.33        | ~ (v10_lattices @ sk_A)
% 33.10/33.33        | ~ (v13_lattices @ sk_A)
% 33.10/33.33        | ~ (l3_lattices @ sk_A)
% 33.10/33.33        | ((k3_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_3) = (sk_B_3)))),
% 33.10/33.33      inference('sup-', [status(thm)], ['23', '24'])).
% 33.10/33.33  thf('26', plain, ((v10_lattices @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf(cc4_lattices, axiom,
% 33.10/33.33    (![A:$i]:
% 33.10/33.33     ( ( l3_lattices @ A ) =>
% 33.10/33.33       ( ( ( ~( v2_struct_0 @ A ) ) & ( v15_lattices @ A ) ) =>
% 33.10/33.33         ( ( ~( v2_struct_0 @ A ) ) & ( v13_lattices @ A ) & 
% 33.10/33.33           ( v14_lattices @ A ) ) ) ))).
% 33.10/33.33  thf('27', plain,
% 33.10/33.33      (![X3 : $i]:
% 33.10/33.33         ((v2_struct_0 @ X3)
% 33.10/33.33          | ~ (v15_lattices @ X3)
% 33.10/33.33          | (v13_lattices @ X3)
% 33.10/33.33          | ~ (l3_lattices @ X3))),
% 33.10/33.33      inference('cnf', [status(esa)], [cc4_lattices])).
% 33.10/33.33  thf('28', plain, (~ (v2_struct_0 @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('29', plain,
% 33.10/33.33      ((~ (l3_lattices @ sk_A)
% 33.10/33.33        | (v13_lattices @ sk_A)
% 33.10/33.33        | ~ (v15_lattices @ sk_A))),
% 33.10/33.33      inference('sup-', [status(thm)], ['27', '28'])).
% 33.10/33.33  thf('30', plain, ((l3_lattices @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('31', plain, (((v13_lattices @ sk_A) | ~ (v15_lattices @ sk_A))),
% 33.10/33.33      inference('demod', [status(thm)], ['29', '30'])).
% 33.10/33.33  thf(cc5_lattices, axiom,
% 33.10/33.33    (![A:$i]:
% 33.10/33.33     ( ( l3_lattices @ A ) =>
% 33.10/33.33       ( ( ( ~( v2_struct_0 @ A ) ) & ( v17_lattices @ A ) ) =>
% 33.10/33.33         ( ( ~( v2_struct_0 @ A ) ) & ( v11_lattices @ A ) & 
% 33.10/33.33           ( v15_lattices @ A ) & ( v16_lattices @ A ) ) ) ))).
% 33.10/33.33  thf('32', plain,
% 33.10/33.33      (![X4 : $i]:
% 33.10/33.33         ((v2_struct_0 @ X4)
% 33.10/33.33          | ~ (v17_lattices @ X4)
% 33.10/33.33          | (v15_lattices @ X4)
% 33.10/33.33          | ~ (l3_lattices @ X4))),
% 33.10/33.33      inference('cnf', [status(esa)], [cc5_lattices])).
% 33.10/33.33  thf('33', plain, (~ (v2_struct_0 @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('34', plain,
% 33.10/33.33      ((~ (l3_lattices @ sk_A)
% 33.10/33.33        | (v15_lattices @ sk_A)
% 33.10/33.33        | ~ (v17_lattices @ sk_A))),
% 33.10/33.33      inference('sup-', [status(thm)], ['32', '33'])).
% 33.10/33.33  thf('35', plain, ((l3_lattices @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('36', plain, ((v17_lattices @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('37', plain, ((v15_lattices @ sk_A)),
% 33.10/33.33      inference('demod', [status(thm)], ['34', '35', '36'])).
% 33.10/33.33  thf('38', plain, ((v13_lattices @ sk_A)),
% 33.10/33.33      inference('demod', [status(thm)], ['31', '37'])).
% 33.10/33.33  thf('39', plain, ((l3_lattices @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('40', plain,
% 33.10/33.33      (![X27 : $i]:
% 33.10/33.33         ((m1_subset_1 @ (k5_lattices @ X27) @ (u1_struct_0 @ X27))
% 33.10/33.33          | ~ (l1_lattices @ X27)
% 33.10/33.33          | (v2_struct_0 @ X27))),
% 33.10/33.33      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 33.10/33.33  thf('41', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf(commutativity_k3_lattices, axiom,
% 33.10/33.33    (![A:$i,B:$i,C:$i]:
% 33.10/33.33     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 33.10/33.33         ( l2_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 33.10/33.33         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 33.10/33.33       ( ( k3_lattices @ A @ B @ C ) = ( k3_lattices @ A @ C @ B ) ) ))).
% 33.10/33.33  thf('42', plain,
% 33.10/33.33      (![X5 : $i, X6 : $i, X7 : $i]:
% 33.10/33.33         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 33.10/33.33          | ~ (l2_lattices @ X6)
% 33.10/33.33          | ~ (v4_lattices @ X6)
% 33.10/33.33          | (v2_struct_0 @ X6)
% 33.10/33.33          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 33.10/33.33          | ((k3_lattices @ X6 @ X5 @ X7) = (k3_lattices @ X6 @ X7 @ X5)))),
% 33.10/33.33      inference('cnf', [status(esa)], [commutativity_k3_lattices])).
% 33.10/33.33  thf('43', plain,
% 33.10/33.33      (![X0 : $i]:
% 33.10/33.33         (((k3_lattices @ sk_A @ sk_B_3 @ X0)
% 33.10/33.33            = (k3_lattices @ sk_A @ X0 @ sk_B_3))
% 33.10/33.33          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | (v2_struct_0 @ sk_A)
% 33.10/33.33          | ~ (v4_lattices @ sk_A)
% 33.10/33.33          | ~ (l2_lattices @ sk_A))),
% 33.10/33.33      inference('sup-', [status(thm)], ['41', '42'])).
% 33.10/33.33  thf('44', plain, ((v4_lattices @ sk_A)),
% 33.10/33.33      inference('demod', [status(thm)], ['6', '7', '8'])).
% 33.10/33.33  thf('45', plain, ((l2_lattices @ sk_A)),
% 33.10/33.33      inference('sup-', [status(thm)], ['10', '11'])).
% 33.10/33.33  thf('46', plain,
% 33.10/33.33      (![X0 : $i]:
% 33.10/33.33         (((k3_lattices @ sk_A @ sk_B_3 @ X0)
% 33.10/33.33            = (k3_lattices @ sk_A @ X0 @ sk_B_3))
% 33.10/33.33          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | (v2_struct_0 @ sk_A))),
% 33.10/33.33      inference('demod', [status(thm)], ['43', '44', '45'])).
% 33.10/33.33  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('48', plain,
% 33.10/33.33      (![X0 : $i]:
% 33.10/33.33         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | ((k3_lattices @ sk_A @ sk_B_3 @ X0)
% 33.10/33.33              = (k3_lattices @ sk_A @ X0 @ sk_B_3)))),
% 33.10/33.33      inference('clc', [status(thm)], ['46', '47'])).
% 33.10/33.33  thf('49', plain,
% 33.10/33.33      (((v2_struct_0 @ sk_A)
% 33.10/33.33        | ~ (l1_lattices @ sk_A)
% 33.10/33.33        | ((k3_lattices @ sk_A @ sk_B_3 @ (k5_lattices @ sk_A))
% 33.10/33.33            = (k3_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_3)))),
% 33.10/33.33      inference('sup-', [status(thm)], ['40', '48'])).
% 33.10/33.33  thf('50', plain, ((l1_lattices @ sk_A)),
% 33.10/33.33      inference('sup-', [status(thm)], ['17', '18'])).
% 33.10/33.33  thf('51', plain,
% 33.10/33.33      (((v2_struct_0 @ sk_A)
% 33.10/33.33        | ((k3_lattices @ sk_A @ sk_B_3 @ (k5_lattices @ sk_A))
% 33.10/33.33            = (k3_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_3)))),
% 33.10/33.33      inference('demod', [status(thm)], ['49', '50'])).
% 33.10/33.33  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('53', plain,
% 33.10/33.33      (((k3_lattices @ sk_A @ sk_B_3 @ (k5_lattices @ sk_A))
% 33.10/33.33         = (k3_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_3))),
% 33.10/33.33      inference('clc', [status(thm)], ['51', '52'])).
% 33.10/33.33  thf('54', plain,
% 33.10/33.33      (((v2_struct_0 @ sk_A)
% 33.10/33.33        | ((k3_lattices @ sk_A @ sk_B_3 @ (k5_lattices @ sk_A)) = (sk_B_3)))),
% 33.10/33.33      inference('demod', [status(thm)], ['25', '26', '38', '39', '53'])).
% 33.10/33.33  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('56', plain,
% 33.10/33.33      (((k3_lattices @ sk_A @ sk_B_3 @ (k5_lattices @ sk_A)) = (sk_B_3))),
% 33.10/33.33      inference('clc', [status(thm)], ['54', '55'])).
% 33.10/33.33  thf('57', plain,
% 33.10/33.33      (((sk_B_3) = (k1_lattices @ sk_A @ sk_B_3 @ (k5_lattices @ sk_A)))),
% 33.10/33.33      inference('demod', [status(thm)], ['22', '56'])).
% 33.10/33.33  thf('58', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf(dt_k7_lattices, axiom,
% 33.10/33.33    (![A:$i,B:$i]:
% 33.10/33.33     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) & 
% 33.10/33.33         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 33.10/33.33       ( m1_subset_1 @ ( k7_lattices @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 33.10/33.33  thf('59', plain,
% 33.10/33.33      (![X29 : $i, X30 : $i]:
% 33.10/33.33         (~ (l3_lattices @ X29)
% 33.10/33.33          | (v2_struct_0 @ X29)
% 33.10/33.33          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X29))
% 33.10/33.33          | (m1_subset_1 @ (k7_lattices @ X29 @ X30) @ (u1_struct_0 @ X29)))),
% 33.10/33.33      inference('cnf', [status(esa)], [dt_k7_lattices])).
% 33.10/33.33  thf('60', plain,
% 33.10/33.33      (((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B_3) @ (u1_struct_0 @ sk_A))
% 33.10/33.33        | (v2_struct_0 @ sk_A)
% 33.10/33.33        | ~ (l3_lattices @ sk_A))),
% 33.10/33.33      inference('sup-', [status(thm)], ['58', '59'])).
% 33.10/33.33  thf('61', plain, ((l3_lattices @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('62', plain,
% 33.10/33.33      (((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B_3) @ (u1_struct_0 @ sk_A))
% 33.10/33.33        | (v2_struct_0 @ sk_A))),
% 33.10/33.33      inference('demod', [status(thm)], ['60', '61'])).
% 33.10/33.33  thf('63', plain, (~ (v2_struct_0 @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('64', plain,
% 33.10/33.33      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B_3) @ (u1_struct_0 @ sk_A))),
% 33.10/33.33      inference('clc', [status(thm)], ['62', '63'])).
% 33.10/33.33  thf('65', plain,
% 33.10/33.33      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B_3) @ (u1_struct_0 @ sk_A))),
% 33.10/33.33      inference('clc', [status(thm)], ['62', '63'])).
% 33.10/33.33  thf('66', plain,
% 33.10/33.33      (![X29 : $i, X30 : $i]:
% 33.10/33.33         (~ (l3_lattices @ X29)
% 33.10/33.33          | (v2_struct_0 @ X29)
% 33.10/33.33          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X29))
% 33.10/33.33          | (m1_subset_1 @ (k7_lattices @ X29 @ X30) @ (u1_struct_0 @ X29)))),
% 33.10/33.33      inference('cnf', [status(esa)], [dt_k7_lattices])).
% 33.10/33.33  thf('67', plain,
% 33.10/33.33      (((m1_subset_1 @ (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ 
% 33.10/33.33         (u1_struct_0 @ sk_A))
% 33.10/33.33        | (v2_struct_0 @ sk_A)
% 33.10/33.33        | ~ (l3_lattices @ sk_A))),
% 33.10/33.33      inference('sup-', [status(thm)], ['65', '66'])).
% 33.10/33.33  thf('68', plain, ((l3_lattices @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('69', plain,
% 33.10/33.33      (((m1_subset_1 @ (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ 
% 33.10/33.33         (u1_struct_0 @ sk_A))
% 33.10/33.33        | (v2_struct_0 @ sk_A))),
% 33.10/33.33      inference('demod', [status(thm)], ['67', '68'])).
% 33.10/33.33  thf('70', plain, (~ (v2_struct_0 @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('71', plain,
% 33.10/33.33      ((m1_subset_1 @ (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ 
% 33.10/33.33        (u1_struct_0 @ sk_A))),
% 33.10/33.33      inference('clc', [status(thm)], ['69', '70'])).
% 33.10/33.33  thf('72', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf(d11_lattices, axiom,
% 33.10/33.33    (![A:$i]:
% 33.10/33.33     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 33.10/33.33       ( ( v11_lattices @ A ) <=>
% 33.10/33.33         ( ![B:$i]:
% 33.10/33.33           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 33.10/33.33             ( ![C:$i]:
% 33.10/33.33               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 33.10/33.33                 ( ![D:$i]:
% 33.10/33.33                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 33.10/33.33                     ( ( k2_lattices @ A @ B @ ( k1_lattices @ A @ C @ D ) ) =
% 33.10/33.33                       ( k1_lattices @
% 33.10/33.33                         A @ ( k2_lattices @ A @ B @ C ) @ 
% 33.10/33.33                         ( k2_lattices @ A @ B @ D ) ) ) ) ) ) ) ) ) ) ))).
% 33.10/33.33  thf('73', plain,
% 33.10/33.33      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 33.10/33.33         (~ (v11_lattices @ X11)
% 33.10/33.33          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 33.10/33.33          | ((k2_lattices @ X11 @ X13 @ (k1_lattices @ X11 @ X12 @ X14))
% 33.10/33.33              = (k1_lattices @ X11 @ (k2_lattices @ X11 @ X13 @ X12) @ 
% 33.10/33.33                 (k2_lattices @ X11 @ X13 @ X14)))
% 33.10/33.33          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X11))
% 33.10/33.33          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 33.10/33.33          | ~ (l3_lattices @ X11)
% 33.10/33.33          | (v2_struct_0 @ X11))),
% 33.10/33.33      inference('cnf', [status(esa)], [d11_lattices])).
% 33.10/33.33  thf('74', plain,
% 33.10/33.33      (![X0 : $i, X1 : $i]:
% 33.10/33.33         ((v2_struct_0 @ sk_A)
% 33.10/33.33          | ~ (l3_lattices @ sk_A)
% 33.10/33.33          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | ((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ sk_B_3 @ X1))
% 33.10/33.33              = (k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_B_3) @ 
% 33.10/33.33                 (k2_lattices @ sk_A @ X0 @ X1)))
% 33.10/33.33          | ~ (v11_lattices @ sk_A))),
% 33.10/33.33      inference('sup-', [status(thm)], ['72', '73'])).
% 33.10/33.33  thf('75', plain, ((l3_lattices @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('76', plain,
% 33.10/33.33      (![X4 : $i]:
% 33.10/33.33         ((v2_struct_0 @ X4)
% 33.10/33.33          | ~ (v17_lattices @ X4)
% 33.10/33.33          | (v11_lattices @ X4)
% 33.10/33.33          | ~ (l3_lattices @ X4))),
% 33.10/33.33      inference('cnf', [status(esa)], [cc5_lattices])).
% 33.10/33.33  thf('77', plain, (~ (v2_struct_0 @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('78', plain,
% 33.10/33.33      ((~ (l3_lattices @ sk_A)
% 33.10/33.33        | (v11_lattices @ sk_A)
% 33.10/33.33        | ~ (v17_lattices @ sk_A))),
% 33.10/33.33      inference('sup-', [status(thm)], ['76', '77'])).
% 33.10/33.33  thf('79', plain, ((l3_lattices @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('80', plain, ((v17_lattices @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('81', plain, ((v11_lattices @ sk_A)),
% 33.10/33.33      inference('demod', [status(thm)], ['78', '79', '80'])).
% 33.10/33.33  thf('82', plain,
% 33.10/33.33      (![X0 : $i, X1 : $i]:
% 33.10/33.33         ((v2_struct_0 @ sk_A)
% 33.10/33.33          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | ((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ sk_B_3 @ X1))
% 33.10/33.33              = (k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_B_3) @ 
% 33.10/33.33                 (k2_lattices @ sk_A @ X0 @ X1))))),
% 33.10/33.33      inference('demod', [status(thm)], ['74', '75', '81'])).
% 33.10/33.33  thf('83', plain,
% 33.10/33.33      (![X0 : $i]:
% 33.10/33.33         (((k2_lattices @ sk_A @ 
% 33.10/33.33            (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ 
% 33.10/33.33            (k1_lattices @ sk_A @ sk_B_3 @ X0))
% 33.10/33.33            = (k1_lattices @ sk_A @ 
% 33.10/33.33               (k2_lattices @ sk_A @ 
% 33.10/33.33                (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ sk_B_3) @ 
% 33.10/33.33               (k2_lattices @ sk_A @ 
% 33.10/33.33                (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ X0)))
% 33.10/33.33          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | (v2_struct_0 @ sk_A))),
% 33.10/33.33      inference('sup-', [status(thm)], ['71', '82'])).
% 33.10/33.33  thf('84', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('85', plain,
% 33.10/33.33      ((m1_subset_1 @ (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ 
% 33.10/33.33        (u1_struct_0 @ sk_A))),
% 33.10/33.33      inference('clc', [status(thm)], ['69', '70'])).
% 33.10/33.33  thf(redefinition_k4_lattices, axiom,
% 33.10/33.33    (![A:$i,B:$i,C:$i]:
% 33.10/33.33     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 33.10/33.33         ( l1_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 33.10/33.33         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 33.10/33.33       ( ( k4_lattices @ A @ B @ C ) = ( k2_lattices @ A @ B @ C ) ) ))).
% 33.10/33.33  thf('86', plain,
% 33.10/33.33      (![X35 : $i, X36 : $i, X37 : $i]:
% 33.10/33.33         (~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X36))
% 33.10/33.33          | ~ (l1_lattices @ X36)
% 33.10/33.33          | ~ (v6_lattices @ X36)
% 33.10/33.33          | (v2_struct_0 @ X36)
% 33.10/33.33          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X36))
% 33.10/33.33          | ((k4_lattices @ X36 @ X35 @ X37) = (k2_lattices @ X36 @ X35 @ X37)))),
% 33.10/33.33      inference('cnf', [status(esa)], [redefinition_k4_lattices])).
% 33.10/33.33  thf('87', plain,
% 33.10/33.33      (![X0 : $i]:
% 33.10/33.33         (((k4_lattices @ sk_A @ 
% 33.10/33.33            (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ X0)
% 33.10/33.33            = (k2_lattices @ sk_A @ 
% 33.10/33.33               (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ X0))
% 33.10/33.33          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | (v2_struct_0 @ sk_A)
% 33.10/33.33          | ~ (v6_lattices @ sk_A)
% 33.10/33.33          | ~ (l1_lattices @ sk_A))),
% 33.10/33.33      inference('sup-', [status(thm)], ['85', '86'])).
% 33.10/33.33  thf('88', plain,
% 33.10/33.33      (![X2 : $i]:
% 33.10/33.33         ((v2_struct_0 @ X2)
% 33.10/33.33          | ~ (v10_lattices @ X2)
% 33.10/33.33          | (v6_lattices @ X2)
% 33.10/33.33          | ~ (l3_lattices @ X2))),
% 33.10/33.33      inference('cnf', [status(esa)], [cc1_lattices])).
% 33.10/33.33  thf('89', plain, (~ (v2_struct_0 @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('90', plain,
% 33.10/33.33      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 33.10/33.33      inference('sup-', [status(thm)], ['88', '89'])).
% 33.10/33.33  thf('91', plain, ((l3_lattices @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('92', plain, ((v10_lattices @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('93', plain, ((v6_lattices @ sk_A)),
% 33.10/33.33      inference('demod', [status(thm)], ['90', '91', '92'])).
% 33.10/33.33  thf('94', plain, ((l1_lattices @ sk_A)),
% 33.10/33.33      inference('sup-', [status(thm)], ['17', '18'])).
% 33.10/33.33  thf('95', plain,
% 33.10/33.33      (![X0 : $i]:
% 33.10/33.33         (((k4_lattices @ sk_A @ 
% 33.10/33.33            (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ X0)
% 33.10/33.33            = (k2_lattices @ sk_A @ 
% 33.10/33.33               (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ X0))
% 33.10/33.33          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | (v2_struct_0 @ sk_A))),
% 33.10/33.33      inference('demod', [status(thm)], ['87', '93', '94'])).
% 33.10/33.33  thf('96', plain, (~ (v2_struct_0 @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('97', plain,
% 33.10/33.33      (![X0 : $i]:
% 33.10/33.33         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | ((k4_lattices @ sk_A @ 
% 33.10/33.33              (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ X0)
% 33.10/33.33              = (k2_lattices @ sk_A @ 
% 33.10/33.33                 (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ X0)))),
% 33.10/33.33      inference('clc', [status(thm)], ['95', '96'])).
% 33.10/33.33  thf('98', plain,
% 33.10/33.33      (((k4_lattices @ sk_A @ 
% 33.10/33.33         (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ sk_B_3)
% 33.10/33.33         = (k2_lattices @ sk_A @ 
% 33.10/33.33            (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ sk_B_3))),
% 33.10/33.33      inference('sup-', [status(thm)], ['84', '97'])).
% 33.10/33.33  thf('99', plain,
% 33.10/33.33      ((m1_subset_1 @ (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ 
% 33.10/33.33        (u1_struct_0 @ sk_A))),
% 33.10/33.33      inference('clc', [status(thm)], ['69', '70'])).
% 33.10/33.33  thf('100', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf(commutativity_k4_lattices, axiom,
% 33.10/33.33    (![A:$i,B:$i,C:$i]:
% 33.10/33.33     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 33.10/33.33         ( l1_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 33.10/33.33         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 33.10/33.33       ( ( k4_lattices @ A @ B @ C ) = ( k4_lattices @ A @ C @ B ) ) ))).
% 33.10/33.33  thf('101', plain,
% 33.10/33.33      (![X8 : $i, X9 : $i, X10 : $i]:
% 33.10/33.33         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 33.10/33.33          | ~ (l1_lattices @ X9)
% 33.10/33.33          | ~ (v6_lattices @ X9)
% 33.10/33.33          | (v2_struct_0 @ X9)
% 33.10/33.33          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 33.10/33.33          | ((k4_lattices @ X9 @ X8 @ X10) = (k4_lattices @ X9 @ X10 @ X8)))),
% 33.10/33.33      inference('cnf', [status(esa)], [commutativity_k4_lattices])).
% 33.10/33.33  thf('102', plain,
% 33.10/33.33      (![X0 : $i]:
% 33.10/33.33         (((k4_lattices @ sk_A @ sk_B_3 @ X0)
% 33.10/33.33            = (k4_lattices @ sk_A @ X0 @ sk_B_3))
% 33.10/33.33          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | (v2_struct_0 @ sk_A)
% 33.10/33.33          | ~ (v6_lattices @ sk_A)
% 33.10/33.33          | ~ (l1_lattices @ sk_A))),
% 33.10/33.33      inference('sup-', [status(thm)], ['100', '101'])).
% 33.10/33.33  thf('103', plain, ((v6_lattices @ sk_A)),
% 33.10/33.33      inference('demod', [status(thm)], ['90', '91', '92'])).
% 33.10/33.33  thf('104', plain, ((l1_lattices @ sk_A)),
% 33.10/33.33      inference('sup-', [status(thm)], ['17', '18'])).
% 33.10/33.33  thf('105', plain,
% 33.10/33.33      (![X0 : $i]:
% 33.10/33.33         (((k4_lattices @ sk_A @ sk_B_3 @ X0)
% 33.10/33.33            = (k4_lattices @ sk_A @ X0 @ sk_B_3))
% 33.10/33.33          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | (v2_struct_0 @ sk_A))),
% 33.10/33.33      inference('demod', [status(thm)], ['102', '103', '104'])).
% 33.10/33.33  thf('106', plain, (~ (v2_struct_0 @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('107', plain,
% 33.10/33.33      (![X0 : $i]:
% 33.10/33.33         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | ((k4_lattices @ sk_A @ sk_B_3 @ X0)
% 33.10/33.33              = (k4_lattices @ sk_A @ X0 @ sk_B_3)))),
% 33.10/33.33      inference('clc', [status(thm)], ['105', '106'])).
% 33.10/33.33  thf('108', plain,
% 33.10/33.33      (((k4_lattices @ sk_A @ sk_B_3 @ 
% 33.10/33.33         (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)))
% 33.10/33.33         = (k4_lattices @ sk_A @ 
% 33.10/33.33            (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ sk_B_3))),
% 33.10/33.33      inference('sup-', [status(thm)], ['99', '107'])).
% 33.10/33.33  thf('109', plain,
% 33.10/33.33      (((k4_lattices @ sk_A @ sk_B_3 @ 
% 33.10/33.33         (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)))
% 33.10/33.33         = (k2_lattices @ sk_A @ 
% 33.10/33.33            (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ sk_B_3))),
% 33.10/33.33      inference('demod', [status(thm)], ['98', '108'])).
% 33.10/33.33  thf('110', plain,
% 33.10/33.33      ((m1_subset_1 @ (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ 
% 33.10/33.33        (u1_struct_0 @ sk_A))),
% 33.10/33.33      inference('clc', [status(thm)], ['69', '70'])).
% 33.10/33.33  thf('111', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('112', plain,
% 33.10/33.33      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B_3) @ (u1_struct_0 @ sk_A))),
% 33.10/33.33      inference('clc', [status(thm)], ['62', '63'])).
% 33.10/33.33  thf('113', plain,
% 33.10/33.33      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 33.10/33.33         (~ (v11_lattices @ X11)
% 33.10/33.33          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 33.10/33.33          | ((k2_lattices @ X11 @ X13 @ (k1_lattices @ X11 @ X12 @ X14))
% 33.10/33.33              = (k1_lattices @ X11 @ (k2_lattices @ X11 @ X13 @ X12) @ 
% 33.10/33.33                 (k2_lattices @ X11 @ X13 @ X14)))
% 33.10/33.33          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X11))
% 33.10/33.33          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 33.10/33.33          | ~ (l3_lattices @ X11)
% 33.10/33.33          | (v2_struct_0 @ X11))),
% 33.10/33.33      inference('cnf', [status(esa)], [d11_lattices])).
% 33.10/33.33  thf('114', plain,
% 33.10/33.33      (![X0 : $i, X1 : $i]:
% 33.10/33.33         ((v2_struct_0 @ sk_A)
% 33.10/33.33          | ~ (l3_lattices @ sk_A)
% 33.10/33.33          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | ((k2_lattices @ sk_A @ X0 @ 
% 33.10/33.33              (k1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3) @ X1))
% 33.10/33.33              = (k1_lattices @ sk_A @ 
% 33.10/33.33                 (k2_lattices @ sk_A @ X0 @ (k7_lattices @ sk_A @ sk_B_3)) @ 
% 33.10/33.33                 (k2_lattices @ sk_A @ X0 @ X1)))
% 33.10/33.33          | ~ (v11_lattices @ sk_A))),
% 33.10/33.33      inference('sup-', [status(thm)], ['112', '113'])).
% 33.10/33.33  thf('115', plain, ((l3_lattices @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('116', plain, ((v11_lattices @ sk_A)),
% 33.10/33.33      inference('demod', [status(thm)], ['78', '79', '80'])).
% 33.10/33.33  thf('117', plain,
% 33.10/33.33      (![X0 : $i, X1 : $i]:
% 33.10/33.33         ((v2_struct_0 @ sk_A)
% 33.10/33.33          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | ((k2_lattices @ sk_A @ X0 @ 
% 33.10/33.33              (k1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3) @ X1))
% 33.10/33.33              = (k1_lattices @ sk_A @ 
% 33.10/33.33                 (k2_lattices @ sk_A @ X0 @ (k7_lattices @ sk_A @ sk_B_3)) @ 
% 33.10/33.33                 (k2_lattices @ sk_A @ X0 @ X1))))),
% 33.10/33.33      inference('demod', [status(thm)], ['114', '115', '116'])).
% 33.10/33.33  thf('118', plain,
% 33.10/33.33      (![X0 : $i]:
% 33.10/33.33         (((k2_lattices @ sk_A @ sk_B_3 @ 
% 33.10/33.33            (k1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3) @ X0))
% 33.10/33.33            = (k1_lattices @ sk_A @ 
% 33.10/33.33               (k2_lattices @ sk_A @ sk_B_3 @ (k7_lattices @ sk_A @ sk_B_3)) @ 
% 33.10/33.33               (k2_lattices @ sk_A @ sk_B_3 @ X0)))
% 33.10/33.33          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | (v2_struct_0 @ sk_A))),
% 33.10/33.33      inference('sup-', [status(thm)], ['111', '117'])).
% 33.10/33.33  thf('119', plain,
% 33.10/33.33      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B_3) @ (u1_struct_0 @ sk_A))),
% 33.10/33.33      inference('clc', [status(thm)], ['62', '63'])).
% 33.10/33.33  thf('120', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('121', plain,
% 33.10/33.33      (![X35 : $i, X36 : $i, X37 : $i]:
% 33.10/33.33         (~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X36))
% 33.10/33.33          | ~ (l1_lattices @ X36)
% 33.10/33.33          | ~ (v6_lattices @ X36)
% 33.10/33.33          | (v2_struct_0 @ X36)
% 33.10/33.33          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X36))
% 33.10/33.33          | ((k4_lattices @ X36 @ X35 @ X37) = (k2_lattices @ X36 @ X35 @ X37)))),
% 33.10/33.33      inference('cnf', [status(esa)], [redefinition_k4_lattices])).
% 33.10/33.33  thf('122', plain,
% 33.10/33.33      (![X0 : $i]:
% 33.10/33.33         (((k4_lattices @ sk_A @ sk_B_3 @ X0)
% 33.10/33.33            = (k2_lattices @ sk_A @ sk_B_3 @ X0))
% 33.10/33.33          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | (v2_struct_0 @ sk_A)
% 33.10/33.33          | ~ (v6_lattices @ sk_A)
% 33.10/33.33          | ~ (l1_lattices @ sk_A))),
% 33.10/33.33      inference('sup-', [status(thm)], ['120', '121'])).
% 33.10/33.33  thf('123', plain, ((v6_lattices @ sk_A)),
% 33.10/33.33      inference('demod', [status(thm)], ['90', '91', '92'])).
% 33.10/33.33  thf('124', plain, ((l1_lattices @ sk_A)),
% 33.10/33.33      inference('sup-', [status(thm)], ['17', '18'])).
% 33.10/33.33  thf('125', plain,
% 33.10/33.33      (![X0 : $i]:
% 33.10/33.33         (((k4_lattices @ sk_A @ sk_B_3 @ X0)
% 33.10/33.33            = (k2_lattices @ sk_A @ sk_B_3 @ X0))
% 33.10/33.33          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | (v2_struct_0 @ sk_A))),
% 33.10/33.33      inference('demod', [status(thm)], ['122', '123', '124'])).
% 33.10/33.33  thf('126', plain, (~ (v2_struct_0 @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('127', plain,
% 33.10/33.33      (![X0 : $i]:
% 33.10/33.33         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | ((k4_lattices @ sk_A @ sk_B_3 @ X0)
% 33.10/33.33              = (k2_lattices @ sk_A @ sk_B_3 @ X0)))),
% 33.10/33.33      inference('clc', [status(thm)], ['125', '126'])).
% 33.10/33.33  thf('128', plain,
% 33.10/33.33      (((k4_lattices @ sk_A @ sk_B_3 @ (k7_lattices @ sk_A @ sk_B_3))
% 33.10/33.33         = (k2_lattices @ sk_A @ sk_B_3 @ (k7_lattices @ sk_A @ sk_B_3)))),
% 33.10/33.33      inference('sup-', [status(thm)], ['119', '127'])).
% 33.10/33.33  thf('129', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf(t47_lattices, axiom,
% 33.10/33.33    (![A:$i]:
% 33.10/33.33     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 33.10/33.33         ( v17_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 33.10/33.33       ( ![B:$i]:
% 33.10/33.33         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 33.10/33.33           ( ( k4_lattices @ A @ ( k7_lattices @ A @ B ) @ B ) =
% 33.10/33.33             ( k5_lattices @ A ) ) ) ) ))).
% 33.10/33.33  thf('130', plain,
% 33.10/33.33      (![X46 : $i, X47 : $i]:
% 33.10/33.33         (~ (m1_subset_1 @ X46 @ (u1_struct_0 @ X47))
% 33.10/33.33          | ((k4_lattices @ X47 @ (k7_lattices @ X47 @ X46) @ X46)
% 33.10/33.33              = (k5_lattices @ X47))
% 33.10/33.33          | ~ (l3_lattices @ X47)
% 33.10/33.33          | ~ (v17_lattices @ X47)
% 33.10/33.33          | ~ (v10_lattices @ X47)
% 33.10/33.33          | (v2_struct_0 @ X47))),
% 33.10/33.33      inference('cnf', [status(esa)], [t47_lattices])).
% 33.10/33.33  thf('131', plain,
% 33.10/33.33      (((v2_struct_0 @ sk_A)
% 33.10/33.33        | ~ (v10_lattices @ sk_A)
% 33.10/33.33        | ~ (v17_lattices @ sk_A)
% 33.10/33.33        | ~ (l3_lattices @ sk_A)
% 33.10/33.33        | ((k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3) @ sk_B_3)
% 33.10/33.33            = (k5_lattices @ sk_A)))),
% 33.10/33.33      inference('sup-', [status(thm)], ['129', '130'])).
% 33.10/33.33  thf('132', plain, ((v10_lattices @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('133', plain, ((v17_lattices @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('134', plain, ((l3_lattices @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('135', plain,
% 33.10/33.33      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B_3) @ (u1_struct_0 @ sk_A))),
% 33.10/33.33      inference('clc', [status(thm)], ['62', '63'])).
% 33.10/33.33  thf('136', plain,
% 33.10/33.33      (![X0 : $i]:
% 33.10/33.33         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | ((k4_lattices @ sk_A @ sk_B_3 @ X0)
% 33.10/33.33              = (k4_lattices @ sk_A @ X0 @ sk_B_3)))),
% 33.10/33.33      inference('clc', [status(thm)], ['105', '106'])).
% 33.10/33.33  thf('137', plain,
% 33.10/33.33      (((k4_lattices @ sk_A @ sk_B_3 @ (k7_lattices @ sk_A @ sk_B_3))
% 33.10/33.33         = (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3) @ sk_B_3))),
% 33.10/33.33      inference('sup-', [status(thm)], ['135', '136'])).
% 33.10/33.33  thf('138', plain,
% 33.10/33.33      (((v2_struct_0 @ sk_A)
% 33.10/33.33        | ((k4_lattices @ sk_A @ sk_B_3 @ (k7_lattices @ sk_A @ sk_B_3))
% 33.10/33.33            = (k5_lattices @ sk_A)))),
% 33.10/33.33      inference('demod', [status(thm)], ['131', '132', '133', '134', '137'])).
% 33.10/33.33  thf('139', plain, (~ (v2_struct_0 @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('140', plain,
% 33.10/33.33      (((k4_lattices @ sk_A @ sk_B_3 @ (k7_lattices @ sk_A @ sk_B_3))
% 33.10/33.33         = (k5_lattices @ sk_A))),
% 33.10/33.33      inference('clc', [status(thm)], ['138', '139'])).
% 33.10/33.33  thf('141', plain,
% 33.10/33.33      (((k5_lattices @ sk_A)
% 33.10/33.33         = (k2_lattices @ sk_A @ sk_B_3 @ (k7_lattices @ sk_A @ sk_B_3)))),
% 33.10/33.33      inference('demod', [status(thm)], ['128', '140'])).
% 33.10/33.33  thf('142', plain,
% 33.10/33.33      (![X0 : $i]:
% 33.10/33.33         (((k2_lattices @ sk_A @ sk_B_3 @ 
% 33.10/33.33            (k1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3) @ X0))
% 33.10/33.33            = (k1_lattices @ sk_A @ (k5_lattices @ sk_A) @ 
% 33.10/33.33               (k2_lattices @ sk_A @ sk_B_3 @ X0)))
% 33.10/33.33          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | (v2_struct_0 @ sk_A))),
% 33.10/33.33      inference('demod', [status(thm)], ['118', '141'])).
% 33.10/33.33  thf('143', plain, (~ (v2_struct_0 @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('144', plain,
% 33.10/33.33      (![X0 : $i]:
% 33.10/33.33         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | ((k2_lattices @ sk_A @ sk_B_3 @ 
% 33.10/33.33              (k1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3) @ X0))
% 33.10/33.33              = (k1_lattices @ sk_A @ (k5_lattices @ sk_A) @ 
% 33.10/33.33                 (k2_lattices @ sk_A @ sk_B_3 @ X0))))),
% 33.10/33.33      inference('clc', [status(thm)], ['142', '143'])).
% 33.10/33.33  thf('145', plain,
% 33.10/33.33      (((k2_lattices @ sk_A @ sk_B_3 @ 
% 33.10/33.33         (k1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3) @ 
% 33.10/33.33          (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3))))
% 33.10/33.33         = (k1_lattices @ sk_A @ (k5_lattices @ sk_A) @ 
% 33.10/33.33            (k2_lattices @ sk_A @ sk_B_3 @ 
% 33.10/33.33             (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)))))),
% 33.10/33.33      inference('sup-', [status(thm)], ['110', '144'])).
% 33.10/33.33  thf('146', plain,
% 33.10/33.33      ((m1_subset_1 @ (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ 
% 33.10/33.33        (u1_struct_0 @ sk_A))),
% 33.10/33.33      inference('clc', [status(thm)], ['69', '70'])).
% 33.10/33.33  thf('147', plain,
% 33.10/33.33      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B_3) @ (u1_struct_0 @ sk_A))),
% 33.10/33.33      inference('clc', [status(thm)], ['62', '63'])).
% 33.10/33.33  thf('148', plain,
% 33.10/33.33      (![X32 : $i, X33 : $i, X34 : $i]:
% 33.10/33.33         (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X33))
% 33.10/33.33          | ~ (l2_lattices @ X33)
% 33.10/33.33          | ~ (v4_lattices @ X33)
% 33.10/33.33          | (v2_struct_0 @ X33)
% 33.10/33.33          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X33))
% 33.10/33.33          | ((k3_lattices @ X33 @ X32 @ X34) = (k1_lattices @ X33 @ X32 @ X34)))),
% 33.10/33.33      inference('cnf', [status(esa)], [redefinition_k3_lattices])).
% 33.10/33.33  thf('149', plain,
% 33.10/33.33      (![X0 : $i]:
% 33.10/33.33         (((k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3) @ X0)
% 33.10/33.33            = (k1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3) @ X0))
% 33.10/33.33          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | (v2_struct_0 @ sk_A)
% 33.10/33.33          | ~ (v4_lattices @ sk_A)
% 33.10/33.33          | ~ (l2_lattices @ sk_A))),
% 33.10/33.33      inference('sup-', [status(thm)], ['147', '148'])).
% 33.10/33.33  thf('150', plain, ((v4_lattices @ sk_A)),
% 33.10/33.33      inference('demod', [status(thm)], ['6', '7', '8'])).
% 33.10/33.33  thf('151', plain, ((l2_lattices @ sk_A)),
% 33.10/33.33      inference('sup-', [status(thm)], ['10', '11'])).
% 33.10/33.33  thf('152', plain,
% 33.10/33.33      (![X0 : $i]:
% 33.10/33.33         (((k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3) @ X0)
% 33.10/33.33            = (k1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3) @ X0))
% 33.10/33.33          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | (v2_struct_0 @ sk_A))),
% 33.10/33.33      inference('demod', [status(thm)], ['149', '150', '151'])).
% 33.10/33.33  thf('153', plain, (~ (v2_struct_0 @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('154', plain,
% 33.10/33.33      (![X0 : $i]:
% 33.10/33.33         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | ((k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3) @ X0)
% 33.10/33.33              = (k1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3) @ X0)))),
% 33.10/33.33      inference('clc', [status(thm)], ['152', '153'])).
% 33.10/33.33  thf('155', plain,
% 33.10/33.33      (((k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3) @ 
% 33.10/33.33         (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)))
% 33.10/33.33         = (k1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3) @ 
% 33.10/33.33            (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3))))),
% 33.10/33.33      inference('sup-', [status(thm)], ['146', '154'])).
% 33.10/33.33  thf('156', plain,
% 33.10/33.33      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B_3) @ (u1_struct_0 @ sk_A))),
% 33.10/33.33      inference('clc', [status(thm)], ['62', '63'])).
% 33.10/33.33  thf(t48_lattices, axiom,
% 33.10/33.33    (![A:$i]:
% 33.10/33.33     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 33.10/33.33         ( v17_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 33.10/33.33       ( ![B:$i]:
% 33.10/33.33         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 33.10/33.33           ( ( k3_lattices @ A @ ( k7_lattices @ A @ B ) @ B ) =
% 33.10/33.33             ( k6_lattices @ A ) ) ) ) ))).
% 33.10/33.33  thf('157', plain,
% 33.10/33.33      (![X48 : $i, X49 : $i]:
% 33.10/33.33         (~ (m1_subset_1 @ X48 @ (u1_struct_0 @ X49))
% 33.10/33.33          | ((k3_lattices @ X49 @ (k7_lattices @ X49 @ X48) @ X48)
% 33.10/33.33              = (k6_lattices @ X49))
% 33.10/33.33          | ~ (l3_lattices @ X49)
% 33.10/33.33          | ~ (v17_lattices @ X49)
% 33.10/33.33          | ~ (v10_lattices @ X49)
% 33.10/33.33          | (v2_struct_0 @ X49))),
% 33.10/33.33      inference('cnf', [status(esa)], [t48_lattices])).
% 33.10/33.33  thf('158', plain,
% 33.10/33.33      (((v2_struct_0 @ sk_A)
% 33.10/33.33        | ~ (v10_lattices @ sk_A)
% 33.10/33.33        | ~ (v17_lattices @ sk_A)
% 33.10/33.33        | ~ (l3_lattices @ sk_A)
% 33.10/33.33        | ((k3_lattices @ sk_A @ 
% 33.10/33.33            (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ 
% 33.10/33.33            (k7_lattices @ sk_A @ sk_B_3)) = (k6_lattices @ sk_A)))),
% 33.10/33.33      inference('sup-', [status(thm)], ['156', '157'])).
% 33.10/33.33  thf('159', plain, ((v10_lattices @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('160', plain, ((v17_lattices @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('161', plain, ((l3_lattices @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('162', plain,
% 33.10/33.33      ((m1_subset_1 @ (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ 
% 33.10/33.33        (u1_struct_0 @ sk_A))),
% 33.10/33.33      inference('clc', [status(thm)], ['69', '70'])).
% 33.10/33.33  thf('163', plain,
% 33.10/33.33      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B_3) @ (u1_struct_0 @ sk_A))),
% 33.10/33.33      inference('clc', [status(thm)], ['62', '63'])).
% 33.10/33.33  thf('164', plain,
% 33.10/33.33      (![X5 : $i, X6 : $i, X7 : $i]:
% 33.10/33.33         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 33.10/33.33          | ~ (l2_lattices @ X6)
% 33.10/33.33          | ~ (v4_lattices @ X6)
% 33.10/33.33          | (v2_struct_0 @ X6)
% 33.10/33.33          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 33.10/33.33          | ((k3_lattices @ X6 @ X5 @ X7) = (k3_lattices @ X6 @ X7 @ X5)))),
% 33.10/33.33      inference('cnf', [status(esa)], [commutativity_k3_lattices])).
% 33.10/33.33  thf('165', plain,
% 33.10/33.33      (![X0 : $i]:
% 33.10/33.33         (((k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3) @ X0)
% 33.10/33.33            = (k3_lattices @ sk_A @ X0 @ (k7_lattices @ sk_A @ sk_B_3)))
% 33.10/33.33          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | (v2_struct_0 @ sk_A)
% 33.10/33.33          | ~ (v4_lattices @ sk_A)
% 33.10/33.33          | ~ (l2_lattices @ sk_A))),
% 33.10/33.33      inference('sup-', [status(thm)], ['163', '164'])).
% 33.10/33.33  thf('166', plain, ((v4_lattices @ sk_A)),
% 33.10/33.33      inference('demod', [status(thm)], ['6', '7', '8'])).
% 33.10/33.33  thf('167', plain, ((l2_lattices @ sk_A)),
% 33.10/33.33      inference('sup-', [status(thm)], ['10', '11'])).
% 33.10/33.33  thf('168', plain,
% 33.10/33.33      (![X0 : $i]:
% 33.10/33.33         (((k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3) @ X0)
% 33.10/33.33            = (k3_lattices @ sk_A @ X0 @ (k7_lattices @ sk_A @ sk_B_3)))
% 33.10/33.33          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | (v2_struct_0 @ sk_A))),
% 33.10/33.33      inference('demod', [status(thm)], ['165', '166', '167'])).
% 33.10/33.33  thf('169', plain, (~ (v2_struct_0 @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('170', plain,
% 33.10/33.33      (![X0 : $i]:
% 33.10/33.33         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | ((k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3) @ X0)
% 33.10/33.33              = (k3_lattices @ sk_A @ X0 @ (k7_lattices @ sk_A @ sk_B_3))))),
% 33.10/33.33      inference('clc', [status(thm)], ['168', '169'])).
% 33.10/33.33  thf('171', plain,
% 33.10/33.33      (((k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3) @ 
% 33.10/33.33         (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)))
% 33.10/33.33         = (k3_lattices @ sk_A @ 
% 33.10/33.33            (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ 
% 33.10/33.33            (k7_lattices @ sk_A @ sk_B_3)))),
% 33.10/33.33      inference('sup-', [status(thm)], ['162', '170'])).
% 33.10/33.33  thf('172', plain,
% 33.10/33.33      (((v2_struct_0 @ sk_A)
% 33.10/33.33        | ((k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3) @ 
% 33.10/33.33            (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)))
% 33.10/33.33            = (k6_lattices @ sk_A)))),
% 33.10/33.33      inference('demod', [status(thm)], ['158', '159', '160', '161', '171'])).
% 33.10/33.33  thf('173', plain, (~ (v2_struct_0 @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('174', plain,
% 33.10/33.33      (((k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3) @ 
% 33.10/33.33         (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)))
% 33.10/33.33         = (k6_lattices @ sk_A))),
% 33.10/33.33      inference('clc', [status(thm)], ['172', '173'])).
% 33.10/33.33  thf('175', plain,
% 33.10/33.33      (((k6_lattices @ sk_A)
% 33.10/33.33         = (k1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3) @ 
% 33.10/33.33            (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3))))),
% 33.10/33.33      inference('demod', [status(thm)], ['155', '174'])).
% 33.10/33.33  thf('176', plain,
% 33.10/33.33      ((m1_subset_1 @ (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ 
% 33.10/33.33        (u1_struct_0 @ sk_A))),
% 33.10/33.33      inference('clc', [status(thm)], ['69', '70'])).
% 33.10/33.33  thf('177', plain,
% 33.10/33.33      (![X0 : $i]:
% 33.10/33.33         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | ((k4_lattices @ sk_A @ sk_B_3 @ X0)
% 33.10/33.33              = (k2_lattices @ sk_A @ sk_B_3 @ X0)))),
% 33.10/33.33      inference('clc', [status(thm)], ['125', '126'])).
% 33.10/33.33  thf('178', plain,
% 33.10/33.33      (((k4_lattices @ sk_A @ sk_B_3 @ 
% 33.10/33.33         (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)))
% 33.10/33.33         = (k2_lattices @ sk_A @ sk_B_3 @ 
% 33.10/33.33            (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3))))),
% 33.10/33.33      inference('sup-', [status(thm)], ['176', '177'])).
% 33.10/33.33  thf('179', plain,
% 33.10/33.33      ((m1_subset_1 @ (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ 
% 33.10/33.33        (u1_struct_0 @ sk_A))),
% 33.10/33.33      inference('clc', [status(thm)], ['69', '70'])).
% 33.10/33.33  thf('180', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('181', plain,
% 33.10/33.33      (![X27 : $i]:
% 33.10/33.33         ((m1_subset_1 @ (k5_lattices @ X27) @ (u1_struct_0 @ X27))
% 33.10/33.33          | ~ (l1_lattices @ X27)
% 33.10/33.33          | (v2_struct_0 @ X27))),
% 33.10/33.33      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 33.10/33.33  thf('182', plain,
% 33.10/33.33      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 33.10/33.33         (~ (v11_lattices @ X11)
% 33.10/33.33          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 33.10/33.33          | ((k2_lattices @ X11 @ X13 @ (k1_lattices @ X11 @ X12 @ X14))
% 33.10/33.33              = (k1_lattices @ X11 @ (k2_lattices @ X11 @ X13 @ X12) @ 
% 33.10/33.33                 (k2_lattices @ X11 @ X13 @ X14)))
% 33.10/33.33          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X11))
% 33.10/33.33          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 33.10/33.33          | ~ (l3_lattices @ X11)
% 33.10/33.33          | (v2_struct_0 @ X11))),
% 33.10/33.33      inference('cnf', [status(esa)], [d11_lattices])).
% 33.10/33.33  thf('183', plain,
% 33.10/33.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 33.10/33.33         ((v2_struct_0 @ X0)
% 33.10/33.33          | ~ (l1_lattices @ X0)
% 33.10/33.33          | (v2_struct_0 @ X0)
% 33.10/33.33          | ~ (l3_lattices @ X0)
% 33.10/33.33          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 33.10/33.33          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 33.10/33.33          | ((k2_lattices @ X0 @ X1 @ 
% 33.10/33.33              (k1_lattices @ X0 @ (k5_lattices @ X0) @ X2))
% 33.10/33.33              = (k1_lattices @ X0 @ 
% 33.10/33.33                 (k2_lattices @ X0 @ X1 @ (k5_lattices @ X0)) @ 
% 33.10/33.33                 (k2_lattices @ X0 @ X1 @ X2)))
% 33.10/33.33          | ~ (v11_lattices @ X0))),
% 33.10/33.33      inference('sup-', [status(thm)], ['181', '182'])).
% 33.10/33.33  thf('184', plain,
% 33.10/33.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 33.10/33.33         (~ (v11_lattices @ X0)
% 33.10/33.33          | ((k2_lattices @ X0 @ X1 @ 
% 33.10/33.33              (k1_lattices @ X0 @ (k5_lattices @ X0) @ X2))
% 33.10/33.33              = (k1_lattices @ X0 @ 
% 33.10/33.33                 (k2_lattices @ X0 @ X1 @ (k5_lattices @ X0)) @ 
% 33.10/33.33                 (k2_lattices @ X0 @ X1 @ X2)))
% 33.10/33.33          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 33.10/33.33          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 33.10/33.33          | ~ (l3_lattices @ X0)
% 33.10/33.33          | ~ (l1_lattices @ X0)
% 33.10/33.33          | (v2_struct_0 @ X0))),
% 33.10/33.33      inference('simplify', [status(thm)], ['183'])).
% 33.10/33.33  thf('185', plain,
% 33.10/33.33      (![X0 : $i]:
% 33.10/33.33         ((v2_struct_0 @ sk_A)
% 33.10/33.33          | ~ (l1_lattices @ sk_A)
% 33.10/33.33          | ~ (l3_lattices @ sk_A)
% 33.10/33.33          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | ((k2_lattices @ sk_A @ X0 @ 
% 33.10/33.33              (k1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_3))
% 33.10/33.33              = (k1_lattices @ sk_A @ 
% 33.10/33.33                 (k2_lattices @ sk_A @ X0 @ (k5_lattices @ sk_A)) @ 
% 33.10/33.33                 (k2_lattices @ sk_A @ X0 @ sk_B_3)))
% 33.10/33.33          | ~ (v11_lattices @ sk_A))),
% 33.10/33.33      inference('sup-', [status(thm)], ['180', '184'])).
% 33.10/33.33  thf('186', plain, ((l1_lattices @ sk_A)),
% 33.10/33.33      inference('sup-', [status(thm)], ['17', '18'])).
% 33.10/33.33  thf('187', plain, ((l3_lattices @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('188', plain,
% 33.10/33.33      (![X27 : $i]:
% 33.10/33.33         ((m1_subset_1 @ (k5_lattices @ X27) @ (u1_struct_0 @ X27))
% 33.10/33.33          | ~ (l1_lattices @ X27)
% 33.10/33.33          | (v2_struct_0 @ X27))),
% 33.10/33.33      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 33.10/33.33  thf('189', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf(d8_lattices, axiom,
% 33.10/33.33    (![A:$i]:
% 33.10/33.33     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 33.10/33.33       ( ( v8_lattices @ A ) <=>
% 33.10/33.33         ( ![B:$i]:
% 33.10/33.33           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 33.10/33.33             ( ![C:$i]:
% 33.10/33.33               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 33.10/33.33                 ( ( k1_lattices @ A @ ( k2_lattices @ A @ B @ C ) @ C ) =
% 33.10/33.33                   ( C ) ) ) ) ) ) ) ))).
% 33.10/33.33  thf('190', plain,
% 33.10/33.33      (![X21 : $i, X22 : $i, X23 : $i]:
% 33.10/33.33         (~ (v8_lattices @ X21)
% 33.10/33.33          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 33.10/33.33          | ((k1_lattices @ X21 @ (k2_lattices @ X21 @ X23 @ X22) @ X22)
% 33.10/33.33              = (X22))
% 33.10/33.33          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X21))
% 33.10/33.33          | ~ (l3_lattices @ X21)
% 33.10/33.33          | (v2_struct_0 @ X21))),
% 33.10/33.33      inference('cnf', [status(esa)], [d8_lattices])).
% 33.10/33.33  thf('191', plain,
% 33.10/33.33      (![X0 : $i]:
% 33.10/33.33         ((v2_struct_0 @ sk_A)
% 33.10/33.33          | ~ (l3_lattices @ sk_A)
% 33.10/33.33          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | ((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_B_3) @ sk_B_3)
% 33.10/33.33              = (sk_B_3))
% 33.10/33.33          | ~ (v8_lattices @ sk_A))),
% 33.10/33.33      inference('sup-', [status(thm)], ['189', '190'])).
% 33.10/33.33  thf('192', plain, ((l3_lattices @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('193', plain,
% 33.10/33.33      (![X2 : $i]:
% 33.10/33.33         ((v2_struct_0 @ X2)
% 33.10/33.33          | ~ (v10_lattices @ X2)
% 33.10/33.33          | (v8_lattices @ X2)
% 33.10/33.33          | ~ (l3_lattices @ X2))),
% 33.10/33.33      inference('cnf', [status(esa)], [cc1_lattices])).
% 33.10/33.33  thf('194', plain, (~ (v2_struct_0 @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('195', plain,
% 33.10/33.33      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 33.10/33.33      inference('sup-', [status(thm)], ['193', '194'])).
% 33.10/33.33  thf('196', plain, ((l3_lattices @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('197', plain, ((v10_lattices @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('198', plain, ((v8_lattices @ sk_A)),
% 33.10/33.33      inference('demod', [status(thm)], ['195', '196', '197'])).
% 33.10/33.33  thf('199', plain,
% 33.10/33.33      (![X0 : $i]:
% 33.10/33.33         ((v2_struct_0 @ sk_A)
% 33.10/33.33          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | ((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_B_3) @ sk_B_3)
% 33.10/33.33              = (sk_B_3)))),
% 33.10/33.33      inference('demod', [status(thm)], ['191', '192', '198'])).
% 33.10/33.33  thf('200', plain, (~ (v2_struct_0 @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('201', plain,
% 33.10/33.33      (![X0 : $i]:
% 33.10/33.33         (((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_B_3) @ sk_B_3)
% 33.10/33.33            = (sk_B_3))
% 33.10/33.33          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 33.10/33.33      inference('clc', [status(thm)], ['199', '200'])).
% 33.10/33.33  thf('202', plain,
% 33.10/33.33      (((v2_struct_0 @ sk_A)
% 33.10/33.33        | ~ (l1_lattices @ sk_A)
% 33.10/33.33        | ((k1_lattices @ sk_A @ 
% 33.10/33.33            (k2_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_3) @ sk_B_3)
% 33.10/33.33            = (sk_B_3)))),
% 33.10/33.33      inference('sup-', [status(thm)], ['188', '201'])).
% 33.10/33.33  thf('203', plain, ((l1_lattices @ sk_A)),
% 33.10/33.33      inference('sup-', [status(thm)], ['17', '18'])).
% 33.10/33.33  thf('204', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('205', plain,
% 33.10/33.33      (![X27 : $i]:
% 33.10/33.33         ((m1_subset_1 @ (k5_lattices @ X27) @ (u1_struct_0 @ X27))
% 33.10/33.33          | ~ (l1_lattices @ X27)
% 33.10/33.33          | (v2_struct_0 @ X27))),
% 33.10/33.33      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 33.10/33.33  thf(d16_lattices, axiom,
% 33.10/33.33    (![A:$i]:
% 33.10/33.33     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 33.10/33.33       ( ( v13_lattices @ A ) =>
% 33.10/33.33         ( ![B:$i]:
% 33.10/33.33           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 33.10/33.33             ( ( ( B ) = ( k5_lattices @ A ) ) <=>
% 33.10/33.33               ( ![C:$i]:
% 33.10/33.33                 ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 33.10/33.33                   ( ( ( k2_lattices @ A @ B @ C ) = ( B ) ) & 
% 33.10/33.33                     ( ( k2_lattices @ A @ C @ B ) = ( B ) ) ) ) ) ) ) ) ) ))).
% 33.10/33.33  thf('206', plain,
% 33.10/33.33      (![X15 : $i, X16 : $i, X17 : $i]:
% 33.10/33.33         (~ (v13_lattices @ X15)
% 33.10/33.33          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 33.10/33.33          | ((X16) != (k5_lattices @ X15))
% 33.10/33.33          | ((k2_lattices @ X15 @ X16 @ X17) = (X16))
% 33.10/33.33          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X15))
% 33.10/33.33          | ~ (l1_lattices @ X15)
% 33.10/33.33          | (v2_struct_0 @ X15))),
% 33.10/33.33      inference('cnf', [status(esa)], [d16_lattices])).
% 33.10/33.33  thf('207', plain,
% 33.10/33.33      (![X15 : $i, X17 : $i]:
% 33.10/33.33         ((v2_struct_0 @ X15)
% 33.10/33.33          | ~ (l1_lattices @ X15)
% 33.10/33.33          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X15))
% 33.10/33.33          | ((k2_lattices @ X15 @ (k5_lattices @ X15) @ X17)
% 33.10/33.33              = (k5_lattices @ X15))
% 33.10/33.33          | ~ (m1_subset_1 @ (k5_lattices @ X15) @ (u1_struct_0 @ X15))
% 33.10/33.33          | ~ (v13_lattices @ X15))),
% 33.10/33.33      inference('simplify', [status(thm)], ['206'])).
% 33.10/33.33  thf('208', plain,
% 33.10/33.33      (![X0 : $i, X1 : $i]:
% 33.10/33.33         ((v2_struct_0 @ X0)
% 33.10/33.33          | ~ (l1_lattices @ X0)
% 33.10/33.33          | ~ (v13_lattices @ X0)
% 33.10/33.33          | ((k2_lattices @ X0 @ (k5_lattices @ X0) @ X1) = (k5_lattices @ X0))
% 33.10/33.33          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 33.10/33.33          | ~ (l1_lattices @ X0)
% 33.10/33.33          | (v2_struct_0 @ X0))),
% 33.10/33.33      inference('sup-', [status(thm)], ['205', '207'])).
% 33.10/33.33  thf('209', plain,
% 33.10/33.33      (![X0 : $i, X1 : $i]:
% 33.10/33.33         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 33.10/33.33          | ((k2_lattices @ X0 @ (k5_lattices @ X0) @ X1) = (k5_lattices @ X0))
% 33.10/33.33          | ~ (v13_lattices @ X0)
% 33.10/33.33          | ~ (l1_lattices @ X0)
% 33.10/33.33          | (v2_struct_0 @ X0))),
% 33.10/33.33      inference('simplify', [status(thm)], ['208'])).
% 33.10/33.33  thf('210', plain,
% 33.10/33.33      (((v2_struct_0 @ sk_A)
% 33.10/33.33        | ~ (l1_lattices @ sk_A)
% 33.10/33.33        | ~ (v13_lattices @ sk_A)
% 33.10/33.33        | ((k2_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_3)
% 33.10/33.33            = (k5_lattices @ sk_A)))),
% 33.10/33.33      inference('sup-', [status(thm)], ['204', '209'])).
% 33.10/33.33  thf('211', plain, ((l1_lattices @ sk_A)),
% 33.10/33.33      inference('sup-', [status(thm)], ['17', '18'])).
% 33.10/33.33  thf('212', plain, ((v13_lattices @ sk_A)),
% 33.10/33.33      inference('demod', [status(thm)], ['31', '37'])).
% 33.10/33.33  thf('213', plain,
% 33.10/33.33      (((v2_struct_0 @ sk_A)
% 33.10/33.33        | ((k2_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_3)
% 33.10/33.33            = (k5_lattices @ sk_A)))),
% 33.10/33.33      inference('demod', [status(thm)], ['210', '211', '212'])).
% 33.10/33.33  thf('214', plain, (~ (v2_struct_0 @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('215', plain,
% 33.10/33.33      (((k2_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_3)
% 33.10/33.33         = (k5_lattices @ sk_A))),
% 33.10/33.33      inference('clc', [status(thm)], ['213', '214'])).
% 33.10/33.33  thf('216', plain,
% 33.10/33.33      (((v2_struct_0 @ sk_A)
% 33.10/33.33        | ((k1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_3) = (sk_B_3)))),
% 33.10/33.33      inference('demod', [status(thm)], ['202', '203', '215'])).
% 33.10/33.33  thf('217', plain, (~ (v2_struct_0 @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('218', plain,
% 33.10/33.33      (((k1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_3) = (sk_B_3))),
% 33.10/33.33      inference('clc', [status(thm)], ['216', '217'])).
% 33.10/33.33  thf('219', plain, ((v11_lattices @ sk_A)),
% 33.10/33.33      inference('demod', [status(thm)], ['78', '79', '80'])).
% 33.10/33.33  thf('220', plain,
% 33.10/33.33      (![X0 : $i]:
% 33.10/33.33         ((v2_struct_0 @ sk_A)
% 33.10/33.33          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | ((k2_lattices @ sk_A @ X0 @ sk_B_3)
% 33.10/33.33              = (k1_lattices @ sk_A @ 
% 33.10/33.33                 (k2_lattices @ sk_A @ X0 @ (k5_lattices @ sk_A)) @ 
% 33.10/33.33                 (k2_lattices @ sk_A @ X0 @ sk_B_3))))),
% 33.10/33.33      inference('demod', [status(thm)], ['185', '186', '187', '218', '219'])).
% 33.10/33.33  thf('221', plain, (~ (v2_struct_0 @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('222', plain,
% 33.10/33.33      (![X0 : $i]:
% 33.10/33.33         (((k2_lattices @ sk_A @ X0 @ sk_B_3)
% 33.10/33.33            = (k1_lattices @ sk_A @ 
% 33.10/33.33               (k2_lattices @ sk_A @ X0 @ (k5_lattices @ sk_A)) @ 
% 33.10/33.33               (k2_lattices @ sk_A @ X0 @ sk_B_3)))
% 33.10/33.33          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 33.10/33.33      inference('clc', [status(thm)], ['220', '221'])).
% 33.10/33.33  thf('223', plain,
% 33.10/33.33      (((k2_lattices @ sk_A @ 
% 33.10/33.33         (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ sk_B_3)
% 33.10/33.33         = (k1_lattices @ sk_A @ 
% 33.10/33.33            (k2_lattices @ sk_A @ 
% 33.10/33.33             (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ 
% 33.10/33.33             (k5_lattices @ sk_A)) @ 
% 33.10/33.33            (k2_lattices @ sk_A @ 
% 33.10/33.33             (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ sk_B_3)))),
% 33.10/33.33      inference('sup-', [status(thm)], ['179', '222'])).
% 33.10/33.33  thf('224', plain,
% 33.10/33.33      (((k4_lattices @ sk_A @ sk_B_3 @ 
% 33.10/33.33         (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)))
% 33.10/33.33         = (k2_lattices @ sk_A @ 
% 33.10/33.33            (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ sk_B_3))),
% 33.10/33.33      inference('demod', [status(thm)], ['98', '108'])).
% 33.10/33.33  thf('225', plain,
% 33.10/33.33      ((m1_subset_1 @ (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ 
% 33.10/33.33        (u1_struct_0 @ sk_A))),
% 33.10/33.33      inference('clc', [status(thm)], ['69', '70'])).
% 33.10/33.33  thf('226', plain,
% 33.10/33.33      (![X27 : $i]:
% 33.10/33.33         ((m1_subset_1 @ (k5_lattices @ X27) @ (u1_struct_0 @ X27))
% 33.10/33.33          | ~ (l1_lattices @ X27)
% 33.10/33.33          | (v2_struct_0 @ X27))),
% 33.10/33.33      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 33.10/33.33  thf('227', plain,
% 33.10/33.33      (![X15 : $i, X16 : $i, X17 : $i]:
% 33.10/33.33         (~ (v13_lattices @ X15)
% 33.10/33.33          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 33.10/33.33          | ((X16) != (k5_lattices @ X15))
% 33.10/33.33          | ((k2_lattices @ X15 @ X17 @ X16) = (X16))
% 33.10/33.33          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X15))
% 33.10/33.33          | ~ (l1_lattices @ X15)
% 33.10/33.33          | (v2_struct_0 @ X15))),
% 33.10/33.33      inference('cnf', [status(esa)], [d16_lattices])).
% 33.10/33.33  thf('228', plain,
% 33.10/33.33      (![X15 : $i, X17 : $i]:
% 33.10/33.33         ((v2_struct_0 @ X15)
% 33.10/33.33          | ~ (l1_lattices @ X15)
% 33.10/33.33          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X15))
% 33.10/33.33          | ((k2_lattices @ X15 @ X17 @ (k5_lattices @ X15))
% 33.10/33.33              = (k5_lattices @ X15))
% 33.10/33.33          | ~ (m1_subset_1 @ (k5_lattices @ X15) @ (u1_struct_0 @ X15))
% 33.10/33.33          | ~ (v13_lattices @ X15))),
% 33.10/33.33      inference('simplify', [status(thm)], ['227'])).
% 33.10/33.33  thf('229', plain,
% 33.10/33.33      (![X0 : $i, X1 : $i]:
% 33.10/33.33         ((v2_struct_0 @ X0)
% 33.10/33.33          | ~ (l1_lattices @ X0)
% 33.10/33.33          | ~ (v13_lattices @ X0)
% 33.10/33.33          | ((k2_lattices @ X0 @ X1 @ (k5_lattices @ X0)) = (k5_lattices @ X0))
% 33.10/33.33          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 33.10/33.33          | ~ (l1_lattices @ X0)
% 33.10/33.33          | (v2_struct_0 @ X0))),
% 33.10/33.33      inference('sup-', [status(thm)], ['226', '228'])).
% 33.10/33.33  thf('230', plain,
% 33.10/33.33      (![X0 : $i, X1 : $i]:
% 33.10/33.33         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 33.10/33.33          | ((k2_lattices @ X0 @ X1 @ (k5_lattices @ X0)) = (k5_lattices @ X0))
% 33.10/33.33          | ~ (v13_lattices @ X0)
% 33.10/33.33          | ~ (l1_lattices @ X0)
% 33.10/33.33          | (v2_struct_0 @ X0))),
% 33.10/33.33      inference('simplify', [status(thm)], ['229'])).
% 33.10/33.33  thf('231', plain,
% 33.10/33.33      (((v2_struct_0 @ sk_A)
% 33.10/33.33        | ~ (l1_lattices @ sk_A)
% 33.10/33.33        | ~ (v13_lattices @ sk_A)
% 33.10/33.33        | ((k2_lattices @ sk_A @ 
% 33.10/33.33            (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ 
% 33.10/33.33            (k5_lattices @ sk_A)) = (k5_lattices @ sk_A)))),
% 33.10/33.33      inference('sup-', [status(thm)], ['225', '230'])).
% 33.10/33.33  thf('232', plain, ((l1_lattices @ sk_A)),
% 33.10/33.33      inference('sup-', [status(thm)], ['17', '18'])).
% 33.10/33.33  thf('233', plain, ((v13_lattices @ sk_A)),
% 33.10/33.33      inference('demod', [status(thm)], ['31', '37'])).
% 33.10/33.33  thf('234', plain,
% 33.10/33.33      (((v2_struct_0 @ sk_A)
% 33.10/33.33        | ((k2_lattices @ sk_A @ 
% 33.10/33.33            (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ 
% 33.10/33.33            (k5_lattices @ sk_A)) = (k5_lattices @ sk_A)))),
% 33.10/33.33      inference('demod', [status(thm)], ['231', '232', '233'])).
% 33.10/33.33  thf('235', plain, (~ (v2_struct_0 @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('236', plain,
% 33.10/33.33      (((k2_lattices @ sk_A @ 
% 33.10/33.33         (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ 
% 33.10/33.33         (k5_lattices @ sk_A)) = (k5_lattices @ sk_A))),
% 33.10/33.33      inference('clc', [status(thm)], ['234', '235'])).
% 33.10/33.33  thf('237', plain,
% 33.10/33.33      (((k4_lattices @ sk_A @ sk_B_3 @ 
% 33.10/33.33         (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)))
% 33.10/33.33         = (k2_lattices @ sk_A @ 
% 33.10/33.33            (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ sk_B_3))),
% 33.10/33.33      inference('demod', [status(thm)], ['98', '108'])).
% 33.10/33.33  thf('238', plain,
% 33.10/33.33      (((k4_lattices @ sk_A @ sk_B_3 @ 
% 33.10/33.33         (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)))
% 33.10/33.33         = (k1_lattices @ sk_A @ (k5_lattices @ sk_A) @ 
% 33.10/33.33            (k4_lattices @ sk_A @ sk_B_3 @ 
% 33.10/33.33             (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)))))),
% 33.10/33.33      inference('demod', [status(thm)], ['223', '224', '236', '237'])).
% 33.10/33.33  thf('239', plain,
% 33.10/33.33      (((k2_lattices @ sk_A @ sk_B_3 @ (k6_lattices @ sk_A))
% 33.10/33.33         = (k4_lattices @ sk_A @ sk_B_3 @ 
% 33.10/33.33            (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3))))),
% 33.10/33.33      inference('demod', [status(thm)], ['145', '175', '178', '238'])).
% 33.10/33.33  thf('240', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('241', plain,
% 33.10/33.33      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B_3) @ (u1_struct_0 @ sk_A))),
% 33.10/33.33      inference('clc', [status(thm)], ['62', '63'])).
% 33.10/33.33  thf(d9_lattices, axiom,
% 33.10/33.33    (![A:$i]:
% 33.10/33.33     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 33.10/33.33       ( ( v9_lattices @ A ) <=>
% 33.10/33.33         ( ![B:$i]:
% 33.10/33.33           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 33.10/33.33             ( ![C:$i]:
% 33.10/33.33               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 33.10/33.33                 ( ( k2_lattices @ A @ B @ ( k1_lattices @ A @ B @ C ) ) =
% 33.10/33.33                   ( B ) ) ) ) ) ) ) ))).
% 33.10/33.33  thf('242', plain,
% 33.10/33.33      (![X24 : $i, X25 : $i, X26 : $i]:
% 33.10/33.33         (~ (v9_lattices @ X24)
% 33.10/33.33          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X24))
% 33.10/33.33          | ((k2_lattices @ X24 @ X26 @ (k1_lattices @ X24 @ X26 @ X25))
% 33.10/33.33              = (X26))
% 33.10/33.33          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X24))
% 33.10/33.33          | ~ (l3_lattices @ X24)
% 33.10/33.33          | (v2_struct_0 @ X24))),
% 33.10/33.33      inference('cnf', [status(esa)], [d9_lattices])).
% 33.10/33.33  thf('243', plain,
% 33.10/33.33      (![X0 : $i]:
% 33.10/33.33         ((v2_struct_0 @ sk_A)
% 33.10/33.33          | ~ (l3_lattices @ sk_A)
% 33.10/33.33          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | ((k2_lattices @ sk_A @ X0 @ 
% 33.10/33.33              (k1_lattices @ sk_A @ X0 @ (k7_lattices @ sk_A @ sk_B_3))) = (
% 33.10/33.33              X0))
% 33.10/33.33          | ~ (v9_lattices @ sk_A))),
% 33.10/33.33      inference('sup-', [status(thm)], ['241', '242'])).
% 33.10/33.33  thf('244', plain, ((l3_lattices @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('245', plain,
% 33.10/33.33      (![X2 : $i]:
% 33.10/33.33         ((v2_struct_0 @ X2)
% 33.10/33.33          | ~ (v10_lattices @ X2)
% 33.10/33.33          | (v9_lattices @ X2)
% 33.10/33.33          | ~ (l3_lattices @ X2))),
% 33.10/33.33      inference('cnf', [status(esa)], [cc1_lattices])).
% 33.10/33.33  thf('246', plain, (~ (v2_struct_0 @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('247', plain,
% 33.10/33.33      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 33.10/33.33      inference('sup-', [status(thm)], ['245', '246'])).
% 33.10/33.33  thf('248', plain, ((l3_lattices @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('249', plain, ((v10_lattices @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('250', plain, ((v9_lattices @ sk_A)),
% 33.10/33.33      inference('demod', [status(thm)], ['247', '248', '249'])).
% 33.10/33.33  thf('251', plain,
% 33.10/33.33      (![X0 : $i]:
% 33.10/33.33         ((v2_struct_0 @ sk_A)
% 33.10/33.33          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | ((k2_lattices @ sk_A @ X0 @ 
% 33.10/33.33              (k1_lattices @ sk_A @ X0 @ (k7_lattices @ sk_A @ sk_B_3))) = (
% 33.10/33.33              X0)))),
% 33.10/33.33      inference('demod', [status(thm)], ['243', '244', '250'])).
% 33.10/33.33  thf('252', plain, (~ (v2_struct_0 @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('253', plain,
% 33.10/33.33      (![X0 : $i]:
% 33.10/33.33         (((k2_lattices @ sk_A @ X0 @ 
% 33.10/33.33            (k1_lattices @ sk_A @ X0 @ (k7_lattices @ sk_A @ sk_B_3))) = (
% 33.10/33.33            X0))
% 33.10/33.33          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 33.10/33.33      inference('clc', [status(thm)], ['251', '252'])).
% 33.10/33.33  thf('254', plain,
% 33.10/33.33      (((k2_lattices @ sk_A @ sk_B_3 @ 
% 33.10/33.33         (k1_lattices @ sk_A @ sk_B_3 @ (k7_lattices @ sk_A @ sk_B_3)))
% 33.10/33.33         = (sk_B_3))),
% 33.10/33.33      inference('sup-', [status(thm)], ['240', '253'])).
% 33.10/33.33  thf('255', plain,
% 33.10/33.33      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B_3) @ (u1_struct_0 @ sk_A))),
% 33.10/33.33      inference('clc', [status(thm)], ['62', '63'])).
% 33.10/33.33  thf('256', plain,
% 33.10/33.33      (![X0 : $i]:
% 33.10/33.33         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | ((k3_lattices @ sk_A @ sk_B_3 @ X0)
% 33.10/33.33              = (k1_lattices @ sk_A @ sk_B_3 @ X0)))),
% 33.10/33.33      inference('clc', [status(thm)], ['13', '14'])).
% 33.10/33.33  thf('257', plain,
% 33.10/33.33      (((k3_lattices @ sk_A @ sk_B_3 @ (k7_lattices @ sk_A @ sk_B_3))
% 33.10/33.33         = (k1_lattices @ sk_A @ sk_B_3 @ (k7_lattices @ sk_A @ sk_B_3)))),
% 33.10/33.33      inference('sup-', [status(thm)], ['255', '256'])).
% 33.10/33.33  thf('258', plain,
% 33.10/33.33      (((k2_lattices @ sk_A @ sk_B_3 @ 
% 33.10/33.33         (k3_lattices @ sk_A @ sk_B_3 @ (k7_lattices @ sk_A @ sk_B_3)))
% 33.10/33.33         = (sk_B_3))),
% 33.10/33.33      inference('demod', [status(thm)], ['254', '257'])).
% 33.10/33.33  thf('259', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('260', plain,
% 33.10/33.33      (![X48 : $i, X49 : $i]:
% 33.10/33.33         (~ (m1_subset_1 @ X48 @ (u1_struct_0 @ X49))
% 33.10/33.33          | ((k3_lattices @ X49 @ (k7_lattices @ X49 @ X48) @ X48)
% 33.10/33.33              = (k6_lattices @ X49))
% 33.10/33.33          | ~ (l3_lattices @ X49)
% 33.10/33.33          | ~ (v17_lattices @ X49)
% 33.10/33.33          | ~ (v10_lattices @ X49)
% 33.10/33.33          | (v2_struct_0 @ X49))),
% 33.10/33.33      inference('cnf', [status(esa)], [t48_lattices])).
% 33.10/33.33  thf('261', plain,
% 33.10/33.33      (((v2_struct_0 @ sk_A)
% 33.10/33.33        | ~ (v10_lattices @ sk_A)
% 33.10/33.33        | ~ (v17_lattices @ sk_A)
% 33.10/33.33        | ~ (l3_lattices @ sk_A)
% 33.10/33.33        | ((k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3) @ sk_B_3)
% 33.10/33.33            = (k6_lattices @ sk_A)))),
% 33.10/33.33      inference('sup-', [status(thm)], ['259', '260'])).
% 33.10/33.33  thf('262', plain, ((v10_lattices @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('263', plain, ((v17_lattices @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('264', plain, ((l3_lattices @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('265', plain,
% 33.10/33.33      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B_3) @ (u1_struct_0 @ sk_A))),
% 33.10/33.33      inference('clc', [status(thm)], ['62', '63'])).
% 33.10/33.33  thf('266', plain,
% 33.10/33.33      (![X0 : $i]:
% 33.10/33.33         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.33          | ((k3_lattices @ sk_A @ sk_B_3 @ X0)
% 33.10/33.33              = (k3_lattices @ sk_A @ X0 @ sk_B_3)))),
% 33.10/33.33      inference('clc', [status(thm)], ['46', '47'])).
% 33.10/33.33  thf('267', plain,
% 33.10/33.33      (((k3_lattices @ sk_A @ sk_B_3 @ (k7_lattices @ sk_A @ sk_B_3))
% 33.10/33.33         = (k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3) @ sk_B_3))),
% 33.10/33.33      inference('sup-', [status(thm)], ['265', '266'])).
% 33.10/33.33  thf('268', plain,
% 33.10/33.33      (((v2_struct_0 @ sk_A)
% 33.10/33.33        | ((k3_lattices @ sk_A @ sk_B_3 @ (k7_lattices @ sk_A @ sk_B_3))
% 33.10/33.33            = (k6_lattices @ sk_A)))),
% 33.10/33.33      inference('demod', [status(thm)], ['261', '262', '263', '264', '267'])).
% 33.10/33.33  thf('269', plain, (~ (v2_struct_0 @ sk_A)),
% 33.10/33.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.33  thf('270', plain,
% 33.10/33.33      (((k3_lattices @ sk_A @ sk_B_3 @ (k7_lattices @ sk_A @ sk_B_3))
% 33.10/33.33         = (k6_lattices @ sk_A))),
% 33.10/33.33      inference('clc', [status(thm)], ['268', '269'])).
% 33.10/33.34  thf('271', plain,
% 33.10/33.34      (((k2_lattices @ sk_A @ sk_B_3 @ (k6_lattices @ sk_A)) = (sk_B_3))),
% 33.10/33.34      inference('demod', [status(thm)], ['258', '270'])).
% 33.10/33.34  thf('272', plain,
% 33.10/33.34      (((sk_B_3)
% 33.10/33.34         = (k4_lattices @ sk_A @ sk_B_3 @ 
% 33.10/33.34            (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3))))),
% 33.10/33.34      inference('demod', [status(thm)], ['239', '271'])).
% 33.10/33.34  thf('273', plain,
% 33.10/33.34      (((sk_B_3)
% 33.10/33.34         = (k2_lattices @ sk_A @ 
% 33.10/33.34            (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ sk_B_3))),
% 33.10/33.34      inference('demod', [status(thm)], ['109', '272'])).
% 33.10/33.34  thf('274', plain,
% 33.10/33.34      (![X0 : $i]:
% 33.10/33.34         (((k2_lattices @ sk_A @ 
% 33.10/33.34            (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ 
% 33.10/33.34            (k1_lattices @ sk_A @ sk_B_3 @ X0))
% 33.10/33.34            = (k1_lattices @ sk_A @ sk_B_3 @ 
% 33.10/33.34               (k2_lattices @ sk_A @ 
% 33.10/33.34                (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ X0)))
% 33.10/33.34          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.34          | (v2_struct_0 @ sk_A))),
% 33.10/33.34      inference('demod', [status(thm)], ['83', '273'])).
% 33.10/33.34  thf('275', plain, (~ (v2_struct_0 @ sk_A)),
% 33.10/33.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.34  thf('276', plain,
% 33.10/33.34      (![X0 : $i]:
% 33.10/33.34         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.34          | ((k2_lattices @ sk_A @ 
% 33.10/33.34              (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ 
% 33.10/33.34              (k1_lattices @ sk_A @ sk_B_3 @ X0))
% 33.10/33.34              = (k1_lattices @ sk_A @ sk_B_3 @ 
% 33.10/33.34                 (k2_lattices @ sk_A @ 
% 33.10/33.34                  (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ X0))))),
% 33.10/33.34      inference('clc', [status(thm)], ['274', '275'])).
% 33.10/33.34  thf('277', plain,
% 33.10/33.34      (((k2_lattices @ sk_A @ 
% 33.10/33.34         (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ 
% 33.10/33.34         (k1_lattices @ sk_A @ sk_B_3 @ (k7_lattices @ sk_A @ sk_B_3)))
% 33.10/33.34         = (k1_lattices @ sk_A @ sk_B_3 @ 
% 33.10/33.34            (k2_lattices @ sk_A @ 
% 33.10/33.34             (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ 
% 33.10/33.34             (k7_lattices @ sk_A @ sk_B_3))))),
% 33.10/33.34      inference('sup-', [status(thm)], ['64', '276'])).
% 33.10/33.34  thf('278', plain,
% 33.10/33.34      (((k3_lattices @ sk_A @ sk_B_3 @ (k7_lattices @ sk_A @ sk_B_3))
% 33.10/33.34         = (k1_lattices @ sk_A @ sk_B_3 @ (k7_lattices @ sk_A @ sk_B_3)))),
% 33.10/33.34      inference('sup-', [status(thm)], ['255', '256'])).
% 33.10/33.34  thf('279', plain,
% 33.10/33.34      (((k3_lattices @ sk_A @ sk_B_3 @ (k7_lattices @ sk_A @ sk_B_3))
% 33.10/33.34         = (k6_lattices @ sk_A))),
% 33.10/33.34      inference('clc', [status(thm)], ['268', '269'])).
% 33.10/33.34  thf('280', plain,
% 33.10/33.34      (((k6_lattices @ sk_A)
% 33.10/33.34         = (k1_lattices @ sk_A @ sk_B_3 @ (k7_lattices @ sk_A @ sk_B_3)))),
% 33.10/33.34      inference('demod', [status(thm)], ['278', '279'])).
% 33.10/33.34  thf('281', plain,
% 33.10/33.34      ((m1_subset_1 @ (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ 
% 33.10/33.34        (u1_struct_0 @ sk_A))),
% 33.10/33.34      inference('clc', [status(thm)], ['69', '70'])).
% 33.10/33.34  thf(dt_k6_lattices, axiom,
% 33.10/33.34    (![A:$i]:
% 33.10/33.34     ( ( ( ~( v2_struct_0 @ A ) ) & ( l2_lattices @ A ) ) =>
% 33.10/33.34       ( m1_subset_1 @ ( k6_lattices @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 33.10/33.34  thf('282', plain,
% 33.10/33.34      (![X28 : $i]:
% 33.10/33.34         ((m1_subset_1 @ (k6_lattices @ X28) @ (u1_struct_0 @ X28))
% 33.10/33.34          | ~ (l2_lattices @ X28)
% 33.10/33.34          | (v2_struct_0 @ X28))),
% 33.10/33.34      inference('cnf', [status(esa)], [dt_k6_lattices])).
% 33.10/33.34  thf('283', plain,
% 33.10/33.34      (![X24 : $i, X25 : $i, X26 : $i]:
% 33.10/33.34         (~ (v9_lattices @ X24)
% 33.10/33.34          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X24))
% 33.10/33.34          | ((k2_lattices @ X24 @ X26 @ (k1_lattices @ X24 @ X26 @ X25))
% 33.10/33.34              = (X26))
% 33.10/33.34          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X24))
% 33.10/33.34          | ~ (l3_lattices @ X24)
% 33.10/33.34          | (v2_struct_0 @ X24))),
% 33.10/33.34      inference('cnf', [status(esa)], [d9_lattices])).
% 33.10/33.34  thf('284', plain,
% 33.10/33.34      (![X0 : $i, X1 : $i]:
% 33.10/33.34         ((v2_struct_0 @ X0)
% 33.10/33.34          | ~ (l2_lattices @ X0)
% 33.10/33.34          | (v2_struct_0 @ X0)
% 33.10/33.34          | ~ (l3_lattices @ X0)
% 33.10/33.34          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 33.10/33.34          | ((k2_lattices @ X0 @ X1 @ 
% 33.10/33.34              (k1_lattices @ X0 @ X1 @ (k6_lattices @ X0))) = (X1))
% 33.10/33.34          | ~ (v9_lattices @ X0))),
% 33.10/33.34      inference('sup-', [status(thm)], ['282', '283'])).
% 33.10/33.34  thf('285', plain,
% 33.10/33.34      (![X0 : $i, X1 : $i]:
% 33.10/33.34         (~ (v9_lattices @ X0)
% 33.10/33.34          | ((k2_lattices @ X0 @ X1 @ 
% 33.10/33.34              (k1_lattices @ X0 @ X1 @ (k6_lattices @ X0))) = (X1))
% 33.10/33.34          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 33.10/33.34          | ~ (l3_lattices @ X0)
% 33.10/33.34          | ~ (l2_lattices @ X0)
% 33.10/33.34          | (v2_struct_0 @ X0))),
% 33.10/33.34      inference('simplify', [status(thm)], ['284'])).
% 33.10/33.34  thf('286', plain,
% 33.10/33.34      (((v2_struct_0 @ sk_A)
% 33.10/33.34        | ~ (l2_lattices @ sk_A)
% 33.10/33.34        | ~ (l3_lattices @ sk_A)
% 33.10/33.34        | ((k2_lattices @ sk_A @ 
% 33.10/33.34            (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ 
% 33.10/33.34            (k1_lattices @ sk_A @ 
% 33.10/33.34             (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ 
% 33.10/33.34             (k6_lattices @ sk_A)))
% 33.10/33.34            = (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)))
% 33.10/33.34        | ~ (v9_lattices @ sk_A))),
% 33.10/33.34      inference('sup-', [status(thm)], ['281', '285'])).
% 33.10/33.34  thf('287', plain, ((l2_lattices @ sk_A)),
% 33.10/33.34      inference('sup-', [status(thm)], ['10', '11'])).
% 33.10/33.34  thf('288', plain, ((l3_lattices @ sk_A)),
% 33.10/33.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.34  thf('289', plain,
% 33.10/33.34      ((m1_subset_1 @ (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ 
% 33.10/33.34        (u1_struct_0 @ sk_A))),
% 33.10/33.34      inference('clc', [status(thm)], ['69', '70'])).
% 33.10/33.34  thf('290', plain,
% 33.10/33.34      (![X28 : $i]:
% 33.10/33.34         ((m1_subset_1 @ (k6_lattices @ X28) @ (u1_struct_0 @ X28))
% 33.10/33.34          | ~ (l2_lattices @ X28)
% 33.10/33.34          | (v2_struct_0 @ X28))),
% 33.10/33.34      inference('cnf', [status(esa)], [dt_k6_lattices])).
% 33.10/33.34  thf(d17_lattices, axiom,
% 33.10/33.34    (![A:$i]:
% 33.10/33.34     ( ( ( ~( v2_struct_0 @ A ) ) & ( l2_lattices @ A ) ) =>
% 33.10/33.34       ( ( v14_lattices @ A ) =>
% 33.10/33.34         ( ![B:$i]:
% 33.10/33.34           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 33.10/33.34             ( ( ( B ) = ( k6_lattices @ A ) ) <=>
% 33.10/33.34               ( ![C:$i]:
% 33.10/33.34                 ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 33.10/33.34                   ( ( ( k1_lattices @ A @ B @ C ) = ( B ) ) & 
% 33.10/33.34                     ( ( k1_lattices @ A @ C @ B ) = ( B ) ) ) ) ) ) ) ) ) ))).
% 33.10/33.34  thf('291', plain,
% 33.10/33.34      (![X18 : $i, X19 : $i, X20 : $i]:
% 33.10/33.34         (~ (v14_lattices @ X18)
% 33.10/33.34          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 33.10/33.34          | ((X19) != (k6_lattices @ X18))
% 33.10/33.34          | ((k1_lattices @ X18 @ X20 @ X19) = (X19))
% 33.10/33.34          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 33.10/33.34          | ~ (l2_lattices @ X18)
% 33.10/33.34          | (v2_struct_0 @ X18))),
% 33.10/33.34      inference('cnf', [status(esa)], [d17_lattices])).
% 33.10/33.34  thf('292', plain,
% 33.10/33.34      (![X18 : $i, X20 : $i]:
% 33.10/33.34         ((v2_struct_0 @ X18)
% 33.10/33.34          | ~ (l2_lattices @ X18)
% 33.10/33.34          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 33.10/33.34          | ((k1_lattices @ X18 @ X20 @ (k6_lattices @ X18))
% 33.10/33.34              = (k6_lattices @ X18))
% 33.10/33.34          | ~ (m1_subset_1 @ (k6_lattices @ X18) @ (u1_struct_0 @ X18))
% 33.10/33.34          | ~ (v14_lattices @ X18))),
% 33.10/33.34      inference('simplify', [status(thm)], ['291'])).
% 33.10/33.34  thf('293', plain,
% 33.10/33.34      (![X0 : $i, X1 : $i]:
% 33.10/33.34         ((v2_struct_0 @ X0)
% 33.10/33.34          | ~ (l2_lattices @ X0)
% 33.10/33.34          | ~ (v14_lattices @ X0)
% 33.10/33.34          | ((k1_lattices @ X0 @ X1 @ (k6_lattices @ X0)) = (k6_lattices @ X0))
% 33.10/33.34          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 33.10/33.34          | ~ (l2_lattices @ X0)
% 33.10/33.34          | (v2_struct_0 @ X0))),
% 33.10/33.34      inference('sup-', [status(thm)], ['290', '292'])).
% 33.10/33.34  thf('294', plain,
% 33.10/33.34      (![X0 : $i, X1 : $i]:
% 33.10/33.34         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 33.10/33.34          | ((k1_lattices @ X0 @ X1 @ (k6_lattices @ X0)) = (k6_lattices @ X0))
% 33.10/33.34          | ~ (v14_lattices @ X0)
% 33.10/33.34          | ~ (l2_lattices @ X0)
% 33.10/33.34          | (v2_struct_0 @ X0))),
% 33.10/33.34      inference('simplify', [status(thm)], ['293'])).
% 33.10/33.34  thf('295', plain,
% 33.10/33.34      (((v2_struct_0 @ sk_A)
% 33.10/33.34        | ~ (l2_lattices @ sk_A)
% 33.10/33.34        | ~ (v14_lattices @ sk_A)
% 33.10/33.34        | ((k1_lattices @ sk_A @ 
% 33.10/33.34            (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ 
% 33.10/33.34            (k6_lattices @ sk_A)) = (k6_lattices @ sk_A)))),
% 33.10/33.34      inference('sup-', [status(thm)], ['289', '294'])).
% 33.10/33.34  thf('296', plain, ((l2_lattices @ sk_A)),
% 33.10/33.34      inference('sup-', [status(thm)], ['10', '11'])).
% 33.10/33.34  thf('297', plain,
% 33.10/33.34      (![X3 : $i]:
% 33.10/33.34         ((v2_struct_0 @ X3)
% 33.10/33.34          | ~ (v15_lattices @ X3)
% 33.10/33.34          | (v14_lattices @ X3)
% 33.10/33.34          | ~ (l3_lattices @ X3))),
% 33.10/33.34      inference('cnf', [status(esa)], [cc4_lattices])).
% 33.10/33.34  thf('298', plain, (~ (v2_struct_0 @ sk_A)),
% 33.10/33.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.34  thf('299', plain,
% 33.10/33.34      ((~ (l3_lattices @ sk_A)
% 33.10/33.34        | (v14_lattices @ sk_A)
% 33.10/33.34        | ~ (v15_lattices @ sk_A))),
% 33.10/33.34      inference('sup-', [status(thm)], ['297', '298'])).
% 33.10/33.34  thf('300', plain, ((l3_lattices @ sk_A)),
% 33.10/33.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.34  thf('301', plain, (((v14_lattices @ sk_A) | ~ (v15_lattices @ sk_A))),
% 33.10/33.34      inference('demod', [status(thm)], ['299', '300'])).
% 33.10/33.34  thf('302', plain, ((v15_lattices @ sk_A)),
% 33.10/33.34      inference('demod', [status(thm)], ['34', '35', '36'])).
% 33.10/33.34  thf('303', plain, ((v14_lattices @ sk_A)),
% 33.10/33.34      inference('demod', [status(thm)], ['301', '302'])).
% 33.10/33.34  thf('304', plain,
% 33.10/33.34      (((v2_struct_0 @ sk_A)
% 33.10/33.34        | ((k1_lattices @ sk_A @ 
% 33.10/33.34            (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ 
% 33.10/33.34            (k6_lattices @ sk_A)) = (k6_lattices @ sk_A)))),
% 33.10/33.34      inference('demod', [status(thm)], ['295', '296', '303'])).
% 33.10/33.34  thf('305', plain, (~ (v2_struct_0 @ sk_A)),
% 33.10/33.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.34  thf('306', plain,
% 33.10/33.34      (((k1_lattices @ sk_A @ 
% 33.10/33.34         (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ 
% 33.10/33.34         (k6_lattices @ sk_A)) = (k6_lattices @ sk_A))),
% 33.10/33.34      inference('clc', [status(thm)], ['304', '305'])).
% 33.10/33.34  thf('307', plain, ((v9_lattices @ sk_A)),
% 33.10/33.34      inference('demod', [status(thm)], ['247', '248', '249'])).
% 33.10/33.34  thf('308', plain,
% 33.10/33.34      (((v2_struct_0 @ sk_A)
% 33.10/33.34        | ((k2_lattices @ sk_A @ 
% 33.10/33.34            (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ 
% 33.10/33.34            (k6_lattices @ sk_A))
% 33.10/33.34            = (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3))))),
% 33.10/33.34      inference('demod', [status(thm)], ['286', '287', '288', '306', '307'])).
% 33.10/33.34  thf('309', plain, (~ (v2_struct_0 @ sk_A)),
% 33.10/33.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.34  thf('310', plain,
% 33.10/33.34      (((k2_lattices @ sk_A @ 
% 33.10/33.34         (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ 
% 33.10/33.34         (k6_lattices @ sk_A))
% 33.10/33.34         = (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)))),
% 33.10/33.34      inference('clc', [status(thm)], ['308', '309'])).
% 33.10/33.34  thf('311', plain,
% 33.10/33.34      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B_3) @ (u1_struct_0 @ sk_A))),
% 33.10/33.34      inference('clc', [status(thm)], ['62', '63'])).
% 33.10/33.34  thf('312', plain,
% 33.10/33.34      (![X0 : $i]:
% 33.10/33.34         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.34          | ((k4_lattices @ sk_A @ 
% 33.10/33.34              (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ X0)
% 33.10/33.34              = (k2_lattices @ sk_A @ 
% 33.10/33.34                 (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ X0)))),
% 33.10/33.34      inference('clc', [status(thm)], ['95', '96'])).
% 33.10/33.34  thf('313', plain,
% 33.10/33.34      (((k4_lattices @ sk_A @ 
% 33.10/33.34         (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ 
% 33.10/33.34         (k7_lattices @ sk_A @ sk_B_3))
% 33.10/33.34         = (k2_lattices @ sk_A @ 
% 33.10/33.34            (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ 
% 33.10/33.34            (k7_lattices @ sk_A @ sk_B_3)))),
% 33.10/33.34      inference('sup-', [status(thm)], ['311', '312'])).
% 33.10/33.34  thf('314', plain,
% 33.10/33.34      ((m1_subset_1 @ (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ 
% 33.10/33.34        (u1_struct_0 @ sk_A))),
% 33.10/33.34      inference('clc', [status(thm)], ['69', '70'])).
% 33.10/33.34  thf('315', plain,
% 33.10/33.34      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B_3) @ (u1_struct_0 @ sk_A))),
% 33.10/33.34      inference('clc', [status(thm)], ['62', '63'])).
% 33.10/33.34  thf('316', plain,
% 33.10/33.34      (![X8 : $i, X9 : $i, X10 : $i]:
% 33.10/33.34         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 33.10/33.34          | ~ (l1_lattices @ X9)
% 33.10/33.34          | ~ (v6_lattices @ X9)
% 33.10/33.34          | (v2_struct_0 @ X9)
% 33.10/33.34          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 33.10/33.34          | ((k4_lattices @ X9 @ X8 @ X10) = (k4_lattices @ X9 @ X10 @ X8)))),
% 33.10/33.34      inference('cnf', [status(esa)], [commutativity_k4_lattices])).
% 33.10/33.34  thf('317', plain,
% 33.10/33.34      (![X0 : $i]:
% 33.10/33.34         (((k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3) @ X0)
% 33.10/33.34            = (k4_lattices @ sk_A @ X0 @ (k7_lattices @ sk_A @ sk_B_3)))
% 33.10/33.34          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.34          | (v2_struct_0 @ sk_A)
% 33.10/33.34          | ~ (v6_lattices @ sk_A)
% 33.10/33.34          | ~ (l1_lattices @ sk_A))),
% 33.10/33.34      inference('sup-', [status(thm)], ['315', '316'])).
% 33.10/33.34  thf('318', plain, ((v6_lattices @ sk_A)),
% 33.10/33.34      inference('demod', [status(thm)], ['90', '91', '92'])).
% 33.10/33.34  thf('319', plain, ((l1_lattices @ sk_A)),
% 33.10/33.34      inference('sup-', [status(thm)], ['17', '18'])).
% 33.10/33.34  thf('320', plain,
% 33.10/33.34      (![X0 : $i]:
% 33.10/33.34         (((k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3) @ X0)
% 33.10/33.34            = (k4_lattices @ sk_A @ X0 @ (k7_lattices @ sk_A @ sk_B_3)))
% 33.10/33.34          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.34          | (v2_struct_0 @ sk_A))),
% 33.10/33.34      inference('demod', [status(thm)], ['317', '318', '319'])).
% 33.10/33.34  thf('321', plain, (~ (v2_struct_0 @ sk_A)),
% 33.10/33.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.34  thf('322', plain,
% 33.10/33.34      (![X0 : $i]:
% 33.10/33.34         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 33.10/33.34          | ((k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3) @ X0)
% 33.10/33.34              = (k4_lattices @ sk_A @ X0 @ (k7_lattices @ sk_A @ sk_B_3))))),
% 33.10/33.34      inference('clc', [status(thm)], ['320', '321'])).
% 33.10/33.34  thf('323', plain,
% 33.10/33.34      (((k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3) @ 
% 33.10/33.34         (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)))
% 33.10/33.34         = (k4_lattices @ sk_A @ 
% 33.10/33.34            (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ 
% 33.10/33.34            (k7_lattices @ sk_A @ sk_B_3)))),
% 33.10/33.34      inference('sup-', [status(thm)], ['314', '322'])).
% 33.10/33.34  thf('324', plain,
% 33.10/33.34      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B_3) @ (u1_struct_0 @ sk_A))),
% 33.10/33.34      inference('clc', [status(thm)], ['62', '63'])).
% 33.10/33.34  thf('325', plain,
% 33.10/33.34      (![X46 : $i, X47 : $i]:
% 33.10/33.34         (~ (m1_subset_1 @ X46 @ (u1_struct_0 @ X47))
% 33.10/33.34          | ((k4_lattices @ X47 @ (k7_lattices @ X47 @ X46) @ X46)
% 33.10/33.34              = (k5_lattices @ X47))
% 33.10/33.34          | ~ (l3_lattices @ X47)
% 33.10/33.34          | ~ (v17_lattices @ X47)
% 33.10/33.34          | ~ (v10_lattices @ X47)
% 33.10/33.34          | (v2_struct_0 @ X47))),
% 33.10/33.34      inference('cnf', [status(esa)], [t47_lattices])).
% 33.10/33.34  thf('326', plain,
% 33.10/33.34      (((v2_struct_0 @ sk_A)
% 33.10/33.34        | ~ (v10_lattices @ sk_A)
% 33.10/33.34        | ~ (v17_lattices @ sk_A)
% 33.10/33.34        | ~ (l3_lattices @ sk_A)
% 33.10/33.34        | ((k4_lattices @ sk_A @ 
% 33.10/33.34            (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ 
% 33.10/33.34            (k7_lattices @ sk_A @ sk_B_3)) = (k5_lattices @ sk_A)))),
% 33.10/33.34      inference('sup-', [status(thm)], ['324', '325'])).
% 33.10/33.34  thf('327', plain, ((v10_lattices @ sk_A)),
% 33.10/33.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.34  thf('328', plain, ((v17_lattices @ sk_A)),
% 33.10/33.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.34  thf('329', plain, ((l3_lattices @ sk_A)),
% 33.10/33.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.34  thf('330', plain,
% 33.10/33.34      (((k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3) @ 
% 33.10/33.34         (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)))
% 33.10/33.34         = (k4_lattices @ sk_A @ 
% 33.10/33.34            (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ 
% 33.10/33.34            (k7_lattices @ sk_A @ sk_B_3)))),
% 33.10/33.34      inference('sup-', [status(thm)], ['314', '322'])).
% 33.10/33.34  thf('331', plain,
% 33.10/33.34      (((v2_struct_0 @ sk_A)
% 33.10/33.34        | ((k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3) @ 
% 33.10/33.34            (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)))
% 33.10/33.34            = (k5_lattices @ sk_A)))),
% 33.10/33.34      inference('demod', [status(thm)], ['326', '327', '328', '329', '330'])).
% 33.10/33.34  thf('332', plain, (~ (v2_struct_0 @ sk_A)),
% 33.10/33.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.34  thf('333', plain,
% 33.10/33.34      (((k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3) @ 
% 33.10/33.34         (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)))
% 33.10/33.34         = (k5_lattices @ sk_A))),
% 33.10/33.34      inference('clc', [status(thm)], ['331', '332'])).
% 33.10/33.34  thf('334', plain,
% 33.10/33.34      (((k5_lattices @ sk_A)
% 33.10/33.34         = (k4_lattices @ sk_A @ 
% 33.10/33.34            (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ 
% 33.10/33.34            (k7_lattices @ sk_A @ sk_B_3)))),
% 33.10/33.34      inference('demod', [status(thm)], ['323', '333'])).
% 33.10/33.34  thf('335', plain,
% 33.10/33.34      (((k5_lattices @ sk_A)
% 33.10/33.34         = (k2_lattices @ sk_A @ 
% 33.10/33.34            (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) @ 
% 33.10/33.34            (k7_lattices @ sk_A @ sk_B_3)))),
% 33.10/33.34      inference('demod', [status(thm)], ['313', '334'])).
% 33.10/33.34  thf('336', plain,
% 33.10/33.34      (((k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3))
% 33.10/33.34         = (k1_lattices @ sk_A @ sk_B_3 @ (k5_lattices @ sk_A)))),
% 33.10/33.34      inference('demod', [status(thm)], ['277', '280', '310', '335'])).
% 33.10/33.34  thf('337', plain,
% 33.10/33.34      (((k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) = (sk_B_3))),
% 33.10/33.34      inference('sup+', [status(thm)], ['57', '336'])).
% 33.10/33.34  thf('338', plain,
% 33.10/33.34      (((k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_3)) != (sk_B_3))),
% 33.10/33.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.10/33.34  thf('339', plain, ($false),
% 33.10/33.34      inference('simplify_reflect-', [status(thm)], ['337', '338'])).
% 33.10/33.34  
% 33.10/33.34  % SZS output end Refutation
% 33.10/33.34  
% 33.10/33.34  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
