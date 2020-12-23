%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1217+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CBA3J8QYMY

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:16 EST 2020

% Result     : Theorem 43.40s
% Output     : Refutation 43.40s
% Verified   : 
% Statistics : Number of formulae       :  253 ( 910 expanded)
%              Number of leaves         :   43 ( 279 expanded)
%              Depth                    :   21
%              Number of atoms          : 2167 (14634 expanded)
%              Number of equality atoms :   52 (  81 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(v16_lattices_type,type,(
    v16_lattices: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(k5_lattices_type,type,(
    k5_lattices: $i > $i )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k7_lattices_type,type,(
    k7_lattices: $i > $i > $i )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v11_lattices_type,type,(
    v11_lattices: $i > $o )).

thf(k4_lattices_type,type,(
    k4_lattices: $i > $i > $i > $i )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(v14_lattices_type,type,(
    v14_lattices: $i > $o )).

thf(v13_lattices_type,type,(
    v13_lattices: $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(v17_lattices_type,type,(
    v17_lattices: $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(v15_lattices_type,type,(
    v15_lattices: $i > $o )).

thf(t53_lattices,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v17_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r3_lattices @ A @ B @ C )
               => ( r3_lattices @ A @ ( k7_lattices @ A @ C ) @ ( k7_lattices @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v17_lattices @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( r3_lattices @ A @ B @ C )
                 => ( r3_lattices @ A @ ( k7_lattices @ A @ C ) @ ( k7_lattices @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t53_lattices])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_lattices,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k7_lattices @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l3_lattices @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( m1_subset_1 @ ( k7_lattices @ X12 @ X13 ) @ ( u1_struct_0 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattices])).

thf('2',plain,
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k2_lattices @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_lattices @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( m1_subset_1 @ ( k2_lattices @ X7 @ X6 @ X8 ) @ ( u1_struct_0 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_lattices])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_lattices @ sk_A @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('11',plain,(
    ! [X14: $i] :
      ( ( l1_lattices @ X14 )
      | ~ ( l3_lattices @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('12',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_lattices @ sk_A @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( k2_lattices @ sk_A @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ ( k2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','15'])).

thf(t41_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v13_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r3_lattices @ A @ ( k5_lattices @ A ) @ B ) ) ) )).

thf('17',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ( r3_lattices @ X29 @ ( k5_lattices @ X29 ) @ X28 )
      | ~ ( l3_lattices @ X29 )
      | ~ ( v13_lattices @ X29 )
      | ~ ( v10_lattices @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t41_lattices])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v13_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( r3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
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

thf('20',plain,(
    ! [X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v15_lattices @ X1 )
      | ( v13_lattices @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc4_lattices])).

thf('21',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v13_lattices @ sk_A )
    | ~ ( v15_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v13_lattices @ sk_A )
    | ~ ( v15_lattices @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(cc5_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v17_lattices @ A ) )
       => ( ~ ( v2_struct_0 @ A )
          & ( v11_lattices @ A )
          & ( v15_lattices @ A )
          & ( v16_lattices @ A ) ) ) ) )).

thf('25',plain,(
    ! [X2: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v17_lattices @ X2 )
      | ( v15_lattices @ X2 )
      | ~ ( l3_lattices @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc5_lattices])).

thf('26',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v15_lattices @ sk_A )
    | ~ ( v17_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v17_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v15_lattices @ sk_A ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    v13_lattices @ sk_A ),
    inference(demod,[status(thm)],['24','30'])).

thf('32',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['18','19','31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l3_lattices @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( m1_subset_1 @ ( k7_lattices @ X12 @ X13 ) @ ( u1_struct_0 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattices])).

thf('38',plain,
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( k2_lattices @ sk_A @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('44',plain,(
    m1_subset_1 @ ( k2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
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

thf('46',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X31 ) )
      | ( ( k4_lattices @ X31 @ ( k7_lattices @ X31 @ X30 ) @ X30 )
        = ( k5_lattices @ X31 ) )
      | ~ ( l3_lattices @ X31 )
      | ~ ( v17_lattices @ X31 )
      | ~ ( v10_lattices @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t47_lattices])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v17_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ sk_B )
      = ( k5_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v17_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
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

thf('53',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_lattices @ X4 )
      | ~ ( v6_lattices @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( ( k4_lattices @ X4 @ X3 @ X5 )
        = ( k4_lattices @ X4 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k4_lattices])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

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
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['10','11'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k4_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_B ) )
    = ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['51','64'])).

thf('66',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('67',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v6_lattices @ A )
        & ( l1_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k4_lattices @ A @ B @ C )
        = ( k2_lattices @ A @ B @ C ) ) ) )).

thf('68',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_lattices @ X16 )
      | ~ ( v6_lattices @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ( ( k4_lattices @ X16 @ X15 @ X17 )
        = ( k2_lattices @ X16 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_lattices])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B @ X0 )
        = ( k2_lattices @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('71',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['10','11'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B @ X0 )
        = ( k2_lattices @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B @ X0 )
        = ( k2_lattices @ sk_A @ sk_B @ X0 ) ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k4_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_B ) )
    = ( k2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','74'])).

thf('76',plain,
    ( ( k2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_B ) )
    = ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['65','75'])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_B ) )
      = ( k5_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48','49','50','76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( k2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_B ) )
    = ( k5_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    m1_subset_1 @ ( k5_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','79'])).

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

thf('81',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l3_lattices @ X19 )
      | ~ ( v9_lattices @ X19 )
      | ~ ( v8_lattices @ X19 )
      | ~ ( v6_lattices @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ( r1_lattices @ X19 @ X18 @ X20 )
      | ~ ( r3_lattices @ X19 @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ X0 )
      | ( r1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ X0 )
      | ( r1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','83','89','95','96'])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['35','97'])).

thf('99',plain,(
    m1_subset_1 @ ( k2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','15'])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    r1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,(
    m1_subset_1 @ ( k2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','15'])).

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

thf('104',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( r1_lattices @ X22 @ X21 @ X23 )
      | ~ ( r1_lattices @ X22 @ X23 @ X21 )
      | ( X21 = X23 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l2_lattices @ X22 )
      | ~ ( v4_lattices @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t26_lattices])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_C ) )
        = X0 )
      | ~ ( r1_lattices @ sk_A @ X0 @ ( k2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_C ) ) )
      | ~ ( r1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_C ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v4_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v4_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X14: $i] :
      ( ( l2_lattices @ X14 )
      | ~ ( l3_lattices @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('114',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_C ) )
        = X0 )
      | ~ ( r1_lattices @ sk_A @ X0 @ ( k2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_C ) ) )
      | ~ ( r1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_C ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['105','111','114'])).

thf('116',plain,
    ( ~ ( r1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_C ) ) @ ( k5_lattices @ sk_A ) )
    | ( ( k2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_C ) )
      = ( k5_lattices @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k5_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['102','115'])).

thf('117',plain,(
    m1_subset_1 @ ( k5_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','79'])).

thf('118',plain,
    ( ~ ( r1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_C ) ) @ ( k5_lattices @ sk_A ) )
    | ( ( k2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_C ) )
      = ( k5_lattices @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('121',plain,
    ( ( k4_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_C ) )
    = ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B @ X0 )
        = ( k2_lattices @ sk_A @ sk_B @ X0 ) ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('124',plain,
    ( ( k4_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_C ) )
    = ( k2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ( k2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_C ) )
    = ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['121','124'])).

thf('126',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['4','5'])).

thf(t52_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v17_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( k4_lattices @ A @ B @ C )
                  = ( k5_lattices @ A ) )
              <=> ( r3_lattices @ A @ B @ ( k7_lattices @ A @ C ) ) ) ) ) ) )).

thf('127',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X33 ) )
      | ( ( k4_lattices @ X33 @ X32 @ X34 )
       != ( k5_lattices @ X33 ) )
      | ( r3_lattices @ X33 @ X32 @ ( k7_lattices @ X33 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X33 ) )
      | ~ ( l3_lattices @ X33 )
      | ~ ( v17_lattices @ X33 )
      | ~ ( v10_lattices @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t52_lattices])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v17_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ ( k7_lattices @ sk_A @ X0 ) )
      | ( ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ X0 )
       != ( k5_lattices @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v17_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ ( k7_lattices @ sk_A @ X0 ) )
      | ( ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ X0 )
       != ( k5_lattices @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['128','129','130','131'])).

thf('133',plain,
    ( ( ( k2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_C ) )
     != ( k5_lattices @ sk_A ) )
    | ( r3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ ( k7_lattices @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['125','132'])).

thf('134',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( ( k2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_C ) )
     != ( k5_lattices @ sk_A ) )
    | ( r3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ ( k7_lattices @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    ~ ( r3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ ( k7_lattices @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_C ) )
     != ( k5_lattices @ sk_A ) ) ),
    inference(clc,[status(thm)],['135','136'])).

thf('138',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    ( k2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_C ) )
 != ( k5_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,
    ( ~ ( r1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_C ) ) @ ( k5_lattices @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['118','139'])).

thf('141',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    ~ ( r1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_C ) ) @ ( k5_lattices @ sk_A ) ) ),
    inference(clc,[status(thm)],['140','141'])).

thf('143',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('144',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t27_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v7_lattices @ A )
        & ( v8_lattices @ A )
        & ( v9_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( r1_lattices @ A @ B @ C )
                   => ( r1_lattices @ A @ ( k2_lattices @ A @ B @ D ) @ ( k2_lattices @ A @ C @ D ) ) ) ) ) ) ) )).

thf('146',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X25 ) )
      | ( r1_lattices @ X25 @ ( k2_lattices @ X25 @ X24 @ X26 ) @ ( k2_lattices @ X25 @ X27 @ X26 ) )
      | ~ ( r1_lattices @ X25 @ X24 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l3_lattices @ X25 )
      | ~ ( v9_lattices @ X25 )
      | ~ ( v8_lattices @ X25 )
      | ~ ( v7_lattices @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t27_lattices])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v7_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_lattices @ sk_A @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B @ X1 ) @ ( k2_lattices @ sk_A @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v7_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('149',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v7_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v7_lattices @ sk_A ),
    inference(demod,[status(thm)],['150','151','152'])).

thf('154',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('155',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('156',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_lattices @ sk_A @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B @ X1 ) @ ( k2_lattices @ sk_A @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['147','153','154','155','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B @ X0 ) @ ( k2_lattices @ sk_A @ sk_C @ X0 ) )
      | ~ ( r1_lattices @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['144','157'])).

thf('159',plain,(
    r3_lattices @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l3_lattices @ X19 )
      | ~ ( v9_lattices @ X19 )
      | ~ ( v8_lattices @ X19 )
      | ~ ( v6_lattices @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ( r1_lattices @ X19 @ X18 @ X20 )
      | ~ ( r3_lattices @ X19 @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('162',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattices @ sk_A @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('164',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('165',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('166',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattices @ sk_A @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['162','163','164','165','166'])).

thf('168',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( r1_lattices @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['159','167'])).

thf('169',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('171',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    r1_lattices @ sk_A @ sk_B @ sk_C ),
    inference(clc,[status(thm)],['170','171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B @ X0 ) @ ( k2_lattices @ sk_A @ sk_C @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['158','172'])).

thf('174',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( r1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B @ X0 ) @ ( k2_lattices @ sk_A @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['173','174'])).

thf('176',plain,(
    r1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_C ) ) @ ( k2_lattices @ sk_A @ sk_C @ ( k7_lattices @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['143','175'])).

thf('177',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X31 ) )
      | ( ( k4_lattices @ X31 @ ( k7_lattices @ X31 @ X30 ) @ X30 )
        = ( k5_lattices @ X31 ) )
      | ~ ( l3_lattices @ X31 )
      | ~ ( v17_lattices @ X31 )
      | ~ ( v10_lattices @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t47_lattices])).

thf('179',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v17_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ sk_C )
      = ( k5_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    v17_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('184',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_lattices @ X4 )
      | ~ ( v6_lattices @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( ( k4_lattices @ X4 @ X3 @ X5 )
        = ( k4_lattices @ X4 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k4_lattices])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_C @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('188',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['10','11'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_C @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['186','187','188'])).

thf('190',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_C @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['189','190'])).

thf('192',plain,
    ( ( k4_lattices @ sk_A @ sk_C @ ( k7_lattices @ sk_A @ sk_C ) )
    = ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['183','191'])).

thf('193',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('194',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_lattices @ X16 )
      | ~ ( v6_lattices @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ( ( k4_lattices @ X16 @ X15 @ X17 )
        = ( k2_lattices @ X16 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_lattices])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_C @ X0 )
        = ( k2_lattices @ sk_A @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('198',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['10','11'])).

thf('199',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_C @ X0 )
        = ( k2_lattices @ sk_A @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['196','197','198'])).

thf('200',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_C @ X0 )
        = ( k2_lattices @ sk_A @ sk_C @ X0 ) ) ) ),
    inference(clc,[status(thm)],['199','200'])).

thf('202',plain,
    ( ( k4_lattices @ sk_A @ sk_C @ ( k7_lattices @ sk_A @ sk_C ) )
    = ( k2_lattices @ sk_A @ sk_C @ ( k7_lattices @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['193','201'])).

thf('203',plain,
    ( ( k2_lattices @ sk_A @ sk_C @ ( k7_lattices @ sk_A @ sk_C ) )
    = ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['192','202'])).

thf('204',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_lattices @ sk_A @ sk_C @ ( k7_lattices @ sk_A @ sk_C ) )
      = ( k5_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['179','180','181','182','203'])).

thf('205',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,
    ( ( k2_lattices @ sk_A @ sk_C @ ( k7_lattices @ sk_A @ sk_C ) )
    = ( k5_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['204','205'])).

thf('207',plain,(
    r1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_C ) ) @ ( k5_lattices @ sk_A ) ),
    inference(demod,[status(thm)],['176','206'])).

thf('208',plain,(
    $false ),
    inference(demod,[status(thm)],['142','207'])).


%------------------------------------------------------------------------------
