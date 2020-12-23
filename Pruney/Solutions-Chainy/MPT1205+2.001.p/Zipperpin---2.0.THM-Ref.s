%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eslc9skJFc

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:33 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 216 expanded)
%              Number of leaves         :   31 (  79 expanded)
%              Depth                    :   15
%              Number of atoms          :  903 (2389 expanded)
%              Number of equality atoms :   35 ( 103 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(k1_lattices_type,type,(
    k1_lattices: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(k5_lattices_type,type,(
    k5_lattices: $i > $i )).

thf(k4_lattices_type,type,(
    k4_lattices: $i > $i > $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_lattices_type,type,(
    k3_lattices: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(v13_lattices_type,type,(
    v13_lattices: $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(t39_lattices,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v13_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k3_lattices @ A @ ( k5_lattices @ A ) @ B )
            = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v13_lattices @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( k3_lattices @ A @ ( k5_lattices @ A ) @ B )
              = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_lattices])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_lattices @ A ) )
     => ( m1_subset_1 @ ( k5_lattices @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t23_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v6_lattices @ A )
        & ( v8_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( r1_lattices @ A @ ( k4_lattices @ A @ B @ C ) @ B ) ) ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ( r1_lattices @ X16 @ ( k4_lattices @ X16 @ X15 @ X17 ) @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l3_lattices @ X16 )
      | ~ ( v8_lattices @ X16 )
      | ~ ( v6_lattices @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t23_lattices])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_B @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

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

thf('5',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('6',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_B @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','10','16','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_B @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_B @ ( k5_lattices @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['1','20'])).

thf('22',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('23',plain,(
    ! [X8: $i] :
      ( ( l1_lattices @ X8 )
      | ~ ( l3_lattices @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('24',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('26',plain,(
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

thf('27',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_lattices @ X13 )
      | ~ ( v6_lattices @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ( ( k4_lattices @ X13 @ X12 @ X14 )
        = ( k2_lattices @ X13 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_lattices])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B @ X0 )
        = ( k2_lattices @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('30',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B @ X0 )
        = ( k2_lattices @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B @ X0 )
        = ( k2_lattices @ sk_A @ sk_B @ X0 ) ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ( ( k4_lattices @ sk_A @ sk_B @ ( k5_lattices @ sk_A ) )
      = ( k2_lattices @ sk_A @ sk_B @ ( k5_lattices @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','33'])).

thf('35',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
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

thf('38',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v13_lattices @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( X2
       != ( k5_lattices @ X1 ) )
      | ( ( k2_lattices @ X1 @ X3 @ X2 )
        = X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d16_lattices])).

thf('39',plain,(
    ! [X1: $i,X3: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_lattices @ X1 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ( ( k2_lattices @ X1 @ X3 @ ( k5_lattices @ X1 ) )
        = ( k5_lattices @ X1 ) )
      | ~ ( m1_subset_1 @ ( k5_lattices @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v13_lattices @ X1 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ X1 @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ X1 @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) )
      | ~ ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ~ ( v13_lattices @ sk_A )
    | ( ( k2_lattices @ sk_A @ sk_B @ ( k5_lattices @ sk_A ) )
      = ( k5_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('44',plain,(
    v13_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_lattices @ sk_A @ sk_B @ ( k5_lattices @ sk_A ) )
      = ( k5_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k2_lattices @ sk_A @ sk_B @ ( k5_lattices @ sk_A ) )
    = ( k5_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_lattices @ sk_A @ sk_B @ ( k5_lattices @ sk_A ) )
      = ( k5_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k4_lattices @ sk_A @ sk_B @ ( k5_lattices @ sk_A ) )
    = ( k5_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['21','24','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    r1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
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

thf('55',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r1_lattices @ X5 @ X4 @ X6 )
      | ( ( k1_lattices @ X5 @ X4 @ X6 )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l2_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_lattices])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
        = X1 )
      | ~ ( r1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
      | ( ( k1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l2_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['53','57'])).

thf('59',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('60',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X8: $i] :
      ( ( l2_lattices @ X8 )
      | ~ ( l3_lattices @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('62',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
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

thf('66',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l2_lattices @ X10 )
      | ~ ( v4_lattices @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( ( k3_lattices @ X10 @ X9 @ X11 )
        = ( k1_lattices @ X10 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_lattices])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( ( k3_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
        = ( k1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_lattices @ X0 )
      | ~ ( l2_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l2_lattices @ X0 )
      | ~ ( v4_lattices @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k3_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
        = ( k1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 ) )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ( ( k3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
      = ( k1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) )
    | ~ ( v4_lattices @ sk_A )
    | ~ ( l2_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['64','68'])).

thf('70',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v4_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('72',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v4_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['60','61'])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
      = ( k1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['69','70','76','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( k3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
    = ( k1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
      = sk_B ) ),
    inference(demod,[status(thm)],['58','59','62','63','80'])).

thf('82',plain,(
    ( k3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['81','82'])).

thf('84',plain,(
    $false ),
    inference(demod,[status(thm)],['0','83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eslc9skJFc
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:16:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.55  % Solved by: fo/fo7.sh
% 0.22/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.55  % done 115 iterations in 0.102s
% 0.22/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.55  % SZS output start Refutation
% 0.22/0.55  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.22/0.55  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 0.22/0.55  thf(k1_lattices_type, type, k1_lattices: $i > $i > $i > $i).
% 0.22/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.55  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.22/0.55  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.22/0.55  thf(k5_lattices_type, type, k5_lattices: $i > $i).
% 0.22/0.55  thf(k4_lattices_type, type, k4_lattices: $i > $i > $i > $i).
% 0.22/0.55  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.22/0.55  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 0.22/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.55  thf(k3_lattices_type, type, k3_lattices: $i > $i > $i > $i).
% 0.22/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.55  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.22/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.55  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.22/0.55  thf(v13_lattices_type, type, v13_lattices: $i > $o).
% 0.22/0.55  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.22/0.55  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.22/0.55  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.22/0.55  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 0.22/0.55  thf(t39_lattices, conjecture,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.22/0.55         ( v13_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.55           ( ( k3_lattices @ A @ ( k5_lattices @ A ) @ B ) = ( B ) ) ) ) ))).
% 0.22/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.55    (~( ![A:$i]:
% 0.22/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.22/0.55            ( v13_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.22/0.55          ( ![B:$i]:
% 0.22/0.55            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.55              ( ( k3_lattices @ A @ ( k5_lattices @ A ) @ B ) = ( B ) ) ) ) ) )),
% 0.22/0.55    inference('cnf.neg', [status(esa)], [t39_lattices])).
% 0.22/0.55  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(dt_k5_lattices, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 0.22/0.55       ( m1_subset_1 @ ( k5_lattices @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 0.22/0.55  thf('1', plain,
% 0.22/0.55      (![X7 : $i]:
% 0.22/0.55         ((m1_subset_1 @ (k5_lattices @ X7) @ (u1_struct_0 @ X7))
% 0.22/0.55          | ~ (l1_lattices @ X7)
% 0.22/0.55          | (v2_struct_0 @ X7))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 0.22/0.55  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(t23_lattices, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.22/0.55         ( v8_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.55           ( ![C:$i]:
% 0.22/0.55             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.55               ( r1_lattices @ A @ ( k4_lattices @ A @ B @ C ) @ B ) ) ) ) ) ))).
% 0.22/0.55  thf('3', plain,
% 0.22/0.55      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 0.22/0.55          | (r1_lattices @ X16 @ (k4_lattices @ X16 @ X15 @ X17) @ X15)
% 0.22/0.55          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.22/0.55          | ~ (l3_lattices @ X16)
% 0.22/0.55          | ~ (v8_lattices @ X16)
% 0.22/0.55          | ~ (v6_lattices @ X16)
% 0.22/0.55          | (v2_struct_0 @ X16))),
% 0.22/0.55      inference('cnf', [status(esa)], [t23_lattices])).
% 0.22/0.55  thf('4', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((v2_struct_0 @ sk_A)
% 0.22/0.55          | ~ (v6_lattices @ sk_A)
% 0.22/0.55          | ~ (v8_lattices @ sk_A)
% 0.22/0.55          | ~ (l3_lattices @ sk_A)
% 0.22/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.55          | (r1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_B @ X0) @ sk_B))),
% 0.22/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.55  thf(cc1_lattices, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( l3_lattices @ A ) =>
% 0.22/0.55       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.22/0.55         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.22/0.55           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.22/0.55           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.22/0.55  thf('5', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((v2_struct_0 @ X0)
% 0.22/0.55          | ~ (v10_lattices @ X0)
% 0.22/0.55          | (v6_lattices @ X0)
% 0.22/0.55          | ~ (l3_lattices @ X0))),
% 0.22/0.55      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.22/0.55  thf('6', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('7', plain,
% 0.22/0.55      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.55  thf('8', plain, ((l3_lattices @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('9', plain, ((v10_lattices @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('10', plain, ((v6_lattices @ sk_A)),
% 0.22/0.55      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.22/0.55  thf('11', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((v2_struct_0 @ X0)
% 0.22/0.55          | ~ (v10_lattices @ X0)
% 0.22/0.55          | (v8_lattices @ X0)
% 0.22/0.55          | ~ (l3_lattices @ X0))),
% 0.22/0.55      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.22/0.55  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('13', plain,
% 0.22/0.55      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.55  thf('14', plain, ((l3_lattices @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('15', plain, ((v10_lattices @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('16', plain, ((v8_lattices @ sk_A)),
% 0.22/0.55      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.22/0.55  thf('17', plain, ((l3_lattices @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('18', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((v2_struct_0 @ sk_A)
% 0.22/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.55          | (r1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_B @ X0) @ sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['4', '10', '16', '17'])).
% 0.22/0.55  thf('19', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('20', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((r1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_B @ X0) @ sk_B)
% 0.22/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.55      inference('clc', [status(thm)], ['18', '19'])).
% 0.22/0.55  thf('21', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_A)
% 0.22/0.55        | ~ (l1_lattices @ sk_A)
% 0.22/0.55        | (r1_lattices @ sk_A @ 
% 0.22/0.55           (k4_lattices @ sk_A @ sk_B @ (k5_lattices @ sk_A)) @ sk_B))),
% 0.22/0.55      inference('sup-', [status(thm)], ['1', '20'])).
% 0.22/0.55  thf('22', plain, ((l3_lattices @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(dt_l3_lattices, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 0.22/0.55  thf('23', plain, (![X8 : $i]: ((l1_lattices @ X8) | ~ (l3_lattices @ X8))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.22/0.55  thf('24', plain, ((l1_lattices @ sk_A)),
% 0.22/0.55      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.55  thf('25', plain,
% 0.22/0.55      (![X7 : $i]:
% 0.22/0.55         ((m1_subset_1 @ (k5_lattices @ X7) @ (u1_struct_0 @ X7))
% 0.22/0.55          | ~ (l1_lattices @ X7)
% 0.22/0.55          | (v2_struct_0 @ X7))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 0.22/0.55  thf('26', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(redefinition_k4_lattices, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i]:
% 0.22/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.22/0.55         ( l1_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.55         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.55       ( ( k4_lattices @ A @ B @ C ) = ( k2_lattices @ A @ B @ C ) ) ))).
% 0.22/0.55  thf('27', plain,
% 0.22/0.55      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.22/0.55          | ~ (l1_lattices @ X13)
% 0.22/0.55          | ~ (v6_lattices @ X13)
% 0.22/0.55          | (v2_struct_0 @ X13)
% 0.22/0.55          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.22/0.55          | ((k4_lattices @ X13 @ X12 @ X14) = (k2_lattices @ X13 @ X12 @ X14)))),
% 0.22/0.55      inference('cnf', [status(esa)], [redefinition_k4_lattices])).
% 0.22/0.55  thf('28', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (((k4_lattices @ sk_A @ sk_B @ X0) = (k2_lattices @ sk_A @ sk_B @ X0))
% 0.22/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.55          | (v2_struct_0 @ sk_A)
% 0.22/0.55          | ~ (v6_lattices @ sk_A)
% 0.22/0.55          | ~ (l1_lattices @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.22/0.55  thf('29', plain, ((v6_lattices @ sk_A)),
% 0.22/0.55      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.22/0.55  thf('30', plain, ((l1_lattices @ sk_A)),
% 0.22/0.55      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.55  thf('31', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (((k4_lattices @ sk_A @ sk_B @ X0) = (k2_lattices @ sk_A @ sk_B @ X0))
% 0.22/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.55          | (v2_struct_0 @ sk_A))),
% 0.22/0.55      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.22/0.55  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('33', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.55          | ((k4_lattices @ sk_A @ sk_B @ X0)
% 0.22/0.55              = (k2_lattices @ sk_A @ sk_B @ X0)))),
% 0.22/0.55      inference('clc', [status(thm)], ['31', '32'])).
% 0.22/0.55  thf('34', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_A)
% 0.22/0.55        | ~ (l1_lattices @ sk_A)
% 0.22/0.55        | ((k4_lattices @ sk_A @ sk_B @ (k5_lattices @ sk_A))
% 0.22/0.55            = (k2_lattices @ sk_A @ sk_B @ (k5_lattices @ sk_A))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['25', '33'])).
% 0.22/0.55  thf('35', plain, ((l1_lattices @ sk_A)),
% 0.22/0.55      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.55  thf('36', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('37', plain,
% 0.22/0.55      (![X7 : $i]:
% 0.22/0.55         ((m1_subset_1 @ (k5_lattices @ X7) @ (u1_struct_0 @ X7))
% 0.22/0.55          | ~ (l1_lattices @ X7)
% 0.22/0.55          | (v2_struct_0 @ X7))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 0.22/0.55  thf(d16_lattices, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 0.22/0.55       ( ( v13_lattices @ A ) =>
% 0.22/0.55         ( ![B:$i]:
% 0.22/0.55           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.55             ( ( ( B ) = ( k5_lattices @ A ) ) <=>
% 0.22/0.55               ( ![C:$i]:
% 0.22/0.55                 ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.55                   ( ( ( k2_lattices @ A @ B @ C ) = ( B ) ) & 
% 0.22/0.55                     ( ( k2_lattices @ A @ C @ B ) = ( B ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.55  thf('38', plain,
% 0.22/0.55      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.55         (~ (v13_lattices @ X1)
% 0.22/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.22/0.55          | ((X2) != (k5_lattices @ X1))
% 0.22/0.55          | ((k2_lattices @ X1 @ X3 @ X2) = (X2))
% 0.22/0.55          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.22/0.55          | ~ (l1_lattices @ X1)
% 0.22/0.55          | (v2_struct_0 @ X1))),
% 0.22/0.55      inference('cnf', [status(esa)], [d16_lattices])).
% 0.22/0.55  thf('39', plain,
% 0.22/0.55      (![X1 : $i, X3 : $i]:
% 0.22/0.55         ((v2_struct_0 @ X1)
% 0.22/0.55          | ~ (l1_lattices @ X1)
% 0.22/0.55          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.22/0.55          | ((k2_lattices @ X1 @ X3 @ (k5_lattices @ X1)) = (k5_lattices @ X1))
% 0.22/0.55          | ~ (m1_subset_1 @ (k5_lattices @ X1) @ (u1_struct_0 @ X1))
% 0.22/0.55          | ~ (v13_lattices @ X1))),
% 0.22/0.55      inference('simplify', [status(thm)], ['38'])).
% 0.22/0.55  thf('40', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         ((v2_struct_0 @ X0)
% 0.22/0.55          | ~ (l1_lattices @ X0)
% 0.22/0.55          | ~ (v13_lattices @ X0)
% 0.22/0.55          | ((k2_lattices @ X0 @ X1 @ (k5_lattices @ X0)) = (k5_lattices @ X0))
% 0.22/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.55          | ~ (l1_lattices @ X0)
% 0.22/0.55          | (v2_struct_0 @ X0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['37', '39'])).
% 0.22/0.55  thf('41', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.55          | ((k2_lattices @ X0 @ X1 @ (k5_lattices @ X0)) = (k5_lattices @ X0))
% 0.22/0.55          | ~ (v13_lattices @ X0)
% 0.22/0.55          | ~ (l1_lattices @ X0)
% 0.22/0.55          | (v2_struct_0 @ X0))),
% 0.22/0.55      inference('simplify', [status(thm)], ['40'])).
% 0.22/0.55  thf('42', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_A)
% 0.22/0.55        | ~ (l1_lattices @ sk_A)
% 0.22/0.55        | ~ (v13_lattices @ sk_A)
% 0.22/0.55        | ((k2_lattices @ sk_A @ sk_B @ (k5_lattices @ sk_A))
% 0.22/0.55            = (k5_lattices @ sk_A)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['36', '41'])).
% 0.22/0.55  thf('43', plain, ((l1_lattices @ sk_A)),
% 0.22/0.55      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.55  thf('44', plain, ((v13_lattices @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('45', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_A)
% 0.22/0.55        | ((k2_lattices @ sk_A @ sk_B @ (k5_lattices @ sk_A))
% 0.22/0.55            = (k5_lattices @ sk_A)))),
% 0.22/0.55      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.22/0.55  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('47', plain,
% 0.22/0.55      (((k2_lattices @ sk_A @ sk_B @ (k5_lattices @ sk_A))
% 0.22/0.55         = (k5_lattices @ sk_A))),
% 0.22/0.55      inference('clc', [status(thm)], ['45', '46'])).
% 0.22/0.55  thf('48', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_A)
% 0.22/0.55        | ((k4_lattices @ sk_A @ sk_B @ (k5_lattices @ sk_A))
% 0.22/0.55            = (k5_lattices @ sk_A)))),
% 0.22/0.55      inference('demod', [status(thm)], ['34', '35', '47'])).
% 0.22/0.55  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('50', plain,
% 0.22/0.55      (((k4_lattices @ sk_A @ sk_B @ (k5_lattices @ sk_A))
% 0.22/0.55         = (k5_lattices @ sk_A))),
% 0.22/0.55      inference('clc', [status(thm)], ['48', '49'])).
% 0.22/0.55  thf('51', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_A)
% 0.22/0.55        | (r1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['21', '24', '50'])).
% 0.22/0.55  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('53', plain, ((r1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)),
% 0.22/0.55      inference('clc', [status(thm)], ['51', '52'])).
% 0.22/0.55  thf('54', plain,
% 0.22/0.55      (![X7 : $i]:
% 0.22/0.55         ((m1_subset_1 @ (k5_lattices @ X7) @ (u1_struct_0 @ X7))
% 0.22/0.55          | ~ (l1_lattices @ X7)
% 0.22/0.55          | (v2_struct_0 @ X7))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 0.22/0.55  thf(d3_lattices, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l2_lattices @ A ) ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.55           ( ![C:$i]:
% 0.22/0.55             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.55               ( ( r1_lattices @ A @ B @ C ) <=>
% 0.22/0.55                 ( ( k1_lattices @ A @ B @ C ) = ( C ) ) ) ) ) ) ) ))).
% 0.22/0.55  thf('55', plain,
% 0.22/0.55      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.22/0.55          | ~ (r1_lattices @ X5 @ X4 @ X6)
% 0.22/0.55          | ((k1_lattices @ X5 @ X4 @ X6) = (X6))
% 0.22/0.55          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.22/0.55          | ~ (l2_lattices @ X5)
% 0.22/0.55          | (v2_struct_0 @ X5))),
% 0.22/0.55      inference('cnf', [status(esa)], [d3_lattices])).
% 0.22/0.55  thf('56', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         ((v2_struct_0 @ X0)
% 0.22/0.55          | ~ (l1_lattices @ X0)
% 0.22/0.55          | (v2_struct_0 @ X0)
% 0.22/0.55          | ~ (l2_lattices @ X0)
% 0.22/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.55          | ((k1_lattices @ X0 @ (k5_lattices @ X0) @ X1) = (X1))
% 0.22/0.55          | ~ (r1_lattices @ X0 @ (k5_lattices @ X0) @ X1))),
% 0.22/0.55      inference('sup-', [status(thm)], ['54', '55'])).
% 0.22/0.55  thf('57', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (~ (r1_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 0.22/0.55          | ((k1_lattices @ X0 @ (k5_lattices @ X0) @ X1) = (X1))
% 0.22/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.55          | ~ (l2_lattices @ X0)
% 0.22/0.55          | ~ (l1_lattices @ X0)
% 0.22/0.55          | (v2_struct_0 @ X0))),
% 0.22/0.55      inference('simplify', [status(thm)], ['56'])).
% 0.22/0.55  thf('58', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_A)
% 0.22/0.55        | ~ (l1_lattices @ sk_A)
% 0.22/0.55        | ~ (l2_lattices @ sk_A)
% 0.22/0.55        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.22/0.55        | ((k1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B) = (sk_B)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['53', '57'])).
% 0.22/0.55  thf('59', plain, ((l1_lattices @ sk_A)),
% 0.22/0.55      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.55  thf('60', plain, ((l3_lattices @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('61', plain, (![X8 : $i]: ((l2_lattices @ X8) | ~ (l3_lattices @ X8))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.22/0.55  thf('62', plain, ((l2_lattices @ sk_A)),
% 0.22/0.55      inference('sup-', [status(thm)], ['60', '61'])).
% 0.22/0.55  thf('63', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('64', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('65', plain,
% 0.22/0.55      (![X7 : $i]:
% 0.22/0.55         ((m1_subset_1 @ (k5_lattices @ X7) @ (u1_struct_0 @ X7))
% 0.22/0.55          | ~ (l1_lattices @ X7)
% 0.22/0.55          | (v2_struct_0 @ X7))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 0.22/0.55  thf(redefinition_k3_lattices, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i]:
% 0.22/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.22/0.55         ( l2_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.55         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.55       ( ( k3_lattices @ A @ B @ C ) = ( k1_lattices @ A @ B @ C ) ) ))).
% 0.22/0.55  thf('66', plain,
% 0.22/0.55      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.22/0.55          | ~ (l2_lattices @ X10)
% 0.22/0.55          | ~ (v4_lattices @ X10)
% 0.22/0.55          | (v2_struct_0 @ X10)
% 0.22/0.55          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.22/0.55          | ((k3_lattices @ X10 @ X9 @ X11) = (k1_lattices @ X10 @ X9 @ X11)))),
% 0.22/0.55      inference('cnf', [status(esa)], [redefinition_k3_lattices])).
% 0.22/0.55  thf('67', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         ((v2_struct_0 @ X0)
% 0.22/0.55          | ~ (l1_lattices @ X0)
% 0.22/0.55          | ((k3_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 0.22/0.55              = (k1_lattices @ X0 @ (k5_lattices @ X0) @ X1))
% 0.22/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.55          | (v2_struct_0 @ X0)
% 0.22/0.55          | ~ (v4_lattices @ X0)
% 0.22/0.55          | ~ (l2_lattices @ X0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['65', '66'])).
% 0.22/0.55  thf('68', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (~ (l2_lattices @ X0)
% 0.22/0.55          | ~ (v4_lattices @ X0)
% 0.22/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.55          | ((k3_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 0.22/0.55              = (k1_lattices @ X0 @ (k5_lattices @ X0) @ X1))
% 0.22/0.55          | ~ (l1_lattices @ X0)
% 0.22/0.55          | (v2_struct_0 @ X0))),
% 0.22/0.55      inference('simplify', [status(thm)], ['67'])).
% 0.22/0.55  thf('69', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_A)
% 0.22/0.55        | ~ (l1_lattices @ sk_A)
% 0.22/0.55        | ((k3_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)
% 0.22/0.55            = (k1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B))
% 0.22/0.55        | ~ (v4_lattices @ sk_A)
% 0.22/0.55        | ~ (l2_lattices @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['64', '68'])).
% 0.22/0.55  thf('70', plain, ((l1_lattices @ sk_A)),
% 0.22/0.55      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.55  thf('71', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((v2_struct_0 @ X0)
% 0.22/0.55          | ~ (v10_lattices @ X0)
% 0.22/0.55          | (v4_lattices @ X0)
% 0.22/0.55          | ~ (l3_lattices @ X0))),
% 0.22/0.55      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.22/0.55  thf('72', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('73', plain,
% 0.22/0.55      ((~ (l3_lattices @ sk_A) | (v4_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['71', '72'])).
% 0.22/0.55  thf('74', plain, ((l3_lattices @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('75', plain, ((v10_lattices @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('76', plain, ((v4_lattices @ sk_A)),
% 0.22/0.55      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.22/0.55  thf('77', plain, ((l2_lattices @ sk_A)),
% 0.22/0.55      inference('sup-', [status(thm)], ['60', '61'])).
% 0.22/0.55  thf('78', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_A)
% 0.22/0.55        | ((k3_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)
% 0.22/0.55            = (k1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)))),
% 0.22/0.55      inference('demod', [status(thm)], ['69', '70', '76', '77'])).
% 0.22/0.55  thf('79', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('80', plain,
% 0.22/0.55      (((k3_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)
% 0.22/0.55         = (k1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B))),
% 0.22/0.55      inference('clc', [status(thm)], ['78', '79'])).
% 0.22/0.55  thf('81', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_A)
% 0.22/0.55        | ((k3_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B) = (sk_B)))),
% 0.22/0.55      inference('demod', [status(thm)], ['58', '59', '62', '63', '80'])).
% 0.22/0.55  thf('82', plain,
% 0.22/0.55      (((k3_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B) != (sk_B))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('83', plain, ((v2_struct_0 @ sk_A)),
% 0.22/0.55      inference('simplify_reflect-', [status(thm)], ['81', '82'])).
% 0.22/0.55  thf('84', plain, ($false), inference('demod', [status(thm)], ['0', '83'])).
% 0.22/0.55  
% 0.22/0.55  % SZS output end Refutation
% 0.22/0.55  
% 0.22/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
