%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fGiptstcm3

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:33 EST 2020

% Result     : Theorem 6.33s
% Output     : Refutation 6.33s
% Verified   : 
% Statistics : Number of formulae       :  196 ( 827 expanded)
%              Number of leaves         :   28 ( 249 expanded)
%              Depth                    :   34
%              Number of atoms          : 2246 (11844 expanded)
%              Number of equality atoms :   60 ( 369 expanded)
%              Maximal formula depth    :   23 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(k5_lattices_type,type,(
    k5_lattices: $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(k4_lattices_type,type,(
    k4_lattices: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(v13_lattices_type,type,(
    v13_lattices: $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

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
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_lattices @ A ) )
     => ( m1_subset_1 @ ( k5_lattices @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ( r1_lattices @ X13 @ ( k4_lattices @ X13 @ X12 @ X14 ) @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l3_lattices @ X13 )
      | ~ ( v8_lattices @ X13 )
      | ~ ( v6_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t23_lattices])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 ) @ ( k5_lattices @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattices @ X0 @ ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 ) @ ( k5_lattices @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ~ ( v6_lattices @ sk_A )
    | ~ ( v8_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) @ ( k5_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('8',plain,(
    ! [X8: $i] :
      ( ( l1_lattices @ X8 )
      | ~ ( l3_lattices @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('9',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

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

thf('10',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) @ ( k5_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','9','15','21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) @ ( k5_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf(dt_k4_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v6_lattices @ A )
        & ( l1_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k4_lattices @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ) )).

thf('28',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_lattices @ X5 )
      | ~ ( v6_lattices @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ( m1_subset_1 @ ( k4_lattices @ X5 @ X4 @ X6 ) @ ( u1_struct_0 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_lattices])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( m1_subset_1 @ ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( l1_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( m1_subset_1 @ ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ( m1_subset_1 @ ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v6_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['26','30'])).

thf('32',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('33',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['34','35'])).

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

thf('37',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( r1_lattices @ X10 @ X9 @ X11 )
      | ( ( k2_lattices @ X10 @ X9 @ X11 )
        = X9 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ~ ( v9_lattices @ X10 )
      | ~ ( v8_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t21_lattices])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) @ X0 )
        = ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) )
      | ~ ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) @ X0 )
        = ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) )
      | ~ ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39','45','46'])).

thf('48',plain,
    ( ( ( k2_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) @ ( k5_lattices @ sk_A ) )
      = ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k5_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','47'])).

thf('49',plain,(
    m1_subset_1 @ ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('50',plain,(
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

thf('51',plain,(
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

thf('52',plain,(
    ! [X1: $i,X3: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_lattices @ X1 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ( ( k2_lattices @ X1 @ X3 @ ( k5_lattices @ X1 ) )
        = ( k5_lattices @ X1 ) )
      | ~ ( m1_subset_1 @ ( k5_lattices @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v13_lattices @ X1 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ X1 @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ X1 @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) )
      | ~ ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ~ ( v13_lattices @ sk_A )
    | ( ( k2_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) @ ( k5_lattices @ sk_A ) )
      = ( k5_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('57',plain,(
    v13_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) @ ( k5_lattices @ sk_A ) )
      = ( k5_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k2_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) @ ( k5_lattices @ sk_A ) )
    = ( k5_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( m1_subset_1 @ ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( m1_subset_1 @ ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( k5_lattices @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v6_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v6_lattices @ X0 )
      | ( m1_subset_1 @ ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( k5_lattices @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ X1 @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) )
      | ~ ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( k5_lattices @ X0 ) ) @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ X0 @ ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( k5_lattices @ X0 ) ) @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) )
      | ~ ( v13_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('69',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattices @ X0 @ ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 ) @ ( k5_lattices @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r1_lattices @ X0 @ ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( k5_lattices @ X0 ) ) @ ( k5_lattices @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r1_lattices @ X0 @ ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( k5_lattices @ X0 ) ) @ ( k5_lattices @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v6_lattices @ X0 )
      | ( m1_subset_1 @ ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( k5_lattices @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('74',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( r1_lattices @ X10 @ X9 @ X11 )
      | ( ( k2_lattices @ X10 @ X9 @ X11 )
        = X9 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ~ ( v9_lattices @ X10 )
      | ~ ( v8_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t21_lattices])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( k5_lattices @ X0 ) ) @ X1 )
        = ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( k5_lattices @ X0 ) ) )
      | ~ ( r1_lattices @ X0 @ ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( k5_lattices @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_lattices @ X0 @ ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( k5_lattices @ X0 ) ) @ X1 )
      | ( ( k2_lattices @ X0 @ ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( k5_lattices @ X0 ) ) @ X1 )
        = ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( k5_lattices @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ ( k5_lattices @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( k5_lattices @ X0 ) ) @ ( k5_lattices @ X0 ) )
        = ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( k5_lattices @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['72','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ X0 @ ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( k5_lattices @ X0 ) ) @ ( k5_lattices @ X0 ) )
        = ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( k5_lattices @ X0 ) ) )
      | ~ ( m1_subset_1 @ ( k5_lattices @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( k5_lattices @ X0 ) ) @ ( k5_lattices @ X0 ) )
        = ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( k5_lattices @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['68','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ X0 @ ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( k5_lattices @ X0 ) ) @ ( k5_lattices @ X0 ) )
        = ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( k5_lattices @ X0 ) ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( ( k5_lattices @ X0 )
        = ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( k5_lattices @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup+',[status(thm)],['67','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k5_lattices @ X0 )
        = ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( k5_lattices @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k5_lattices @ X0 )
        = ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( k5_lattices @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('84',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_lattices @ X5 )
      | ~ ( v6_lattices @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ( m1_subset_1 @ ( k4_lattices @ X5 @ X4 @ X6 ) @ ( u1_struct_0 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_lattices])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_lattices @ sk_A @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('89',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_lattices @ sk_A @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( k4_lattices @ sk_A @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    m1_subset_1 @ ( k4_lattices @ sk_A @ sk_B @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['84','92'])).

thf('94',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('95',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v13_lattices @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( X2
       != ( k5_lattices @ X1 ) )
      | ( ( k2_lattices @ X1 @ X2 @ X3 )
        = X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d16_lattices])).

thf('96',plain,(
    ! [X1: $i,X3: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_lattices @ X1 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ( ( k2_lattices @ X1 @ ( k5_lattices @ X1 ) @ X3 )
        = ( k5_lattices @ X1 ) )
      | ~ ( m1_subset_1 @ ( k5_lattices @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v13_lattices @ X1 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
        = ( k5_lattices @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
        = ( k5_lattices @ X0 ) )
      | ~ ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ~ ( v13_lattices @ sk_A )
    | ( ( k2_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k4_lattices @ sk_A @ sk_B @ sk_B ) )
      = ( k5_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['93','98'])).

thf('100',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('101',plain,(
    v13_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k4_lattices @ sk_A @ sk_B @ sk_B ) )
      = ( k5_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( k2_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k4_lattices @ sk_A @ sk_B @ sk_B ) )
    = ( k5_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k5_lattices @ X0 )
        = ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( k5_lattices @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( v6_lattices @ X0 )
      | ( m1_subset_1 @ ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( k5_lattices @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('107',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ( ( k2_lattices @ X10 @ X9 @ X11 )
       != X9 )
      | ( r1_lattices @ X10 @ X9 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ~ ( v9_lattices @ X10 )
      | ~ ( v8_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t21_lattices])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( k5_lattices @ X0 ) ) @ X1 )
      | ( ( k2_lattices @ X0 @ ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( k5_lattices @ X0 ) ) @ X1 )
       != ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( k5_lattices @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X0 @ ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( k5_lattices @ X0 ) ) @ X1 )
       != ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( k5_lattices @ X0 ) ) )
      | ( r1_lattices @ X0 @ ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( k5_lattices @ X0 ) ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
       != ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( k5_lattices @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( k5_lattices @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['105','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattices @ X0 @ ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( k5_lattices @ X0 ) ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
       != ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( k5_lattices @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,
    ( ( ( k5_lattices @ sk_A )
     != ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k5_lattices @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ~ ( v6_lattices @ sk_A )
    | ~ ( v13_lattices @ sk_A )
    | ~ ( v8_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v9_lattices @ sk_A )
    | ~ ( m1_subset_1 @ ( k4_lattices @ sk_A @ sk_B @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k5_lattices @ sk_A ) ) @ ( k4_lattices @ sk_A @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['104','111'])).

thf('113',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('114',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('115',plain,(
    v13_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('117',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('119',plain,(
    m1_subset_1 @ ( k4_lattices @ sk_A @ sk_B @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['84','92'])).

thf('120',plain,
    ( ( ( k5_lattices @ sk_A )
     != ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k5_lattices @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k5_lattices @ sk_A ) ) @ ( k4_lattices @ sk_A @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['112','113','114','115','116','117','118','119'])).

thf('121',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k5_lattices @ sk_A ) ) @ ( k4_lattices @ sk_A @ sk_B @ sk_B ) )
    | ( ( k5_lattices @ sk_A )
     != ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k5_lattices @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( ( k5_lattices @ sk_A )
     != ( k5_lattices @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ~ ( v6_lattices @ sk_A )
    | ~ ( v13_lattices @ sk_A )
    | ~ ( v8_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v9_lattices @ sk_A )
    | ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k5_lattices @ sk_A ) ) @ ( k4_lattices @ sk_A @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['83','122'])).

thf('124',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('125',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('126',plain,(
    v13_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('128',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('130',plain,
    ( ( ( k5_lattices @ sk_A )
     != ( k5_lattices @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k5_lattices @ sk_A ) ) @ ( k4_lattices @ sk_A @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['123','124','125','126','127','128','129'])).

thf('131',plain,
    ( ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k5_lattices @ sk_A ) ) @ ( k4_lattices @ sk_A @ sk_B @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k5_lattices @ sk_A ) ) @ ( k4_lattices @ sk_A @ sk_B @ sk_B ) ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_lattices @ X0 @ ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( k5_lattices @ X0 ) ) @ X1 )
      | ( ( k2_lattices @ X0 @ ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( k5_lattices @ X0 ) ) @ X1 )
        = ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( k5_lattices @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('135',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ~ ( v6_lattices @ sk_A )
    | ~ ( v8_lattices @ sk_A )
    | ~ ( v9_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( m1_subset_1 @ ( k4_lattices @ sk_A @ sk_B @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k5_lattices @ sk_A ) ) @ ( k4_lattices @ sk_A @ sk_B @ sk_B ) )
      = ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k5_lattices @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('137',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('138',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('139',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('140',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    m1_subset_1 @ ( k4_lattices @ sk_A @ sk_B @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['84','92'])).

thf('142',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k5_lattices @ sk_A ) ) @ ( k4_lattices @ sk_A @ sk_B @ sk_B ) )
      = ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k5_lattices @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['135','136','137','138','139','140','141'])).

thf('143',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( k2_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k5_lattices @ sk_A ) ) @ ( k4_lattices @ sk_A @ sk_B @ sk_B ) )
    = ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k5_lattices @ sk_A ) ) ),
    inference(clc,[status(thm)],['142','143'])).

thf('145',plain,
    ( ( ( k2_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k4_lattices @ sk_A @ sk_B @ sk_B ) )
      = ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k5_lattices @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ~ ( v6_lattices @ sk_A )
    | ~ ( v13_lattices @ sk_A )
    | ~ ( v8_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v9_lattices @ sk_A ) ),
    inference('sup+',[status(thm)],['82','144'])).

thf('146',plain,
    ( ( k2_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k4_lattices @ sk_A @ sk_B @ sk_B ) )
    = ( k5_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('147',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('148',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('149',plain,(
    v13_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('151',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('153',plain,
    ( ( ( k5_lattices @ sk_A )
      = ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k5_lattices @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['145','146','147','148','149','150','151','152'])).

thf('154',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( k5_lattices @ sk_A )
    = ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k5_lattices @ sk_A ) ) ),
    inference(clc,[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( v6_lattices @ X0 )
      | ( m1_subset_1 @ ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( k5_lattices @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('157',plain,
    ( ( m1_subset_1 @ ( k5_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ~ ( v6_lattices @ sk_A ) ),
    inference('sup+',[status(thm)],['155','156'])).

thf('158',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('159',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('160',plain,
    ( ( m1_subset_1 @ ( k5_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['157','158','159'])).

thf('161',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    m1_subset_1 @ ( k5_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['160','161'])).

thf('163',plain,
    ( ( ( k5_lattices @ sk_A )
      = ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','60','162'])).

thf('164',plain,(
    ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
 != ( k5_lattices @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['163','164'])).

thf('166',plain,(
    $false ),
    inference(demod,[status(thm)],['0','165'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fGiptstcm3
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:09:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 6.33/6.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.33/6.54  % Solved by: fo/fo7.sh
% 6.33/6.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.33/6.54  % done 3508 iterations in 6.030s
% 6.33/6.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.33/6.54  % SZS output start Refutation
% 6.33/6.54  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 6.33/6.54  thf(sk_A_type, type, sk_A: $i).
% 6.33/6.54  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 6.33/6.54  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 6.33/6.54  thf(k5_lattices_type, type, k5_lattices: $i > $i).
% 6.33/6.54  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 6.33/6.54  thf(k4_lattices_type, type, k4_lattices: $i > $i > $i > $i).
% 6.33/6.54  thf(sk_B_type, type, sk_B: $i).
% 6.33/6.54  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 6.33/6.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 6.33/6.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.33/6.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 6.33/6.54  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 6.33/6.54  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 6.33/6.54  thf(v13_lattices_type, type, v13_lattices: $i > $o).
% 6.33/6.54  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 6.33/6.54  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 6.33/6.54  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 6.33/6.54  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 6.33/6.54  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 6.33/6.54  thf(t40_lattices, conjecture,
% 6.33/6.54    (![A:$i]:
% 6.33/6.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 6.33/6.54         ( v13_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 6.33/6.54       ( ![B:$i]:
% 6.33/6.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 6.33/6.54           ( ( k4_lattices @ A @ ( k5_lattices @ A ) @ B ) =
% 6.33/6.54             ( k5_lattices @ A ) ) ) ) ))).
% 6.33/6.54  thf(zf_stmt_0, negated_conjecture,
% 6.33/6.54    (~( ![A:$i]:
% 6.33/6.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 6.33/6.54            ( v13_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 6.33/6.54          ( ![B:$i]:
% 6.33/6.54            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 6.33/6.54              ( ( k4_lattices @ A @ ( k5_lattices @ A ) @ B ) =
% 6.33/6.54                ( k5_lattices @ A ) ) ) ) ) )),
% 6.33/6.54    inference('cnf.neg', [status(esa)], [t40_lattices])).
% 6.33/6.54  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 6.33/6.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.54  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 6.33/6.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.54  thf(dt_k5_lattices, axiom,
% 6.33/6.54    (![A:$i]:
% 6.33/6.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 6.33/6.54       ( m1_subset_1 @ ( k5_lattices @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 6.33/6.54  thf('2', plain,
% 6.33/6.54      (![X7 : $i]:
% 6.33/6.54         ((m1_subset_1 @ (k5_lattices @ X7) @ (u1_struct_0 @ X7))
% 6.33/6.54          | ~ (l1_lattices @ X7)
% 6.33/6.54          | (v2_struct_0 @ X7))),
% 6.33/6.54      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 6.33/6.54  thf(t23_lattices, axiom,
% 6.33/6.54    (![A:$i]:
% 6.33/6.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 6.33/6.54         ( v8_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 6.33/6.54       ( ![B:$i]:
% 6.33/6.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 6.33/6.54           ( ![C:$i]:
% 6.33/6.54             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 6.33/6.54               ( r1_lattices @ A @ ( k4_lattices @ A @ B @ C ) @ B ) ) ) ) ) ))).
% 6.33/6.54  thf('3', plain,
% 6.33/6.54      (![X12 : $i, X13 : $i, X14 : $i]:
% 6.33/6.54         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 6.33/6.54          | (r1_lattices @ X13 @ (k4_lattices @ X13 @ X12 @ X14) @ X12)
% 6.33/6.54          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 6.33/6.54          | ~ (l3_lattices @ X13)
% 6.33/6.54          | ~ (v8_lattices @ X13)
% 6.33/6.54          | ~ (v6_lattices @ X13)
% 6.33/6.54          | (v2_struct_0 @ X13))),
% 6.33/6.54      inference('cnf', [status(esa)], [t23_lattices])).
% 6.33/6.54  thf('4', plain,
% 6.33/6.54      (![X0 : $i, X1 : $i]:
% 6.33/6.54         ((v2_struct_0 @ X0)
% 6.33/6.54          | ~ (l1_lattices @ X0)
% 6.33/6.54          | (v2_struct_0 @ X0)
% 6.33/6.54          | ~ (v6_lattices @ X0)
% 6.33/6.54          | ~ (v8_lattices @ X0)
% 6.33/6.54          | ~ (l3_lattices @ X0)
% 6.33/6.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 6.33/6.54          | (r1_lattices @ X0 @ (k4_lattices @ X0 @ (k5_lattices @ X0) @ X1) @ 
% 6.33/6.54             (k5_lattices @ X0)))),
% 6.33/6.54      inference('sup-', [status(thm)], ['2', '3'])).
% 6.33/6.54  thf('5', plain,
% 6.33/6.54      (![X0 : $i, X1 : $i]:
% 6.33/6.54         ((r1_lattices @ X0 @ (k4_lattices @ X0 @ (k5_lattices @ X0) @ X1) @ 
% 6.33/6.54           (k5_lattices @ X0))
% 6.33/6.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 6.33/6.54          | ~ (l3_lattices @ X0)
% 6.33/6.54          | ~ (v8_lattices @ X0)
% 6.33/6.54          | ~ (v6_lattices @ X0)
% 6.33/6.54          | ~ (l1_lattices @ X0)
% 6.33/6.54          | (v2_struct_0 @ X0))),
% 6.33/6.54      inference('simplify', [status(thm)], ['4'])).
% 6.33/6.54  thf('6', plain,
% 6.33/6.54      (((v2_struct_0 @ sk_A)
% 6.33/6.54        | ~ (l1_lattices @ sk_A)
% 6.33/6.54        | ~ (v6_lattices @ sk_A)
% 6.33/6.54        | ~ (v8_lattices @ sk_A)
% 6.33/6.54        | ~ (l3_lattices @ sk_A)
% 6.33/6.54        | (r1_lattices @ sk_A @ 
% 6.33/6.54           (k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B) @ 
% 6.33/6.54           (k5_lattices @ sk_A)))),
% 6.33/6.54      inference('sup-', [status(thm)], ['1', '5'])).
% 6.33/6.54  thf('7', plain, ((l3_lattices @ sk_A)),
% 6.33/6.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.54  thf(dt_l3_lattices, axiom,
% 6.33/6.54    (![A:$i]:
% 6.33/6.54     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 6.33/6.54  thf('8', plain, (![X8 : $i]: ((l1_lattices @ X8) | ~ (l3_lattices @ X8))),
% 6.33/6.54      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 6.33/6.54  thf('9', plain, ((l1_lattices @ sk_A)),
% 6.33/6.54      inference('sup-', [status(thm)], ['7', '8'])).
% 6.33/6.54  thf(cc1_lattices, axiom,
% 6.33/6.54    (![A:$i]:
% 6.33/6.54     ( ( l3_lattices @ A ) =>
% 6.33/6.54       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 6.33/6.54         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 6.33/6.54           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 6.33/6.54           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 6.33/6.54  thf('10', plain,
% 6.33/6.54      (![X0 : $i]:
% 6.33/6.54         ((v2_struct_0 @ X0)
% 6.33/6.54          | ~ (v10_lattices @ X0)
% 6.33/6.54          | (v6_lattices @ X0)
% 6.33/6.54          | ~ (l3_lattices @ X0))),
% 6.33/6.54      inference('cnf', [status(esa)], [cc1_lattices])).
% 6.33/6.54  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 6.33/6.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.54  thf('12', plain,
% 6.33/6.54      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 6.33/6.54      inference('sup-', [status(thm)], ['10', '11'])).
% 6.33/6.54  thf('13', plain, ((l3_lattices @ sk_A)),
% 6.33/6.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.54  thf('14', plain, ((v10_lattices @ sk_A)),
% 6.33/6.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.54  thf('15', plain, ((v6_lattices @ sk_A)),
% 6.33/6.54      inference('demod', [status(thm)], ['12', '13', '14'])).
% 6.33/6.54  thf('16', plain,
% 6.33/6.54      (![X0 : $i]:
% 6.33/6.54         ((v2_struct_0 @ X0)
% 6.33/6.54          | ~ (v10_lattices @ X0)
% 6.33/6.54          | (v8_lattices @ X0)
% 6.33/6.54          | ~ (l3_lattices @ X0))),
% 6.33/6.54      inference('cnf', [status(esa)], [cc1_lattices])).
% 6.33/6.54  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 6.33/6.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.54  thf('18', plain,
% 6.33/6.54      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 6.33/6.54      inference('sup-', [status(thm)], ['16', '17'])).
% 6.33/6.54  thf('19', plain, ((l3_lattices @ sk_A)),
% 6.33/6.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.54  thf('20', plain, ((v10_lattices @ sk_A)),
% 6.33/6.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.54  thf('21', plain, ((v8_lattices @ sk_A)),
% 6.33/6.54      inference('demod', [status(thm)], ['18', '19', '20'])).
% 6.33/6.54  thf('22', plain, ((l3_lattices @ sk_A)),
% 6.33/6.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.54  thf('23', plain,
% 6.33/6.54      (((v2_struct_0 @ sk_A)
% 6.33/6.54        | (r1_lattices @ sk_A @ 
% 6.33/6.54           (k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B) @ 
% 6.33/6.54           (k5_lattices @ sk_A)))),
% 6.33/6.54      inference('demod', [status(thm)], ['6', '9', '15', '21', '22'])).
% 6.33/6.54  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 6.33/6.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.54  thf('25', plain,
% 6.33/6.54      ((r1_lattices @ sk_A @ 
% 6.33/6.54        (k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B) @ 
% 6.33/6.54        (k5_lattices @ sk_A))),
% 6.33/6.54      inference('clc', [status(thm)], ['23', '24'])).
% 6.33/6.54  thf('26', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 6.33/6.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.54  thf('27', plain,
% 6.33/6.54      (![X7 : $i]:
% 6.33/6.54         ((m1_subset_1 @ (k5_lattices @ X7) @ (u1_struct_0 @ X7))
% 6.33/6.54          | ~ (l1_lattices @ X7)
% 6.33/6.54          | (v2_struct_0 @ X7))),
% 6.33/6.54      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 6.33/6.54  thf(dt_k4_lattices, axiom,
% 6.33/6.54    (![A:$i,B:$i,C:$i]:
% 6.33/6.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 6.33/6.54         ( l1_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 6.33/6.54         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 6.33/6.54       ( m1_subset_1 @ ( k4_lattices @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ))).
% 6.33/6.54  thf('28', plain,
% 6.33/6.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 6.33/6.54         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 6.33/6.54          | ~ (l1_lattices @ X5)
% 6.33/6.54          | ~ (v6_lattices @ X5)
% 6.33/6.54          | (v2_struct_0 @ X5)
% 6.33/6.54          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 6.33/6.54          | (m1_subset_1 @ (k4_lattices @ X5 @ X4 @ X6) @ (u1_struct_0 @ X5)))),
% 6.33/6.54      inference('cnf', [status(esa)], [dt_k4_lattices])).
% 6.33/6.54  thf('29', plain,
% 6.33/6.54      (![X0 : $i, X1 : $i]:
% 6.33/6.54         ((v2_struct_0 @ X0)
% 6.33/6.54          | ~ (l1_lattices @ X0)
% 6.33/6.54          | (m1_subset_1 @ (k4_lattices @ X0 @ (k5_lattices @ X0) @ X1) @ 
% 6.33/6.54             (u1_struct_0 @ X0))
% 6.33/6.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 6.33/6.54          | (v2_struct_0 @ X0)
% 6.33/6.54          | ~ (v6_lattices @ X0)
% 6.33/6.54          | ~ (l1_lattices @ X0))),
% 6.33/6.54      inference('sup-', [status(thm)], ['27', '28'])).
% 6.33/6.54  thf('30', plain,
% 6.33/6.54      (![X0 : $i, X1 : $i]:
% 6.33/6.54         (~ (v6_lattices @ X0)
% 6.33/6.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 6.33/6.54          | (m1_subset_1 @ (k4_lattices @ X0 @ (k5_lattices @ X0) @ X1) @ 
% 6.33/6.54             (u1_struct_0 @ X0))
% 6.33/6.54          | ~ (l1_lattices @ X0)
% 6.33/6.54          | (v2_struct_0 @ X0))),
% 6.33/6.54      inference('simplify', [status(thm)], ['29'])).
% 6.33/6.54  thf('31', plain,
% 6.33/6.54      (((v2_struct_0 @ sk_A)
% 6.33/6.54        | ~ (l1_lattices @ sk_A)
% 6.33/6.54        | (m1_subset_1 @ (k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B) @ 
% 6.33/6.54           (u1_struct_0 @ sk_A))
% 6.33/6.54        | ~ (v6_lattices @ sk_A))),
% 6.33/6.54      inference('sup-', [status(thm)], ['26', '30'])).
% 6.33/6.54  thf('32', plain, ((l1_lattices @ sk_A)),
% 6.33/6.54      inference('sup-', [status(thm)], ['7', '8'])).
% 6.33/6.54  thf('33', plain, ((v6_lattices @ sk_A)),
% 6.33/6.54      inference('demod', [status(thm)], ['12', '13', '14'])).
% 6.33/6.54  thf('34', plain,
% 6.33/6.54      (((v2_struct_0 @ sk_A)
% 6.33/6.54        | (m1_subset_1 @ (k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B) @ 
% 6.33/6.54           (u1_struct_0 @ sk_A)))),
% 6.33/6.54      inference('demod', [status(thm)], ['31', '32', '33'])).
% 6.33/6.54  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 6.33/6.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.54  thf('36', plain,
% 6.33/6.54      ((m1_subset_1 @ (k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B) @ 
% 6.33/6.54        (u1_struct_0 @ sk_A))),
% 6.33/6.54      inference('clc', [status(thm)], ['34', '35'])).
% 6.33/6.54  thf(t21_lattices, axiom,
% 6.33/6.54    (![A:$i]:
% 6.33/6.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v8_lattices @ A ) & 
% 6.33/6.54         ( v9_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 6.33/6.54       ( ![B:$i]:
% 6.33/6.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 6.33/6.54           ( ![C:$i]:
% 6.33/6.54             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 6.33/6.54               ( ( r1_lattices @ A @ B @ C ) <=>
% 6.33/6.54                 ( ( k2_lattices @ A @ B @ C ) = ( B ) ) ) ) ) ) ) ))).
% 6.33/6.54  thf('37', plain,
% 6.33/6.54      (![X9 : $i, X10 : $i, X11 : $i]:
% 6.33/6.54         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 6.33/6.54          | ~ (r1_lattices @ X10 @ X9 @ X11)
% 6.33/6.54          | ((k2_lattices @ X10 @ X9 @ X11) = (X9))
% 6.33/6.54          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 6.33/6.54          | ~ (l3_lattices @ X10)
% 6.33/6.54          | ~ (v9_lattices @ X10)
% 6.33/6.54          | ~ (v8_lattices @ X10)
% 6.33/6.54          | (v2_struct_0 @ X10))),
% 6.33/6.54      inference('cnf', [status(esa)], [t21_lattices])).
% 6.33/6.54  thf('38', plain,
% 6.33/6.54      (![X0 : $i]:
% 6.33/6.54         ((v2_struct_0 @ sk_A)
% 6.33/6.54          | ~ (v8_lattices @ sk_A)
% 6.33/6.54          | ~ (v9_lattices @ sk_A)
% 6.33/6.54          | ~ (l3_lattices @ sk_A)
% 6.33/6.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.33/6.54          | ((k2_lattices @ sk_A @ 
% 6.33/6.54              (k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B) @ X0)
% 6.33/6.54              = (k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B))
% 6.33/6.54          | ~ (r1_lattices @ sk_A @ 
% 6.33/6.54               (k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B) @ X0))),
% 6.33/6.54      inference('sup-', [status(thm)], ['36', '37'])).
% 6.33/6.54  thf('39', plain, ((v8_lattices @ sk_A)),
% 6.33/6.54      inference('demod', [status(thm)], ['18', '19', '20'])).
% 6.33/6.54  thf('40', plain,
% 6.33/6.54      (![X0 : $i]:
% 6.33/6.54         ((v2_struct_0 @ X0)
% 6.33/6.54          | ~ (v10_lattices @ X0)
% 6.33/6.54          | (v9_lattices @ X0)
% 6.33/6.54          | ~ (l3_lattices @ X0))),
% 6.33/6.54      inference('cnf', [status(esa)], [cc1_lattices])).
% 6.33/6.54  thf('41', plain, (~ (v2_struct_0 @ sk_A)),
% 6.33/6.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.54  thf('42', plain,
% 6.33/6.54      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 6.33/6.54      inference('sup-', [status(thm)], ['40', '41'])).
% 6.33/6.54  thf('43', plain, ((l3_lattices @ sk_A)),
% 6.33/6.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.54  thf('44', plain, ((v10_lattices @ sk_A)),
% 6.33/6.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.54  thf('45', plain, ((v9_lattices @ sk_A)),
% 6.33/6.54      inference('demod', [status(thm)], ['42', '43', '44'])).
% 6.33/6.54  thf('46', plain, ((l3_lattices @ sk_A)),
% 6.33/6.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.54  thf('47', plain,
% 6.33/6.54      (![X0 : $i]:
% 6.33/6.54         ((v2_struct_0 @ sk_A)
% 6.33/6.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.33/6.54          | ((k2_lattices @ sk_A @ 
% 6.33/6.54              (k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B) @ X0)
% 6.33/6.54              = (k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B))
% 6.33/6.54          | ~ (r1_lattices @ sk_A @ 
% 6.33/6.54               (k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B) @ X0))),
% 6.33/6.54      inference('demod', [status(thm)], ['38', '39', '45', '46'])).
% 6.33/6.54  thf('48', plain,
% 6.33/6.54      ((((k2_lattices @ sk_A @ 
% 6.33/6.54          (k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B) @ 
% 6.33/6.54          (k5_lattices @ sk_A))
% 6.33/6.54          = (k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B))
% 6.33/6.54        | ~ (m1_subset_1 @ (k5_lattices @ sk_A) @ (u1_struct_0 @ sk_A))
% 6.33/6.54        | (v2_struct_0 @ sk_A))),
% 6.33/6.54      inference('sup-', [status(thm)], ['25', '47'])).
% 6.33/6.54  thf('49', plain,
% 6.33/6.54      ((m1_subset_1 @ (k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B) @ 
% 6.33/6.54        (u1_struct_0 @ sk_A))),
% 6.33/6.54      inference('clc', [status(thm)], ['34', '35'])).
% 6.33/6.54  thf('50', plain,
% 6.33/6.54      (![X7 : $i]:
% 6.33/6.54         ((m1_subset_1 @ (k5_lattices @ X7) @ (u1_struct_0 @ X7))
% 6.33/6.54          | ~ (l1_lattices @ X7)
% 6.33/6.54          | (v2_struct_0 @ X7))),
% 6.33/6.54      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 6.33/6.54  thf(d16_lattices, axiom,
% 6.33/6.54    (![A:$i]:
% 6.33/6.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 6.33/6.54       ( ( v13_lattices @ A ) =>
% 6.33/6.54         ( ![B:$i]:
% 6.33/6.54           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 6.33/6.54             ( ( ( B ) = ( k5_lattices @ A ) ) <=>
% 6.33/6.54               ( ![C:$i]:
% 6.33/6.54                 ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 6.33/6.54                   ( ( ( k2_lattices @ A @ B @ C ) = ( B ) ) & 
% 6.33/6.54                     ( ( k2_lattices @ A @ C @ B ) = ( B ) ) ) ) ) ) ) ) ) ))).
% 6.33/6.54  thf('51', plain,
% 6.33/6.54      (![X1 : $i, X2 : $i, X3 : $i]:
% 6.33/6.54         (~ (v13_lattices @ X1)
% 6.33/6.54          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 6.33/6.54          | ((X2) != (k5_lattices @ X1))
% 6.33/6.54          | ((k2_lattices @ X1 @ X3 @ X2) = (X2))
% 6.33/6.54          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 6.33/6.54          | ~ (l1_lattices @ X1)
% 6.33/6.54          | (v2_struct_0 @ X1))),
% 6.33/6.54      inference('cnf', [status(esa)], [d16_lattices])).
% 6.33/6.54  thf('52', plain,
% 6.33/6.54      (![X1 : $i, X3 : $i]:
% 6.33/6.54         ((v2_struct_0 @ X1)
% 6.33/6.54          | ~ (l1_lattices @ X1)
% 6.33/6.54          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 6.33/6.54          | ((k2_lattices @ X1 @ X3 @ (k5_lattices @ X1)) = (k5_lattices @ X1))
% 6.33/6.54          | ~ (m1_subset_1 @ (k5_lattices @ X1) @ (u1_struct_0 @ X1))
% 6.33/6.54          | ~ (v13_lattices @ X1))),
% 6.33/6.54      inference('simplify', [status(thm)], ['51'])).
% 6.33/6.54  thf('53', plain,
% 6.33/6.54      (![X0 : $i, X1 : $i]:
% 6.33/6.54         ((v2_struct_0 @ X0)
% 6.33/6.54          | ~ (l1_lattices @ X0)
% 6.33/6.54          | ~ (v13_lattices @ X0)
% 6.33/6.54          | ((k2_lattices @ X0 @ X1 @ (k5_lattices @ X0)) = (k5_lattices @ X0))
% 6.33/6.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 6.33/6.54          | ~ (l1_lattices @ X0)
% 6.33/6.54          | (v2_struct_0 @ X0))),
% 6.33/6.54      inference('sup-', [status(thm)], ['50', '52'])).
% 6.33/6.54  thf('54', plain,
% 6.33/6.54      (![X0 : $i, X1 : $i]:
% 6.33/6.54         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 6.33/6.54          | ((k2_lattices @ X0 @ X1 @ (k5_lattices @ X0)) = (k5_lattices @ X0))
% 6.33/6.54          | ~ (v13_lattices @ X0)
% 6.33/6.54          | ~ (l1_lattices @ X0)
% 6.33/6.54          | (v2_struct_0 @ X0))),
% 6.33/6.54      inference('simplify', [status(thm)], ['53'])).
% 6.33/6.54  thf('55', plain,
% 6.33/6.54      (((v2_struct_0 @ sk_A)
% 6.33/6.54        | ~ (l1_lattices @ sk_A)
% 6.33/6.54        | ~ (v13_lattices @ sk_A)
% 6.33/6.54        | ((k2_lattices @ sk_A @ 
% 6.33/6.54            (k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B) @ 
% 6.33/6.54            (k5_lattices @ sk_A)) = (k5_lattices @ sk_A)))),
% 6.33/6.54      inference('sup-', [status(thm)], ['49', '54'])).
% 6.33/6.54  thf('56', plain, ((l1_lattices @ sk_A)),
% 6.33/6.54      inference('sup-', [status(thm)], ['7', '8'])).
% 6.33/6.54  thf('57', plain, ((v13_lattices @ sk_A)),
% 6.33/6.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.54  thf('58', plain,
% 6.33/6.54      (((v2_struct_0 @ sk_A)
% 6.33/6.54        | ((k2_lattices @ sk_A @ 
% 6.33/6.54            (k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B) @ 
% 6.33/6.54            (k5_lattices @ sk_A)) = (k5_lattices @ sk_A)))),
% 6.33/6.54      inference('demod', [status(thm)], ['55', '56', '57'])).
% 6.33/6.54  thf('59', plain, (~ (v2_struct_0 @ sk_A)),
% 6.33/6.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.54  thf('60', plain,
% 6.33/6.54      (((k2_lattices @ sk_A @ 
% 6.33/6.54         (k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B) @ 
% 6.33/6.54         (k5_lattices @ sk_A)) = (k5_lattices @ sk_A))),
% 6.33/6.54      inference('clc', [status(thm)], ['58', '59'])).
% 6.33/6.54  thf('61', plain,
% 6.33/6.54      (![X7 : $i]:
% 6.33/6.54         ((m1_subset_1 @ (k5_lattices @ X7) @ (u1_struct_0 @ X7))
% 6.33/6.54          | ~ (l1_lattices @ X7)
% 6.33/6.54          | (v2_struct_0 @ X7))),
% 6.33/6.54      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 6.33/6.54  thf('62', plain,
% 6.33/6.54      (![X0 : $i, X1 : $i]:
% 6.33/6.54         (~ (v6_lattices @ X0)
% 6.33/6.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 6.33/6.54          | (m1_subset_1 @ (k4_lattices @ X0 @ (k5_lattices @ X0) @ X1) @ 
% 6.33/6.54             (u1_struct_0 @ X0))
% 6.33/6.54          | ~ (l1_lattices @ X0)
% 6.33/6.54          | (v2_struct_0 @ X0))),
% 6.33/6.54      inference('simplify', [status(thm)], ['29'])).
% 6.33/6.54  thf('63', plain,
% 6.33/6.54      (![X0 : $i]:
% 6.33/6.54         ((v2_struct_0 @ X0)
% 6.33/6.54          | ~ (l1_lattices @ X0)
% 6.33/6.54          | (v2_struct_0 @ X0)
% 6.33/6.54          | ~ (l1_lattices @ X0)
% 6.33/6.54          | (m1_subset_1 @ 
% 6.33/6.54             (k4_lattices @ X0 @ (k5_lattices @ X0) @ (k5_lattices @ X0)) @ 
% 6.33/6.54             (u1_struct_0 @ X0))
% 6.33/6.54          | ~ (v6_lattices @ X0))),
% 6.33/6.54      inference('sup-', [status(thm)], ['61', '62'])).
% 6.33/6.54  thf('64', plain,
% 6.33/6.54      (![X0 : $i]:
% 6.33/6.54         (~ (v6_lattices @ X0)
% 6.33/6.54          | (m1_subset_1 @ 
% 6.33/6.54             (k4_lattices @ X0 @ (k5_lattices @ X0) @ (k5_lattices @ X0)) @ 
% 6.33/6.54             (u1_struct_0 @ X0))
% 6.33/6.54          | ~ (l1_lattices @ X0)
% 6.33/6.54          | (v2_struct_0 @ X0))),
% 6.33/6.54      inference('simplify', [status(thm)], ['63'])).
% 6.33/6.54  thf('65', plain,
% 6.33/6.54      (![X0 : $i, X1 : $i]:
% 6.33/6.54         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 6.33/6.54          | ((k2_lattices @ X0 @ X1 @ (k5_lattices @ X0)) = (k5_lattices @ X0))
% 6.33/6.54          | ~ (v13_lattices @ X0)
% 6.33/6.54          | ~ (l1_lattices @ X0)
% 6.33/6.54          | (v2_struct_0 @ X0))),
% 6.33/6.54      inference('simplify', [status(thm)], ['53'])).
% 6.33/6.54  thf('66', plain,
% 6.33/6.54      (![X0 : $i]:
% 6.33/6.54         ((v2_struct_0 @ X0)
% 6.33/6.54          | ~ (l1_lattices @ X0)
% 6.33/6.54          | ~ (v6_lattices @ X0)
% 6.33/6.54          | (v2_struct_0 @ X0)
% 6.33/6.54          | ~ (l1_lattices @ X0)
% 6.33/6.54          | ~ (v13_lattices @ X0)
% 6.33/6.54          | ((k2_lattices @ X0 @ 
% 6.33/6.54              (k4_lattices @ X0 @ (k5_lattices @ X0) @ (k5_lattices @ X0)) @ 
% 6.33/6.54              (k5_lattices @ X0)) = (k5_lattices @ X0)))),
% 6.33/6.54      inference('sup-', [status(thm)], ['64', '65'])).
% 6.33/6.54  thf('67', plain,
% 6.33/6.54      (![X0 : $i]:
% 6.33/6.54         (((k2_lattices @ X0 @ 
% 6.33/6.54            (k4_lattices @ X0 @ (k5_lattices @ X0) @ (k5_lattices @ X0)) @ 
% 6.33/6.54            (k5_lattices @ X0)) = (k5_lattices @ X0))
% 6.33/6.54          | ~ (v13_lattices @ X0)
% 6.33/6.54          | ~ (v6_lattices @ X0)
% 6.33/6.54          | ~ (l1_lattices @ X0)
% 6.33/6.54          | (v2_struct_0 @ X0))),
% 6.33/6.54      inference('simplify', [status(thm)], ['66'])).
% 6.33/6.54  thf('68', plain,
% 6.33/6.54      (![X7 : $i]:
% 6.33/6.54         ((m1_subset_1 @ (k5_lattices @ X7) @ (u1_struct_0 @ X7))
% 6.33/6.54          | ~ (l1_lattices @ X7)
% 6.33/6.54          | (v2_struct_0 @ X7))),
% 6.33/6.54      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 6.33/6.54  thf('69', plain,
% 6.33/6.54      (![X7 : $i]:
% 6.33/6.54         ((m1_subset_1 @ (k5_lattices @ X7) @ (u1_struct_0 @ X7))
% 6.33/6.54          | ~ (l1_lattices @ X7)
% 6.33/6.54          | (v2_struct_0 @ X7))),
% 6.33/6.54      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 6.33/6.54  thf('70', plain,
% 6.33/6.54      (![X0 : $i, X1 : $i]:
% 6.33/6.54         ((r1_lattices @ X0 @ (k4_lattices @ X0 @ (k5_lattices @ X0) @ X1) @ 
% 6.33/6.54           (k5_lattices @ X0))
% 6.33/6.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 6.33/6.54          | ~ (l3_lattices @ X0)
% 6.33/6.54          | ~ (v8_lattices @ X0)
% 6.33/6.54          | ~ (v6_lattices @ X0)
% 6.33/6.54          | ~ (l1_lattices @ X0)
% 6.33/6.54          | (v2_struct_0 @ X0))),
% 6.33/6.54      inference('simplify', [status(thm)], ['4'])).
% 6.33/6.54  thf('71', plain,
% 6.33/6.54      (![X0 : $i]:
% 6.33/6.54         ((v2_struct_0 @ X0)
% 6.33/6.54          | ~ (l1_lattices @ X0)
% 6.33/6.54          | (v2_struct_0 @ X0)
% 6.33/6.54          | ~ (l1_lattices @ X0)
% 6.33/6.54          | ~ (v6_lattices @ X0)
% 6.33/6.54          | ~ (v8_lattices @ X0)
% 6.33/6.54          | ~ (l3_lattices @ X0)
% 6.33/6.54          | (r1_lattices @ X0 @ 
% 6.33/6.54             (k4_lattices @ X0 @ (k5_lattices @ X0) @ (k5_lattices @ X0)) @ 
% 6.33/6.54             (k5_lattices @ X0)))),
% 6.33/6.54      inference('sup-', [status(thm)], ['69', '70'])).
% 6.33/6.54  thf('72', plain,
% 6.33/6.54      (![X0 : $i]:
% 6.33/6.54         ((r1_lattices @ X0 @ 
% 6.33/6.54           (k4_lattices @ X0 @ (k5_lattices @ X0) @ (k5_lattices @ X0)) @ 
% 6.33/6.54           (k5_lattices @ X0))
% 6.33/6.54          | ~ (l3_lattices @ X0)
% 6.33/6.54          | ~ (v8_lattices @ X0)
% 6.33/6.54          | ~ (v6_lattices @ X0)
% 6.33/6.54          | ~ (l1_lattices @ X0)
% 6.33/6.54          | (v2_struct_0 @ X0))),
% 6.33/6.54      inference('simplify', [status(thm)], ['71'])).
% 6.33/6.54  thf('73', plain,
% 6.33/6.54      (![X0 : $i]:
% 6.33/6.54         (~ (v6_lattices @ X0)
% 6.33/6.54          | (m1_subset_1 @ 
% 6.33/6.54             (k4_lattices @ X0 @ (k5_lattices @ X0) @ (k5_lattices @ X0)) @ 
% 6.33/6.54             (u1_struct_0 @ X0))
% 6.33/6.54          | ~ (l1_lattices @ X0)
% 6.33/6.54          | (v2_struct_0 @ X0))),
% 6.33/6.54      inference('simplify', [status(thm)], ['63'])).
% 6.33/6.54  thf('74', plain,
% 6.33/6.54      (![X9 : $i, X10 : $i, X11 : $i]:
% 6.33/6.54         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 6.33/6.54          | ~ (r1_lattices @ X10 @ X9 @ X11)
% 6.33/6.54          | ((k2_lattices @ X10 @ X9 @ X11) = (X9))
% 6.33/6.54          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 6.33/6.54          | ~ (l3_lattices @ X10)
% 6.33/6.54          | ~ (v9_lattices @ X10)
% 6.33/6.54          | ~ (v8_lattices @ X10)
% 6.33/6.54          | (v2_struct_0 @ X10))),
% 6.33/6.54      inference('cnf', [status(esa)], [t21_lattices])).
% 6.33/6.54  thf('75', plain,
% 6.33/6.54      (![X0 : $i, X1 : $i]:
% 6.33/6.54         ((v2_struct_0 @ X0)
% 6.33/6.54          | ~ (l1_lattices @ X0)
% 6.33/6.54          | ~ (v6_lattices @ X0)
% 6.33/6.54          | (v2_struct_0 @ X0)
% 6.33/6.54          | ~ (v8_lattices @ X0)
% 6.33/6.54          | ~ (v9_lattices @ X0)
% 6.33/6.54          | ~ (l3_lattices @ X0)
% 6.33/6.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 6.33/6.54          | ((k2_lattices @ X0 @ 
% 6.33/6.54              (k4_lattices @ X0 @ (k5_lattices @ X0) @ (k5_lattices @ X0)) @ X1)
% 6.33/6.54              = (k4_lattices @ X0 @ (k5_lattices @ X0) @ (k5_lattices @ X0)))
% 6.33/6.54          | ~ (r1_lattices @ X0 @ 
% 6.33/6.54               (k4_lattices @ X0 @ (k5_lattices @ X0) @ (k5_lattices @ X0)) @ 
% 6.33/6.54               X1))),
% 6.33/6.54      inference('sup-', [status(thm)], ['73', '74'])).
% 6.33/6.54  thf('76', plain,
% 6.33/6.54      (![X0 : $i, X1 : $i]:
% 6.33/6.54         (~ (r1_lattices @ X0 @ 
% 6.33/6.54             (k4_lattices @ X0 @ (k5_lattices @ X0) @ (k5_lattices @ X0)) @ X1)
% 6.33/6.54          | ((k2_lattices @ X0 @ 
% 6.33/6.54              (k4_lattices @ X0 @ (k5_lattices @ X0) @ (k5_lattices @ X0)) @ X1)
% 6.33/6.54              = (k4_lattices @ X0 @ (k5_lattices @ X0) @ (k5_lattices @ X0)))
% 6.33/6.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 6.33/6.54          | ~ (l3_lattices @ X0)
% 6.33/6.54          | ~ (v9_lattices @ X0)
% 6.33/6.54          | ~ (v8_lattices @ X0)
% 6.33/6.54          | ~ (v6_lattices @ X0)
% 6.33/6.54          | ~ (l1_lattices @ X0)
% 6.33/6.54          | (v2_struct_0 @ X0))),
% 6.33/6.54      inference('simplify', [status(thm)], ['75'])).
% 6.33/6.54  thf('77', plain,
% 6.33/6.54      (![X0 : $i]:
% 6.33/6.54         ((v2_struct_0 @ X0)
% 6.33/6.54          | ~ (l1_lattices @ X0)
% 6.33/6.54          | ~ (v6_lattices @ X0)
% 6.33/6.54          | ~ (v8_lattices @ X0)
% 6.33/6.54          | ~ (l3_lattices @ X0)
% 6.33/6.54          | (v2_struct_0 @ X0)
% 6.33/6.54          | ~ (l1_lattices @ X0)
% 6.33/6.54          | ~ (v6_lattices @ X0)
% 6.33/6.54          | ~ (v8_lattices @ X0)
% 6.33/6.54          | ~ (v9_lattices @ X0)
% 6.33/6.54          | ~ (l3_lattices @ X0)
% 6.33/6.54          | ~ (m1_subset_1 @ (k5_lattices @ X0) @ (u1_struct_0 @ X0))
% 6.33/6.54          | ((k2_lattices @ X0 @ 
% 6.33/6.54              (k4_lattices @ X0 @ (k5_lattices @ X0) @ (k5_lattices @ X0)) @ 
% 6.33/6.54              (k5_lattices @ X0))
% 6.33/6.54              = (k4_lattices @ X0 @ (k5_lattices @ X0) @ (k5_lattices @ X0))))),
% 6.33/6.54      inference('sup-', [status(thm)], ['72', '76'])).
% 6.33/6.54  thf('78', plain,
% 6.33/6.54      (![X0 : $i]:
% 6.33/6.54         (((k2_lattices @ X0 @ 
% 6.33/6.55            (k4_lattices @ X0 @ (k5_lattices @ X0) @ (k5_lattices @ X0)) @ 
% 6.33/6.55            (k5_lattices @ X0))
% 6.33/6.55            = (k4_lattices @ X0 @ (k5_lattices @ X0) @ (k5_lattices @ X0)))
% 6.33/6.55          | ~ (m1_subset_1 @ (k5_lattices @ X0) @ (u1_struct_0 @ X0))
% 6.33/6.55          | ~ (v9_lattices @ X0)
% 6.33/6.55          | ~ (l3_lattices @ X0)
% 6.33/6.55          | ~ (v8_lattices @ X0)
% 6.33/6.55          | ~ (v6_lattices @ X0)
% 6.33/6.55          | ~ (l1_lattices @ X0)
% 6.33/6.55          | (v2_struct_0 @ X0))),
% 6.33/6.55      inference('simplify', [status(thm)], ['77'])).
% 6.33/6.55  thf('79', plain,
% 6.33/6.55      (![X0 : $i]:
% 6.33/6.55         ((v2_struct_0 @ X0)
% 6.33/6.55          | ~ (l1_lattices @ X0)
% 6.33/6.55          | (v2_struct_0 @ X0)
% 6.33/6.55          | ~ (l1_lattices @ X0)
% 6.33/6.55          | ~ (v6_lattices @ X0)
% 6.33/6.55          | ~ (v8_lattices @ X0)
% 6.33/6.55          | ~ (l3_lattices @ X0)
% 6.33/6.55          | ~ (v9_lattices @ X0)
% 6.33/6.55          | ((k2_lattices @ X0 @ 
% 6.33/6.55              (k4_lattices @ X0 @ (k5_lattices @ X0) @ (k5_lattices @ X0)) @ 
% 6.33/6.55              (k5_lattices @ X0))
% 6.33/6.55              = (k4_lattices @ X0 @ (k5_lattices @ X0) @ (k5_lattices @ X0))))),
% 6.33/6.55      inference('sup-', [status(thm)], ['68', '78'])).
% 6.33/6.55  thf('80', plain,
% 6.33/6.55      (![X0 : $i]:
% 6.33/6.55         (((k2_lattices @ X0 @ 
% 6.33/6.55            (k4_lattices @ X0 @ (k5_lattices @ X0) @ (k5_lattices @ X0)) @ 
% 6.33/6.55            (k5_lattices @ X0))
% 6.33/6.55            = (k4_lattices @ X0 @ (k5_lattices @ X0) @ (k5_lattices @ X0)))
% 6.33/6.55          | ~ (v9_lattices @ X0)
% 6.33/6.55          | ~ (l3_lattices @ X0)
% 6.33/6.55          | ~ (v8_lattices @ X0)
% 6.33/6.55          | ~ (v6_lattices @ X0)
% 6.33/6.55          | ~ (l1_lattices @ X0)
% 6.33/6.55          | (v2_struct_0 @ X0))),
% 6.33/6.55      inference('simplify', [status(thm)], ['79'])).
% 6.33/6.55  thf('81', plain,
% 6.33/6.55      (![X0 : $i]:
% 6.33/6.55         (((k5_lattices @ X0)
% 6.33/6.55            = (k4_lattices @ X0 @ (k5_lattices @ X0) @ (k5_lattices @ X0)))
% 6.33/6.55          | (v2_struct_0 @ X0)
% 6.33/6.55          | ~ (l1_lattices @ X0)
% 6.33/6.55          | ~ (v6_lattices @ X0)
% 6.33/6.55          | ~ (v13_lattices @ X0)
% 6.33/6.55          | (v2_struct_0 @ X0)
% 6.33/6.55          | ~ (l1_lattices @ X0)
% 6.33/6.55          | ~ (v6_lattices @ X0)
% 6.33/6.55          | ~ (v8_lattices @ X0)
% 6.33/6.55          | ~ (l3_lattices @ X0)
% 6.33/6.55          | ~ (v9_lattices @ X0))),
% 6.33/6.55      inference('sup+', [status(thm)], ['67', '80'])).
% 6.33/6.55  thf('82', plain,
% 6.33/6.55      (![X0 : $i]:
% 6.33/6.55         (~ (v9_lattices @ X0)
% 6.33/6.55          | ~ (l3_lattices @ X0)
% 6.33/6.55          | ~ (v8_lattices @ X0)
% 6.33/6.55          | ~ (v13_lattices @ X0)
% 6.33/6.55          | ~ (v6_lattices @ X0)
% 6.33/6.55          | ~ (l1_lattices @ X0)
% 6.33/6.55          | (v2_struct_0 @ X0)
% 6.33/6.55          | ((k5_lattices @ X0)
% 6.33/6.55              = (k4_lattices @ X0 @ (k5_lattices @ X0) @ (k5_lattices @ X0))))),
% 6.33/6.55      inference('simplify', [status(thm)], ['81'])).
% 6.33/6.55  thf('83', plain,
% 6.33/6.55      (![X0 : $i]:
% 6.33/6.55         (~ (v9_lattices @ X0)
% 6.33/6.55          | ~ (l3_lattices @ X0)
% 6.33/6.55          | ~ (v8_lattices @ X0)
% 6.33/6.55          | ~ (v13_lattices @ X0)
% 6.33/6.55          | ~ (v6_lattices @ X0)
% 6.33/6.55          | ~ (l1_lattices @ X0)
% 6.33/6.55          | (v2_struct_0 @ X0)
% 6.33/6.55          | ((k5_lattices @ X0)
% 6.33/6.55              = (k4_lattices @ X0 @ (k5_lattices @ X0) @ (k5_lattices @ X0))))),
% 6.33/6.55      inference('simplify', [status(thm)], ['81'])).
% 6.33/6.55  thf('84', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 6.33/6.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.55  thf('85', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 6.33/6.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.55  thf('86', plain,
% 6.33/6.55      (![X4 : $i, X5 : $i, X6 : $i]:
% 6.33/6.55         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 6.33/6.55          | ~ (l1_lattices @ X5)
% 6.33/6.55          | ~ (v6_lattices @ X5)
% 6.33/6.55          | (v2_struct_0 @ X5)
% 6.33/6.55          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 6.33/6.55          | (m1_subset_1 @ (k4_lattices @ X5 @ X4 @ X6) @ (u1_struct_0 @ X5)))),
% 6.33/6.55      inference('cnf', [status(esa)], [dt_k4_lattices])).
% 6.33/6.55  thf('87', plain,
% 6.33/6.55      (![X0 : $i]:
% 6.33/6.55         ((m1_subset_1 @ (k4_lattices @ sk_A @ sk_B @ X0) @ 
% 6.33/6.55           (u1_struct_0 @ sk_A))
% 6.33/6.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.33/6.55          | (v2_struct_0 @ sk_A)
% 6.33/6.55          | ~ (v6_lattices @ sk_A)
% 6.33/6.55          | ~ (l1_lattices @ sk_A))),
% 6.33/6.55      inference('sup-', [status(thm)], ['85', '86'])).
% 6.33/6.55  thf('88', plain, ((v6_lattices @ sk_A)),
% 6.33/6.55      inference('demod', [status(thm)], ['12', '13', '14'])).
% 6.33/6.55  thf('89', plain, ((l1_lattices @ sk_A)),
% 6.33/6.55      inference('sup-', [status(thm)], ['7', '8'])).
% 6.33/6.55  thf('90', plain,
% 6.33/6.55      (![X0 : $i]:
% 6.33/6.55         ((m1_subset_1 @ (k4_lattices @ sk_A @ sk_B @ X0) @ 
% 6.33/6.55           (u1_struct_0 @ sk_A))
% 6.33/6.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.33/6.55          | (v2_struct_0 @ sk_A))),
% 6.33/6.55      inference('demod', [status(thm)], ['87', '88', '89'])).
% 6.33/6.55  thf('91', plain, (~ (v2_struct_0 @ sk_A)),
% 6.33/6.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.55  thf('92', plain,
% 6.33/6.55      (![X0 : $i]:
% 6.33/6.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.33/6.55          | (m1_subset_1 @ (k4_lattices @ sk_A @ sk_B @ X0) @ 
% 6.33/6.55             (u1_struct_0 @ sk_A)))),
% 6.33/6.55      inference('clc', [status(thm)], ['90', '91'])).
% 6.33/6.55  thf('93', plain,
% 6.33/6.55      ((m1_subset_1 @ (k4_lattices @ sk_A @ sk_B @ sk_B) @ (u1_struct_0 @ sk_A))),
% 6.33/6.55      inference('sup-', [status(thm)], ['84', '92'])).
% 6.33/6.55  thf('94', plain,
% 6.33/6.55      (![X7 : $i]:
% 6.33/6.55         ((m1_subset_1 @ (k5_lattices @ X7) @ (u1_struct_0 @ X7))
% 6.33/6.55          | ~ (l1_lattices @ X7)
% 6.33/6.55          | (v2_struct_0 @ X7))),
% 6.33/6.55      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 6.33/6.55  thf('95', plain,
% 6.33/6.55      (![X1 : $i, X2 : $i, X3 : $i]:
% 6.33/6.55         (~ (v13_lattices @ X1)
% 6.33/6.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 6.33/6.55          | ((X2) != (k5_lattices @ X1))
% 6.33/6.55          | ((k2_lattices @ X1 @ X2 @ X3) = (X2))
% 6.33/6.55          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 6.33/6.55          | ~ (l1_lattices @ X1)
% 6.33/6.55          | (v2_struct_0 @ X1))),
% 6.33/6.55      inference('cnf', [status(esa)], [d16_lattices])).
% 6.33/6.55  thf('96', plain,
% 6.33/6.55      (![X1 : $i, X3 : $i]:
% 6.33/6.55         ((v2_struct_0 @ X1)
% 6.33/6.55          | ~ (l1_lattices @ X1)
% 6.33/6.55          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 6.33/6.55          | ((k2_lattices @ X1 @ (k5_lattices @ X1) @ X3) = (k5_lattices @ X1))
% 6.33/6.55          | ~ (m1_subset_1 @ (k5_lattices @ X1) @ (u1_struct_0 @ X1))
% 6.33/6.55          | ~ (v13_lattices @ X1))),
% 6.33/6.55      inference('simplify', [status(thm)], ['95'])).
% 6.33/6.55  thf('97', plain,
% 6.33/6.55      (![X0 : $i, X1 : $i]:
% 6.33/6.55         ((v2_struct_0 @ X0)
% 6.33/6.55          | ~ (l1_lattices @ X0)
% 6.33/6.55          | ~ (v13_lattices @ X0)
% 6.33/6.55          | ((k2_lattices @ X0 @ (k5_lattices @ X0) @ X1) = (k5_lattices @ X0))
% 6.33/6.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 6.33/6.55          | ~ (l1_lattices @ X0)
% 6.33/6.55          | (v2_struct_0 @ X0))),
% 6.33/6.55      inference('sup-', [status(thm)], ['94', '96'])).
% 6.33/6.55  thf('98', plain,
% 6.33/6.55      (![X0 : $i, X1 : $i]:
% 6.33/6.55         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 6.33/6.55          | ((k2_lattices @ X0 @ (k5_lattices @ X0) @ X1) = (k5_lattices @ X0))
% 6.33/6.55          | ~ (v13_lattices @ X0)
% 6.33/6.55          | ~ (l1_lattices @ X0)
% 6.33/6.55          | (v2_struct_0 @ X0))),
% 6.33/6.55      inference('simplify', [status(thm)], ['97'])).
% 6.33/6.55  thf('99', plain,
% 6.33/6.55      (((v2_struct_0 @ sk_A)
% 6.33/6.55        | ~ (l1_lattices @ sk_A)
% 6.33/6.55        | ~ (v13_lattices @ sk_A)
% 6.33/6.55        | ((k2_lattices @ sk_A @ (k5_lattices @ sk_A) @ 
% 6.33/6.55            (k4_lattices @ sk_A @ sk_B @ sk_B)) = (k5_lattices @ sk_A)))),
% 6.33/6.55      inference('sup-', [status(thm)], ['93', '98'])).
% 6.33/6.55  thf('100', plain, ((l1_lattices @ sk_A)),
% 6.33/6.55      inference('sup-', [status(thm)], ['7', '8'])).
% 6.33/6.55  thf('101', plain, ((v13_lattices @ sk_A)),
% 6.33/6.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.55  thf('102', plain,
% 6.33/6.55      (((v2_struct_0 @ sk_A)
% 6.33/6.55        | ((k2_lattices @ sk_A @ (k5_lattices @ sk_A) @ 
% 6.33/6.55            (k4_lattices @ sk_A @ sk_B @ sk_B)) = (k5_lattices @ sk_A)))),
% 6.33/6.55      inference('demod', [status(thm)], ['99', '100', '101'])).
% 6.33/6.55  thf('103', plain, (~ (v2_struct_0 @ sk_A)),
% 6.33/6.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.55  thf('104', plain,
% 6.33/6.55      (((k2_lattices @ sk_A @ (k5_lattices @ sk_A) @ 
% 6.33/6.55         (k4_lattices @ sk_A @ sk_B @ sk_B)) = (k5_lattices @ sk_A))),
% 6.33/6.55      inference('clc', [status(thm)], ['102', '103'])).
% 6.33/6.55  thf('105', plain,
% 6.33/6.55      (![X0 : $i]:
% 6.33/6.55         (~ (v9_lattices @ X0)
% 6.33/6.55          | ~ (l3_lattices @ X0)
% 6.33/6.55          | ~ (v8_lattices @ X0)
% 6.33/6.55          | ~ (v13_lattices @ X0)
% 6.33/6.55          | ~ (v6_lattices @ X0)
% 6.33/6.55          | ~ (l1_lattices @ X0)
% 6.33/6.55          | (v2_struct_0 @ X0)
% 6.33/6.55          | ((k5_lattices @ X0)
% 6.33/6.55              = (k4_lattices @ X0 @ (k5_lattices @ X0) @ (k5_lattices @ X0))))),
% 6.33/6.55      inference('simplify', [status(thm)], ['81'])).
% 6.33/6.55  thf('106', plain,
% 6.33/6.55      (![X0 : $i]:
% 6.33/6.55         (~ (v6_lattices @ X0)
% 6.33/6.55          | (m1_subset_1 @ 
% 6.33/6.55             (k4_lattices @ X0 @ (k5_lattices @ X0) @ (k5_lattices @ X0)) @ 
% 6.33/6.55             (u1_struct_0 @ X0))
% 6.33/6.55          | ~ (l1_lattices @ X0)
% 6.33/6.55          | (v2_struct_0 @ X0))),
% 6.33/6.55      inference('simplify', [status(thm)], ['63'])).
% 6.33/6.55  thf('107', plain,
% 6.33/6.55      (![X9 : $i, X10 : $i, X11 : $i]:
% 6.33/6.55         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 6.33/6.55          | ((k2_lattices @ X10 @ X9 @ X11) != (X9))
% 6.33/6.55          | (r1_lattices @ X10 @ X9 @ X11)
% 6.33/6.55          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 6.33/6.55          | ~ (l3_lattices @ X10)
% 6.33/6.55          | ~ (v9_lattices @ X10)
% 6.33/6.55          | ~ (v8_lattices @ X10)
% 6.33/6.55          | (v2_struct_0 @ X10))),
% 6.33/6.55      inference('cnf', [status(esa)], [t21_lattices])).
% 6.33/6.55  thf('108', plain,
% 6.33/6.55      (![X0 : $i, X1 : $i]:
% 6.33/6.55         ((v2_struct_0 @ X0)
% 6.33/6.55          | ~ (l1_lattices @ X0)
% 6.33/6.55          | ~ (v6_lattices @ X0)
% 6.33/6.55          | (v2_struct_0 @ X0)
% 6.33/6.55          | ~ (v8_lattices @ X0)
% 6.33/6.55          | ~ (v9_lattices @ X0)
% 6.33/6.55          | ~ (l3_lattices @ X0)
% 6.33/6.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 6.33/6.55          | (r1_lattices @ X0 @ 
% 6.33/6.55             (k4_lattices @ X0 @ (k5_lattices @ X0) @ (k5_lattices @ X0)) @ X1)
% 6.33/6.55          | ((k2_lattices @ X0 @ 
% 6.33/6.55              (k4_lattices @ X0 @ (k5_lattices @ X0) @ (k5_lattices @ X0)) @ X1)
% 6.33/6.55              != (k4_lattices @ X0 @ (k5_lattices @ X0) @ (k5_lattices @ X0))))),
% 6.33/6.55      inference('sup-', [status(thm)], ['106', '107'])).
% 6.33/6.55  thf('109', plain,
% 6.33/6.55      (![X0 : $i, X1 : $i]:
% 6.33/6.55         (((k2_lattices @ X0 @ 
% 6.33/6.55            (k4_lattices @ X0 @ (k5_lattices @ X0) @ (k5_lattices @ X0)) @ X1)
% 6.33/6.55            != (k4_lattices @ X0 @ (k5_lattices @ X0) @ (k5_lattices @ X0)))
% 6.33/6.55          | (r1_lattices @ X0 @ 
% 6.33/6.55             (k4_lattices @ X0 @ (k5_lattices @ X0) @ (k5_lattices @ X0)) @ X1)
% 6.33/6.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 6.33/6.55          | ~ (l3_lattices @ X0)
% 6.33/6.55          | ~ (v9_lattices @ X0)
% 6.33/6.55          | ~ (v8_lattices @ X0)
% 6.33/6.55          | ~ (v6_lattices @ X0)
% 6.33/6.55          | ~ (l1_lattices @ X0)
% 6.33/6.55          | (v2_struct_0 @ X0))),
% 6.33/6.55      inference('simplify', [status(thm)], ['108'])).
% 6.33/6.55  thf('110', plain,
% 6.33/6.55      (![X0 : $i, X1 : $i]:
% 6.33/6.55         (((k2_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 6.33/6.55            != (k4_lattices @ X0 @ (k5_lattices @ X0) @ (k5_lattices @ X0)))
% 6.33/6.55          | (v2_struct_0 @ X0)
% 6.33/6.55          | ~ (l1_lattices @ X0)
% 6.33/6.55          | ~ (v6_lattices @ X0)
% 6.33/6.55          | ~ (v13_lattices @ X0)
% 6.33/6.55          | ~ (v8_lattices @ X0)
% 6.33/6.55          | ~ (l3_lattices @ X0)
% 6.33/6.55          | ~ (v9_lattices @ X0)
% 6.33/6.55          | (v2_struct_0 @ X0)
% 6.33/6.55          | ~ (l1_lattices @ X0)
% 6.33/6.55          | ~ (v6_lattices @ X0)
% 6.33/6.55          | ~ (v8_lattices @ X0)
% 6.33/6.55          | ~ (v9_lattices @ X0)
% 6.33/6.55          | ~ (l3_lattices @ X0)
% 6.33/6.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 6.33/6.55          | (r1_lattices @ X0 @ 
% 6.33/6.55             (k4_lattices @ X0 @ (k5_lattices @ X0) @ (k5_lattices @ X0)) @ X1))),
% 6.33/6.55      inference('sup-', [status(thm)], ['105', '109'])).
% 6.33/6.55  thf('111', plain,
% 6.33/6.55      (![X0 : $i, X1 : $i]:
% 6.33/6.55         ((r1_lattices @ X0 @ 
% 6.33/6.55           (k4_lattices @ X0 @ (k5_lattices @ X0) @ (k5_lattices @ X0)) @ X1)
% 6.33/6.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 6.33/6.55          | ~ (v9_lattices @ X0)
% 6.33/6.55          | ~ (l3_lattices @ X0)
% 6.33/6.55          | ~ (v8_lattices @ X0)
% 6.33/6.55          | ~ (v13_lattices @ X0)
% 6.33/6.55          | ~ (v6_lattices @ X0)
% 6.33/6.55          | ~ (l1_lattices @ X0)
% 6.33/6.55          | (v2_struct_0 @ X0)
% 6.33/6.55          | ((k2_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 6.33/6.55              != (k4_lattices @ X0 @ (k5_lattices @ X0) @ (k5_lattices @ X0))))),
% 6.33/6.55      inference('simplify', [status(thm)], ['110'])).
% 6.33/6.55  thf('112', plain,
% 6.33/6.55      ((((k5_lattices @ sk_A)
% 6.33/6.55          != (k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ (k5_lattices @ sk_A)))
% 6.33/6.55        | (v2_struct_0 @ sk_A)
% 6.33/6.55        | ~ (l1_lattices @ sk_A)
% 6.33/6.55        | ~ (v6_lattices @ sk_A)
% 6.33/6.55        | ~ (v13_lattices @ sk_A)
% 6.33/6.55        | ~ (v8_lattices @ sk_A)
% 6.33/6.55        | ~ (l3_lattices @ sk_A)
% 6.33/6.55        | ~ (v9_lattices @ sk_A)
% 6.33/6.55        | ~ (m1_subset_1 @ (k4_lattices @ sk_A @ sk_B @ sk_B) @ 
% 6.33/6.55             (u1_struct_0 @ sk_A))
% 6.33/6.55        | (r1_lattices @ sk_A @ 
% 6.33/6.55           (k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ (k5_lattices @ sk_A)) @ 
% 6.33/6.55           (k4_lattices @ sk_A @ sk_B @ sk_B)))),
% 6.33/6.55      inference('sup-', [status(thm)], ['104', '111'])).
% 6.33/6.55  thf('113', plain, ((l1_lattices @ sk_A)),
% 6.33/6.55      inference('sup-', [status(thm)], ['7', '8'])).
% 6.33/6.55  thf('114', plain, ((v6_lattices @ sk_A)),
% 6.33/6.55      inference('demod', [status(thm)], ['12', '13', '14'])).
% 6.33/6.55  thf('115', plain, ((v13_lattices @ sk_A)),
% 6.33/6.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.55  thf('116', plain, ((v8_lattices @ sk_A)),
% 6.33/6.55      inference('demod', [status(thm)], ['18', '19', '20'])).
% 6.33/6.55  thf('117', plain, ((l3_lattices @ sk_A)),
% 6.33/6.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.55  thf('118', plain, ((v9_lattices @ sk_A)),
% 6.33/6.55      inference('demod', [status(thm)], ['42', '43', '44'])).
% 6.33/6.55  thf('119', plain,
% 6.33/6.55      ((m1_subset_1 @ (k4_lattices @ sk_A @ sk_B @ sk_B) @ (u1_struct_0 @ sk_A))),
% 6.33/6.55      inference('sup-', [status(thm)], ['84', '92'])).
% 6.33/6.55  thf('120', plain,
% 6.33/6.55      ((((k5_lattices @ sk_A)
% 6.33/6.55          != (k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ (k5_lattices @ sk_A)))
% 6.33/6.55        | (v2_struct_0 @ sk_A)
% 6.33/6.55        | (r1_lattices @ sk_A @ 
% 6.33/6.55           (k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ (k5_lattices @ sk_A)) @ 
% 6.33/6.55           (k4_lattices @ sk_A @ sk_B @ sk_B)))),
% 6.33/6.55      inference('demod', [status(thm)],
% 6.33/6.55                ['112', '113', '114', '115', '116', '117', '118', '119'])).
% 6.33/6.55  thf('121', plain, (~ (v2_struct_0 @ sk_A)),
% 6.33/6.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.55  thf('122', plain,
% 6.33/6.55      (((r1_lattices @ sk_A @ 
% 6.33/6.55         (k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ (k5_lattices @ sk_A)) @ 
% 6.33/6.55         (k4_lattices @ sk_A @ sk_B @ sk_B))
% 6.33/6.55        | ((k5_lattices @ sk_A)
% 6.33/6.55            != (k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ 
% 6.33/6.55                (k5_lattices @ sk_A))))),
% 6.33/6.55      inference('clc', [status(thm)], ['120', '121'])).
% 6.33/6.55  thf('123', plain,
% 6.33/6.55      ((((k5_lattices @ sk_A) != (k5_lattices @ sk_A))
% 6.33/6.55        | (v2_struct_0 @ sk_A)
% 6.33/6.55        | ~ (l1_lattices @ sk_A)
% 6.33/6.55        | ~ (v6_lattices @ sk_A)
% 6.33/6.55        | ~ (v13_lattices @ sk_A)
% 6.33/6.55        | ~ (v8_lattices @ sk_A)
% 6.33/6.55        | ~ (l3_lattices @ sk_A)
% 6.33/6.55        | ~ (v9_lattices @ sk_A)
% 6.33/6.55        | (r1_lattices @ sk_A @ 
% 6.33/6.55           (k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ (k5_lattices @ sk_A)) @ 
% 6.33/6.55           (k4_lattices @ sk_A @ sk_B @ sk_B)))),
% 6.33/6.55      inference('sup-', [status(thm)], ['83', '122'])).
% 6.33/6.55  thf('124', plain, ((l1_lattices @ sk_A)),
% 6.33/6.55      inference('sup-', [status(thm)], ['7', '8'])).
% 6.33/6.55  thf('125', plain, ((v6_lattices @ sk_A)),
% 6.33/6.55      inference('demod', [status(thm)], ['12', '13', '14'])).
% 6.33/6.55  thf('126', plain, ((v13_lattices @ sk_A)),
% 6.33/6.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.55  thf('127', plain, ((v8_lattices @ sk_A)),
% 6.33/6.55      inference('demod', [status(thm)], ['18', '19', '20'])).
% 6.33/6.55  thf('128', plain, ((l3_lattices @ sk_A)),
% 6.33/6.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.55  thf('129', plain, ((v9_lattices @ sk_A)),
% 6.33/6.55      inference('demod', [status(thm)], ['42', '43', '44'])).
% 6.33/6.55  thf('130', plain,
% 6.33/6.55      ((((k5_lattices @ sk_A) != (k5_lattices @ sk_A))
% 6.33/6.55        | (v2_struct_0 @ sk_A)
% 6.33/6.55        | (r1_lattices @ sk_A @ 
% 6.33/6.55           (k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ (k5_lattices @ sk_A)) @ 
% 6.33/6.55           (k4_lattices @ sk_A @ sk_B @ sk_B)))),
% 6.33/6.55      inference('demod', [status(thm)],
% 6.33/6.55                ['123', '124', '125', '126', '127', '128', '129'])).
% 6.33/6.55  thf('131', plain,
% 6.33/6.55      (((r1_lattices @ sk_A @ 
% 6.33/6.55         (k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ (k5_lattices @ sk_A)) @ 
% 6.33/6.55         (k4_lattices @ sk_A @ sk_B @ sk_B))
% 6.33/6.55        | (v2_struct_0 @ sk_A))),
% 6.33/6.55      inference('simplify', [status(thm)], ['130'])).
% 6.33/6.55  thf('132', plain, (~ (v2_struct_0 @ sk_A)),
% 6.33/6.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.55  thf('133', plain,
% 6.33/6.55      ((r1_lattices @ sk_A @ 
% 6.33/6.55        (k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ (k5_lattices @ sk_A)) @ 
% 6.33/6.55        (k4_lattices @ sk_A @ sk_B @ sk_B))),
% 6.33/6.55      inference('clc', [status(thm)], ['131', '132'])).
% 6.33/6.55  thf('134', plain,
% 6.33/6.55      (![X0 : $i, X1 : $i]:
% 6.33/6.55         (~ (r1_lattices @ X0 @ 
% 6.33/6.55             (k4_lattices @ X0 @ (k5_lattices @ X0) @ (k5_lattices @ X0)) @ X1)
% 6.33/6.55          | ((k2_lattices @ X0 @ 
% 6.33/6.55              (k4_lattices @ X0 @ (k5_lattices @ X0) @ (k5_lattices @ X0)) @ X1)
% 6.33/6.55              = (k4_lattices @ X0 @ (k5_lattices @ X0) @ (k5_lattices @ X0)))
% 6.33/6.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 6.33/6.55          | ~ (l3_lattices @ X0)
% 6.33/6.55          | ~ (v9_lattices @ X0)
% 6.33/6.55          | ~ (v8_lattices @ X0)
% 6.33/6.55          | ~ (v6_lattices @ X0)
% 6.33/6.55          | ~ (l1_lattices @ X0)
% 6.33/6.55          | (v2_struct_0 @ X0))),
% 6.33/6.55      inference('simplify', [status(thm)], ['75'])).
% 6.33/6.55  thf('135', plain,
% 6.33/6.55      (((v2_struct_0 @ sk_A)
% 6.33/6.55        | ~ (l1_lattices @ sk_A)
% 6.33/6.55        | ~ (v6_lattices @ sk_A)
% 6.33/6.55        | ~ (v8_lattices @ sk_A)
% 6.33/6.55        | ~ (v9_lattices @ sk_A)
% 6.33/6.55        | ~ (l3_lattices @ sk_A)
% 6.33/6.55        | ~ (m1_subset_1 @ (k4_lattices @ sk_A @ sk_B @ sk_B) @ 
% 6.33/6.55             (u1_struct_0 @ sk_A))
% 6.33/6.55        | ((k2_lattices @ sk_A @ 
% 6.33/6.55            (k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ (k5_lattices @ sk_A)) @ 
% 6.33/6.55            (k4_lattices @ sk_A @ sk_B @ sk_B))
% 6.33/6.55            = (k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ (k5_lattices @ sk_A))))),
% 6.33/6.55      inference('sup-', [status(thm)], ['133', '134'])).
% 6.33/6.55  thf('136', plain, ((l1_lattices @ sk_A)),
% 6.33/6.55      inference('sup-', [status(thm)], ['7', '8'])).
% 6.33/6.55  thf('137', plain, ((v6_lattices @ sk_A)),
% 6.33/6.55      inference('demod', [status(thm)], ['12', '13', '14'])).
% 6.33/6.55  thf('138', plain, ((v8_lattices @ sk_A)),
% 6.33/6.55      inference('demod', [status(thm)], ['18', '19', '20'])).
% 6.33/6.55  thf('139', plain, ((v9_lattices @ sk_A)),
% 6.33/6.55      inference('demod', [status(thm)], ['42', '43', '44'])).
% 6.33/6.55  thf('140', plain, ((l3_lattices @ sk_A)),
% 6.33/6.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.55  thf('141', plain,
% 6.33/6.55      ((m1_subset_1 @ (k4_lattices @ sk_A @ sk_B @ sk_B) @ (u1_struct_0 @ sk_A))),
% 6.33/6.55      inference('sup-', [status(thm)], ['84', '92'])).
% 6.33/6.55  thf('142', plain,
% 6.33/6.55      (((v2_struct_0 @ sk_A)
% 6.33/6.55        | ((k2_lattices @ sk_A @ 
% 6.33/6.55            (k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ (k5_lattices @ sk_A)) @ 
% 6.33/6.55            (k4_lattices @ sk_A @ sk_B @ sk_B))
% 6.33/6.55            = (k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ (k5_lattices @ sk_A))))),
% 6.33/6.55      inference('demod', [status(thm)],
% 6.33/6.55                ['135', '136', '137', '138', '139', '140', '141'])).
% 6.33/6.55  thf('143', plain, (~ (v2_struct_0 @ sk_A)),
% 6.33/6.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.55  thf('144', plain,
% 6.33/6.55      (((k2_lattices @ sk_A @ 
% 6.33/6.55         (k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ (k5_lattices @ sk_A)) @ 
% 6.33/6.55         (k4_lattices @ sk_A @ sk_B @ sk_B))
% 6.33/6.55         = (k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ (k5_lattices @ sk_A)))),
% 6.33/6.55      inference('clc', [status(thm)], ['142', '143'])).
% 6.33/6.55  thf('145', plain,
% 6.33/6.55      ((((k2_lattices @ sk_A @ (k5_lattices @ sk_A) @ 
% 6.33/6.55          (k4_lattices @ sk_A @ sk_B @ sk_B))
% 6.33/6.55          = (k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ (k5_lattices @ sk_A)))
% 6.33/6.55        | (v2_struct_0 @ sk_A)
% 6.33/6.55        | ~ (l1_lattices @ sk_A)
% 6.33/6.55        | ~ (v6_lattices @ sk_A)
% 6.33/6.55        | ~ (v13_lattices @ sk_A)
% 6.33/6.55        | ~ (v8_lattices @ sk_A)
% 6.33/6.55        | ~ (l3_lattices @ sk_A)
% 6.33/6.55        | ~ (v9_lattices @ sk_A))),
% 6.33/6.55      inference('sup+', [status(thm)], ['82', '144'])).
% 6.33/6.55  thf('146', plain,
% 6.33/6.55      (((k2_lattices @ sk_A @ (k5_lattices @ sk_A) @ 
% 6.33/6.55         (k4_lattices @ sk_A @ sk_B @ sk_B)) = (k5_lattices @ sk_A))),
% 6.33/6.55      inference('clc', [status(thm)], ['102', '103'])).
% 6.33/6.55  thf('147', plain, ((l1_lattices @ sk_A)),
% 6.33/6.55      inference('sup-', [status(thm)], ['7', '8'])).
% 6.33/6.55  thf('148', plain, ((v6_lattices @ sk_A)),
% 6.33/6.55      inference('demod', [status(thm)], ['12', '13', '14'])).
% 6.33/6.55  thf('149', plain, ((v13_lattices @ sk_A)),
% 6.33/6.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.55  thf('150', plain, ((v8_lattices @ sk_A)),
% 6.33/6.55      inference('demod', [status(thm)], ['18', '19', '20'])).
% 6.33/6.55  thf('151', plain, ((l3_lattices @ sk_A)),
% 6.33/6.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.55  thf('152', plain, ((v9_lattices @ sk_A)),
% 6.33/6.55      inference('demod', [status(thm)], ['42', '43', '44'])).
% 6.33/6.55  thf('153', plain,
% 6.33/6.55      ((((k5_lattices @ sk_A)
% 6.33/6.55          = (k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ (k5_lattices @ sk_A)))
% 6.33/6.55        | (v2_struct_0 @ sk_A))),
% 6.33/6.55      inference('demod', [status(thm)],
% 6.33/6.55                ['145', '146', '147', '148', '149', '150', '151', '152'])).
% 6.33/6.55  thf('154', plain, (~ (v2_struct_0 @ sk_A)),
% 6.33/6.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.55  thf('155', plain,
% 6.33/6.55      (((k5_lattices @ sk_A)
% 6.33/6.55         = (k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ (k5_lattices @ sk_A)))),
% 6.33/6.55      inference('clc', [status(thm)], ['153', '154'])).
% 6.33/6.55  thf('156', plain,
% 6.33/6.55      (![X0 : $i]:
% 6.33/6.55         (~ (v6_lattices @ X0)
% 6.33/6.55          | (m1_subset_1 @ 
% 6.33/6.55             (k4_lattices @ X0 @ (k5_lattices @ X0) @ (k5_lattices @ X0)) @ 
% 6.33/6.55             (u1_struct_0 @ X0))
% 6.33/6.55          | ~ (l1_lattices @ X0)
% 6.33/6.55          | (v2_struct_0 @ X0))),
% 6.33/6.55      inference('simplify', [status(thm)], ['63'])).
% 6.33/6.55  thf('157', plain,
% 6.33/6.55      (((m1_subset_1 @ (k5_lattices @ sk_A) @ (u1_struct_0 @ sk_A))
% 6.33/6.55        | (v2_struct_0 @ sk_A)
% 6.33/6.55        | ~ (l1_lattices @ sk_A)
% 6.33/6.55        | ~ (v6_lattices @ sk_A))),
% 6.33/6.55      inference('sup+', [status(thm)], ['155', '156'])).
% 6.33/6.55  thf('158', plain, ((l1_lattices @ sk_A)),
% 6.33/6.55      inference('sup-', [status(thm)], ['7', '8'])).
% 6.33/6.55  thf('159', plain, ((v6_lattices @ sk_A)),
% 6.33/6.55      inference('demod', [status(thm)], ['12', '13', '14'])).
% 6.33/6.55  thf('160', plain,
% 6.33/6.55      (((m1_subset_1 @ (k5_lattices @ sk_A) @ (u1_struct_0 @ sk_A))
% 6.33/6.55        | (v2_struct_0 @ sk_A))),
% 6.33/6.55      inference('demod', [status(thm)], ['157', '158', '159'])).
% 6.33/6.55  thf('161', plain, (~ (v2_struct_0 @ sk_A)),
% 6.33/6.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.55  thf('162', plain,
% 6.33/6.55      ((m1_subset_1 @ (k5_lattices @ sk_A) @ (u1_struct_0 @ sk_A))),
% 6.33/6.55      inference('clc', [status(thm)], ['160', '161'])).
% 6.33/6.55  thf('163', plain,
% 6.33/6.55      ((((k5_lattices @ sk_A)
% 6.33/6.55          = (k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B))
% 6.33/6.55        | (v2_struct_0 @ sk_A))),
% 6.33/6.55      inference('demod', [status(thm)], ['48', '60', '162'])).
% 6.33/6.55  thf('164', plain,
% 6.33/6.55      (((k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)
% 6.33/6.55         != (k5_lattices @ sk_A))),
% 6.33/6.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.55  thf('165', plain, ((v2_struct_0 @ sk_A)),
% 6.33/6.55      inference('simplify_reflect-', [status(thm)], ['163', '164'])).
% 6.33/6.55  thf('166', plain, ($false), inference('demod', [status(thm)], ['0', '165'])).
% 6.33/6.55  
% 6.33/6.55  % SZS output end Refutation
% 6.33/6.55  
% 6.33/6.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
