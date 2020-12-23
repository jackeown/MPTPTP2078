%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HaeGhRQMGV

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 194 expanded)
%              Number of leaves         :   29 (  72 expanded)
%              Depth                    :   11
%              Number of atoms          :  728 (2086 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_lattices_type,type,(
    k4_lattices: $i > $i > $i > $i )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v13_lattices_type,type,(
    v13_lattices: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(k5_lattices_type,type,(
    k5_lattices: $i > $i )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(t41_lattices,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v13_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r3_lattices @ A @ ( k5_lattices @ A ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v13_lattices @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( r3_lattices @ A @ ( k5_lattices @ A ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t41_lattices])).

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
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
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

thf('3',plain,(
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

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
      | ( ( k2_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
       != ( k5_lattices @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
       != ( k5_lattices @ X0 ) )
      | ( r1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ~ ( v8_lattices @ sk_A )
    | ~ ( v9_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( r1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
    | ( ( k2_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
     != ( k5_lattices @ sk_A ) ) ),
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
    ! [X2: $i] :
      ( ( l1_lattices @ X2 )
      | ~ ( l3_lattices @ X2 ) ) ),
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
      | ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
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

thf('25',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_lattices @ X4 )
      | ~ ( v6_lattices @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( ( k4_lattices @ X4 @ X3 @ X5 )
        = ( k2_lattices @ X4 @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_lattices])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
        = ( k2_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( l1_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
        = ( k2_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 ) )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ( ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
      = ( k2_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) )
    | ~ ( v6_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['23','27'])).

thf('29',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t40_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v13_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k4_lattices @ A @ ( k5_lattices @ A ) @ B )
            = ( k5_lattices @ A ) ) ) ) )).

thf('31',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ( ( k4_lattices @ X13 @ ( k5_lattices @ X13 ) @ X12 )
        = ( k5_lattices @ X13 ) )
      | ~ ( l3_lattices @ X13 )
      | ~ ( v13_lattices @ X13 )
      | ~ ( v10_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t40_lattices])).

thf('32',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v13_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
      = ( k5_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v13_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
      = ( k5_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33','34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
    = ( k5_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k5_lattices @ sk_A )
      = ( k2_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29','38','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k5_lattices @ sk_A )
    = ( k2_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
    | ( ( k5_lattices @ sk_A )
     != ( k5_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','9','15','21','22','47'])).

thf('49',plain,
    ( ( r1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

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

thf('52',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l3_lattices @ X7 )
      | ~ ( v9_lattices @ X7 )
      | ~ ( v8_lattices @ X7 )
      | ~ ( v6_lattices @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( r3_lattices @ X7 @ X6 @ X8 )
      | ~ ( r1_lattices @ X7 @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( r1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
      | ( r3_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r3_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
      | ~ ( r1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ~ ( r1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
    | ( r3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
    | ~ ( v6_lattices @ sk_A )
    | ~ ( v8_lattices @ sk_A )
    | ~ ( v9_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['50','54'])).

thf('56',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('57',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('58',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('59',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('60',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( r1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
    | ( r3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['55','56','57','58','59','60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( r3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
    | ~ ( r1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    ~ ( r3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ~ ( r1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['49','65'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['0','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HaeGhRQMGV
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:04:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 48 iterations in 0.030s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.20/0.48  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 0.20/0.48  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.20/0.48  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.20/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.48  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 0.20/0.48  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(k4_lattices_type, type, k4_lattices: $i > $i > $i > $i).
% 0.20/0.48  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(v13_lattices_type, type, v13_lattices: $i > $o).
% 0.20/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.48  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.20/0.48  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 0.20/0.48  thf(k5_lattices_type, type, k5_lattices: $i > $i).
% 0.20/0.48  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.20/0.48  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.20/0.48  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 0.20/0.48  thf(t41_lattices, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.20/0.48         ( v13_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48           ( r3_lattices @ A @ ( k5_lattices @ A ) @ B ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.20/0.48            ( v13_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.20/0.48          ( ![B:$i]:
% 0.20/0.48            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48              ( r3_lattices @ A @ ( k5_lattices @ A ) @ B ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t41_lattices])).
% 0.20/0.48  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(dt_k5_lattices, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 0.20/0.48       ( m1_subset_1 @ ( k5_lattices @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X1 : $i]:
% 0.20/0.48         ((m1_subset_1 @ (k5_lattices @ X1) @ (u1_struct_0 @ X1))
% 0.20/0.48          | ~ (l1_lattices @ X1)
% 0.20/0.48          | (v2_struct_0 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 0.20/0.48  thf(t21_lattices, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v8_lattices @ A ) & 
% 0.20/0.48         ( v9_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48               ( ( r1_lattices @ A @ B @ C ) <=>
% 0.20/0.48                 ( ( k2_lattices @ A @ B @ C ) = ( B ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.20/0.48          | ((k2_lattices @ X10 @ X9 @ X11) != (X9))
% 0.20/0.48          | (r1_lattices @ X10 @ X9 @ X11)
% 0.20/0.48          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.20/0.48          | ~ (l3_lattices @ X10)
% 0.20/0.48          | ~ (v9_lattices @ X10)
% 0.20/0.48          | ~ (v8_lattices @ X10)
% 0.20/0.48          | (v2_struct_0 @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [t21_lattices])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X0)
% 0.20/0.48          | ~ (l1_lattices @ X0)
% 0.20/0.48          | (v2_struct_0 @ X0)
% 0.20/0.48          | ~ (v8_lattices @ X0)
% 0.20/0.48          | ~ (v9_lattices @ X0)
% 0.20/0.48          | ~ (l3_lattices @ X0)
% 0.20/0.48          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.48          | (r1_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 0.20/0.48          | ((k2_lattices @ X0 @ (k5_lattices @ X0) @ X1) != (k5_lattices @ X0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((k2_lattices @ X0 @ (k5_lattices @ X0) @ X1) != (k5_lattices @ X0))
% 0.20/0.48          | (r1_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 0.20/0.48          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.48          | ~ (l3_lattices @ X0)
% 0.20/0.48          | ~ (v9_lattices @ X0)
% 0.20/0.48          | ~ (v8_lattices @ X0)
% 0.20/0.48          | ~ (l1_lattices @ X0)
% 0.20/0.48          | (v2_struct_0 @ X0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (l1_lattices @ sk_A)
% 0.20/0.48        | ~ (v8_lattices @ sk_A)
% 0.20/0.48        | ~ (v9_lattices @ sk_A)
% 0.20/0.48        | ~ (l3_lattices @ sk_A)
% 0.20/0.48        | (r1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)
% 0.20/0.48        | ((k2_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)
% 0.20/0.48            != (k5_lattices @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '5'])).
% 0.20/0.48  thf('7', plain, ((l3_lattices @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(dt_l3_lattices, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 0.20/0.48  thf('8', plain, (![X2 : $i]: ((l1_lattices @ X2) | ~ (l3_lattices @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.20/0.48  thf('9', plain, ((l1_lattices @ sk_A)),
% 0.20/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.48  thf(cc1_lattices, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l3_lattices @ A ) =>
% 0.20/0.48       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.20/0.48         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.20/0.48           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.20/0.48           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X0)
% 0.20/0.48          | ~ (v10_lattices @ X0)
% 0.20/0.48          | (v8_lattices @ X0)
% 0.20/0.48          | ~ (l3_lattices @ X0))),
% 0.20/0.48      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.20/0.48  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.48  thf('13', plain, ((l3_lattices @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('14', plain, ((v10_lattices @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('15', plain, ((v8_lattices @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X0)
% 0.20/0.48          | ~ (v10_lattices @ X0)
% 0.20/0.48          | (v9_lattices @ X0)
% 0.20/0.48          | ~ (l3_lattices @ X0))),
% 0.20/0.48      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.20/0.48  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.48  thf('19', plain, ((l3_lattices @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('20', plain, ((v10_lattices @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('21', plain, ((v9_lattices @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.20/0.48  thf('22', plain, ((l3_lattices @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('23', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (![X1 : $i]:
% 0.20/0.48         ((m1_subset_1 @ (k5_lattices @ X1) @ (u1_struct_0 @ X1))
% 0.20/0.48          | ~ (l1_lattices @ X1)
% 0.20/0.48          | (v2_struct_0 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 0.20/0.48  thf(redefinition_k4_lattices, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.20/0.48         ( l1_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.48         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48       ( ( k4_lattices @ A @ B @ C ) = ( k2_lattices @ A @ B @ C ) ) ))).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.20/0.48          | ~ (l1_lattices @ X4)
% 0.20/0.48          | ~ (v6_lattices @ X4)
% 0.20/0.48          | (v2_struct_0 @ X4)
% 0.20/0.48          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.20/0.48          | ((k4_lattices @ X4 @ X3 @ X5) = (k2_lattices @ X4 @ X3 @ X5)))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k4_lattices])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X0)
% 0.20/0.48          | ~ (l1_lattices @ X0)
% 0.20/0.48          | ((k4_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 0.20/0.48              = (k2_lattices @ X0 @ (k5_lattices @ X0) @ X1))
% 0.20/0.48          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.48          | (v2_struct_0 @ X0)
% 0.20/0.48          | ~ (v6_lattices @ X0)
% 0.20/0.48          | ~ (l1_lattices @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (v6_lattices @ X0)
% 0.20/0.48          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.48          | ((k4_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 0.20/0.48              = (k2_lattices @ X0 @ (k5_lattices @ X0) @ X1))
% 0.20/0.48          | ~ (l1_lattices @ X0)
% 0.20/0.48          | (v2_struct_0 @ X0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (l1_lattices @ sk_A)
% 0.20/0.48        | ((k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)
% 0.20/0.48            = (k2_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B))
% 0.20/0.48        | ~ (v6_lattices @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['23', '27'])).
% 0.20/0.48  thf('29', plain, ((l1_lattices @ sk_A)),
% 0.20/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.48  thf('30', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t40_lattices, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.20/0.48         ( v13_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48           ( ( k4_lattices @ A @ ( k5_lattices @ A ) @ B ) =
% 0.20/0.48             ( k5_lattices @ A ) ) ) ) ))).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      (![X12 : $i, X13 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.20/0.48          | ((k4_lattices @ X13 @ (k5_lattices @ X13) @ X12)
% 0.20/0.48              = (k5_lattices @ X13))
% 0.20/0.48          | ~ (l3_lattices @ X13)
% 0.20/0.48          | ~ (v13_lattices @ X13)
% 0.20/0.48          | ~ (v10_lattices @ X13)
% 0.20/0.48          | (v2_struct_0 @ X13))),
% 0.20/0.48      inference('cnf', [status(esa)], [t40_lattices])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (v10_lattices @ sk_A)
% 0.20/0.48        | ~ (v13_lattices @ sk_A)
% 0.20/0.48        | ~ (l3_lattices @ sk_A)
% 0.20/0.48        | ((k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)
% 0.20/0.48            = (k5_lattices @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.48  thf('33', plain, ((v10_lattices @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('34', plain, ((v13_lattices @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('35', plain, ((l3_lattices @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | ((k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)
% 0.20/0.48            = (k5_lattices @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 0.20/0.48  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      (((k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)
% 0.20/0.48         = (k5_lattices @ sk_A))),
% 0.20/0.48      inference('clc', [status(thm)], ['36', '37'])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X0)
% 0.20/0.48          | ~ (v10_lattices @ X0)
% 0.20/0.48          | (v6_lattices @ X0)
% 0.20/0.48          | ~ (l3_lattices @ X0))),
% 0.20/0.48      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.20/0.48  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('41', plain,
% 0.20/0.48      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.48  thf('42', plain, ((l3_lattices @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('43', plain, ((v10_lattices @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('44', plain, ((v6_lattices @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.20/0.48  thf('45', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | ((k5_lattices @ sk_A)
% 0.20/0.48            = (k2_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)))),
% 0.20/0.48      inference('demod', [status(thm)], ['28', '29', '38', '44'])).
% 0.20/0.48  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('47', plain,
% 0.20/0.48      (((k5_lattices @ sk_A)
% 0.20/0.48         = (k2_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B))),
% 0.20/0.48      inference('clc', [status(thm)], ['45', '46'])).
% 0.20/0.48  thf('48', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | (r1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)
% 0.20/0.48        | ((k5_lattices @ sk_A) != (k5_lattices @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['6', '9', '15', '21', '22', '47'])).
% 0.20/0.48  thf('49', plain,
% 0.20/0.48      (((r1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)
% 0.20/0.48        | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('simplify', [status(thm)], ['48'])).
% 0.20/0.48  thf('50', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('51', plain,
% 0.20/0.48      (![X1 : $i]:
% 0.20/0.48         ((m1_subset_1 @ (k5_lattices @ X1) @ (u1_struct_0 @ X1))
% 0.20/0.48          | ~ (l1_lattices @ X1)
% 0.20/0.48          | (v2_struct_0 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 0.20/0.48  thf(redefinition_r3_lattices, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.20/0.48         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 0.20/0.48         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.48         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 0.20/0.48  thf('52', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 0.20/0.48          | ~ (l3_lattices @ X7)
% 0.20/0.48          | ~ (v9_lattices @ X7)
% 0.20/0.48          | ~ (v8_lattices @ X7)
% 0.20/0.48          | ~ (v6_lattices @ X7)
% 0.20/0.48          | (v2_struct_0 @ X7)
% 0.20/0.48          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.20/0.48          | (r3_lattices @ X7 @ X6 @ X8)
% 0.20/0.48          | ~ (r1_lattices @ X7 @ X6 @ X8))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.20/0.48  thf('53', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X0)
% 0.20/0.48          | ~ (l1_lattices @ X0)
% 0.20/0.48          | ~ (r1_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 0.20/0.48          | (r3_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 0.20/0.48          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.48          | (v2_struct_0 @ X0)
% 0.20/0.48          | ~ (v6_lattices @ X0)
% 0.20/0.48          | ~ (v8_lattices @ X0)
% 0.20/0.48          | ~ (v9_lattices @ X0)
% 0.20/0.48          | ~ (l3_lattices @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.48  thf('54', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (l3_lattices @ X0)
% 0.20/0.48          | ~ (v9_lattices @ X0)
% 0.20/0.48          | ~ (v8_lattices @ X0)
% 0.20/0.48          | ~ (v6_lattices @ X0)
% 0.20/0.48          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.48          | (r3_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 0.20/0.48          | ~ (r1_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 0.20/0.48          | ~ (l1_lattices @ X0)
% 0.20/0.48          | (v2_struct_0 @ X0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['53'])).
% 0.20/0.48  thf('55', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (l1_lattices @ sk_A)
% 0.20/0.48        | ~ (r1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)
% 0.20/0.48        | (r3_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)
% 0.20/0.48        | ~ (v6_lattices @ sk_A)
% 0.20/0.48        | ~ (v8_lattices @ sk_A)
% 0.20/0.48        | ~ (v9_lattices @ sk_A)
% 0.20/0.48        | ~ (l3_lattices @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['50', '54'])).
% 0.20/0.48  thf('56', plain, ((l1_lattices @ sk_A)),
% 0.20/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.48  thf('57', plain, ((v6_lattices @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.20/0.48  thf('58', plain, ((v8_lattices @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.20/0.48  thf('59', plain, ((v9_lattices @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.20/0.48  thf('60', plain, ((l3_lattices @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('61', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (r1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)
% 0.20/0.48        | (r3_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['55', '56', '57', '58', '59', '60'])).
% 0.20/0.48  thf('62', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('63', plain,
% 0.20/0.48      (((r3_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)
% 0.20/0.48        | ~ (r1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B))),
% 0.20/0.48      inference('clc', [status(thm)], ['61', '62'])).
% 0.20/0.48  thf('64', plain, (~ (r3_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('65', plain, (~ (r1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)),
% 0.20/0.48      inference('clc', [status(thm)], ['63', '64'])).
% 0.20/0.48  thf('66', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('clc', [status(thm)], ['49', '65'])).
% 0.20/0.48  thf('67', plain, ($false), inference('demod', [status(thm)], ['0', '66'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
