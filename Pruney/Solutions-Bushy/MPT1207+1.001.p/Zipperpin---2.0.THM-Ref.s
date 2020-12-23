%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1207+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0WTFCjH06S

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:15 EST 2020

% Result     : Theorem 0.26s
% Output     : Refutation 0.26s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 225 expanded)
%              Number of leaves         :   29 (  82 expanded)
%              Depth                    :   10
%              Number of atoms          :  770 (2412 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(k1_lattices_type,type,(
    k1_lattices: $i > $i > $i > $i )).

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

thf(k3_lattices_type,type,(
    k3_lattices: $i > $i > $i > $i )).

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
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_lattices @ A ) )
     => ( m1_subset_1 @ ( k5_lattices @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
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

thf('2',plain,(
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

thf('3',plain,(
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
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
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
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ~ ( r1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
    | ( r3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
    | ~ ( v6_lattices @ sk_A )
    | ~ ( v8_lattices @ sk_A )
    | ~ ( v9_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
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
    ! [X2: $i] :
      ( ( l1_lattices @ X2 )
      | ~ ( l3_lattices @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('8',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

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

thf('9',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( r1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
    | ( r3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['5','8','14','20','26','27'])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( r3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
    | ~ ( r1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( r3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ~ ( r1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf(t22_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_lattices @ A )
        & ( v6_lattices @ A )
        & ( v8_lattices @ A )
        & ( v9_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( r1_lattices @ A @ B @ ( k1_lattices @ A @ B @ C ) ) ) ) ) )).

thf('35',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ( r1_lattices @ X10 @ X9 @ ( k1_lattices @ X10 @ X9 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ~ ( v9_lattices @ X10 )
      | ~ ( v8_lattices @ X10 )
      | ~ ( v6_lattices @ X10 )
      | ~ ( v5_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t22_lattices])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v5_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( k1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( k1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v5_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ~ ( v5_lattices @ sk_A )
    | ~ ( v6_lattices @ sk_A )
    | ~ ( v8_lattices @ sk_A )
    | ~ ( v9_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( r1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','37'])).

thf('39',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v5_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v5_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v5_lattices @ sk_A ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('47',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('48',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('49',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
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

thf('52',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l2_lattices @ X4 )
      | ~ ( v4_lattices @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( ( k3_lattices @ X4 @ X3 @ X5 )
        = ( k1_lattices @ X4 @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_lattices])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( ( k3_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
        = ( k1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_lattices @ X0 )
      | ~ ( l2_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l2_lattices @ X0 )
      | ~ ( v4_lattices @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k3_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
        = ( k1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 ) )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ( ( k3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
      = ( k1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) )
    | ~ ( v4_lattices @ sk_A )
    | ~ ( l2_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['50','54'])).

thf('56',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('57',plain,(
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

thf('58',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ( ( k3_lattices @ X13 @ ( k5_lattices @ X13 ) @ X12 )
        = X12 )
      | ~ ( l3_lattices @ X13 )
      | ~ ( v13_lattices @ X13 )
      | ~ ( v10_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_lattices])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v13_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v13_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
      = sk_B ) ),
    inference(demod,[status(thm)],['59','60','61','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( k3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
    = sk_B ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v4_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v4_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X2: $i] :
      ( ( l2_lattices @ X2 )
      | ~ ( l3_lattices @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('74',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','56','65','71','74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( sk_B
    = ( k1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['38','39','45','46','47','48','49','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    r1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,(
    $false ),
    inference(demod,[status(thm)],['32','80'])).


%------------------------------------------------------------------------------
