%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6lC7hxSoNn

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:34 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 162 expanded)
%              Number of leaves         :   29 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :  713 (1841 expanded)
%              Number of equality atoms :   32 (  84 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(k5_lattices_type,type,(
    k5_lattices: $i > $i )).

thf(v13_lattices_type,type,(
    v13_lattices: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_lattices_type,type,(
    k1_lattices: $i > $i > $i > $i )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(k3_lattices_type,type,(
    k3_lattices: $i > $i > $i > $i )).

thf(k4_lattices_type,type,(
    k4_lattices: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

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
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
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

thf(redefinition_k4_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v6_lattices @ A )
        & ( l1_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k4_lattices @ A @ B @ C )
        = ( k2_lattices @ A @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_lattices @ X10 )
      | ~ ( v6_lattices @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( ( k4_lattices @ X10 @ X9 @ X11 )
        = ( k2_lattices @ X10 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_lattices])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
        = ( k2_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( l1_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k4_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
        = ( k2_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 ) )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ( ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 )
      = ( k2_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 ) )
    | ~ ( v6_lattices @ sk_A ) ),
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

thf('15',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 )
      = ( k2_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['5','8','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 )
    = ( k2_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X4 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_lattices @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('19',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('20',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v9_lattices @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( ( k2_lattices @ X1 @ X3 @ ( k1_lattices @ X1 @ X3 @ X2 ) )
        = X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d9_lattices])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ X0 @ sk_B_1 ) )
        = X0 )
      | ~ ( v9_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ X0 @ sk_B_1 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['21','22','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ X0 @ sk_B_1 ) )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ( ( k2_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 ) )
      = ( k5_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','31'])).

thf('33',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 ) )
      = ( k5_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k2_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 ) )
    = ( k5_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
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

thf('39',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l2_lattices @ X7 )
      | ~ ( v4_lattices @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( ( k3_lattices @ X7 @ X6 @ X8 )
        = ( k1_lattices @ X7 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_lattices])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( ( k3_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
        = ( k1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_lattices @ X0 )
      | ~ ( l2_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l2_lattices @ X0 )
      | ~ ( v4_lattices @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k3_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
        = ( k1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 ) )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ( ( k3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 )
      = ( k1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 ) )
    | ~ ( v4_lattices @ sk_A )
    | ~ ( l2_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['37','41'])).

thf('43',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('44',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
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

thf('45',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ( ( k3_lattices @ X13 @ ( k5_lattices @ X13 ) @ X12 )
        = X12 )
      | ~ ( l3_lattices @ X13 )
      | ~ ( v13_lattices @ X13 )
      | ~ ( v10_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_lattices])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v13_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v13_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 )
      = sk_B_1 ) ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 )
    = sk_B_1 ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v4_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v4_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X5: $i] :
      ( ( l2_lattices @ X5 )
      | ~ ( l3_lattices @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('61',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( k1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['42','43','52','58','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( sk_B_1
    = ( k1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k2_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 )
    = ( k5_lattices @ sk_A ) ),
    inference(demod,[status(thm)],['36','64'])).

thf('66',plain,
    ( ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 )
    = ( k5_lattices @ sk_A ) ),
    inference('sup+',[status(thm)],['17','65'])).

thf('67',plain,(
    ( k4_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 )
 != ( k5_lattices @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['66','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6lC7hxSoNn
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:30:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 58 iterations in 0.035s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.20/0.49  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 0.20/0.49  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 0.20/0.49  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.20/0.49  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.20/0.49  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.20/0.49  thf(k5_lattices_type, type, k5_lattices: $i > $i).
% 0.20/0.49  thf(v13_lattices_type, type, v13_lattices: $i > $o).
% 0.20/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.49  thf(k1_lattices_type, type, k1_lattices: $i > $i > $i > $i).
% 0.20/0.49  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.20/0.49  thf(k3_lattices_type, type, k3_lattices: $i > $i > $i > $i).
% 0.20/0.49  thf(k4_lattices_type, type, k4_lattices: $i > $i > $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.49  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.20/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.49  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.20/0.49  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.20/0.49  thf(t40_lattices, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.20/0.49         ( v13_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.49           ( ( k4_lattices @ A @ ( k5_lattices @ A ) @ B ) =
% 0.20/0.49             ( k5_lattices @ A ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.20/0.49            ( v13_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.20/0.49          ( ![B:$i]:
% 0.20/0.49            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.49              ( ( k4_lattices @ A @ ( k5_lattices @ A ) @ B ) =
% 0.20/0.49                ( k5_lattices @ A ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t40_lattices])).
% 0.20/0.49  thf('0', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(dt_k5_lattices, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 0.20/0.49       ( m1_subset_1 @ ( k5_lattices @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X4 : $i]:
% 0.20/0.49         ((m1_subset_1 @ (k5_lattices @ X4) @ (u1_struct_0 @ X4))
% 0.20/0.49          | ~ (l1_lattices @ X4)
% 0.20/0.49          | (v2_struct_0 @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 0.20/0.49  thf(redefinition_k4_lattices, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.20/0.49         ( l1_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.49         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49       ( ( k4_lattices @ A @ B @ C ) = ( k2_lattices @ A @ B @ C ) ) ))).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.20/0.49          | ~ (l1_lattices @ X10)
% 0.20/0.49          | ~ (v6_lattices @ X10)
% 0.20/0.49          | (v2_struct_0 @ X10)
% 0.20/0.49          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.20/0.49          | ((k4_lattices @ X10 @ X9 @ X11) = (k2_lattices @ X10 @ X9 @ X11)))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k4_lattices])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((v2_struct_0 @ X0)
% 0.20/0.49          | ~ (l1_lattices @ X0)
% 0.20/0.49          | ((k4_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 0.20/0.49              = (k2_lattices @ X0 @ (k5_lattices @ X0) @ X1))
% 0.20/0.49          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.49          | (v2_struct_0 @ X0)
% 0.20/0.49          | ~ (v6_lattices @ X0)
% 0.20/0.49          | ~ (l1_lattices @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (v6_lattices @ X0)
% 0.20/0.49          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.49          | ((k4_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 0.20/0.49              = (k2_lattices @ X0 @ (k5_lattices @ X0) @ X1))
% 0.20/0.49          | ~ (l1_lattices @ X0)
% 0.20/0.49          | (v2_struct_0 @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | ~ (l1_lattices @ sk_A)
% 0.20/0.49        | ((k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_1)
% 0.20/0.49            = (k2_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_1))
% 0.20/0.49        | ~ (v6_lattices @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '4'])).
% 0.20/0.49  thf('6', plain, ((l3_lattices @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(dt_l3_lattices, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 0.20/0.49  thf('7', plain, (![X5 : $i]: ((l1_lattices @ X5) | ~ (l3_lattices @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.20/0.49  thf('8', plain, ((l1_lattices @ sk_A)),
% 0.20/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.49  thf(cc1_lattices, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( l3_lattices @ A ) =>
% 0.20/0.49       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.20/0.49         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.20/0.49           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.20/0.49           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ X0)
% 0.20/0.49          | ~ (v10_lattices @ X0)
% 0.20/0.49          | (v6_lattices @ X0)
% 0.20/0.49          | ~ (l3_lattices @ X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.20/0.49  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.49  thf('12', plain, ((l3_lattices @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('13', plain, ((v10_lattices @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('14', plain, ((v6_lattices @ sk_A)),
% 0.20/0.49      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | ((k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_1)
% 0.20/0.49            = (k2_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_1)))),
% 0.20/0.49      inference('demod', [status(thm)], ['5', '8', '14'])).
% 0.20/0.49  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (((k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_1)
% 0.20/0.49         = (k2_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_1))),
% 0.20/0.49      inference('clc', [status(thm)], ['15', '16'])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X4 : $i]:
% 0.20/0.49         ((m1_subset_1 @ (k5_lattices @ X4) @ (u1_struct_0 @ X4))
% 0.20/0.49          | ~ (l1_lattices @ X4)
% 0.20/0.49          | (v2_struct_0 @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 0.20/0.49  thf('19', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(d9_lattices, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.20/0.49       ( ( v9_lattices @ A ) <=>
% 0.20/0.49         ( ![B:$i]:
% 0.20/0.49           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.49             ( ![C:$i]:
% 0.20/0.49               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.49                 ( ( k2_lattices @ A @ B @ ( k1_lattices @ A @ B @ C ) ) =
% 0.20/0.49                   ( B ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         (~ (v9_lattices @ X1)
% 0.20/0.49          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.49          | ((k2_lattices @ X1 @ X3 @ (k1_lattices @ X1 @ X3 @ X2)) = (X3))
% 0.20/0.49          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.20/0.49          | ~ (l3_lattices @ X1)
% 0.20/0.49          | (v2_struct_0 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d9_lattices])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_A)
% 0.20/0.49          | ~ (l3_lattices @ sk_A)
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49          | ((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ X0 @ sk_B_1))
% 0.20/0.49              = (X0))
% 0.20/0.49          | ~ (v9_lattices @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.49  thf('22', plain, ((l3_lattices @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ X0)
% 0.20/0.49          | ~ (v10_lattices @ X0)
% 0.20/0.49          | (v9_lattices @ X0)
% 0.20/0.49          | ~ (l3_lattices @ X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.20/0.49  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.49  thf('26', plain, ((l3_lattices @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('27', plain, ((v10_lattices @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('28', plain, ((v9_lattices @ sk_A)),
% 0.20/0.49      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_A)
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49          | ((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ X0 @ sk_B_1))
% 0.20/0.49              = (X0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['21', '22', '28'])).
% 0.20/0.49  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ X0 @ sk_B_1))
% 0.20/0.49            = (X0))
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('clc', [status(thm)], ['29', '30'])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | ~ (l1_lattices @ sk_A)
% 0.20/0.49        | ((k2_lattices @ sk_A @ (k5_lattices @ sk_A) @ 
% 0.20/0.49            (k1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_1))
% 0.20/0.49            = (k5_lattices @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['18', '31'])).
% 0.20/0.49  thf('33', plain, ((l1_lattices @ sk_A)),
% 0.20/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | ((k2_lattices @ sk_A @ (k5_lattices @ sk_A) @ 
% 0.20/0.49            (k1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_1))
% 0.20/0.49            = (k5_lattices @ sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.49  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      (((k2_lattices @ sk_A @ (k5_lattices @ sk_A) @ 
% 0.20/0.49         (k1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_1))
% 0.20/0.49         = (k5_lattices @ sk_A))),
% 0.20/0.49      inference('clc', [status(thm)], ['34', '35'])).
% 0.20/0.49  thf('37', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      (![X4 : $i]:
% 0.20/0.49         ((m1_subset_1 @ (k5_lattices @ X4) @ (u1_struct_0 @ X4))
% 0.20/0.49          | ~ (l1_lattices @ X4)
% 0.20/0.49          | (v2_struct_0 @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 0.20/0.49  thf(redefinition_k3_lattices, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.20/0.49         ( l2_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.49         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49       ( ( k3_lattices @ A @ B @ C ) = ( k1_lattices @ A @ B @ C ) ) ))).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 0.20/0.49          | ~ (l2_lattices @ X7)
% 0.20/0.49          | ~ (v4_lattices @ X7)
% 0.20/0.49          | (v2_struct_0 @ X7)
% 0.20/0.49          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.20/0.49          | ((k3_lattices @ X7 @ X6 @ X8) = (k1_lattices @ X7 @ X6 @ X8)))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k3_lattices])).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((v2_struct_0 @ X0)
% 0.20/0.49          | ~ (l1_lattices @ X0)
% 0.20/0.49          | ((k3_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 0.20/0.49              = (k1_lattices @ X0 @ (k5_lattices @ X0) @ X1))
% 0.20/0.49          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.49          | (v2_struct_0 @ X0)
% 0.20/0.49          | ~ (v4_lattices @ X0)
% 0.20/0.49          | ~ (l2_lattices @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.49  thf('41', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (l2_lattices @ X0)
% 0.20/0.49          | ~ (v4_lattices @ X0)
% 0.20/0.49          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.49          | ((k3_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 0.20/0.49              = (k1_lattices @ X0 @ (k5_lattices @ X0) @ X1))
% 0.20/0.49          | ~ (l1_lattices @ X0)
% 0.20/0.49          | (v2_struct_0 @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['40'])).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | ~ (l1_lattices @ sk_A)
% 0.20/0.49        | ((k3_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_1)
% 0.20/0.49            = (k1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_1))
% 0.20/0.49        | ~ (v4_lattices @ sk_A)
% 0.20/0.49        | ~ (l2_lattices @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['37', '41'])).
% 0.20/0.49  thf('43', plain, ((l1_lattices @ sk_A)),
% 0.20/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.49  thf('44', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t39_lattices, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.20/0.49         ( v13_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.49           ( ( k3_lattices @ A @ ( k5_lattices @ A ) @ B ) = ( B ) ) ) ) ))).
% 0.20/0.49  thf('45', plain,
% 0.20/0.49      (![X12 : $i, X13 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.20/0.49          | ((k3_lattices @ X13 @ (k5_lattices @ X13) @ X12) = (X12))
% 0.20/0.49          | ~ (l3_lattices @ X13)
% 0.20/0.49          | ~ (v13_lattices @ X13)
% 0.20/0.49          | ~ (v10_lattices @ X13)
% 0.20/0.49          | (v2_struct_0 @ X13))),
% 0.20/0.49      inference('cnf', [status(esa)], [t39_lattices])).
% 0.20/0.49  thf('46', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | ~ (v10_lattices @ sk_A)
% 0.20/0.49        | ~ (v13_lattices @ sk_A)
% 0.20/0.49        | ~ (l3_lattices @ sk_A)
% 0.20/0.49        | ((k3_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_1) = (sk_B_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.49  thf('47', plain, ((v10_lattices @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('48', plain, ((v13_lattices @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('49', plain, ((l3_lattices @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('50', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | ((k3_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_1) = (sk_B_1)))),
% 0.20/0.49      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 0.20/0.49  thf('51', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('52', plain,
% 0.20/0.49      (((k3_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_1) = (sk_B_1))),
% 0.20/0.49      inference('clc', [status(thm)], ['50', '51'])).
% 0.20/0.49  thf('53', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ X0)
% 0.20/0.49          | ~ (v10_lattices @ X0)
% 0.20/0.49          | (v4_lattices @ X0)
% 0.20/0.49          | ~ (l3_lattices @ X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.20/0.49  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('55', plain,
% 0.20/0.49      ((~ (l3_lattices @ sk_A) | (v4_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.49  thf('56', plain, ((l3_lattices @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('57', plain, ((v10_lattices @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('58', plain, ((v4_lattices @ sk_A)),
% 0.20/0.49      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.20/0.49  thf('59', plain, ((l3_lattices @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('60', plain, (![X5 : $i]: ((l2_lattices @ X5) | ~ (l3_lattices @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.20/0.49  thf('61', plain, ((l2_lattices @ sk_A)),
% 0.20/0.49      inference('sup-', [status(thm)], ['59', '60'])).
% 0.20/0.49  thf('62', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | ((sk_B_1) = (k1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_1)))),
% 0.20/0.49      inference('demod', [status(thm)], ['42', '43', '52', '58', '61'])).
% 0.20/0.49  thf('63', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('64', plain,
% 0.20/0.49      (((sk_B_1) = (k1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_1))),
% 0.20/0.49      inference('clc', [status(thm)], ['62', '63'])).
% 0.20/0.49  thf('65', plain,
% 0.20/0.49      (((k2_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_1)
% 0.20/0.49         = (k5_lattices @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['36', '64'])).
% 0.20/0.49  thf('66', plain,
% 0.20/0.49      (((k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_1)
% 0.20/0.49         = (k5_lattices @ sk_A))),
% 0.20/0.49      inference('sup+', [status(thm)], ['17', '65'])).
% 0.20/0.49  thf('67', plain,
% 0.20/0.49      (((k4_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_1)
% 0.20/0.49         != (k5_lattices @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('68', plain, ($false),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['66', '67'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
