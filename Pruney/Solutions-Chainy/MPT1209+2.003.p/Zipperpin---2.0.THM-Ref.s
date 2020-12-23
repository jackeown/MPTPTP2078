%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9MvKrS4Eob

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 276 expanded)
%              Number of leaves         :   32 (  96 expanded)
%              Depth                    :   12
%              Number of atoms          : 1076 (3284 expanded)
%              Number of equality atoms :   43 ( 139 expanded)
%              Maximal formula depth    :   15 (   5 average)

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

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_lattices_type,type,(
    k3_lattices: $i > $i > $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(v14_lattices_type,type,(
    v14_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_lattices_type,type,(
    k6_lattices: $i > $i )).

thf(k4_lattices_type,type,(
    k4_lattices: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t44_lattices,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v14_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k3_lattices @ A @ ( k6_lattices @ A ) @ B )
            = ( k6_lattices @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v14_lattices @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( k3_lattices @ A @ ( k6_lattices @ A ) @ B )
              = ( k6_lattices @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_lattices])).

thf('0',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l2_lattices @ A ) )
     => ( m1_subset_1 @ ( k6_lattices @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k6_lattices @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( l2_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_lattices])).

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

thf('2',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v8_lattices @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( ( k1_lattices @ X4 @ ( k2_lattices @ X4 @ X6 @ X5 ) @ X5 )
        = X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l3_lattices @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_lattices])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k1_lattices @ X0 @ ( k2_lattices @ X0 @ X1 @ ( k6_lattices @ X0 ) ) @ ( k6_lattices @ X0 ) )
        = ( k6_lattices @ X0 ) )
      | ~ ( v8_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v8_lattices @ X0 )
      | ( ( k1_lattices @ X0 @ ( k2_lattices @ X0 @ X1 @ ( k6_lattices @ X0 ) ) @ ( k6_lattices @ X0 ) )
        = ( k6_lattices @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) ) @ ( k6_lattices @ sk_A ) )
      = ( k6_lattices @ sk_A ) )
    | ~ ( v8_lattices @ sk_A ) ),
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
    ! [X8: $i] :
      ( ( l2_lattices @ X8 )
      | ~ ( l3_lattices @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('8',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
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

thf('16',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) ) @ ( k6_lattices @ sk_A ) )
      = ( k6_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','8','9','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) ) @ ( k6_lattices @ sk_A ) )
    = ( k6_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k6_lattices @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( l2_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_lattices])).

thf('20',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('21',plain,(
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

thf('22',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ sk_B_1 @ X0 )
        = sk_B_1 )
      | ~ ( r1_lattices @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ sk_B_1 @ X0 )
        = sk_B_1 )
      | ~ ( r1_lattices @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23','29','30'])).

thf('32',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ~ ( r1_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
    | ( ( k2_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
      = sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','31'])).

thf('33',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( r1_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
    | ( ( k2_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
      = sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k2_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
      = sk_B_1 )
    | ~ ( r1_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ~ ( r1_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
    | ( ( k2_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
      = sk_B_1 ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k6_lattices @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( l2_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_lattices])).

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

thf('40',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ( r1_lattices @ X16 @ ( k4_lattices @ X16 @ X15 @ X17 ) @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l3_lattices @ X16 )
      | ~ ( v8_lattices @ X16 )
      | ~ ( v6_lattices @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t23_lattices])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k4_lattices @ X0 @ ( k6_lattices @ X0 ) @ X1 ) @ ( k6_lattices @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattices @ X0 @ ( k4_lattices @ X0 @ ( k6_lattices @ X0 ) @ X1 ) @ ( k6_lattices @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ~ ( v6_lattices @ sk_A )
    | ~ ( v8_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_B_1 ) @ ( k6_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','42'])).

thf('44',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('52',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t43_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v14_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k4_lattices @ A @ ( k6_lattices @ A ) @ B )
            = B ) ) ) )).

thf('54',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ( ( k4_lattices @ X19 @ ( k6_lattices @ X19 ) @ X18 )
        = X18 )
      | ~ ( l3_lattices @ X19 )
      | ~ ( v14_lattices @ X19 )
      | ~ ( v10_lattices @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t43_lattices])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v14_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k4_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_B_1 )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v14_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_B_1 )
      = sk_B_1 ) ),
    inference(demod,[status(thm)],['55','56','57','58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( k4_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_B_1 )
    = sk_B_1 ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44','50','51','52','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    r1_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k2_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['37','64'])).

thf('66',plain,
    ( ( k1_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
    = ( k6_lattices @ sk_A ) ),
    inference(demod,[status(thm)],['18','65'])).

thf('67',plain,(
    ( k3_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_B_1 )
 != ( k6_lattices @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k6_lattices @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( l2_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_lattices])).

thf('69',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
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

thf('70',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l2_lattices @ X2 )
      | ~ ( v4_lattices @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( ( k3_lattices @ X2 @ X1 @ X3 )
        = ( k3_lattices @ X2 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_lattices])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v4_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v4_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['71','77','78'])).

thf('80',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ( ( k3_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
      = ( k3_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['68','81'])).

thf('83',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
      = ( k3_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( k3_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
    = ( k3_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,(
    ( k3_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
 != ( k6_lattices @ sk_A ) ),
    inference(demod,[status(thm)],['67','86'])).

thf('88',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k6_lattices @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( l2_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_lattices])).

thf('89',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
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

thf('90',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l2_lattices @ X10 )
      | ~ ( v4_lattices @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( ( k3_lattices @ X10 @ X9 @ X11 )
        = ( k1_lattices @ X10 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_lattices])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k1_lattices @ sk_A @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('93',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k1_lattices @ sk_A @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k1_lattices @ sk_A @ sk_B_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ( ( k3_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
      = ( k1_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['88','96'])).

thf('98',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
      = ( k1_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( k3_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
    = ( k1_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,(
    ( k1_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
 != ( k6_lattices @ sk_A ) ),
    inference(demod,[status(thm)],['87','101'])).

thf('103',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['66','102'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9MvKrS4Eob
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:39:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 77 iterations in 0.054s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.20/0.50  thf(k1_lattices_type, type, k1_lattices: $i > $i > $i > $i).
% 0.20/0.50  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.20/0.50  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.20/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.50  thf(k3_lattices_type, type, k3_lattices: $i > $i > $i > $i).
% 0.20/0.50  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.20/0.50  thf(v14_lattices_type, type, v14_lattices: $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k6_lattices_type, type, k6_lattices: $i > $i).
% 0.20/0.50  thf(k4_lattices_type, type, k4_lattices: $i > $i > $i > $i).
% 0.20/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.50  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.20/0.50  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 0.20/0.50  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.20/0.50  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 0.20/0.50  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.20/0.50  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.20/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.50  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 0.20/0.50  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(t44_lattices, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.20/0.50         ( v14_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50           ( ( k3_lattices @ A @ ( k6_lattices @ A ) @ B ) =
% 0.20/0.50             ( k6_lattices @ A ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.20/0.50            ( v14_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.20/0.50          ( ![B:$i]:
% 0.20/0.50            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50              ( ( k3_lattices @ A @ ( k6_lattices @ A ) @ B ) =
% 0.20/0.50                ( k6_lattices @ A ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t44_lattices])).
% 0.20/0.50  thf('0', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(dt_k6_lattices, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l2_lattices @ A ) ) =>
% 0.20/0.50       ( m1_subset_1 @ ( k6_lattices @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X7 : $i]:
% 0.20/0.50         ((m1_subset_1 @ (k6_lattices @ X7) @ (u1_struct_0 @ X7))
% 0.20/0.50          | ~ (l2_lattices @ X7)
% 0.20/0.50          | (v2_struct_0 @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k6_lattices])).
% 0.20/0.50  thf(d8_lattices, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.20/0.50       ( ( v8_lattices @ A ) <=>
% 0.20/0.50         ( ![B:$i]:
% 0.20/0.50           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50             ( ![C:$i]:
% 0.20/0.50               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50                 ( ( k1_lattices @ A @ ( k2_lattices @ A @ B @ C ) @ C ) =
% 0.20/0.50                   ( C ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.50         (~ (v8_lattices @ X4)
% 0.20/0.50          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.20/0.50          | ((k1_lattices @ X4 @ (k2_lattices @ X4 @ X6 @ X5) @ X5) = (X5))
% 0.20/0.50          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X4))
% 0.20/0.50          | ~ (l3_lattices @ X4)
% 0.20/0.50          | (v2_struct_0 @ X4))),
% 0.20/0.50      inference('cnf', [status(esa)], [d8_lattices])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X0)
% 0.20/0.50          | ~ (l2_lattices @ X0)
% 0.20/0.50          | (v2_struct_0 @ X0)
% 0.20/0.50          | ~ (l3_lattices @ X0)
% 0.20/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.50          | ((k1_lattices @ X0 @ 
% 0.20/0.50              (k2_lattices @ X0 @ X1 @ (k6_lattices @ X0)) @ (k6_lattices @ X0))
% 0.20/0.50              = (k6_lattices @ X0))
% 0.20/0.50          | ~ (v8_lattices @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (v8_lattices @ X0)
% 0.20/0.50          | ((k1_lattices @ X0 @ 
% 0.20/0.50              (k2_lattices @ X0 @ X1 @ (k6_lattices @ X0)) @ (k6_lattices @ X0))
% 0.20/0.50              = (k6_lattices @ X0))
% 0.20/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.50          | ~ (l3_lattices @ X0)
% 0.20/0.50          | ~ (l2_lattices @ X0)
% 0.20/0.50          | (v2_struct_0 @ X0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ~ (l2_lattices @ sk_A)
% 0.20/0.50        | ~ (l3_lattices @ sk_A)
% 0.20/0.50        | ((k1_lattices @ sk_A @ 
% 0.20/0.50            (k2_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A)) @ 
% 0.20/0.50            (k6_lattices @ sk_A)) = (k6_lattices @ sk_A))
% 0.20/0.50        | ~ (v8_lattices @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '4'])).
% 0.20/0.50  thf('6', plain, ((l3_lattices @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(dt_l3_lattices, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 0.20/0.50  thf('7', plain, (![X8 : $i]: ((l2_lattices @ X8) | ~ (l3_lattices @ X8))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.20/0.50  thf('8', plain, ((l2_lattices @ sk_A)),
% 0.20/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf('9', plain, ((l3_lattices @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(cc1_lattices, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l3_lattices @ A ) =>
% 0.20/0.50       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.20/0.50         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.20/0.50           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.20/0.50           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X0)
% 0.20/0.50          | ~ (v10_lattices @ X0)
% 0.20/0.50          | (v8_lattices @ X0)
% 0.20/0.50          | ~ (l3_lattices @ X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.20/0.50  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.50  thf('13', plain, ((l3_lattices @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('14', plain, ((v10_lattices @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('15', plain, ((v8_lattices @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ((k1_lattices @ sk_A @ 
% 0.20/0.50            (k2_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A)) @ 
% 0.20/0.50            (k6_lattices @ sk_A)) = (k6_lattices @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['5', '8', '9', '15'])).
% 0.20/0.50  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (((k1_lattices @ sk_A @ 
% 0.20/0.50         (k2_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A)) @ 
% 0.20/0.50         (k6_lattices @ sk_A)) = (k6_lattices @ sk_A))),
% 0.20/0.50      inference('clc', [status(thm)], ['16', '17'])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X7 : $i]:
% 0.20/0.50         ((m1_subset_1 @ (k6_lattices @ X7) @ (u1_struct_0 @ X7))
% 0.20/0.50          | ~ (l2_lattices @ X7)
% 0.20/0.50          | (v2_struct_0 @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k6_lattices])).
% 0.20/0.50  thf('20', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t21_lattices, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v8_lattices @ A ) & 
% 0.20/0.50         ( v9_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50               ( ( r1_lattices @ A @ B @ C ) <=>
% 0.20/0.50                 ( ( k2_lattices @ A @ B @ C ) = ( B ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.20/0.50          | ~ (r1_lattices @ X13 @ X12 @ X14)
% 0.20/0.50          | ((k2_lattices @ X13 @ X12 @ X14) = (X12))
% 0.20/0.50          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.20/0.50          | ~ (l3_lattices @ X13)
% 0.20/0.50          | ~ (v9_lattices @ X13)
% 0.20/0.50          | ~ (v8_lattices @ X13)
% 0.20/0.50          | (v2_struct_0 @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [t21_lattices])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (v8_lattices @ sk_A)
% 0.20/0.50          | ~ (v9_lattices @ sk_A)
% 0.20/0.50          | ~ (l3_lattices @ sk_A)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | ((k2_lattices @ sk_A @ sk_B_1 @ X0) = (sk_B_1))
% 0.20/0.50          | ~ (r1_lattices @ sk_A @ sk_B_1 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.50  thf('23', plain, ((v8_lattices @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X0)
% 0.20/0.50          | ~ (v10_lattices @ X0)
% 0.20/0.50          | (v9_lattices @ X0)
% 0.20/0.50          | ~ (l3_lattices @ X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.20/0.50  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.50  thf('27', plain, ((l3_lattices @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('28', plain, ((v10_lattices @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('29', plain, ((v9_lattices @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.20/0.50  thf('30', plain, ((l3_lattices @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | ((k2_lattices @ sk_A @ sk_B_1 @ X0) = (sk_B_1))
% 0.20/0.50          | ~ (r1_lattices @ sk_A @ sk_B_1 @ X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['22', '23', '29', '30'])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ~ (l2_lattices @ sk_A)
% 0.20/0.50        | ~ (r1_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A))
% 0.20/0.50        | ((k2_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A)) = (sk_B_1))
% 0.20/0.50        | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['19', '31'])).
% 0.20/0.50  thf('33', plain, ((l2_lattices @ sk_A)),
% 0.20/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ~ (r1_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A))
% 0.20/0.50        | ((k2_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A)) = (sk_B_1))
% 0.20/0.50        | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      ((((k2_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A)) = (sk_B_1))
% 0.20/0.50        | ~ (r1_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A))
% 0.20/0.50        | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('simplify', [status(thm)], ['34'])).
% 0.20/0.50  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      ((~ (r1_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A))
% 0.20/0.50        | ((k2_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A)) = (sk_B_1)))),
% 0.20/0.50      inference('clc', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf('38', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      (![X7 : $i]:
% 0.20/0.50         ((m1_subset_1 @ (k6_lattices @ X7) @ (u1_struct_0 @ X7))
% 0.20/0.50          | ~ (l2_lattices @ X7)
% 0.20/0.50          | (v2_struct_0 @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k6_lattices])).
% 0.20/0.50  thf(t23_lattices, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.20/0.50         ( v8_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50               ( r1_lattices @ A @ ( k4_lattices @ A @ B @ C ) @ B ) ) ) ) ) ))).
% 0.20/0.50  thf('40', plain,
% 0.20/0.50      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 0.20/0.50          | (r1_lattices @ X16 @ (k4_lattices @ X16 @ X15 @ X17) @ X15)
% 0.20/0.50          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.20/0.50          | ~ (l3_lattices @ X16)
% 0.20/0.50          | ~ (v8_lattices @ X16)
% 0.20/0.50          | ~ (v6_lattices @ X16)
% 0.20/0.50          | (v2_struct_0 @ X16))),
% 0.20/0.50      inference('cnf', [status(esa)], [t23_lattices])).
% 0.20/0.50  thf('41', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X0)
% 0.20/0.50          | ~ (l2_lattices @ X0)
% 0.20/0.50          | (v2_struct_0 @ X0)
% 0.20/0.50          | ~ (v6_lattices @ X0)
% 0.20/0.50          | ~ (v8_lattices @ X0)
% 0.20/0.50          | ~ (l3_lattices @ X0)
% 0.20/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.50          | (r1_lattices @ X0 @ (k4_lattices @ X0 @ (k6_lattices @ X0) @ X1) @ 
% 0.20/0.50             (k6_lattices @ X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r1_lattices @ X0 @ (k4_lattices @ X0 @ (k6_lattices @ X0) @ X1) @ 
% 0.20/0.50           (k6_lattices @ X0))
% 0.20/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.50          | ~ (l3_lattices @ X0)
% 0.20/0.50          | ~ (v8_lattices @ X0)
% 0.20/0.50          | ~ (v6_lattices @ X0)
% 0.20/0.50          | ~ (l2_lattices @ X0)
% 0.20/0.50          | (v2_struct_0 @ X0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['41'])).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ~ (l2_lattices @ sk_A)
% 0.20/0.50        | ~ (v6_lattices @ sk_A)
% 0.20/0.50        | ~ (v8_lattices @ sk_A)
% 0.20/0.50        | ~ (l3_lattices @ sk_A)
% 0.20/0.50        | (r1_lattices @ sk_A @ 
% 0.20/0.50           (k4_lattices @ sk_A @ (k6_lattices @ sk_A) @ sk_B_1) @ 
% 0.20/0.50           (k6_lattices @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['38', '42'])).
% 0.20/0.50  thf('44', plain, ((l2_lattices @ sk_A)),
% 0.20/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X0)
% 0.20/0.50          | ~ (v10_lattices @ X0)
% 0.20/0.50          | (v6_lattices @ X0)
% 0.20/0.50          | ~ (l3_lattices @ X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.20/0.50  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('47', plain,
% 0.20/0.50      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.50  thf('48', plain, ((l3_lattices @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('49', plain, ((v10_lattices @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('50', plain, ((v6_lattices @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.20/0.50  thf('51', plain, ((v8_lattices @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.20/0.50  thf('52', plain, ((l3_lattices @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('53', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t43_lattices, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.20/0.50         ( v14_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50           ( ( k4_lattices @ A @ ( k6_lattices @ A ) @ B ) = ( B ) ) ) ) ))).
% 0.20/0.50  thf('54', plain,
% 0.20/0.50      (![X18 : $i, X19 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.20/0.50          | ((k4_lattices @ X19 @ (k6_lattices @ X19) @ X18) = (X18))
% 0.20/0.50          | ~ (l3_lattices @ X19)
% 0.20/0.50          | ~ (v14_lattices @ X19)
% 0.20/0.50          | ~ (v10_lattices @ X19)
% 0.20/0.50          | (v2_struct_0 @ X19))),
% 0.20/0.50      inference('cnf', [status(esa)], [t43_lattices])).
% 0.20/0.50  thf('55', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ~ (v10_lattices @ sk_A)
% 0.20/0.50        | ~ (v14_lattices @ sk_A)
% 0.20/0.50        | ~ (l3_lattices @ sk_A)
% 0.20/0.50        | ((k4_lattices @ sk_A @ (k6_lattices @ sk_A) @ sk_B_1) = (sk_B_1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.50  thf('56', plain, ((v10_lattices @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('57', plain, ((v14_lattices @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('58', plain, ((l3_lattices @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('59', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ((k4_lattices @ sk_A @ (k6_lattices @ sk_A) @ sk_B_1) = (sk_B_1)))),
% 0.20/0.50      inference('demod', [status(thm)], ['55', '56', '57', '58'])).
% 0.20/0.50  thf('60', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('61', plain,
% 0.20/0.50      (((k4_lattices @ sk_A @ (k6_lattices @ sk_A) @ sk_B_1) = (sk_B_1))),
% 0.20/0.50      inference('clc', [status(thm)], ['59', '60'])).
% 0.20/0.50  thf('62', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | (r1_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['43', '44', '50', '51', '52', '61'])).
% 0.20/0.50  thf('63', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('64', plain, ((r1_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A))),
% 0.20/0.50      inference('clc', [status(thm)], ['62', '63'])).
% 0.20/0.50  thf('65', plain,
% 0.20/0.50      (((k2_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A)) = (sk_B_1))),
% 0.20/0.50      inference('demod', [status(thm)], ['37', '64'])).
% 0.20/0.50  thf('66', plain,
% 0.20/0.50      (((k1_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A))
% 0.20/0.50         = (k6_lattices @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['18', '65'])).
% 0.20/0.50  thf('67', plain,
% 0.20/0.50      (((k3_lattices @ sk_A @ (k6_lattices @ sk_A) @ sk_B_1)
% 0.20/0.50         != (k6_lattices @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('68', plain,
% 0.20/0.50      (![X7 : $i]:
% 0.20/0.50         ((m1_subset_1 @ (k6_lattices @ X7) @ (u1_struct_0 @ X7))
% 0.20/0.50          | ~ (l2_lattices @ X7)
% 0.20/0.50          | (v2_struct_0 @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k6_lattices])).
% 0.20/0.50  thf('69', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(commutativity_k3_lattices, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.20/0.50         ( l2_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.50         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50       ( ( k3_lattices @ A @ B @ C ) = ( k3_lattices @ A @ C @ B ) ) ))).
% 0.20/0.50  thf('70', plain,
% 0.20/0.50      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.20/0.50          | ~ (l2_lattices @ X2)
% 0.20/0.50          | ~ (v4_lattices @ X2)
% 0.20/0.50          | (v2_struct_0 @ X2)
% 0.20/0.50          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.20/0.50          | ((k3_lattices @ X2 @ X1 @ X3) = (k3_lattices @ X2 @ X3 @ X1)))),
% 0.20/0.50      inference('cnf', [status(esa)], [commutativity_k3_lattices])).
% 0.20/0.50  thf('71', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k3_lattices @ sk_A @ sk_B_1 @ X0)
% 0.20/0.50            = (k3_lattices @ sk_A @ X0 @ sk_B_1))
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | (v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (v4_lattices @ sk_A)
% 0.20/0.50          | ~ (l2_lattices @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['69', '70'])).
% 0.20/0.50  thf('72', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X0)
% 0.20/0.50          | ~ (v10_lattices @ X0)
% 0.20/0.50          | (v4_lattices @ X0)
% 0.20/0.50          | ~ (l3_lattices @ X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.20/0.50  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('74', plain,
% 0.20/0.50      ((~ (l3_lattices @ sk_A) | (v4_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['72', '73'])).
% 0.20/0.50  thf('75', plain, ((l3_lattices @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('76', plain, ((v10_lattices @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('77', plain, ((v4_lattices @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.20/0.50  thf('78', plain, ((l2_lattices @ sk_A)),
% 0.20/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf('79', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k3_lattices @ sk_A @ sk_B_1 @ X0)
% 0.20/0.50            = (k3_lattices @ sk_A @ X0 @ sk_B_1))
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['71', '77', '78'])).
% 0.20/0.50  thf('80', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('81', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | ((k3_lattices @ sk_A @ sk_B_1 @ X0)
% 0.20/0.50              = (k3_lattices @ sk_A @ X0 @ sk_B_1)))),
% 0.20/0.50      inference('clc', [status(thm)], ['79', '80'])).
% 0.20/0.50  thf('82', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ~ (l2_lattices @ sk_A)
% 0.20/0.50        | ((k3_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A))
% 0.20/0.50            = (k3_lattices @ sk_A @ (k6_lattices @ sk_A) @ sk_B_1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['68', '81'])).
% 0.20/0.50  thf('83', plain, ((l2_lattices @ sk_A)),
% 0.20/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf('84', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ((k3_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A))
% 0.20/0.50            = (k3_lattices @ sk_A @ (k6_lattices @ sk_A) @ sk_B_1)))),
% 0.20/0.50      inference('demod', [status(thm)], ['82', '83'])).
% 0.20/0.50  thf('85', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('86', plain,
% 0.20/0.50      (((k3_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A))
% 0.20/0.50         = (k3_lattices @ sk_A @ (k6_lattices @ sk_A) @ sk_B_1))),
% 0.20/0.50      inference('clc', [status(thm)], ['84', '85'])).
% 0.20/0.50  thf('87', plain,
% 0.20/0.50      (((k3_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A))
% 0.20/0.50         != (k6_lattices @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['67', '86'])).
% 0.20/0.50  thf('88', plain,
% 0.20/0.50      (![X7 : $i]:
% 0.20/0.50         ((m1_subset_1 @ (k6_lattices @ X7) @ (u1_struct_0 @ X7))
% 0.20/0.50          | ~ (l2_lattices @ X7)
% 0.20/0.50          | (v2_struct_0 @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k6_lattices])).
% 0.20/0.50  thf('89', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(redefinition_k3_lattices, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.20/0.50         ( l2_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.50         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50       ( ( k3_lattices @ A @ B @ C ) = ( k1_lattices @ A @ B @ C ) ) ))).
% 0.20/0.50  thf('90', plain,
% 0.20/0.50      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.20/0.50          | ~ (l2_lattices @ X10)
% 0.20/0.50          | ~ (v4_lattices @ X10)
% 0.20/0.50          | (v2_struct_0 @ X10)
% 0.20/0.50          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.20/0.50          | ((k3_lattices @ X10 @ X9 @ X11) = (k1_lattices @ X10 @ X9 @ X11)))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k3_lattices])).
% 0.20/0.50  thf('91', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k3_lattices @ sk_A @ sk_B_1 @ X0)
% 0.20/0.50            = (k1_lattices @ sk_A @ sk_B_1 @ X0))
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | (v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (v4_lattices @ sk_A)
% 0.20/0.50          | ~ (l2_lattices @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['89', '90'])).
% 0.20/0.50  thf('92', plain, ((v4_lattices @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.20/0.50  thf('93', plain, ((l2_lattices @ sk_A)),
% 0.20/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf('94', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k3_lattices @ sk_A @ sk_B_1 @ X0)
% 0.20/0.50            = (k1_lattices @ sk_A @ sk_B_1 @ X0))
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.20/0.50  thf('95', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('96', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | ((k3_lattices @ sk_A @ sk_B_1 @ X0)
% 0.20/0.50              = (k1_lattices @ sk_A @ sk_B_1 @ X0)))),
% 0.20/0.50      inference('clc', [status(thm)], ['94', '95'])).
% 0.20/0.50  thf('97', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ~ (l2_lattices @ sk_A)
% 0.20/0.50        | ((k3_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A))
% 0.20/0.50            = (k1_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['88', '96'])).
% 0.20/0.50  thf('98', plain, ((l2_lattices @ sk_A)),
% 0.20/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf('99', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ((k3_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A))
% 0.20/0.50            = (k1_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A))))),
% 0.20/0.50      inference('demod', [status(thm)], ['97', '98'])).
% 0.20/0.50  thf('100', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('101', plain,
% 0.20/0.50      (((k3_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A))
% 0.20/0.50         = (k1_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A)))),
% 0.20/0.50      inference('clc', [status(thm)], ['99', '100'])).
% 0.20/0.50  thf('102', plain,
% 0.20/0.50      (((k1_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A))
% 0.20/0.50         != (k6_lattices @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['87', '101'])).
% 0.20/0.50  thf('103', plain, ($false),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['66', '102'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
