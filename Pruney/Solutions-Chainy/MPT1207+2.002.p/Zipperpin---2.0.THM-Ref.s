%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.W8brZga5da

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 231 expanded)
%              Number of leaves         :   29 (  83 expanded)
%              Depth                    :   12
%              Number of atoms          :  827 (2504 expanded)
%              Number of equality atoms :   19 (  19 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_lattices_type,type,(
    k5_lattices: $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(k1_lattices_type,type,(
    k1_lattices: $i > $i > $i > $i )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

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
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ~ ( v9_lattices @ X10 )
      | ~ ( v8_lattices @ X10 )
      | ~ ( v6_lattices @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( r3_lattices @ X10 @ X9 @ X11 )
      | ~ ( r1_lattices @ X10 @ X9 @ X11 ) ) ),
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
    | ~ ( r1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 )
    | ( r3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 )
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
    ! [X8: $i] :
      ( ( l1_lattices @ X8 )
      | ~ ( l3_lattices @ X8 ) ) ),
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
    | ~ ( r1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 )
    | ( r3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['5','8','14','20','26','27'])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( r3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 )
    | ~ ( r1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( r3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ~ ( r1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ( r1_lattices @ X13 @ X12 @ ( k1_lattices @ X13 @ X12 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l3_lattices @ X13 )
      | ~ ( v9_lattices @ X13 )
      | ~ ( v8_lattices @ X13 )
      | ~ ( v6_lattices @ X13 )
      | ~ ( v5_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
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
    | ( r1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ ( k1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 ) ) ),
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
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('51',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
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

thf('52',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v8_lattices @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( ( k1_lattices @ X4 @ ( k2_lattices @ X4 @ X6 @ X5 ) @ X5 )
        = X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l3_lattices @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_lattices])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_B_1 ) @ sk_B_1 )
        = sk_B_1 )
      | ~ ( v8_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_B_1 ) @ sk_B_1 )
        = sk_B_1 ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_B_1 ) @ sk_B_1 )
        = sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 ) @ sk_B_1 )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['50','58'])).

thf('60',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('61',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
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

thf('63',plain,(
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

thf('64',plain,(
    ! [X1: $i,X3: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_lattices @ X1 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ( ( k2_lattices @ X1 @ ( k5_lattices @ X1 ) @ X3 )
        = ( k5_lattices @ X1 ) )
      | ~ ( m1_subset_1 @ ( k5_lattices @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v13_lattices @ X1 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
        = ( k5_lattices @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
        = ( k5_lattices @ X0 ) )
      | ~ ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ~ ( v13_lattices @ sk_A )
    | ( ( k2_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 )
      = ( k5_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('68',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('69',plain,(
    v13_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 )
      = ( k5_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( k2_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 )
    = ( k5_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 )
      = sk_B_1 ) ),
    inference(demod,[status(thm)],['59','60','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( k1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 )
    = sk_B_1 ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['38','39','45','46','47','48','49','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    r1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B_1 ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    $false ),
    inference(demod,[status(thm)],['32','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.W8brZga5da
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:48:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 95 iterations in 0.074s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.21/0.53  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.21/0.53  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(k5_lattices_type, type, k5_lattices: $i > $i).
% 0.21/0.53  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.21/0.53  thf(k1_lattices_type, type, k1_lattices: $i > $i > $i > $i).
% 0.21/0.53  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 0.21/0.53  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.21/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.53  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.21/0.53  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 0.21/0.53  thf(v13_lattices_type, type, v13_lattices: $i > $o).
% 0.21/0.53  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.21/0.53  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 0.21/0.53  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.21/0.53  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.21/0.53  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 0.21/0.53  thf(t41_lattices, conjecture,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.53         ( v13_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53           ( r3_lattices @ A @ ( k5_lattices @ A ) @ B ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i]:
% 0.21/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.53            ( v13_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.53          ( ![B:$i]:
% 0.21/0.53            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53              ( r3_lattices @ A @ ( k5_lattices @ A ) @ B ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t41_lattices])).
% 0.21/0.53  thf('0', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(dt_k5_lattices, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 0.21/0.53       ( m1_subset_1 @ ( k5_lattices @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X7 : $i]:
% 0.21/0.53         ((m1_subset_1 @ (k5_lattices @ X7) @ (u1_struct_0 @ X7))
% 0.21/0.53          | ~ (l1_lattices @ X7)
% 0.21/0.53          | (v2_struct_0 @ X7))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 0.21/0.53  thf(redefinition_r3_lattices, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.21/0.53         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 0.21/0.53         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.53         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.21/0.53          | ~ (l3_lattices @ X10)
% 0.21/0.53          | ~ (v9_lattices @ X10)
% 0.21/0.53          | ~ (v8_lattices @ X10)
% 0.21/0.53          | ~ (v6_lattices @ X10)
% 0.21/0.53          | (v2_struct_0 @ X10)
% 0.21/0.53          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.21/0.53          | (r3_lattices @ X10 @ X9 @ X11)
% 0.21/0.53          | ~ (r1_lattices @ X10 @ X9 @ X11))),
% 0.21/0.53      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X0)
% 0.21/0.53          | ~ (l1_lattices @ X0)
% 0.21/0.53          | ~ (r1_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 0.21/0.53          | (r3_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 0.21/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.53          | (v2_struct_0 @ X0)
% 0.21/0.53          | ~ (v6_lattices @ X0)
% 0.21/0.53          | ~ (v8_lattices @ X0)
% 0.21/0.53          | ~ (v9_lattices @ X0)
% 0.21/0.53          | ~ (l3_lattices @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (l3_lattices @ X0)
% 0.21/0.53          | ~ (v9_lattices @ X0)
% 0.21/0.53          | ~ (v8_lattices @ X0)
% 0.21/0.53          | ~ (v6_lattices @ X0)
% 0.21/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.53          | (r3_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 0.21/0.53          | ~ (r1_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 0.21/0.53          | ~ (l1_lattices @ X0)
% 0.21/0.53          | (v2_struct_0 @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_A)
% 0.21/0.53        | ~ (l1_lattices @ sk_A)
% 0.21/0.53        | ~ (r1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_1)
% 0.21/0.53        | (r3_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_1)
% 0.21/0.53        | ~ (v6_lattices @ sk_A)
% 0.21/0.53        | ~ (v8_lattices @ sk_A)
% 0.21/0.53        | ~ (v9_lattices @ sk_A)
% 0.21/0.53        | ~ (l3_lattices @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['0', '4'])).
% 0.21/0.53  thf('6', plain, ((l3_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(dt_l3_lattices, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 0.21/0.53  thf('7', plain, (![X8 : $i]: ((l1_lattices @ X8) | ~ (l3_lattices @ X8))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.21/0.53  thf('8', plain, ((l1_lattices @ sk_A)),
% 0.21/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.53  thf(cc1_lattices, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l3_lattices @ A ) =>
% 0.21/0.53       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.21/0.53         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.21/0.53           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.21/0.53           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X0)
% 0.21/0.53          | ~ (v10_lattices @ X0)
% 0.21/0.53          | (v6_lattices @ X0)
% 0.21/0.53          | ~ (l3_lattices @ X0))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.53  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.53  thf('12', plain, ((l3_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('13', plain, ((v10_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('14', plain, ((v6_lattices @ sk_A)),
% 0.21/0.53      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X0)
% 0.21/0.53          | ~ (v10_lattices @ X0)
% 0.21/0.53          | (v8_lattices @ X0)
% 0.21/0.53          | ~ (l3_lattices @ X0))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.53  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.53  thf('18', plain, ((l3_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('19', plain, ((v10_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('20', plain, ((v8_lattices @ sk_A)),
% 0.21/0.53      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X0)
% 0.21/0.53          | ~ (v10_lattices @ X0)
% 0.21/0.53          | (v9_lattices @ X0)
% 0.21/0.53          | ~ (l3_lattices @ X0))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.53  thf('22', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.53  thf('24', plain, ((l3_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('25', plain, ((v10_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('26', plain, ((v9_lattices @ sk_A)),
% 0.21/0.53      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.21/0.53  thf('27', plain, ((l3_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_A)
% 0.21/0.53        | ~ (r1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_1)
% 0.21/0.53        | (r3_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_1))),
% 0.21/0.53      inference('demod', [status(thm)], ['5', '8', '14', '20', '26', '27'])).
% 0.21/0.53  thf('29', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      (((r3_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_1)
% 0.21/0.53        | ~ (r1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_1))),
% 0.21/0.53      inference('clc', [status(thm)], ['28', '29'])).
% 0.21/0.53  thf('31', plain, (~ (r3_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('32', plain, (~ (r1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_1)),
% 0.21/0.53      inference('clc', [status(thm)], ['30', '31'])).
% 0.21/0.53  thf('33', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      (![X7 : $i]:
% 0.21/0.53         ((m1_subset_1 @ (k5_lattices @ X7) @ (u1_struct_0 @ X7))
% 0.21/0.53          | ~ (l1_lattices @ X7)
% 0.21/0.53          | (v2_struct_0 @ X7))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 0.21/0.53  thf(t22_lattices, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_lattices @ A ) & 
% 0.21/0.53         ( v6_lattices @ A ) & ( v8_lattices @ A ) & ( v9_lattices @ A ) & 
% 0.21/0.53         ( l3_lattices @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53               ( r1_lattices @ A @ B @ ( k1_lattices @ A @ B @ C ) ) ) ) ) ) ))).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.21/0.53          | (r1_lattices @ X13 @ X12 @ (k1_lattices @ X13 @ X12 @ X14))
% 0.21/0.53          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.21/0.53          | ~ (l3_lattices @ X13)
% 0.21/0.53          | ~ (v9_lattices @ X13)
% 0.21/0.53          | ~ (v8_lattices @ X13)
% 0.21/0.53          | ~ (v6_lattices @ X13)
% 0.21/0.53          | ~ (v5_lattices @ X13)
% 0.21/0.53          | (v2_struct_0 @ X13))),
% 0.21/0.53      inference('cnf', [status(esa)], [t22_lattices])).
% 0.21/0.53  thf('36', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X0)
% 0.21/0.53          | ~ (l1_lattices @ X0)
% 0.21/0.53          | (v2_struct_0 @ X0)
% 0.21/0.53          | ~ (v5_lattices @ X0)
% 0.21/0.53          | ~ (v6_lattices @ X0)
% 0.21/0.53          | ~ (v8_lattices @ X0)
% 0.21/0.53          | ~ (v9_lattices @ X0)
% 0.21/0.53          | ~ (l3_lattices @ X0)
% 0.21/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.53          | (r1_lattices @ X0 @ (k5_lattices @ X0) @ 
% 0.21/0.53             (k1_lattices @ X0 @ (k5_lattices @ X0) @ X1)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.53  thf('37', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((r1_lattices @ X0 @ (k5_lattices @ X0) @ 
% 0.21/0.53           (k1_lattices @ X0 @ (k5_lattices @ X0) @ X1))
% 0.21/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.53          | ~ (l3_lattices @ X0)
% 0.21/0.53          | ~ (v9_lattices @ X0)
% 0.21/0.53          | ~ (v8_lattices @ X0)
% 0.21/0.53          | ~ (v6_lattices @ X0)
% 0.21/0.53          | ~ (v5_lattices @ X0)
% 0.21/0.53          | ~ (l1_lattices @ X0)
% 0.21/0.53          | (v2_struct_0 @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['36'])).
% 0.21/0.53  thf('38', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_A)
% 0.21/0.53        | ~ (l1_lattices @ sk_A)
% 0.21/0.53        | ~ (v5_lattices @ sk_A)
% 0.21/0.53        | ~ (v6_lattices @ sk_A)
% 0.21/0.53        | ~ (v8_lattices @ sk_A)
% 0.21/0.53        | ~ (v9_lattices @ sk_A)
% 0.21/0.53        | ~ (l3_lattices @ sk_A)
% 0.21/0.53        | (r1_lattices @ sk_A @ (k5_lattices @ sk_A) @ 
% 0.21/0.53           (k1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_1)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['33', '37'])).
% 0.21/0.53  thf('39', plain, ((l1_lattices @ sk_A)),
% 0.21/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.53  thf('40', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X0)
% 0.21/0.53          | ~ (v10_lattices @ X0)
% 0.21/0.53          | (v5_lattices @ X0)
% 0.21/0.53          | ~ (l3_lattices @ X0))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.53  thf('41', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('42', plain,
% 0.21/0.53      ((~ (l3_lattices @ sk_A) | (v5_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.53  thf('43', plain, ((l3_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('44', plain, ((v10_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('45', plain, ((v5_lattices @ sk_A)),
% 0.21/0.53      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.21/0.53  thf('46', plain, ((v6_lattices @ sk_A)),
% 0.21/0.53      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.21/0.53  thf('47', plain, ((v8_lattices @ sk_A)),
% 0.21/0.53      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.21/0.53  thf('48', plain, ((v9_lattices @ sk_A)),
% 0.21/0.53      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.21/0.53  thf('49', plain, ((l3_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('50', plain,
% 0.21/0.53      (![X7 : $i]:
% 0.21/0.53         ((m1_subset_1 @ (k5_lattices @ X7) @ (u1_struct_0 @ X7))
% 0.21/0.53          | ~ (l1_lattices @ X7)
% 0.21/0.53          | (v2_struct_0 @ X7))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 0.21/0.53  thf('51', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(d8_lattices, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.21/0.53       ( ( v8_lattices @ A ) <=>
% 0.21/0.53         ( ![B:$i]:
% 0.21/0.53           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53             ( ![C:$i]:
% 0.21/0.53               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53                 ( ( k1_lattices @ A @ ( k2_lattices @ A @ B @ C ) @ C ) =
% 0.21/0.53                   ( C ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('52', plain,
% 0.21/0.53      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.53         (~ (v8_lattices @ X4)
% 0.21/0.53          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.21/0.53          | ((k1_lattices @ X4 @ (k2_lattices @ X4 @ X6 @ X5) @ X5) = (X5))
% 0.21/0.53          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X4))
% 0.21/0.53          | ~ (l3_lattices @ X4)
% 0.21/0.53          | (v2_struct_0 @ X4))),
% 0.21/0.53      inference('cnf', [status(esa)], [d8_lattices])).
% 0.21/0.53  thf('53', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (l3_lattices @ sk_A)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | ((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_B_1) @ sk_B_1)
% 0.21/0.53              = (sk_B_1))
% 0.21/0.53          | ~ (v8_lattices @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.53  thf('54', plain, ((l3_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('55', plain, ((v8_lattices @ sk_A)),
% 0.21/0.53      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.21/0.53  thf('56', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | ((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_B_1) @ sk_B_1)
% 0.21/0.53              = (sk_B_1)))),
% 0.21/0.53      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.21/0.53  thf('57', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('58', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_B_1) @ sk_B_1)
% 0.21/0.53            = (sk_B_1))
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('clc', [status(thm)], ['56', '57'])).
% 0.21/0.53  thf('59', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_A)
% 0.21/0.53        | ~ (l1_lattices @ sk_A)
% 0.21/0.53        | ((k1_lattices @ sk_A @ 
% 0.21/0.53            (k2_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_1) @ sk_B_1)
% 0.21/0.53            = (sk_B_1)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['50', '58'])).
% 0.21/0.53  thf('60', plain, ((l1_lattices @ sk_A)),
% 0.21/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.53  thf('61', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('62', plain,
% 0.21/0.53      (![X7 : $i]:
% 0.21/0.53         ((m1_subset_1 @ (k5_lattices @ X7) @ (u1_struct_0 @ X7))
% 0.21/0.53          | ~ (l1_lattices @ X7)
% 0.21/0.53          | (v2_struct_0 @ X7))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 0.21/0.53  thf(d16_lattices, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 0.21/0.53       ( ( v13_lattices @ A ) =>
% 0.21/0.53         ( ![B:$i]:
% 0.21/0.53           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53             ( ( ( B ) = ( k5_lattices @ A ) ) <=>
% 0.21/0.53               ( ![C:$i]:
% 0.21/0.53                 ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53                   ( ( ( k2_lattices @ A @ B @ C ) = ( B ) ) & 
% 0.21/0.53                     ( ( k2_lattices @ A @ C @ B ) = ( B ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('63', plain,
% 0.21/0.53      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.53         (~ (v13_lattices @ X1)
% 0.21/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.21/0.53          | ((X2) != (k5_lattices @ X1))
% 0.21/0.53          | ((k2_lattices @ X1 @ X2 @ X3) = (X2))
% 0.21/0.53          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.21/0.53          | ~ (l1_lattices @ X1)
% 0.21/0.53          | (v2_struct_0 @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [d16_lattices])).
% 0.21/0.53  thf('64', plain,
% 0.21/0.53      (![X1 : $i, X3 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X1)
% 0.21/0.53          | ~ (l1_lattices @ X1)
% 0.21/0.53          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.21/0.53          | ((k2_lattices @ X1 @ (k5_lattices @ X1) @ X3) = (k5_lattices @ X1))
% 0.21/0.53          | ~ (m1_subset_1 @ (k5_lattices @ X1) @ (u1_struct_0 @ X1))
% 0.21/0.53          | ~ (v13_lattices @ X1))),
% 0.21/0.53      inference('simplify', [status(thm)], ['63'])).
% 0.21/0.53  thf('65', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X0)
% 0.21/0.53          | ~ (l1_lattices @ X0)
% 0.21/0.53          | ~ (v13_lattices @ X0)
% 0.21/0.53          | ((k2_lattices @ X0 @ (k5_lattices @ X0) @ X1) = (k5_lattices @ X0))
% 0.21/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.53          | ~ (l1_lattices @ X0)
% 0.21/0.53          | (v2_struct_0 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['62', '64'])).
% 0.21/0.53  thf('66', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.53          | ((k2_lattices @ X0 @ (k5_lattices @ X0) @ X1) = (k5_lattices @ X0))
% 0.21/0.53          | ~ (v13_lattices @ X0)
% 0.21/0.53          | ~ (l1_lattices @ X0)
% 0.21/0.53          | (v2_struct_0 @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['65'])).
% 0.21/0.53  thf('67', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_A)
% 0.21/0.53        | ~ (l1_lattices @ sk_A)
% 0.21/0.53        | ~ (v13_lattices @ sk_A)
% 0.21/0.53        | ((k2_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_1)
% 0.21/0.53            = (k5_lattices @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['61', '66'])).
% 0.21/0.53  thf('68', plain, ((l1_lattices @ sk_A)),
% 0.21/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.53  thf('69', plain, ((v13_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('70', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_A)
% 0.21/0.53        | ((k2_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_1)
% 0.21/0.53            = (k5_lattices @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.21/0.53  thf('71', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('72', plain,
% 0.21/0.53      (((k2_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_1)
% 0.21/0.53         = (k5_lattices @ sk_A))),
% 0.21/0.53      inference('clc', [status(thm)], ['70', '71'])).
% 0.21/0.53  thf('73', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_A)
% 0.21/0.53        | ((k1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_1) = (sk_B_1)))),
% 0.21/0.53      inference('demod', [status(thm)], ['59', '60', '72'])).
% 0.21/0.53  thf('74', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('75', plain,
% 0.21/0.53      (((k1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_1) = (sk_B_1))),
% 0.21/0.53      inference('clc', [status(thm)], ['73', '74'])).
% 0.21/0.53  thf('76', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_A)
% 0.21/0.53        | (r1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_1))),
% 0.21/0.53      inference('demod', [status(thm)],
% 0.21/0.53                ['38', '39', '45', '46', '47', '48', '49', '75'])).
% 0.21/0.53  thf('77', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('78', plain, ((r1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B_1)),
% 0.21/0.53      inference('clc', [status(thm)], ['76', '77'])).
% 0.21/0.53  thf('79', plain, ($false), inference('demod', [status(thm)], ['32', '78'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
