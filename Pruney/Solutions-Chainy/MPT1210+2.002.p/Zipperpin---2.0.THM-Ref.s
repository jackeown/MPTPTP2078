%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Xr85BqopTE

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 206 expanded)
%              Number of leaves         :   29 (  75 expanded)
%              Depth                    :   18
%              Number of atoms          :  759 (2172 expanded)
%              Number of equality atoms :   24 (  24 expanded)
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

thf(k6_lattices_type,type,(
    k6_lattices: $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(k1_lattices_type,type,(
    k1_lattices: $i > $i > $i > $i )).

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

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(v14_lattices_type,type,(
    v14_lattices: $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(t45_lattices,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v14_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r3_lattices @ A @ B @ ( k6_lattices @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v14_lattices @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( r3_lattices @ A @ B @ ( k6_lattices @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t45_lattices])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
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

thf('2',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k6_lattices @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( l2_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_lattices])).

thf('3',plain,(
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

thf('4',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ( ( k2_lattices @ X13 @ X12 @ X14 )
       != X12 )
      | ( r1_lattices @ X13 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l3_lattices @ X13 )
      | ~ ( v9_lattices @ X13 )
      | ~ ( v8_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t21_lattices])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ sk_B_1 @ X0 )
      | ( ( k2_lattices @ sk_A @ sk_B_1 @ X0 )
       != sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

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

thf('6',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('7',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ sk_B_1 @ X0 )
      | ( ( k2_lattices @ sk_A @ sk_B_1 @ X0 )
       != sk_B_1 ) ) ),
    inference(demod,[status(thm)],['5','11','17','18'])).

thf('20',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ( ( k2_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
     != sk_B_1 )
    | ( r1_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','19'])).

thf('21',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('22',plain,(
    ! [X8: $i] :
      ( ( l2_lattices @ X8 )
      | ~ ( l3_lattices @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('23',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k6_lattices @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( l2_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_lattices])).

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

thf('26',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v9_lattices @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( ( k2_lattices @ X4 @ X6 @ ( k1_lattices @ X4 @ X6 @ X5 ) )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l3_lattices @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d9_lattices])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ X1 @ ( k1_lattices @ X0 @ X1 @ ( k6_lattices @ X0 ) ) )
        = X1 )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ X1 @ ( k1_lattices @ X0 @ X1 @ ( k6_lattices @ X0 ) ) )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k2_lattices @ sk_A @ sk_B_1 @ ( k1_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) ) )
      = sk_B_1 )
    | ~ ( v9_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['24','28'])).

thf('30',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['21','22'])).

thf('31',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k6_lattices @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( l2_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
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

thf('34',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v14_lattices @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( X2
       != ( k6_lattices @ X1 ) )
      | ( ( k1_lattices @ X1 @ X3 @ X2 )
        = X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l2_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d17_lattices])).

thf('35',plain,(
    ! [X1: $i,X3: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l2_lattices @ X1 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ( ( k1_lattices @ X1 @ X3 @ ( k6_lattices @ X1 ) )
        = ( k6_lattices @ X1 ) )
      | ~ ( m1_subset_1 @ ( k6_lattices @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v14_lattices @ X1 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ~ ( v14_lattices @ X0 )
      | ( ( k1_lattices @ X0 @ X1 @ ( k6_lattices @ X0 ) )
        = ( k6_lattices @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l2_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k1_lattices @ X0 @ X1 @ ( k6_lattices @ X0 ) )
        = ( k6_lattices @ X0 ) )
      | ~ ( v14_lattices @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ~ ( v14_lattices @ sk_A )
    | ( ( k1_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
      = ( k6_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['21','22'])).

thf('40',plain,(
    v14_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
      = ( k6_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k1_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
    = ( k6_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
      = sk_B_1 ) ),
    inference(demod,[status(thm)],['29','30','31','43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k2_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
    = sk_B_1 ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1 != sk_B_1 )
    | ( r1_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','23','47'])).

thf('49',plain,
    ( ( r1_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    r1_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('53',plain,(
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

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ sk_B_1 @ X0 )
      | ( r3_lattices @ sk_A @ sk_B_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

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
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('62',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('63',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ sk_B_1 @ X0 )
      | ( r3_lattices @ sk_A @ sk_B_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','60','61','62','63'])).

thf('65',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k6_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r3_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( r3_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k6_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( r3_lattices @ sk_A @ sk_B_1 @ ( k6_lattices @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ~ ( m1_subset_1 @ ( k6_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['1','69'])).

thf('71',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['21','22'])).

thf('72',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    $false ),
    inference(demod,[status(thm)],['0','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Xr85BqopTE
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:12:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 116 iterations in 0.092s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.21/0.55  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.21/0.55  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(k6_lattices_type, type, k6_lattices: $i > $i).
% 0.21/0.55  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.21/0.55  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 0.21/0.55  thf(k1_lattices_type, type, k1_lattices: $i > $i > $i > $i).
% 0.21/0.55  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.21/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.55  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.21/0.55  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 0.21/0.55  thf(v14_lattices_type, type, v14_lattices: $i > $o).
% 0.21/0.55  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.21/0.55  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 0.21/0.55  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.21/0.55  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.21/0.55  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 0.21/0.55  thf(t45_lattices, conjecture,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.55         ( v14_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.55           ( r3_lattices @ A @ B @ ( k6_lattices @ A ) ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i]:
% 0.21/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.55            ( v14_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.55          ( ![B:$i]:
% 0.21/0.55            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.55              ( r3_lattices @ A @ B @ ( k6_lattices @ A ) ) ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t45_lattices])).
% 0.21/0.55  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(dt_k6_lattices, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l2_lattices @ A ) ) =>
% 0.21/0.55       ( m1_subset_1 @ ( k6_lattices @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      (![X7 : $i]:
% 0.21/0.55         ((m1_subset_1 @ (k6_lattices @ X7) @ (u1_struct_0 @ X7))
% 0.21/0.55          | ~ (l2_lattices @ X7)
% 0.21/0.55          | (v2_struct_0 @ X7))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k6_lattices])).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      (![X7 : $i]:
% 0.21/0.55         ((m1_subset_1 @ (k6_lattices @ X7) @ (u1_struct_0 @ X7))
% 0.21/0.55          | ~ (l2_lattices @ X7)
% 0.21/0.55          | (v2_struct_0 @ X7))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k6_lattices])).
% 0.21/0.55  thf('3', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(t21_lattices, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v8_lattices @ A ) & 
% 0.21/0.55         ( v9_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.55           ( ![C:$i]:
% 0.21/0.55             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.55               ( ( r1_lattices @ A @ B @ C ) <=>
% 0.21/0.55                 ( ( k2_lattices @ A @ B @ C ) = ( B ) ) ) ) ) ) ) ))).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.21/0.55          | ((k2_lattices @ X13 @ X12 @ X14) != (X12))
% 0.21/0.55          | (r1_lattices @ X13 @ X12 @ X14)
% 0.21/0.55          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.21/0.55          | ~ (l3_lattices @ X13)
% 0.21/0.55          | ~ (v9_lattices @ X13)
% 0.21/0.55          | ~ (v8_lattices @ X13)
% 0.21/0.55          | (v2_struct_0 @ X13))),
% 0.21/0.55      inference('cnf', [status(esa)], [t21_lattices])).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((v2_struct_0 @ sk_A)
% 0.21/0.55          | ~ (v8_lattices @ sk_A)
% 0.21/0.55          | ~ (v9_lattices @ sk_A)
% 0.21/0.55          | ~ (l3_lattices @ sk_A)
% 0.21/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | (r1_lattices @ sk_A @ sk_B_1 @ X0)
% 0.21/0.55          | ((k2_lattices @ sk_A @ sk_B_1 @ X0) != (sk_B_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.55  thf(cc1_lattices, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( l3_lattices @ A ) =>
% 0.21/0.55       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.21/0.55         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.21/0.55           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.21/0.55           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((v2_struct_0 @ X0)
% 0.21/0.55          | ~ (v10_lattices @ X0)
% 0.21/0.55          | (v8_lattices @ X0)
% 0.21/0.55          | ~ (l3_lattices @ X0))),
% 0.21/0.55      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.55  thf('7', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.55  thf('9', plain, ((l3_lattices @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('10', plain, ((v10_lattices @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('11', plain, ((v8_lattices @ sk_A)),
% 0.21/0.55      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((v2_struct_0 @ X0)
% 0.21/0.55          | ~ (v10_lattices @ X0)
% 0.21/0.55          | (v9_lattices @ X0)
% 0.21/0.55          | ~ (l3_lattices @ X0))),
% 0.21/0.55      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.55  thf('13', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('14', plain,
% 0.21/0.55      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.55  thf('15', plain, ((l3_lattices @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('16', plain, ((v10_lattices @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('17', plain, ((v9_lattices @ sk_A)),
% 0.21/0.55      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.21/0.55  thf('18', plain, ((l3_lattices @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((v2_struct_0 @ sk_A)
% 0.21/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | (r1_lattices @ sk_A @ sk_B_1 @ X0)
% 0.21/0.55          | ((k2_lattices @ sk_A @ sk_B_1 @ X0) != (sk_B_1)))),
% 0.21/0.55      inference('demod', [status(thm)], ['5', '11', '17', '18'])).
% 0.21/0.55  thf('20', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_A)
% 0.21/0.55        | ~ (l2_lattices @ sk_A)
% 0.21/0.55        | ((k2_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A)) != (sk_B_1))
% 0.21/0.55        | (r1_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A))
% 0.21/0.55        | (v2_struct_0 @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['2', '19'])).
% 0.21/0.55  thf('21', plain, ((l3_lattices @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(dt_l3_lattices, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 0.21/0.55  thf('22', plain, (![X8 : $i]: ((l2_lattices @ X8) | ~ (l3_lattices @ X8))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.21/0.55  thf('23', plain, ((l2_lattices @ sk_A)),
% 0.21/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.55  thf('24', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('25', plain,
% 0.21/0.55      (![X7 : $i]:
% 0.21/0.55         ((m1_subset_1 @ (k6_lattices @ X7) @ (u1_struct_0 @ X7))
% 0.21/0.55          | ~ (l2_lattices @ X7)
% 0.21/0.55          | (v2_struct_0 @ X7))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k6_lattices])).
% 0.21/0.55  thf(d9_lattices, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.21/0.55       ( ( v9_lattices @ A ) <=>
% 0.21/0.55         ( ![B:$i]:
% 0.21/0.55           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.55             ( ![C:$i]:
% 0.21/0.55               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.55                 ( ( k2_lattices @ A @ B @ ( k1_lattices @ A @ B @ C ) ) =
% 0.21/0.55                   ( B ) ) ) ) ) ) ) ))).
% 0.21/0.55  thf('26', plain,
% 0.21/0.55      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.55         (~ (v9_lattices @ X4)
% 0.21/0.55          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.21/0.55          | ((k2_lattices @ X4 @ X6 @ (k1_lattices @ X4 @ X6 @ X5)) = (X6))
% 0.21/0.55          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X4))
% 0.21/0.55          | ~ (l3_lattices @ X4)
% 0.21/0.55          | (v2_struct_0 @ X4))),
% 0.21/0.55      inference('cnf', [status(esa)], [d9_lattices])).
% 0.21/0.55  thf('27', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((v2_struct_0 @ X0)
% 0.21/0.55          | ~ (l2_lattices @ X0)
% 0.21/0.55          | (v2_struct_0 @ X0)
% 0.21/0.55          | ~ (l3_lattices @ X0)
% 0.21/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.55          | ((k2_lattices @ X0 @ X1 @ 
% 0.21/0.55              (k1_lattices @ X0 @ X1 @ (k6_lattices @ X0))) = (X1))
% 0.21/0.55          | ~ (v9_lattices @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.55  thf('28', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (v9_lattices @ X0)
% 0.21/0.55          | ((k2_lattices @ X0 @ X1 @ 
% 0.21/0.55              (k1_lattices @ X0 @ X1 @ (k6_lattices @ X0))) = (X1))
% 0.21/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.55          | ~ (l3_lattices @ X0)
% 0.21/0.55          | ~ (l2_lattices @ X0)
% 0.21/0.55          | (v2_struct_0 @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['27'])).
% 0.21/0.55  thf('29', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_A)
% 0.21/0.55        | ~ (l2_lattices @ sk_A)
% 0.21/0.55        | ~ (l3_lattices @ sk_A)
% 0.21/0.55        | ((k2_lattices @ sk_A @ sk_B_1 @ 
% 0.21/0.55            (k1_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A))) = (sk_B_1))
% 0.21/0.55        | ~ (v9_lattices @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['24', '28'])).
% 0.21/0.55  thf('30', plain, ((l2_lattices @ sk_A)),
% 0.21/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.55  thf('31', plain, ((l3_lattices @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('32', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('33', plain,
% 0.21/0.55      (![X7 : $i]:
% 0.21/0.55         ((m1_subset_1 @ (k6_lattices @ X7) @ (u1_struct_0 @ X7))
% 0.21/0.55          | ~ (l2_lattices @ X7)
% 0.21/0.55          | (v2_struct_0 @ X7))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k6_lattices])).
% 0.21/0.55  thf(d17_lattices, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l2_lattices @ A ) ) =>
% 0.21/0.55       ( ( v14_lattices @ A ) =>
% 0.21/0.55         ( ![B:$i]:
% 0.21/0.55           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.55             ( ( ( B ) = ( k6_lattices @ A ) ) <=>
% 0.21/0.55               ( ![C:$i]:
% 0.21/0.55                 ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.55                   ( ( ( k1_lattices @ A @ B @ C ) = ( B ) ) & 
% 0.21/0.55                     ( ( k1_lattices @ A @ C @ B ) = ( B ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.55  thf('34', plain,
% 0.21/0.55      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.55         (~ (v14_lattices @ X1)
% 0.21/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.21/0.55          | ((X2) != (k6_lattices @ X1))
% 0.21/0.55          | ((k1_lattices @ X1 @ X3 @ X2) = (X2))
% 0.21/0.55          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.21/0.55          | ~ (l2_lattices @ X1)
% 0.21/0.55          | (v2_struct_0 @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [d17_lattices])).
% 0.21/0.55  thf('35', plain,
% 0.21/0.55      (![X1 : $i, X3 : $i]:
% 0.21/0.55         ((v2_struct_0 @ X1)
% 0.21/0.55          | ~ (l2_lattices @ X1)
% 0.21/0.55          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.21/0.55          | ((k1_lattices @ X1 @ X3 @ (k6_lattices @ X1)) = (k6_lattices @ X1))
% 0.21/0.55          | ~ (m1_subset_1 @ (k6_lattices @ X1) @ (u1_struct_0 @ X1))
% 0.21/0.55          | ~ (v14_lattices @ X1))),
% 0.21/0.55      inference('simplify', [status(thm)], ['34'])).
% 0.21/0.55  thf('36', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((v2_struct_0 @ X0)
% 0.21/0.55          | ~ (l2_lattices @ X0)
% 0.21/0.55          | ~ (v14_lattices @ X0)
% 0.21/0.55          | ((k1_lattices @ X0 @ X1 @ (k6_lattices @ X0)) = (k6_lattices @ X0))
% 0.21/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.55          | ~ (l2_lattices @ X0)
% 0.21/0.55          | (v2_struct_0 @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['33', '35'])).
% 0.21/0.55  thf('37', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.55          | ((k1_lattices @ X0 @ X1 @ (k6_lattices @ X0)) = (k6_lattices @ X0))
% 0.21/0.55          | ~ (v14_lattices @ X0)
% 0.21/0.55          | ~ (l2_lattices @ X0)
% 0.21/0.55          | (v2_struct_0 @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['36'])).
% 0.21/0.55  thf('38', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_A)
% 0.21/0.55        | ~ (l2_lattices @ sk_A)
% 0.21/0.55        | ~ (v14_lattices @ sk_A)
% 0.21/0.55        | ((k1_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A))
% 0.21/0.55            = (k6_lattices @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['32', '37'])).
% 0.21/0.55  thf('39', plain, ((l2_lattices @ sk_A)),
% 0.21/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.55  thf('40', plain, ((v14_lattices @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('41', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_A)
% 0.21/0.55        | ((k1_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A))
% 0.21/0.55            = (k6_lattices @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.21/0.55  thf('42', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('43', plain,
% 0.21/0.55      (((k1_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A))
% 0.21/0.55         = (k6_lattices @ sk_A))),
% 0.21/0.55      inference('clc', [status(thm)], ['41', '42'])).
% 0.21/0.55  thf('44', plain, ((v9_lattices @ sk_A)),
% 0.21/0.55      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.21/0.55  thf('45', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_A)
% 0.21/0.55        | ((k2_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A)) = (sk_B_1)))),
% 0.21/0.55      inference('demod', [status(thm)], ['29', '30', '31', '43', '44'])).
% 0.21/0.55  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('47', plain,
% 0.21/0.55      (((k2_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A)) = (sk_B_1))),
% 0.21/0.55      inference('clc', [status(thm)], ['45', '46'])).
% 0.21/0.55  thf('48', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_A)
% 0.21/0.55        | ((sk_B_1) != (sk_B_1))
% 0.21/0.55        | (r1_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A))
% 0.21/0.55        | (v2_struct_0 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['20', '23', '47'])).
% 0.21/0.55  thf('49', plain,
% 0.21/0.55      (((r1_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A))
% 0.21/0.55        | (v2_struct_0 @ sk_A))),
% 0.21/0.55      inference('simplify', [status(thm)], ['48'])).
% 0.21/0.55  thf('50', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('51', plain, ((r1_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A))),
% 0.21/0.55      inference('clc', [status(thm)], ['49', '50'])).
% 0.21/0.55  thf('52', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(redefinition_r3_lattices, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.21/0.55         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 0.21/0.55         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.55         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 0.21/0.55  thf('53', plain,
% 0.21/0.55      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.21/0.55          | ~ (l3_lattices @ X10)
% 0.21/0.55          | ~ (v9_lattices @ X10)
% 0.21/0.55          | ~ (v8_lattices @ X10)
% 0.21/0.55          | ~ (v6_lattices @ X10)
% 0.21/0.55          | (v2_struct_0 @ X10)
% 0.21/0.55          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.21/0.55          | (r3_lattices @ X10 @ X9 @ X11)
% 0.21/0.55          | ~ (r1_lattices @ X10 @ X9 @ X11))),
% 0.21/0.55      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.21/0.55  thf('54', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (r1_lattices @ sk_A @ sk_B_1 @ X0)
% 0.21/0.55          | (r3_lattices @ sk_A @ sk_B_1 @ X0)
% 0.21/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | (v2_struct_0 @ sk_A)
% 0.21/0.55          | ~ (v6_lattices @ sk_A)
% 0.21/0.55          | ~ (v8_lattices @ sk_A)
% 0.21/0.55          | ~ (v9_lattices @ sk_A)
% 0.21/0.55          | ~ (l3_lattices @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.55  thf('55', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((v2_struct_0 @ X0)
% 0.21/0.55          | ~ (v10_lattices @ X0)
% 0.21/0.55          | (v6_lattices @ X0)
% 0.21/0.55          | ~ (l3_lattices @ X0))),
% 0.21/0.55      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.55  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('57', plain,
% 0.21/0.55      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.55  thf('58', plain, ((l3_lattices @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('59', plain, ((v10_lattices @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('60', plain, ((v6_lattices @ sk_A)),
% 0.21/0.55      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.21/0.55  thf('61', plain, ((v8_lattices @ sk_A)),
% 0.21/0.55      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.21/0.55  thf('62', plain, ((v9_lattices @ sk_A)),
% 0.21/0.55      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.21/0.55  thf('63', plain, ((l3_lattices @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('64', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (r1_lattices @ sk_A @ sk_B_1 @ X0)
% 0.21/0.55          | (r3_lattices @ sk_A @ sk_B_1 @ X0)
% 0.21/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | (v2_struct_0 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['54', '60', '61', '62', '63'])).
% 0.21/0.55  thf('65', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_A)
% 0.21/0.55        | ~ (m1_subset_1 @ (k6_lattices @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.21/0.55        | (r3_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['51', '64'])).
% 0.21/0.55  thf('66', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('67', plain,
% 0.21/0.55      (((r3_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A))
% 0.21/0.55        | ~ (m1_subset_1 @ (k6_lattices @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('clc', [status(thm)], ['65', '66'])).
% 0.21/0.55  thf('68', plain, (~ (r3_lattices @ sk_A @ sk_B_1 @ (k6_lattices @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('69', plain,
% 0.21/0.55      (~ (m1_subset_1 @ (k6_lattices @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('clc', [status(thm)], ['67', '68'])).
% 0.21/0.55  thf('70', plain, (((v2_struct_0 @ sk_A) | ~ (l2_lattices @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['1', '69'])).
% 0.21/0.55  thf('71', plain, ((l2_lattices @ sk_A)),
% 0.21/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.55  thf('72', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('demod', [status(thm)], ['70', '71'])).
% 0.21/0.55  thf('73', plain, ($false), inference('demod', [status(thm)], ['0', '72'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
