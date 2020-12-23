%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.U0xz1cTOL4

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 214 expanded)
%              Number of leaves         :   30 (  77 expanded)
%              Depth                    :   14
%              Number of atoms          :  865 (2444 expanded)
%              Number of equality atoms :   33 ( 103 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(k3_lattices_type,type,(
    k3_lattices: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(k6_lattices_type,type,(
    k6_lattices: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(k1_lattices_type,type,(
    k1_lattices: $i > $i > $i > $i )).

thf(k4_lattices_type,type,(
    k4_lattices: $i > $i > $i > $i )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(v14_lattices_type,type,(
    v14_lattices: $i > $o )).

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

thf(dt_k6_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l2_lattices @ A ) )
     => ( m1_subset_1 @ ( k6_lattices @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k6_lattices @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( l2_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_lattices])).

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

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('2',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r1_lattices @ X5 @ X4 @ X6 )
      | ( ( k1_lattices @ X5 @ X4 @ X6 )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l2_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_lattices])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l2_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ sk_B @ X0 )
        = X0 )
      | ~ ( r1_lattices @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('5',plain,(
    ! [X8: $i] :
      ( ( l2_lattices @ X8 )
      | ~ ( l3_lattices @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('6',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ sk_B @ X0 )
        = X0 )
      | ~ ( r1_lattices @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ~ ( r1_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
    | ( ( k1_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
      = ( k6_lattices @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('10',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( r1_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
    | ( ( k1_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
      = ( k6_lattices @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( ( k1_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
      = ( k6_lattices @ sk_A ) )
    | ~ ( r1_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ( k3_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_B )
 != ( k6_lattices @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k6_lattices @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( l2_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_lattices])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
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

thf('15',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l2_lattices @ X2 )
      | ~ ( v4_lattices @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( ( k3_lattices @ X2 @ X1 @ X3 )
        = ( k3_lattices @ X2 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_lattices])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

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

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v4_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v4_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_B @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ( ( k3_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
      = ( k3_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','26'])).

thf('28',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
      = ( k3_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k3_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
    = ( k3_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    ( k3_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
 != ( k6_lattices @ sk_A ) ),
    inference(demod,[status(thm)],['12','31'])).

thf('33',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k6_lattices @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( l2_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_lattices])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
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

thf('35',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l2_lattices @ X10 )
      | ~ ( v4_lattices @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( ( k3_lattices @ X10 @ X9 @ X11 )
        = ( k1_lattices @ X10 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_lattices])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B @ X0 )
        = ( k1_lattices @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('38',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B @ X0 )
        = ( k1_lattices @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_B @ X0 )
        = ( k1_lattices @ sk_A @ sk_B @ X0 ) ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ( ( k3_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
      = ( k1_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','41'])).

thf('43',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
      = ( k1_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k3_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
    = ( k1_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    ( k1_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
 != ( k6_lattices @ sk_A ) ),
    inference(demod,[status(thm)],['32','46'])).

thf('48',plain,
    ( ~ ( r1_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['11','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ~ ( r1_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
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

thf('53',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ( r1_lattices @ X13 @ ( k4_lattices @ X13 @ X12 @ X14 ) @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l3_lattices @ X13 )
      | ~ ( v8_lattices @ X13 )
      | ~ ( v6_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t23_lattices])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k4_lattices @ X0 @ ( k6_lattices @ X0 ) @ X1 ) @ ( k6_lattices @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattices @ X0 @ ( k4_lattices @ X0 @ ( k6_lattices @ X0 ) @ X1 ) @ ( k6_lattices @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ~ ( v6_lattices @ sk_A )
    | ~ ( v8_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_B ) @ ( k6_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','55'])).

thf('57',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
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

thf('72',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ( ( k4_lattices @ X16 @ ( k6_lattices @ X16 ) @ X15 )
        = X15 )
      | ~ ( l3_lattices @ X16 )
      | ~ ( v14_lattices @ X16 )
      | ~ ( v10_lattices @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t43_lattices])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v14_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k4_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v14_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_B )
      = sk_B ) ),
    inference(demod,[status(thm)],['73','74','75','76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( k4_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_B )
    = sk_B ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57','63','69','70','79'])).

thf('81',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    r1_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    $false ),
    inference(demod,[status(thm)],['50','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.U0xz1cTOL4
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:30:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 61 iterations in 0.026s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.21/0.47  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.21/0.47  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.21/0.47  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.21/0.47  thf(k3_lattices_type, type, k3_lattices: $i > $i > $i > $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.21/0.47  thf(k6_lattices_type, type, k6_lattices: $i > $i).
% 0.21/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.47  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.21/0.47  thf(k1_lattices_type, type, k1_lattices: $i > $i > $i > $i).
% 0.21/0.47  thf(k4_lattices_type, type, k4_lattices: $i > $i > $i > $i).
% 0.21/0.47  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.21/0.47  thf(v14_lattices_type, type, v14_lattices: $i > $o).
% 0.21/0.47  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.21/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.47  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 0.21/0.47  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(dt_k6_lattices, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l2_lattices @ A ) ) =>
% 0.21/0.47       ( m1_subset_1 @ ( k6_lattices @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      (![X7 : $i]:
% 0.21/0.47         ((m1_subset_1 @ (k6_lattices @ X7) @ (u1_struct_0 @ X7))
% 0.21/0.47          | ~ (l2_lattices @ X7)
% 0.21/0.47          | (v2_struct_0 @ X7))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k6_lattices])).
% 0.21/0.47  thf(t44_lattices, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.47         ( v14_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.47           ( ( k3_lattices @ A @ ( k6_lattices @ A ) @ B ) =
% 0.21/0.47             ( k6_lattices @ A ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.47            ( v14_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.47          ( ![B:$i]:
% 0.21/0.47            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.47              ( ( k3_lattices @ A @ ( k6_lattices @ A ) @ B ) =
% 0.21/0.47                ( k6_lattices @ A ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t44_lattices])).
% 0.21/0.47  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(d3_lattices, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l2_lattices @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.47           ( ![C:$i]:
% 0.21/0.47             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.47               ( ( r1_lattices @ A @ B @ C ) <=>
% 0.21/0.47                 ( ( k1_lattices @ A @ B @ C ) = ( C ) ) ) ) ) ) ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.21/0.47          | ~ (r1_lattices @ X5 @ X4 @ X6)
% 0.21/0.47          | ((k1_lattices @ X5 @ X4 @ X6) = (X6))
% 0.21/0.47          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.21/0.47          | ~ (l2_lattices @ X5)
% 0.21/0.47          | (v2_struct_0 @ X5))),
% 0.21/0.47      inference('cnf', [status(esa)], [d3_lattices])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((v2_struct_0 @ sk_A)
% 0.21/0.47          | ~ (l2_lattices @ sk_A)
% 0.21/0.47          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.47          | ((k1_lattices @ sk_A @ sk_B @ X0) = (X0))
% 0.21/0.47          | ~ (r1_lattices @ sk_A @ sk_B @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf('4', plain, ((l3_lattices @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(dt_l3_lattices, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 0.21/0.47  thf('5', plain, (![X8 : $i]: ((l2_lattices @ X8) | ~ (l3_lattices @ X8))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.21/0.47  thf('6', plain, ((l2_lattices @ sk_A)),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((v2_struct_0 @ sk_A)
% 0.21/0.47          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.47          | ((k1_lattices @ sk_A @ sk_B @ X0) = (X0))
% 0.21/0.47          | ~ (r1_lattices @ sk_A @ sk_B @ X0))),
% 0.21/0.47      inference('demod', [status(thm)], ['3', '6'])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (((v2_struct_0 @ sk_A)
% 0.21/0.47        | ~ (l2_lattices @ sk_A)
% 0.21/0.47        | ~ (r1_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.21/0.47        | ((k1_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.21/0.47            = (k6_lattices @ sk_A))
% 0.21/0.47        | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '7'])).
% 0.21/0.47  thf('9', plain, ((l2_lattices @ sk_A)),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (((v2_struct_0 @ sk_A)
% 0.21/0.47        | ~ (r1_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.21/0.47        | ((k1_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.21/0.47            = (k6_lattices @ sk_A))
% 0.21/0.47        | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      ((((k1_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.21/0.47          = (k6_lattices @ sk_A))
% 0.21/0.47        | ~ (r1_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.21/0.47        | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (((k3_lattices @ sk_A @ (k6_lattices @ sk_A) @ sk_B)
% 0.21/0.47         != (k6_lattices @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (![X7 : $i]:
% 0.21/0.47         ((m1_subset_1 @ (k6_lattices @ X7) @ (u1_struct_0 @ X7))
% 0.21/0.47          | ~ (l2_lattices @ X7)
% 0.21/0.47          | (v2_struct_0 @ X7))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k6_lattices])).
% 0.21/0.47  thf('14', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(commutativity_k3_lattices, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.21/0.47         ( l2_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.47         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47       ( ( k3_lattices @ A @ B @ C ) = ( k3_lattices @ A @ C @ B ) ) ))).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.21/0.47          | ~ (l2_lattices @ X2)
% 0.21/0.47          | ~ (v4_lattices @ X2)
% 0.21/0.47          | (v2_struct_0 @ X2)
% 0.21/0.47          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.21/0.47          | ((k3_lattices @ X2 @ X1 @ X3) = (k3_lattices @ X2 @ X3 @ X1)))),
% 0.21/0.47      inference('cnf', [status(esa)], [commutativity_k3_lattices])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (((k3_lattices @ sk_A @ sk_B @ X0) = (k3_lattices @ sk_A @ X0 @ sk_B))
% 0.21/0.47          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.47          | (v2_struct_0 @ sk_A)
% 0.21/0.47          | ~ (v4_lattices @ sk_A)
% 0.21/0.47          | ~ (l2_lattices @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.47  thf(cc1_lattices, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( l3_lattices @ A ) =>
% 0.21/0.47       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.21/0.47         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.21/0.47           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.21/0.47           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((v2_struct_0 @ X0)
% 0.21/0.47          | ~ (v10_lattices @ X0)
% 0.21/0.47          | (v4_lattices @ X0)
% 0.21/0.47          | ~ (l3_lattices @ X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.47  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      ((~ (l3_lattices @ sk_A) | (v4_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.47  thf('20', plain, ((l3_lattices @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('21', plain, ((v10_lattices @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('22', plain, ((v4_lattices @ sk_A)),
% 0.21/0.47      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.21/0.47  thf('23', plain, ((l2_lattices @ sk_A)),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.47  thf('24', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (((k3_lattices @ sk_A @ sk_B @ X0) = (k3_lattices @ sk_A @ X0 @ sk_B))
% 0.21/0.47          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.47          | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['16', '22', '23'])).
% 0.21/0.47  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('26', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.47          | ((k3_lattices @ sk_A @ sk_B @ X0)
% 0.21/0.47              = (k3_lattices @ sk_A @ X0 @ sk_B)))),
% 0.21/0.47      inference('clc', [status(thm)], ['24', '25'])).
% 0.21/0.47  thf('27', plain,
% 0.21/0.47      (((v2_struct_0 @ sk_A)
% 0.21/0.47        | ~ (l2_lattices @ sk_A)
% 0.21/0.47        | ((k3_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.21/0.47            = (k3_lattices @ sk_A @ (k6_lattices @ sk_A) @ sk_B)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['13', '26'])).
% 0.21/0.47  thf('28', plain, ((l2_lattices @ sk_A)),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.47  thf('29', plain,
% 0.21/0.47      (((v2_struct_0 @ sk_A)
% 0.21/0.47        | ((k3_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.21/0.47            = (k3_lattices @ sk_A @ (k6_lattices @ sk_A) @ sk_B)))),
% 0.21/0.47      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.47  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('31', plain,
% 0.21/0.47      (((k3_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.21/0.47         = (k3_lattices @ sk_A @ (k6_lattices @ sk_A) @ sk_B))),
% 0.21/0.47      inference('clc', [status(thm)], ['29', '30'])).
% 0.21/0.47  thf('32', plain,
% 0.21/0.47      (((k3_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.21/0.47         != (k6_lattices @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['12', '31'])).
% 0.21/0.47  thf('33', plain,
% 0.21/0.47      (![X7 : $i]:
% 0.21/0.47         ((m1_subset_1 @ (k6_lattices @ X7) @ (u1_struct_0 @ X7))
% 0.21/0.47          | ~ (l2_lattices @ X7)
% 0.21/0.47          | (v2_struct_0 @ X7))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k6_lattices])).
% 0.21/0.47  thf('34', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(redefinition_k3_lattices, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.21/0.47         ( l2_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.47         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47       ( ( k3_lattices @ A @ B @ C ) = ( k1_lattices @ A @ B @ C ) ) ))).
% 0.21/0.47  thf('35', plain,
% 0.21/0.47      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.21/0.47          | ~ (l2_lattices @ X10)
% 0.21/0.47          | ~ (v4_lattices @ X10)
% 0.21/0.47          | (v2_struct_0 @ X10)
% 0.21/0.47          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.21/0.47          | ((k3_lattices @ X10 @ X9 @ X11) = (k1_lattices @ X10 @ X9 @ X11)))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k3_lattices])).
% 0.21/0.47  thf('36', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (((k3_lattices @ sk_A @ sk_B @ X0) = (k1_lattices @ sk_A @ sk_B @ X0))
% 0.21/0.47          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.47          | (v2_struct_0 @ sk_A)
% 0.21/0.47          | ~ (v4_lattices @ sk_A)
% 0.21/0.47          | ~ (l2_lattices @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.47  thf('37', plain, ((v4_lattices @ sk_A)),
% 0.21/0.47      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.21/0.47  thf('38', plain, ((l2_lattices @ sk_A)),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.47  thf('39', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (((k3_lattices @ sk_A @ sk_B @ X0) = (k1_lattices @ sk_A @ sk_B @ X0))
% 0.21/0.47          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.47          | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.21/0.47  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('41', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.47          | ((k3_lattices @ sk_A @ sk_B @ X0)
% 0.21/0.47              = (k1_lattices @ sk_A @ sk_B @ X0)))),
% 0.21/0.47      inference('clc', [status(thm)], ['39', '40'])).
% 0.21/0.47  thf('42', plain,
% 0.21/0.47      (((v2_struct_0 @ sk_A)
% 0.21/0.47        | ~ (l2_lattices @ sk_A)
% 0.21/0.47        | ((k3_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.21/0.47            = (k1_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['33', '41'])).
% 0.21/0.47  thf('43', plain, ((l2_lattices @ sk_A)),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.47  thf('44', plain,
% 0.21/0.47      (((v2_struct_0 @ sk_A)
% 0.21/0.47        | ((k3_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.21/0.47            = (k1_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))))),
% 0.21/0.47      inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.47  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('46', plain,
% 0.21/0.47      (((k3_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.21/0.47         = (k1_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A)))),
% 0.21/0.47      inference('clc', [status(thm)], ['44', '45'])).
% 0.21/0.47  thf('47', plain,
% 0.21/0.47      (((k1_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.21/0.47         != (k6_lattices @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['32', '46'])).
% 0.21/0.47  thf('48', plain,
% 0.21/0.47      ((~ (r1_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.21/0.47        | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['11', '47'])).
% 0.21/0.47  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('50', plain, (~ (r1_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))),
% 0.21/0.47      inference('clc', [status(thm)], ['48', '49'])).
% 0.21/0.47  thf('51', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('52', plain,
% 0.21/0.47      (![X7 : $i]:
% 0.21/0.47         ((m1_subset_1 @ (k6_lattices @ X7) @ (u1_struct_0 @ X7))
% 0.21/0.47          | ~ (l2_lattices @ X7)
% 0.21/0.47          | (v2_struct_0 @ X7))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k6_lattices])).
% 0.21/0.47  thf(t23_lattices, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.21/0.47         ( v8_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.47           ( ![C:$i]:
% 0.21/0.47             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.47               ( r1_lattices @ A @ ( k4_lattices @ A @ B @ C ) @ B ) ) ) ) ) ))).
% 0.21/0.47  thf('53', plain,
% 0.21/0.47      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.21/0.47          | (r1_lattices @ X13 @ (k4_lattices @ X13 @ X12 @ X14) @ X12)
% 0.21/0.47          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.21/0.47          | ~ (l3_lattices @ X13)
% 0.21/0.47          | ~ (v8_lattices @ X13)
% 0.21/0.47          | ~ (v6_lattices @ X13)
% 0.21/0.47          | (v2_struct_0 @ X13))),
% 0.21/0.47      inference('cnf', [status(esa)], [t23_lattices])).
% 0.21/0.47  thf('54', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((v2_struct_0 @ X0)
% 0.21/0.47          | ~ (l2_lattices @ X0)
% 0.21/0.47          | (v2_struct_0 @ X0)
% 0.21/0.47          | ~ (v6_lattices @ X0)
% 0.21/0.47          | ~ (v8_lattices @ X0)
% 0.21/0.47          | ~ (l3_lattices @ X0)
% 0.21/0.47          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.47          | (r1_lattices @ X0 @ (k4_lattices @ X0 @ (k6_lattices @ X0) @ X1) @ 
% 0.21/0.47             (k6_lattices @ X0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.47  thf('55', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((r1_lattices @ X0 @ (k4_lattices @ X0 @ (k6_lattices @ X0) @ X1) @ 
% 0.21/0.47           (k6_lattices @ X0))
% 0.21/0.47          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.47          | ~ (l3_lattices @ X0)
% 0.21/0.47          | ~ (v8_lattices @ X0)
% 0.21/0.47          | ~ (v6_lattices @ X0)
% 0.21/0.47          | ~ (l2_lattices @ X0)
% 0.21/0.47          | (v2_struct_0 @ X0))),
% 0.21/0.47      inference('simplify', [status(thm)], ['54'])).
% 0.21/0.47  thf('56', plain,
% 0.21/0.47      (((v2_struct_0 @ sk_A)
% 0.21/0.47        | ~ (l2_lattices @ sk_A)
% 0.21/0.47        | ~ (v6_lattices @ sk_A)
% 0.21/0.47        | ~ (v8_lattices @ sk_A)
% 0.21/0.47        | ~ (l3_lattices @ sk_A)
% 0.21/0.47        | (r1_lattices @ sk_A @ 
% 0.21/0.47           (k4_lattices @ sk_A @ (k6_lattices @ sk_A) @ sk_B) @ 
% 0.21/0.47           (k6_lattices @ sk_A)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['51', '55'])).
% 0.21/0.47  thf('57', plain, ((l2_lattices @ sk_A)),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.47  thf('58', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((v2_struct_0 @ X0)
% 0.21/0.47          | ~ (v10_lattices @ X0)
% 0.21/0.47          | (v6_lattices @ X0)
% 0.21/0.47          | ~ (l3_lattices @ X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.47  thf('59', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('60', plain,
% 0.21/0.47      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['58', '59'])).
% 0.21/0.47  thf('61', plain, ((l3_lattices @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('62', plain, ((v10_lattices @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('63', plain, ((v6_lattices @ sk_A)),
% 0.21/0.47      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.21/0.47  thf('64', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((v2_struct_0 @ X0)
% 0.21/0.47          | ~ (v10_lattices @ X0)
% 0.21/0.47          | (v8_lattices @ X0)
% 0.21/0.47          | ~ (l3_lattices @ X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.47  thf('65', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('66', plain,
% 0.21/0.47      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.47  thf('67', plain, ((l3_lattices @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('68', plain, ((v10_lattices @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('69', plain, ((v8_lattices @ sk_A)),
% 0.21/0.47      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.21/0.47  thf('70', plain, ((l3_lattices @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('71', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t43_lattices, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.47         ( v14_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.47           ( ( k4_lattices @ A @ ( k6_lattices @ A ) @ B ) = ( B ) ) ) ) ))).
% 0.21/0.47  thf('72', plain,
% 0.21/0.47      (![X15 : $i, X16 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 0.21/0.47          | ((k4_lattices @ X16 @ (k6_lattices @ X16) @ X15) = (X15))
% 0.21/0.47          | ~ (l3_lattices @ X16)
% 0.21/0.47          | ~ (v14_lattices @ X16)
% 0.21/0.47          | ~ (v10_lattices @ X16)
% 0.21/0.47          | (v2_struct_0 @ X16))),
% 0.21/0.47      inference('cnf', [status(esa)], [t43_lattices])).
% 0.21/0.47  thf('73', plain,
% 0.21/0.47      (((v2_struct_0 @ sk_A)
% 0.21/0.47        | ~ (v10_lattices @ sk_A)
% 0.21/0.47        | ~ (v14_lattices @ sk_A)
% 0.21/0.47        | ~ (l3_lattices @ sk_A)
% 0.21/0.47        | ((k4_lattices @ sk_A @ (k6_lattices @ sk_A) @ sk_B) = (sk_B)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['71', '72'])).
% 0.21/0.47  thf('74', plain, ((v10_lattices @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('75', plain, ((v14_lattices @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('76', plain, ((l3_lattices @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('77', plain,
% 0.21/0.47      (((v2_struct_0 @ sk_A)
% 0.21/0.48        | ((k4_lattices @ sk_A @ (k6_lattices @ sk_A) @ sk_B) = (sk_B)))),
% 0.21/0.48      inference('demod', [status(thm)], ['73', '74', '75', '76'])).
% 0.21/0.48  thf('78', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('79', plain,
% 0.21/0.48      (((k4_lattices @ sk_A @ (k6_lattices @ sk_A) @ sk_B) = (sk_B))),
% 0.21/0.48      inference('clc', [status(thm)], ['77', '78'])).
% 0.21/0.48  thf('80', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_A)
% 0.21/0.48        | (r1_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A)))),
% 0.21/0.48      inference('demod', [status(thm)], ['56', '57', '63', '69', '70', '79'])).
% 0.21/0.48  thf('81', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('82', plain, ((r1_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))),
% 0.21/0.48      inference('clc', [status(thm)], ['80', '81'])).
% 0.21/0.48  thf('83', plain, ($false), inference('demod', [status(thm)], ['50', '82'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
