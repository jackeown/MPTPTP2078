%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mjLH1xWAWy

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:35 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 221 expanded)
%              Number of leaves         :   30 (  78 expanded)
%              Depth                    :   14
%              Number of atoms          :  974 (2460 expanded)
%              Number of equality atoms :   48 ( 116 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(v14_lattices_type,type,(
    v14_lattices: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(k4_lattices_type,type,(
    k4_lattices: $i > $i > $i > $i )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(k6_lattices_type,type,(
    k6_lattices: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_lattices_type,type,(
    k1_lattices: $i > $i > $i > $i )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t43_lattices,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v14_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k4_lattices @ A @ ( k6_lattices @ A ) @ B )
            = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v14_lattices @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( k4_lattices @ A @ ( k6_lattices @ A ) @ B )
              = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_lattices])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l2_lattices @ A ) )
     => ( m1_subset_1 @ ( k6_lattices @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( k6_lattices @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( l2_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_lattices])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
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

thf('3',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( r1_lattices @ X16 @ X15 @ X17 )
      | ( ( k2_lattices @ X16 @ X15 @ X17 )
        = X15 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l3_lattices @ X16 )
      | ~ ( v9_lattices @ X16 )
      | ~ ( v8_lattices @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t21_lattices])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ sk_B @ X0 )
        = sk_B )
      | ~ ( r1_lattices @ sk_A @ sk_B @ X0 ) ) ),
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
      | ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('6',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ sk_B @ X0 )
        = sk_B )
      | ~ ( r1_lattices @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['4','10','16','17'])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ~ ( r1_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
    | ( ( k2_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
      = sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','18'])).

thf('20',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('21',plain,(
    ! [X11: $i] :
      ( ( l2_lattices @ X11 )
      | ~ ( l3_lattices @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('22',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( k6_lattices @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( l2_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_lattices])).

thf('24',plain,(
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

thf('25',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ( ( k1_lattices @ X8 @ X7 @ X9 )
       != X9 )
      | ( r1_lattices @ X8 @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l2_lattices @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_lattices])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l2_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ sk_B @ X0 )
      | ( ( k1_lattices @ sk_A @ sk_B @ X0 )
       != X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ sk_B @ X0 )
      | ( ( k1_lattices @ sk_A @ sk_B @ X0 )
       != X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ( ( k1_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
     != ( k6_lattices @ sk_A ) )
    | ( r1_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
     != ( k6_lattices @ sk_A ) )
    | ( r1_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r1_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
    | ( ( k1_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
     != ( k6_lattices @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( ( k1_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
     != ( k6_lattices @ sk_A ) )
    | ( r1_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( k6_lattices @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( l2_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
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

thf('37',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v14_lattices @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( X5
       != ( k6_lattices @ X4 ) )
      | ( ( k1_lattices @ X4 @ X6 @ X5 )
        = X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l2_lattices @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d17_lattices])).

thf('38',plain,(
    ! [X4: $i,X6: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( l2_lattices @ X4 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X4 ) )
      | ( ( k1_lattices @ X4 @ X6 @ ( k6_lattices @ X4 ) )
        = ( k6_lattices @ X4 ) )
      | ~ ( m1_subset_1 @ ( k6_lattices @ X4 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( v14_lattices @ X4 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ~ ( v14_lattices @ X0 )
      | ( ( k1_lattices @ X0 @ X1 @ ( k6_lattices @ X0 ) )
        = ( k6_lattices @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l2_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k1_lattices @ X0 @ X1 @ ( k6_lattices @ X0 ) )
        = ( k6_lattices @ X0 ) )
      | ~ ( v14_lattices @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ~ ( v14_lattices @ sk_A )
    | ( ( k1_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
      = ( k6_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf('43',plain,(
    v14_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
      = ( k6_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k1_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
    = ( k6_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k6_lattices @ sk_A )
     != ( k6_lattices @ sk_A ) )
    | ( r1_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','46'])).

thf('48',plain,(
    r1_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
      = sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','22','48'])).

thf('50',plain,
    ( ( ( k2_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
      = sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ( k4_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( k6_lattices @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( l2_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_lattices])).

thf('53',plain,(
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

thf('54',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_lattices @ X2 )
      | ~ ( v6_lattices @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( ( k4_lattices @ X2 @ X1 @ X3 )
        = ( k4_lattices @ X2 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k4_lattices])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X11: $i] :
      ( ( l1_lattices @ X11 )
      | ~ ( l3_lattices @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('64',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','61','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ( ( k4_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
      = ( k4_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','67'])).

thf('69',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
      = ( k4_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( k4_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
    = ( k4_lattices @ sk_A @ ( k6_lattices @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    ( k4_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
 != sk_B ),
    inference(demod,[status(thm)],['51','72'])).

thf('74',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( k6_lattices @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( l2_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_lattices])).

thf('75',plain,(
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

thf('76',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_lattices @ X13 )
      | ~ ( v6_lattices @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ( ( k4_lattices @ X13 @ X12 @ X14 )
        = ( k2_lattices @ X13 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_lattices])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B @ X0 )
        = ( k2_lattices @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('79',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['62','63'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B @ X0 )
        = ( k2_lattices @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B @ X0 )
        = ( k2_lattices @ sk_A @ sk_B @ X0 ) ) ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ( ( k4_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
      = ( k2_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['74','82'])).

thf('84',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
      = ( k2_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( k4_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
    = ( k2_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    ( k2_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
 != sk_B ),
    inference(demod,[status(thm)],['73','87'])).

thf('89',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['50','88'])).

thf('90',plain,(
    $false ),
    inference(demod,[status(thm)],['0','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mjLH1xWAWy
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:07:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 95 iterations in 0.089s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.22/0.52  thf(v14_lattices_type, type, v14_lattices: $i > $o).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.52  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.22/0.52  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.22/0.52  thf(k4_lattices_type, type, k4_lattices: $i > $i > $i > $i).
% 0.22/0.52  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 0.22/0.52  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.22/0.52  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.22/0.52  thf(k6_lattices_type, type, k6_lattices: $i > $i).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.52  thf(k1_lattices_type, type, k1_lattices: $i > $i > $i > $i).
% 0.22/0.52  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.22/0.52  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.22/0.52  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.22/0.52  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 0.22/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.52  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 0.22/0.52  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.22/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.52  thf(t43_lattices, conjecture,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.22/0.52         ( v14_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.52           ( ( k4_lattices @ A @ ( k6_lattices @ A ) @ B ) = ( B ) ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i]:
% 0.22/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.22/0.52            ( v14_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.22/0.52          ( ![B:$i]:
% 0.22/0.52            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.52              ( ( k4_lattices @ A @ ( k6_lattices @ A ) @ B ) = ( B ) ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t43_lattices])).
% 0.22/0.52  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(dt_k6_lattices, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l2_lattices @ A ) ) =>
% 0.22/0.52       ( m1_subset_1 @ ( k6_lattices @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      (![X10 : $i]:
% 0.22/0.52         ((m1_subset_1 @ (k6_lattices @ X10) @ (u1_struct_0 @ X10))
% 0.22/0.52          | ~ (l2_lattices @ X10)
% 0.22/0.52          | (v2_struct_0 @ X10))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k6_lattices])).
% 0.22/0.52  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t21_lattices, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v8_lattices @ A ) & 
% 0.22/0.52         ( v9_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.52           ( ![C:$i]:
% 0.22/0.52             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.52               ( ( r1_lattices @ A @ B @ C ) <=>
% 0.22/0.52                 ( ( k2_lattices @ A @ B @ C ) = ( B ) ) ) ) ) ) ) ))).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 0.22/0.52          | ~ (r1_lattices @ X16 @ X15 @ X17)
% 0.22/0.52          | ((k2_lattices @ X16 @ X15 @ X17) = (X15))
% 0.22/0.52          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.22/0.52          | ~ (l3_lattices @ X16)
% 0.22/0.52          | ~ (v9_lattices @ X16)
% 0.22/0.52          | ~ (v8_lattices @ X16)
% 0.22/0.52          | (v2_struct_0 @ X16))),
% 0.22/0.52      inference('cnf', [status(esa)], [t21_lattices])).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_A)
% 0.22/0.52          | ~ (v8_lattices @ sk_A)
% 0.22/0.52          | ~ (v9_lattices @ sk_A)
% 0.22/0.52          | ~ (l3_lattices @ sk_A)
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.52          | ((k2_lattices @ sk_A @ sk_B @ X0) = (sk_B))
% 0.22/0.52          | ~ (r1_lattices @ sk_A @ sk_B @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.52  thf(cc1_lattices, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( l3_lattices @ A ) =>
% 0.22/0.52       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.22/0.52         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.22/0.52           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.22/0.52           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.22/0.52  thf('5', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X0)
% 0.22/0.52          | ~ (v10_lattices @ X0)
% 0.22/0.52          | (v8_lattices @ X0)
% 0.22/0.52          | ~ (l3_lattices @ X0))),
% 0.22/0.52      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.22/0.52  thf('6', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('7', plain,
% 0.22/0.52      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.52  thf('8', plain, ((l3_lattices @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('9', plain, ((v10_lattices @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('10', plain, ((v8_lattices @ sk_A)),
% 0.22/0.52      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X0)
% 0.22/0.52          | ~ (v10_lattices @ X0)
% 0.22/0.52          | (v9_lattices @ X0)
% 0.22/0.52          | ~ (l3_lattices @ X0))),
% 0.22/0.52      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.22/0.52  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.52  thf('14', plain, ((l3_lattices @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('15', plain, ((v10_lattices @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('16', plain, ((v9_lattices @ sk_A)),
% 0.22/0.52      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.22/0.52  thf('17', plain, ((l3_lattices @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_A)
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.52          | ((k2_lattices @ sk_A @ sk_B @ X0) = (sk_B))
% 0.22/0.52          | ~ (r1_lattices @ sk_A @ sk_B @ X0))),
% 0.22/0.52      inference('demod', [status(thm)], ['4', '10', '16', '17'])).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_A)
% 0.22/0.52        | ~ (l2_lattices @ sk_A)
% 0.22/0.52        | ~ (r1_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.22/0.52        | ((k2_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A)) = (sk_B))
% 0.22/0.52        | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['1', '18'])).
% 0.22/0.52  thf('20', plain, ((l3_lattices @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(dt_l3_lattices, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      (![X11 : $i]: ((l2_lattices @ X11) | ~ (l3_lattices @ X11))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.22/0.52  thf('22', plain, ((l2_lattices @ sk_A)),
% 0.22/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      (![X10 : $i]:
% 0.22/0.52         ((m1_subset_1 @ (k6_lattices @ X10) @ (u1_struct_0 @ X10))
% 0.22/0.52          | ~ (l2_lattices @ X10)
% 0.22/0.52          | (v2_struct_0 @ X10))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k6_lattices])).
% 0.22/0.52  thf('24', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(d3_lattices, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l2_lattices @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.52           ( ![C:$i]:
% 0.22/0.52             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.52               ( ( r1_lattices @ A @ B @ C ) <=>
% 0.22/0.52                 ( ( k1_lattices @ A @ B @ C ) = ( C ) ) ) ) ) ) ) ))).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.22/0.52          | ((k1_lattices @ X8 @ X7 @ X9) != (X9))
% 0.22/0.52          | (r1_lattices @ X8 @ X7 @ X9)
% 0.22/0.52          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.22/0.52          | ~ (l2_lattices @ X8)
% 0.22/0.52          | (v2_struct_0 @ X8))),
% 0.22/0.52      inference('cnf', [status(esa)], [d3_lattices])).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_A)
% 0.22/0.52          | ~ (l2_lattices @ sk_A)
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.52          | (r1_lattices @ sk_A @ sk_B @ X0)
% 0.22/0.52          | ((k1_lattices @ sk_A @ sk_B @ X0) != (X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.52  thf('27', plain, ((l2_lattices @ sk_A)),
% 0.22/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.52  thf('28', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_A)
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.52          | (r1_lattices @ sk_A @ sk_B @ X0)
% 0.22/0.52          | ((k1_lattices @ sk_A @ sk_B @ X0) != (X0)))),
% 0.22/0.52      inference('demod', [status(thm)], ['26', '27'])).
% 0.22/0.52  thf('29', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_A)
% 0.22/0.52        | ~ (l2_lattices @ sk_A)
% 0.22/0.52        | ((k1_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.22/0.52            != (k6_lattices @ sk_A))
% 0.22/0.52        | (r1_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.22/0.52        | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['23', '28'])).
% 0.22/0.52  thf('30', plain, ((l2_lattices @ sk_A)),
% 0.22/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.52  thf('31', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_A)
% 0.22/0.52        | ((k1_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.22/0.52            != (k6_lattices @ sk_A))
% 0.22/0.52        | (r1_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.22/0.52        | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['29', '30'])).
% 0.22/0.52  thf('32', plain,
% 0.22/0.52      (((r1_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.22/0.52        | ((k1_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.22/0.52            != (k6_lattices @ sk_A))
% 0.22/0.52        | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('simplify', [status(thm)], ['31'])).
% 0.22/0.52  thf('33', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('34', plain,
% 0.22/0.52      ((((k1_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.22/0.52          != (k6_lattices @ sk_A))
% 0.22/0.52        | (r1_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A)))),
% 0.22/0.52      inference('clc', [status(thm)], ['32', '33'])).
% 0.22/0.52  thf('35', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('36', plain,
% 0.22/0.52      (![X10 : $i]:
% 0.22/0.52         ((m1_subset_1 @ (k6_lattices @ X10) @ (u1_struct_0 @ X10))
% 0.22/0.52          | ~ (l2_lattices @ X10)
% 0.22/0.52          | (v2_struct_0 @ X10))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k6_lattices])).
% 0.22/0.52  thf(d17_lattices, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l2_lattices @ A ) ) =>
% 0.22/0.52       ( ( v14_lattices @ A ) =>
% 0.22/0.52         ( ![B:$i]:
% 0.22/0.52           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.52             ( ( ( B ) = ( k6_lattices @ A ) ) <=>
% 0.22/0.52               ( ![C:$i]:
% 0.22/0.52                 ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.52                   ( ( ( k1_lattices @ A @ B @ C ) = ( B ) ) & 
% 0.22/0.52                     ( ( k1_lattices @ A @ C @ B ) = ( B ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.52  thf('37', plain,
% 0.22/0.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.52         (~ (v14_lattices @ X4)
% 0.22/0.52          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.22/0.52          | ((X5) != (k6_lattices @ X4))
% 0.22/0.52          | ((k1_lattices @ X4 @ X6 @ X5) = (X5))
% 0.22/0.52          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X4))
% 0.22/0.52          | ~ (l2_lattices @ X4)
% 0.22/0.52          | (v2_struct_0 @ X4))),
% 0.22/0.52      inference('cnf', [status(esa)], [d17_lattices])).
% 0.22/0.52  thf('38', plain,
% 0.22/0.52      (![X4 : $i, X6 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X4)
% 0.22/0.52          | ~ (l2_lattices @ X4)
% 0.22/0.52          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X4))
% 0.22/0.52          | ((k1_lattices @ X4 @ X6 @ (k6_lattices @ X4)) = (k6_lattices @ X4))
% 0.22/0.52          | ~ (m1_subset_1 @ (k6_lattices @ X4) @ (u1_struct_0 @ X4))
% 0.22/0.52          | ~ (v14_lattices @ X4))),
% 0.22/0.52      inference('simplify', [status(thm)], ['37'])).
% 0.22/0.52  thf('39', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X0)
% 0.22/0.52          | ~ (l2_lattices @ X0)
% 0.22/0.52          | ~ (v14_lattices @ X0)
% 0.22/0.52          | ((k1_lattices @ X0 @ X1 @ (k6_lattices @ X0)) = (k6_lattices @ X0))
% 0.22/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.52          | ~ (l2_lattices @ X0)
% 0.22/0.52          | (v2_struct_0 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['36', '38'])).
% 0.22/0.52  thf('40', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.52          | ((k1_lattices @ X0 @ X1 @ (k6_lattices @ X0)) = (k6_lattices @ X0))
% 0.22/0.52          | ~ (v14_lattices @ X0)
% 0.22/0.52          | ~ (l2_lattices @ X0)
% 0.22/0.52          | (v2_struct_0 @ X0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['39'])).
% 0.22/0.52  thf('41', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_A)
% 0.22/0.52        | ~ (l2_lattices @ sk_A)
% 0.22/0.52        | ~ (v14_lattices @ sk_A)
% 0.22/0.52        | ((k1_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.22/0.52            = (k6_lattices @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['35', '40'])).
% 0.22/0.52  thf('42', plain, ((l2_lattices @ sk_A)),
% 0.22/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.52  thf('43', plain, ((v14_lattices @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('44', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_A)
% 0.22/0.52        | ((k1_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.22/0.52            = (k6_lattices @ sk_A)))),
% 0.22/0.52      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.22/0.52  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('46', plain,
% 0.22/0.52      (((k1_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.22/0.52         = (k6_lattices @ sk_A))),
% 0.22/0.52      inference('clc', [status(thm)], ['44', '45'])).
% 0.22/0.52  thf('47', plain,
% 0.22/0.52      ((((k6_lattices @ sk_A) != (k6_lattices @ sk_A))
% 0.22/0.52        | (r1_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A)))),
% 0.22/0.52      inference('demod', [status(thm)], ['34', '46'])).
% 0.22/0.52  thf('48', plain, ((r1_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))),
% 0.22/0.52      inference('simplify', [status(thm)], ['47'])).
% 0.22/0.52  thf('49', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_A)
% 0.22/0.52        | ((k2_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A)) = (sk_B))
% 0.22/0.52        | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['19', '22', '48'])).
% 0.22/0.52  thf('50', plain,
% 0.22/0.52      ((((k2_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A)) = (sk_B))
% 0.22/0.52        | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('simplify', [status(thm)], ['49'])).
% 0.22/0.52  thf('51', plain,
% 0.22/0.52      (((k4_lattices @ sk_A @ (k6_lattices @ sk_A) @ sk_B) != (sk_B))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('52', plain,
% 0.22/0.52      (![X10 : $i]:
% 0.22/0.52         ((m1_subset_1 @ (k6_lattices @ X10) @ (u1_struct_0 @ X10))
% 0.22/0.52          | ~ (l2_lattices @ X10)
% 0.22/0.52          | (v2_struct_0 @ X10))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k6_lattices])).
% 0.22/0.52  thf('53', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(commutativity_k4_lattices, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.22/0.52         ( l1_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.52         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52       ( ( k4_lattices @ A @ B @ C ) = ( k4_lattices @ A @ C @ B ) ) ))).
% 0.22/0.52  thf('54', plain,
% 0.22/0.52      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.22/0.52          | ~ (l1_lattices @ X2)
% 0.22/0.52          | ~ (v6_lattices @ X2)
% 0.22/0.52          | (v2_struct_0 @ X2)
% 0.22/0.52          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.22/0.52          | ((k4_lattices @ X2 @ X1 @ X3) = (k4_lattices @ X2 @ X3 @ X1)))),
% 0.22/0.52      inference('cnf', [status(esa)], [commutativity_k4_lattices])).
% 0.22/0.52  thf('55', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k4_lattices @ sk_A @ sk_B @ X0) = (k4_lattices @ sk_A @ X0 @ sk_B))
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.52          | (v2_struct_0 @ sk_A)
% 0.22/0.52          | ~ (v6_lattices @ sk_A)
% 0.22/0.52          | ~ (l1_lattices @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['53', '54'])).
% 0.22/0.52  thf('56', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X0)
% 0.22/0.52          | ~ (v10_lattices @ X0)
% 0.22/0.52          | (v6_lattices @ X0)
% 0.22/0.52          | ~ (l3_lattices @ X0))),
% 0.22/0.52      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.22/0.52  thf('57', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('58', plain,
% 0.22/0.52      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['56', '57'])).
% 0.22/0.52  thf('59', plain, ((l3_lattices @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('60', plain, ((v10_lattices @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('61', plain, ((v6_lattices @ sk_A)),
% 0.22/0.52      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.22/0.52  thf('62', plain, ((l3_lattices @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('63', plain,
% 0.22/0.52      (![X11 : $i]: ((l1_lattices @ X11) | ~ (l3_lattices @ X11))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.22/0.52  thf('64', plain, ((l1_lattices @ sk_A)),
% 0.22/0.52      inference('sup-', [status(thm)], ['62', '63'])).
% 0.22/0.52  thf('65', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k4_lattices @ sk_A @ sk_B @ X0) = (k4_lattices @ sk_A @ X0 @ sk_B))
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.52          | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['55', '61', '64'])).
% 0.22/0.52  thf('66', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('67', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.52          | ((k4_lattices @ sk_A @ sk_B @ X0)
% 0.22/0.52              = (k4_lattices @ sk_A @ X0 @ sk_B)))),
% 0.22/0.52      inference('clc', [status(thm)], ['65', '66'])).
% 0.22/0.52  thf('68', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_A)
% 0.22/0.52        | ~ (l2_lattices @ sk_A)
% 0.22/0.52        | ((k4_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.22/0.52            = (k4_lattices @ sk_A @ (k6_lattices @ sk_A) @ sk_B)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['52', '67'])).
% 0.22/0.52  thf('69', plain, ((l2_lattices @ sk_A)),
% 0.22/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.52  thf('70', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_A)
% 0.22/0.52        | ((k4_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.22/0.52            = (k4_lattices @ sk_A @ (k6_lattices @ sk_A) @ sk_B)))),
% 0.22/0.52      inference('demod', [status(thm)], ['68', '69'])).
% 0.22/0.52  thf('71', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('72', plain,
% 0.22/0.52      (((k4_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.22/0.52         = (k4_lattices @ sk_A @ (k6_lattices @ sk_A) @ sk_B))),
% 0.22/0.52      inference('clc', [status(thm)], ['70', '71'])).
% 0.22/0.52  thf('73', plain,
% 0.22/0.52      (((k4_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A)) != (sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['51', '72'])).
% 0.22/0.52  thf('74', plain,
% 0.22/0.52      (![X10 : $i]:
% 0.22/0.52         ((m1_subset_1 @ (k6_lattices @ X10) @ (u1_struct_0 @ X10))
% 0.22/0.52          | ~ (l2_lattices @ X10)
% 0.22/0.52          | (v2_struct_0 @ X10))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k6_lattices])).
% 0.22/0.52  thf('75', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(redefinition_k4_lattices, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.22/0.52         ( l1_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.52         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52       ( ( k4_lattices @ A @ B @ C ) = ( k2_lattices @ A @ B @ C ) ) ))).
% 0.22/0.52  thf('76', plain,
% 0.22/0.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.22/0.52          | ~ (l1_lattices @ X13)
% 0.22/0.52          | ~ (v6_lattices @ X13)
% 0.22/0.52          | (v2_struct_0 @ X13)
% 0.22/0.52          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.22/0.52          | ((k4_lattices @ X13 @ X12 @ X14) = (k2_lattices @ X13 @ X12 @ X14)))),
% 0.22/0.52      inference('cnf', [status(esa)], [redefinition_k4_lattices])).
% 0.22/0.52  thf('77', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k4_lattices @ sk_A @ sk_B @ X0) = (k2_lattices @ sk_A @ sk_B @ X0))
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.52          | (v2_struct_0 @ sk_A)
% 0.22/0.52          | ~ (v6_lattices @ sk_A)
% 0.22/0.52          | ~ (l1_lattices @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['75', '76'])).
% 0.22/0.52  thf('78', plain, ((v6_lattices @ sk_A)),
% 0.22/0.52      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.22/0.52  thf('79', plain, ((l1_lattices @ sk_A)),
% 0.22/0.52      inference('sup-', [status(thm)], ['62', '63'])).
% 0.22/0.52  thf('80', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k4_lattices @ sk_A @ sk_B @ X0) = (k2_lattices @ sk_A @ sk_B @ X0))
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.52          | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.22/0.52  thf('81', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('82', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.52          | ((k4_lattices @ sk_A @ sk_B @ X0)
% 0.22/0.52              = (k2_lattices @ sk_A @ sk_B @ X0)))),
% 0.22/0.52      inference('clc', [status(thm)], ['80', '81'])).
% 0.22/0.52  thf('83', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_A)
% 0.22/0.52        | ~ (l2_lattices @ sk_A)
% 0.22/0.52        | ((k4_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.22/0.52            = (k2_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['74', '82'])).
% 0.22/0.52  thf('84', plain, ((l2_lattices @ sk_A)),
% 0.22/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.52  thf('85', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_A)
% 0.22/0.52        | ((k4_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.22/0.52            = (k2_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))))),
% 0.22/0.52      inference('demod', [status(thm)], ['83', '84'])).
% 0.22/0.52  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('87', plain,
% 0.22/0.52      (((k4_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.22/0.52         = (k2_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A)))),
% 0.22/0.52      inference('clc', [status(thm)], ['85', '86'])).
% 0.22/0.52  thf('88', plain,
% 0.22/0.52      (((k2_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A)) != (sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['73', '87'])).
% 0.22/0.52  thf('89', plain, ((v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['50', '88'])).
% 0.22/0.52  thf('90', plain, ($false), inference('demod', [status(thm)], ['0', '89'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
