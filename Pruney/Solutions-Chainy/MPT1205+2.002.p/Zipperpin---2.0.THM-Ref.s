%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KUl15pDH8U

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 168 expanded)
%              Number of leaves         :   29 (  64 expanded)
%              Depth                    :   16
%              Number of atoms          :  786 (1857 expanded)
%              Number of equality atoms :   33 (  83 expanded)
%              Maximal formula depth    :   16 (   5 average)

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

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

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

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(redefinition_k3_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v4_lattices @ A )
        & ( l2_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k3_lattices @ A @ B @ C )
        = ( k1_lattices @ A @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l2_lattices @ X10 )
      | ~ ( v4_lattices @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( ( k3_lattices @ X10 @ X9 @ X11 )
        = ( k1_lattices @ X10 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_lattices])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( ( k3_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
        = ( k1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_lattices @ X0 )
      | ~ ( l2_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l2_lattices @ X0 )
      | ~ ( v4_lattices @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k3_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
        = ( k1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 ) )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ( ( k3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
      = ( k1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ) )
    | ~ ( v4_lattices @ sk_A )
    | ~ ( l2_lattices @ sk_A ) ),
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

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
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

thf('12',plain,(
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

thf('13',plain,(
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
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
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
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ~ ( v8_lattices @ sk_A )
    | ~ ( v9_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( r1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
    | ( ( k2_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
     != ( k5_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,(
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

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['19','20','21'])).

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
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
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

thf('32',plain,(
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

thf('33',plain,(
    ! [X1: $i,X3: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_lattices @ X1 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ( ( k2_lattices @ X1 @ ( k5_lattices @ X1 ) @ X3 )
        = ( k5_lattices @ X1 ) )
      | ~ ( m1_subset_1 @ ( k5_lattices @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v13_lattices @ X1 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
        = ( k5_lattices @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
        = ( k5_lattices @ X0 ) )
      | ~ ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ~ ( v13_lattices @ sk_A )
    | ( ( k2_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
      = ( k5_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf('37',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('38',plain,(
    v13_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
      = ( k5_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k2_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
    = ( k5_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
    | ( ( k5_lattices @ sk_A )
     != ( k5_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','22','28','29','41'])).

thf('43',plain,
    ( ( r1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    r1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
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

thf('47',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r1_lattices @ X5 @ X4 @ X6 )
      | ( ( k1_lattices @ X5 @ X4 @ X6 )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l2_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_lattices])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
        = X1 )
      | ~ ( r1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
      | ( ( k1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l2_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['45','49'])).

thf('51',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('52',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X8: $i] :
      ( ( l2_lattices @ X8 )
      | ~ ( l3_lattices @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('54',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
      = sk_B ) ),
    inference(demod,[status(thm)],['50','51','54','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k1_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
    = sk_B ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v4_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v4_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['52','53'])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
      = sk_B ) ),
    inference(demod,[status(thm)],['6','9','58','64','65'])).

thf('67',plain,(
    ( k3_lattices @ sk_A @ ( k5_lattices @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['66','67'])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['0','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KUl15pDH8U
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:39:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 95 iterations in 0.090s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.21/0.51  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 0.21/0.51  thf(k1_lattices_type, type, k1_lattices: $i > $i > $i > $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.21/0.51  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.21/0.51  thf(k5_lattices_type, type, k5_lattices: $i > $i).
% 0.21/0.51  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.21/0.51  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 0.21/0.51  thf(k3_lattices_type, type, k3_lattices: $i > $i > $i > $i).
% 0.21/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.51  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.21/0.51  thf(v13_lattices_type, type, v13_lattices: $i > $o).
% 0.21/0.51  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.21/0.51  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.21/0.51  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.21/0.51  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 0.21/0.51  thf(t39_lattices, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.51         ( v13_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51           ( ( k3_lattices @ A @ ( k5_lattices @ A ) @ B ) = ( B ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.51            ( v13_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.51          ( ![B:$i]:
% 0.21/0.51            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51              ( ( k3_lattices @ A @ ( k5_lattices @ A ) @ B ) = ( B ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t39_lattices])).
% 0.21/0.51  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_k5_lattices, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 0.21/0.51       ( m1_subset_1 @ ( k5_lattices @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X7 : $i]:
% 0.21/0.51         ((m1_subset_1 @ (k5_lattices @ X7) @ (u1_struct_0 @ X7))
% 0.21/0.51          | ~ (l1_lattices @ X7)
% 0.21/0.51          | (v2_struct_0 @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 0.21/0.51  thf(redefinition_k3_lattices, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.21/0.51         ( l2_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.51         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51       ( ( k3_lattices @ A @ B @ C ) = ( k1_lattices @ A @ B @ C ) ) ))).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.21/0.51          | ~ (l2_lattices @ X10)
% 0.21/0.51          | ~ (v4_lattices @ X10)
% 0.21/0.51          | (v2_struct_0 @ X10)
% 0.21/0.51          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.21/0.51          | ((k3_lattices @ X10 @ X9 @ X11) = (k1_lattices @ X10 @ X9 @ X11)))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k3_lattices])).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X0)
% 0.21/0.51          | ~ (l1_lattices @ X0)
% 0.21/0.51          | ((k3_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 0.21/0.51              = (k1_lattices @ X0 @ (k5_lattices @ X0) @ X1))
% 0.21/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.51          | (v2_struct_0 @ X0)
% 0.21/0.51          | ~ (v4_lattices @ X0)
% 0.21/0.51          | ~ (l2_lattices @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (l2_lattices @ X0)
% 0.21/0.51          | ~ (v4_lattices @ X0)
% 0.21/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.51          | ((k3_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 0.21/0.51              = (k1_lattices @ X0 @ (k5_lattices @ X0) @ X1))
% 0.21/0.51          | ~ (l1_lattices @ X0)
% 0.21/0.51          | (v2_struct_0 @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (l1_lattices @ sk_A)
% 0.21/0.51        | ((k3_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)
% 0.21/0.51            = (k1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B))
% 0.21/0.51        | ~ (v4_lattices @ sk_A)
% 0.21/0.51        | ~ (l2_lattices @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '5'])).
% 0.21/0.51  thf('7', plain, ((l3_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_l3_lattices, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 0.21/0.51  thf('8', plain, (![X8 : $i]: ((l1_lattices @ X8) | ~ (l3_lattices @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.21/0.51  thf('9', plain, ((l1_lattices @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf('10', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (![X7 : $i]:
% 0.21/0.51         ((m1_subset_1 @ (k5_lattices @ X7) @ (u1_struct_0 @ X7))
% 0.21/0.51          | ~ (l1_lattices @ X7)
% 0.21/0.51          | (v2_struct_0 @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 0.21/0.51  thf(t21_lattices, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v8_lattices @ A ) & 
% 0.21/0.51         ( v9_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51               ( ( r1_lattices @ A @ B @ C ) <=>
% 0.21/0.51                 ( ( k2_lattices @ A @ B @ C ) = ( B ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.21/0.51          | ((k2_lattices @ X13 @ X12 @ X14) != (X12))
% 0.21/0.51          | (r1_lattices @ X13 @ X12 @ X14)
% 0.21/0.51          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.21/0.51          | ~ (l3_lattices @ X13)
% 0.21/0.51          | ~ (v9_lattices @ X13)
% 0.21/0.51          | ~ (v8_lattices @ X13)
% 0.21/0.51          | (v2_struct_0 @ X13))),
% 0.21/0.51      inference('cnf', [status(esa)], [t21_lattices])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X0)
% 0.21/0.51          | ~ (l1_lattices @ X0)
% 0.21/0.51          | (v2_struct_0 @ X0)
% 0.21/0.51          | ~ (v8_lattices @ X0)
% 0.21/0.51          | ~ (v9_lattices @ X0)
% 0.21/0.51          | ~ (l3_lattices @ X0)
% 0.21/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.51          | (r1_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 0.21/0.51          | ((k2_lattices @ X0 @ (k5_lattices @ X0) @ X1) != (k5_lattices @ X0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((k2_lattices @ X0 @ (k5_lattices @ X0) @ X1) != (k5_lattices @ X0))
% 0.21/0.51          | (r1_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 0.21/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.51          | ~ (l3_lattices @ X0)
% 0.21/0.51          | ~ (v9_lattices @ X0)
% 0.21/0.51          | ~ (v8_lattices @ X0)
% 0.21/0.51          | ~ (l1_lattices @ X0)
% 0.21/0.51          | (v2_struct_0 @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (l1_lattices @ sk_A)
% 0.21/0.51        | ~ (v8_lattices @ sk_A)
% 0.21/0.51        | ~ (v9_lattices @ sk_A)
% 0.21/0.51        | ~ (l3_lattices @ sk_A)
% 0.21/0.51        | (r1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)
% 0.21/0.51        | ((k2_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)
% 0.21/0.51            != (k5_lattices @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['10', '14'])).
% 0.21/0.51  thf('16', plain, ((l1_lattices @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf(cc1_lattices, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l3_lattices @ A ) =>
% 0.21/0.51       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.21/0.51         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.21/0.51           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.21/0.51           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X0)
% 0.21/0.51          | ~ (v10_lattices @ X0)
% 0.21/0.51          | (v8_lattices @ X0)
% 0.21/0.51          | ~ (l3_lattices @ X0))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.51  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.51  thf('20', plain, ((l3_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('21', plain, ((v10_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('22', plain, ((v8_lattices @ sk_A)),
% 0.21/0.51      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X0)
% 0.21/0.51          | ~ (v10_lattices @ X0)
% 0.21/0.51          | (v9_lattices @ X0)
% 0.21/0.51          | ~ (l3_lattices @ X0))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.51  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.51  thf('26', plain, ((l3_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('27', plain, ((v10_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('28', plain, ((v9_lattices @ sk_A)),
% 0.21/0.51      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.21/0.51  thf('29', plain, ((l3_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('30', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (![X7 : $i]:
% 0.21/0.51         ((m1_subset_1 @ (k5_lattices @ X7) @ (u1_struct_0 @ X7))
% 0.21/0.51          | ~ (l1_lattices @ X7)
% 0.21/0.51          | (v2_struct_0 @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 0.21/0.51  thf(d16_lattices, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 0.21/0.51       ( ( v13_lattices @ A ) =>
% 0.21/0.51         ( ![B:$i]:
% 0.21/0.51           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51             ( ( ( B ) = ( k5_lattices @ A ) ) <=>
% 0.21/0.51               ( ![C:$i]:
% 0.21/0.51                 ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51                   ( ( ( k2_lattices @ A @ B @ C ) = ( B ) ) & 
% 0.21/0.51                     ( ( k2_lattices @ A @ C @ B ) = ( B ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         (~ (v13_lattices @ X1)
% 0.21/0.51          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.21/0.51          | ((X2) != (k5_lattices @ X1))
% 0.21/0.51          | ((k2_lattices @ X1 @ X2 @ X3) = (X2))
% 0.21/0.51          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.21/0.51          | ~ (l1_lattices @ X1)
% 0.21/0.51          | (v2_struct_0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [d16_lattices])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      (![X1 : $i, X3 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X1)
% 0.21/0.51          | ~ (l1_lattices @ X1)
% 0.21/0.51          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.21/0.51          | ((k2_lattices @ X1 @ (k5_lattices @ X1) @ X3) = (k5_lattices @ X1))
% 0.21/0.51          | ~ (m1_subset_1 @ (k5_lattices @ X1) @ (u1_struct_0 @ X1))
% 0.21/0.51          | ~ (v13_lattices @ X1))),
% 0.21/0.51      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X0)
% 0.21/0.51          | ~ (l1_lattices @ X0)
% 0.21/0.51          | ~ (v13_lattices @ X0)
% 0.21/0.51          | ((k2_lattices @ X0 @ (k5_lattices @ X0) @ X1) = (k5_lattices @ X0))
% 0.21/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.51          | ~ (l1_lattices @ X0)
% 0.21/0.51          | (v2_struct_0 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['31', '33'])).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.51          | ((k2_lattices @ X0 @ (k5_lattices @ X0) @ X1) = (k5_lattices @ X0))
% 0.21/0.51          | ~ (v13_lattices @ X0)
% 0.21/0.51          | ~ (l1_lattices @ X0)
% 0.21/0.51          | (v2_struct_0 @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['34'])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (l1_lattices @ sk_A)
% 0.21/0.51        | ~ (v13_lattices @ sk_A)
% 0.21/0.51        | ((k2_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)
% 0.21/0.51            = (k5_lattices @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['30', '35'])).
% 0.21/0.51  thf('37', plain, ((l1_lattices @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf('38', plain, ((v13_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ((k2_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)
% 0.21/0.51            = (k5_lattices @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.21/0.51  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('41', plain,
% 0.21/0.51      (((k2_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)
% 0.21/0.51         = (k5_lattices @ sk_A))),
% 0.21/0.51      inference('clc', [status(thm)], ['39', '40'])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | (r1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)
% 0.21/0.51        | ((k5_lattices @ sk_A) != (k5_lattices @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['15', '16', '22', '28', '29', '41'])).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      (((r1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('simplify', [status(thm)], ['42'])).
% 0.21/0.51  thf('44', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('45', plain, ((r1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B)),
% 0.21/0.51      inference('clc', [status(thm)], ['43', '44'])).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      (![X7 : $i]:
% 0.21/0.51         ((m1_subset_1 @ (k5_lattices @ X7) @ (u1_struct_0 @ X7))
% 0.21/0.51          | ~ (l1_lattices @ X7)
% 0.21/0.51          | (v2_struct_0 @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 0.21/0.51  thf(d3_lattices, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l2_lattices @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51               ( ( r1_lattices @ A @ B @ C ) <=>
% 0.21/0.51                 ( ( k1_lattices @ A @ B @ C ) = ( C ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.21/0.51          | ~ (r1_lattices @ X5 @ X4 @ X6)
% 0.21/0.51          | ((k1_lattices @ X5 @ X4 @ X6) = (X6))
% 0.21/0.51          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.21/0.51          | ~ (l2_lattices @ X5)
% 0.21/0.51          | (v2_struct_0 @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_lattices])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X0)
% 0.21/0.51          | ~ (l1_lattices @ X0)
% 0.21/0.51          | (v2_struct_0 @ X0)
% 0.21/0.51          | ~ (l2_lattices @ X0)
% 0.21/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.51          | ((k1_lattices @ X0 @ (k5_lattices @ X0) @ X1) = (X1))
% 0.21/0.51          | ~ (r1_lattices @ X0 @ (k5_lattices @ X0) @ X1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.51  thf('49', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (r1_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 0.21/0.51          | ((k1_lattices @ X0 @ (k5_lattices @ X0) @ X1) = (X1))
% 0.21/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.51          | ~ (l2_lattices @ X0)
% 0.21/0.51          | ~ (l1_lattices @ X0)
% 0.21/0.51          | (v2_struct_0 @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['48'])).
% 0.21/0.51  thf('50', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (l1_lattices @ sk_A)
% 0.21/0.51        | ~ (l2_lattices @ sk_A)
% 0.21/0.51        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.51        | ((k1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B) = (sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['45', '49'])).
% 0.21/0.51  thf('51', plain, ((l1_lattices @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf('52', plain, ((l3_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('53', plain, (![X8 : $i]: ((l2_lattices @ X8) | ~ (l3_lattices @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.21/0.51  thf('54', plain, ((l2_lattices @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.51  thf('55', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('56', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ((k1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B) = (sk_B)))),
% 0.21/0.51      inference('demod', [status(thm)], ['50', '51', '54', '55'])).
% 0.21/0.51  thf('57', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('58', plain,
% 0.21/0.51      (((k1_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B) = (sk_B))),
% 0.21/0.51      inference('clc', [status(thm)], ['56', '57'])).
% 0.21/0.51  thf('59', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X0)
% 0.21/0.51          | ~ (v10_lattices @ X0)
% 0.21/0.51          | (v4_lattices @ X0)
% 0.21/0.51          | ~ (l3_lattices @ X0))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.51  thf('60', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('61', plain,
% 0.21/0.51      ((~ (l3_lattices @ sk_A) | (v4_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.51  thf('62', plain, ((l3_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('63', plain, ((v10_lattices @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('64', plain, ((v4_lattices @ sk_A)),
% 0.21/0.51      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.21/0.51  thf('65', plain, ((l2_lattices @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.51  thf('66', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ((k3_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B) = (sk_B)))),
% 0.21/0.51      inference('demod', [status(thm)], ['6', '9', '58', '64', '65'])).
% 0.21/0.51  thf('67', plain,
% 0.21/0.51      (((k3_lattices @ sk_A @ (k5_lattices @ sk_A) @ sk_B) != (sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('68', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['66', '67'])).
% 0.21/0.51  thf('69', plain, ($false), inference('demod', [status(thm)], ['0', '68'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
