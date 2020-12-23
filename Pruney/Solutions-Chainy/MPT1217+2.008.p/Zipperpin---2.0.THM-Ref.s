%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6ujaiBoT0j

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:39 EST 2020

% Result     : Theorem 0.80s
% Output     : Refutation 0.80s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 373 expanded)
%              Number of leaves         :   34 ( 124 expanded)
%              Depth                    :   18
%              Number of atoms          : 1217 (5945 expanded)
%              Number of equality atoms :   28 (  28 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(k4_lattices_type,type,(
    k4_lattices: $i > $i > $i > $i )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(k7_lattices_type,type,(
    k7_lattices: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(v17_lattices_type,type,(
    v17_lattices: $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_lattices_type,type,(
    k1_lattices: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_lattices_type,type,(
    k3_lattices: $i > $i > $i > $i )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(t53_lattices,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v17_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r3_lattices @ A @ B @ C )
               => ( r3_lattices @ A @ ( k7_lattices @ A @ C ) @ ( k7_lattices @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v17_lattices @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( r3_lattices @ A @ B @ C )
                 => ( r3_lattices @ A @ ( k7_lattices @ A @ C ) @ ( k7_lattices @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t53_lattices])).

thf('0',plain,(
    ~ ( r3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_1 ) @ ( k7_lattices @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_lattices,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k7_lattices @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l3_lattices @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( m1_subset_1 @ ( k7_lattices @ X4 @ X5 ) @ ( u1_struct_0 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattices])).

thf('3',plain,
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l3_lattices @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( m1_subset_1 @ ( k7_lattices @ X4 @ X5 ) @ ( u1_struct_0 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattices])).

thf('10',plain,
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['12','13'])).

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

thf('15',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ( r1_lattices @ X17 @ ( k4_lattices @ X17 @ X16 @ X18 ) @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l3_lattices @ X17 )
      | ~ ( v8_lattices @ X17 )
      | ~ ( v6_lattices @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t23_lattices])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_1 ) @ X0 ) @ ( k7_lattices @ sk_A @ sk_B_1 ) ) ) ),
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
      | ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_1 ) @ X0 ) @ ( k7_lattices @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['16','22','28','29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_1 ) @ X0 ) @ ( k7_lattices @ sk_A @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_1 ) @ ( k7_lattices @ sk_A @ sk_C_1 ) ) @ ( k7_lattices @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['7','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t51_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v17_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( k7_lattices @ A @ ( k3_lattices @ A @ B @ C ) )
                = ( k4_lattices @ A @ ( k7_lattices @ A @ B ) @ ( k7_lattices @ A @ C ) ) ) ) ) ) )).

thf('36',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ( ( k7_lattices @ X20 @ ( k3_lattices @ X20 @ X19 @ X21 ) )
        = ( k4_lattices @ X20 @ ( k7_lattices @ X20 @ X19 ) @ ( k7_lattices @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l3_lattices @ X20 )
      | ~ ( v17_lattices @ X20 )
      | ~ ( v10_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t51_lattices])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v17_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k7_lattices @ sk_A @ ( k3_lattices @ sk_A @ sk_B_1 @ X0 ) )
        = ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_1 ) @ ( k7_lattices @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v17_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k7_lattices @ sk_A @ ( k3_lattices @ sk_A @ sk_B_1 @ X0 ) )
        = ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_1 ) @ ( k7_lattices @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k7_lattices @ sk_A @ ( k3_lattices @ sk_A @ sk_B_1 @ X0 ) )
        = ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_1 ) @ ( k7_lattices @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k7_lattices @ sk_A @ ( k3_lattices @ sk_A @ sk_B_1 @ sk_C_1 ) )
    = ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_1 ) @ ( k7_lattices @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['34','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
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

thf('47',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v8_lattices @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( ( k1_lattices @ X1 @ ( k2_lattices @ X1 @ X3 @ X2 ) @ X2 )
        = X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_lattices])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_C_1 ) @ sk_C_1 )
        = sk_C_1 )
      | ~ ( v8_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_C_1 ) @ sk_C_1 )
        = sk_C_1 ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_C_1 ) @ sk_C_1 )
        = sk_C_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_1 @ sk_C_1 ) @ sk_C_1 )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['45','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
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

thf('57',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( r1_lattices @ X14 @ X13 @ X15 )
      | ( ( k2_lattices @ X14 @ X13 @ X15 )
        = X13 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l3_lattices @ X14 )
      | ~ ( v9_lattices @ X14 )
      | ~ ( v8_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t21_lattices])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ sk_B_1 @ X0 )
        = sk_B_1 )
      | ~ ( r1_lattices @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ sk_B_1 @ X0 )
        = sk_B_1 )
      | ~ ( r1_lattices @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['58','59','65','66'])).

thf('68',plain,
    ( ~ ( r1_lattices @ sk_A @ sk_B_1 @ sk_C_1 )
    | ( ( k2_lattices @ sk_A @ sk_B_1 @ sk_C_1 )
      = sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['55','67'])).

thf('69',plain,(
    r3_lattices @ sk_A @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
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

thf('71',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l3_lattices @ X11 )
      | ~ ( v9_lattices @ X11 )
      | ~ ( v8_lattices @ X11 )
      | ~ ( v6_lattices @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( r1_lattices @ X11 @ X10 @ X12 )
      | ~ ( r3_lattices @ X11 @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattices @ sk_A @ sk_B_1 @ X0 )
      | ( r1_lattices @ sk_A @ sk_B_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('74',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('75',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('76',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattices @ sk_A @ sk_B_1 @ X0 )
      | ( r1_lattices @ sk_A @ sk_B_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73','74','75','76'])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_lattices @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['69','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    r1_lattices @ sk_A @ sk_B_1 @ sk_C_1 ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( k2_lattices @ sk_A @ sk_B_1 @ sk_C_1 )
      = sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['68','82'])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( k2_lattices @ sk_A @ sk_B_1 @ sk_C_1 )
    = sk_B_1 ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k1_lattices @ sk_A @ sk_B_1 @ sk_C_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['54','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
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

thf('89',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l2_lattices @ X8 )
      | ~ ( v4_lattices @ X8 )
      | ( v2_struct_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ( ( k3_lattices @ X8 @ X7 @ X9 )
        = ( k1_lattices @ X8 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_lattices])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k1_lattices @ sk_A @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v4_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v4_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('98',plain,(
    ! [X6: $i] :
      ( ( l2_lattices @ X6 )
      | ~ ( l3_lattices @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('99',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k1_lattices @ sk_A @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','96','99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k1_lattices @ sk_A @ sk_B_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k3_lattices @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k1_lattices @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['87','102'])).

thf('104',plain,
    ( ( k3_lattices @ sk_A @ sk_B_1 @ sk_C_1 )
    = sk_C_1 ),
    inference('sup+',[status(thm)],['86','103'])).

thf('105',plain,
    ( ( k7_lattices @ sk_A @ sk_C_1 )
    = ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B_1 ) @ ( k7_lattices @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['44','104'])).

thf('106',plain,(
    r1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_1 ) @ ( k7_lattices @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['33','105'])).

thf('107',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('108',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l3_lattices @ X11 )
      | ~ ( v9_lattices @ X11 )
      | ~ ( v8_lattices @ X11 )
      | ~ ( v6_lattices @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( r3_lattices @ X11 @ X10 @ X12 )
      | ~ ( r1_lattices @ X11 @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_1 ) @ X0 )
      | ( r3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_1 ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('111',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('112',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('113',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_1 ) @ X0 )
      | ( r3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_1 ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['109','110','111','112','113'])).

thf('115',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( r3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_1 ) @ ( k7_lattices @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['106','114'])).

thf('116',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('117',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_1 ) @ ( k7_lattices @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    r3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_1 ) @ ( k7_lattices @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,(
    $false ),
    inference(demod,[status(thm)],['0','119'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6ujaiBoT0j
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:30:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.80/1.00  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.80/1.00  % Solved by: fo/fo7.sh
% 0.80/1.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.80/1.00  % done 371 iterations in 0.544s
% 0.80/1.00  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.80/1.00  % SZS output start Refutation
% 0.80/1.00  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.80/1.00  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 0.80/1.00  thf(k4_lattices_type, type, k4_lattices: $i > $i > $i > $i).
% 0.80/1.00  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.80/1.00  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.80/1.00  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.80/1.00  thf(k7_lattices_type, type, k7_lattices: $i > $i > $i).
% 0.80/1.00  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.80/1.00  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 0.80/1.00  thf(sk_A_type, type, sk_A: $i).
% 0.80/1.00  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 0.80/1.00  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.80/1.00  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 0.80/1.00  thf(v17_lattices_type, type, v17_lattices: $i > $o).
% 0.80/1.00  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.80/1.00  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.80/1.00  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.80/1.00  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.80/1.00  thf(k1_lattices_type, type, k1_lattices: $i > $i > $i > $i).
% 0.80/1.00  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.80/1.00  thf(k3_lattices_type, type, k3_lattices: $i > $i > $i > $i).
% 0.80/1.00  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.80/1.00  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.80/1.00  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.80/1.00  thf(t53_lattices, conjecture,
% 0.80/1.00    (![A:$i]:
% 0.80/1.00     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.80/1.00         ( v17_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.80/1.00       ( ![B:$i]:
% 0.80/1.00         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.80/1.00           ( ![C:$i]:
% 0.80/1.00             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.80/1.00               ( ( r3_lattices @ A @ B @ C ) =>
% 0.80/1.00                 ( r3_lattices @
% 0.80/1.00                   A @ ( k7_lattices @ A @ C ) @ ( k7_lattices @ A @ B ) ) ) ) ) ) ) ))).
% 0.80/1.00  thf(zf_stmt_0, negated_conjecture,
% 0.80/1.00    (~( ![A:$i]:
% 0.80/1.00        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.80/1.00            ( v17_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.80/1.00          ( ![B:$i]:
% 0.80/1.00            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.80/1.00              ( ![C:$i]:
% 0.80/1.00                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.80/1.00                  ( ( r3_lattices @ A @ B @ C ) =>
% 0.80/1.00                    ( r3_lattices @
% 0.80/1.00                      A @ ( k7_lattices @ A @ C ) @ ( k7_lattices @ A @ B ) ) ) ) ) ) ) ) )),
% 0.80/1.00    inference('cnf.neg', [status(esa)], [t53_lattices])).
% 0.80/1.00  thf('0', plain,
% 0.80/1.00      (~ (r3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_1) @ 
% 0.80/1.00          (k7_lattices @ sk_A @ sk_B_1))),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf(dt_k7_lattices, axiom,
% 0.80/1.00    (![A:$i,B:$i]:
% 0.80/1.00     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) & 
% 0.80/1.00         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.80/1.00       ( m1_subset_1 @ ( k7_lattices @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.80/1.00  thf('2', plain,
% 0.80/1.00      (![X4 : $i, X5 : $i]:
% 0.80/1.00         (~ (l3_lattices @ X4)
% 0.80/1.00          | (v2_struct_0 @ X4)
% 0.80/1.00          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.80/1.00          | (m1_subset_1 @ (k7_lattices @ X4 @ X5) @ (u1_struct_0 @ X4)))),
% 0.80/1.00      inference('cnf', [status(esa)], [dt_k7_lattices])).
% 0.80/1.00  thf('3', plain,
% 0.80/1.00      (((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C_1) @ (u1_struct_0 @ sk_A))
% 0.80/1.00        | (v2_struct_0 @ sk_A)
% 0.80/1.00        | ~ (l3_lattices @ sk_A))),
% 0.80/1.00      inference('sup-', [status(thm)], ['1', '2'])).
% 0.80/1.00  thf('4', plain, ((l3_lattices @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('5', plain,
% 0.80/1.00      (((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C_1) @ (u1_struct_0 @ sk_A))
% 0.80/1.00        | (v2_struct_0 @ sk_A))),
% 0.80/1.00      inference('demod', [status(thm)], ['3', '4'])).
% 0.80/1.00  thf('6', plain, (~ (v2_struct_0 @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('7', plain,
% 0.80/1.00      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C_1) @ (u1_struct_0 @ sk_A))),
% 0.80/1.00      inference('clc', [status(thm)], ['5', '6'])).
% 0.80/1.00  thf('8', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('9', plain,
% 0.80/1.00      (![X4 : $i, X5 : $i]:
% 0.80/1.00         (~ (l3_lattices @ X4)
% 0.80/1.00          | (v2_struct_0 @ X4)
% 0.80/1.00          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.80/1.00          | (m1_subset_1 @ (k7_lattices @ X4 @ X5) @ (u1_struct_0 @ X4)))),
% 0.80/1.00      inference('cnf', [status(esa)], [dt_k7_lattices])).
% 0.80/1.00  thf('10', plain,
% 0.80/1.00      (((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.80/1.00        | (v2_struct_0 @ sk_A)
% 0.80/1.00        | ~ (l3_lattices @ sk_A))),
% 0.80/1.00      inference('sup-', [status(thm)], ['8', '9'])).
% 0.80/1.00  thf('11', plain, ((l3_lattices @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('12', plain,
% 0.80/1.00      (((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.80/1.00        | (v2_struct_0 @ sk_A))),
% 0.80/1.00      inference('demod', [status(thm)], ['10', '11'])).
% 0.80/1.00  thf('13', plain, (~ (v2_struct_0 @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('14', plain,
% 0.80/1.00      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.80/1.00      inference('clc', [status(thm)], ['12', '13'])).
% 0.80/1.00  thf(t23_lattices, axiom,
% 0.80/1.00    (![A:$i]:
% 0.80/1.00     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.80/1.00         ( v8_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.80/1.00       ( ![B:$i]:
% 0.80/1.00         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.80/1.00           ( ![C:$i]:
% 0.80/1.00             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.80/1.00               ( r1_lattices @ A @ ( k4_lattices @ A @ B @ C ) @ B ) ) ) ) ) ))).
% 0.80/1.00  thf('15', plain,
% 0.80/1.00      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.80/1.00         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.80/1.00          | (r1_lattices @ X17 @ (k4_lattices @ X17 @ X16 @ X18) @ X16)
% 0.80/1.00          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.80/1.00          | ~ (l3_lattices @ X17)
% 0.80/1.00          | ~ (v8_lattices @ X17)
% 0.80/1.00          | ~ (v6_lattices @ X17)
% 0.80/1.00          | (v2_struct_0 @ X17))),
% 0.80/1.00      inference('cnf', [status(esa)], [t23_lattices])).
% 0.80/1.00  thf('16', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         ((v2_struct_0 @ sk_A)
% 0.80/1.00          | ~ (v6_lattices @ sk_A)
% 0.80/1.00          | ~ (v8_lattices @ sk_A)
% 0.80/1.00          | ~ (l3_lattices @ sk_A)
% 0.80/1.00          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.80/1.00          | (r1_lattices @ sk_A @ 
% 0.80/1.00             (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_1) @ X0) @ 
% 0.80/1.00             (k7_lattices @ sk_A @ sk_B_1)))),
% 0.80/1.00      inference('sup-', [status(thm)], ['14', '15'])).
% 0.80/1.00  thf(cc1_lattices, axiom,
% 0.80/1.00    (![A:$i]:
% 0.80/1.00     ( ( l3_lattices @ A ) =>
% 0.80/1.00       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.80/1.00         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.80/1.00           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.80/1.00           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.80/1.00  thf('17', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         ((v2_struct_0 @ X0)
% 0.80/1.00          | ~ (v10_lattices @ X0)
% 0.80/1.00          | (v6_lattices @ X0)
% 0.80/1.00          | ~ (l3_lattices @ X0))),
% 0.80/1.00      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.80/1.00  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('19', plain,
% 0.80/1.00      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.80/1.00      inference('sup-', [status(thm)], ['17', '18'])).
% 0.80/1.00  thf('20', plain, ((l3_lattices @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('21', plain, ((v10_lattices @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('22', plain, ((v6_lattices @ sk_A)),
% 0.80/1.00      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.80/1.00  thf('23', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         ((v2_struct_0 @ X0)
% 0.80/1.00          | ~ (v10_lattices @ X0)
% 0.80/1.00          | (v8_lattices @ X0)
% 0.80/1.00          | ~ (l3_lattices @ X0))),
% 0.80/1.00      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.80/1.00  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('25', plain,
% 0.80/1.00      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.80/1.00      inference('sup-', [status(thm)], ['23', '24'])).
% 0.80/1.00  thf('26', plain, ((l3_lattices @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('27', plain, ((v10_lattices @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('28', plain, ((v8_lattices @ sk_A)),
% 0.80/1.00      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.80/1.00  thf('29', plain, ((l3_lattices @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('30', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         ((v2_struct_0 @ sk_A)
% 0.80/1.00          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.80/1.00          | (r1_lattices @ sk_A @ 
% 0.80/1.00             (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_1) @ X0) @ 
% 0.80/1.00             (k7_lattices @ sk_A @ sk_B_1)))),
% 0.80/1.00      inference('demod', [status(thm)], ['16', '22', '28', '29'])).
% 0.80/1.00  thf('31', plain, (~ (v2_struct_0 @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('32', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         ((r1_lattices @ sk_A @ 
% 0.80/1.00           (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_1) @ X0) @ 
% 0.80/1.00           (k7_lattices @ sk_A @ sk_B_1))
% 0.80/1.00          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.00      inference('clc', [status(thm)], ['30', '31'])).
% 0.80/1.00  thf('33', plain,
% 0.80/1.00      ((r1_lattices @ sk_A @ 
% 0.80/1.00        (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_1) @ 
% 0.80/1.00         (k7_lattices @ sk_A @ sk_C_1)) @ 
% 0.80/1.00        (k7_lattices @ sk_A @ sk_B_1))),
% 0.80/1.00      inference('sup-', [status(thm)], ['7', '32'])).
% 0.80/1.00  thf('34', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('35', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf(t51_lattices, axiom,
% 0.80/1.00    (![A:$i]:
% 0.80/1.00     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.80/1.00         ( v17_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.80/1.00       ( ![B:$i]:
% 0.80/1.00         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.80/1.00           ( ![C:$i]:
% 0.80/1.00             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.80/1.00               ( ( k7_lattices @ A @ ( k3_lattices @ A @ B @ C ) ) =
% 0.80/1.00                 ( k4_lattices @
% 0.80/1.00                   A @ ( k7_lattices @ A @ B ) @ ( k7_lattices @ A @ C ) ) ) ) ) ) ) ))).
% 0.80/1.00  thf('36', plain,
% 0.80/1.00      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.80/1.00         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 0.80/1.00          | ((k7_lattices @ X20 @ (k3_lattices @ X20 @ X19 @ X21))
% 0.80/1.00              = (k4_lattices @ X20 @ (k7_lattices @ X20 @ X19) @ 
% 0.80/1.00                 (k7_lattices @ X20 @ X21)))
% 0.80/1.00          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.80/1.00          | ~ (l3_lattices @ X20)
% 0.80/1.00          | ~ (v17_lattices @ X20)
% 0.80/1.00          | ~ (v10_lattices @ X20)
% 0.80/1.00          | (v2_struct_0 @ X20))),
% 0.80/1.00      inference('cnf', [status(esa)], [t51_lattices])).
% 0.80/1.00  thf('37', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         ((v2_struct_0 @ sk_A)
% 0.80/1.00          | ~ (v10_lattices @ sk_A)
% 0.80/1.00          | ~ (v17_lattices @ sk_A)
% 0.80/1.00          | ~ (l3_lattices @ sk_A)
% 0.80/1.00          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.80/1.00          | ((k7_lattices @ sk_A @ (k3_lattices @ sk_A @ sk_B_1 @ X0))
% 0.80/1.00              = (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_1) @ 
% 0.80/1.00                 (k7_lattices @ sk_A @ X0))))),
% 0.80/1.00      inference('sup-', [status(thm)], ['35', '36'])).
% 0.80/1.00  thf('38', plain, ((v10_lattices @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('39', plain, ((v17_lattices @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('40', plain, ((l3_lattices @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('41', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         ((v2_struct_0 @ sk_A)
% 0.80/1.00          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.80/1.00          | ((k7_lattices @ sk_A @ (k3_lattices @ sk_A @ sk_B_1 @ X0))
% 0.80/1.00              = (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_1) @ 
% 0.80/1.00                 (k7_lattices @ sk_A @ X0))))),
% 0.80/1.00      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 0.80/1.00  thf('42', plain, (~ (v2_struct_0 @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('43', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         (((k7_lattices @ sk_A @ (k3_lattices @ sk_A @ sk_B_1 @ X0))
% 0.80/1.00            = (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_1) @ 
% 0.80/1.00               (k7_lattices @ sk_A @ X0)))
% 0.80/1.00          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.00      inference('clc', [status(thm)], ['41', '42'])).
% 0.80/1.00  thf('44', plain,
% 0.80/1.00      (((k7_lattices @ sk_A @ (k3_lattices @ sk_A @ sk_B_1 @ sk_C_1))
% 0.80/1.00         = (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_1) @ 
% 0.80/1.00            (k7_lattices @ sk_A @ sk_C_1)))),
% 0.80/1.00      inference('sup-', [status(thm)], ['34', '43'])).
% 0.80/1.00  thf('45', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('46', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf(d8_lattices, axiom,
% 0.80/1.00    (![A:$i]:
% 0.80/1.00     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.80/1.00       ( ( v8_lattices @ A ) <=>
% 0.80/1.00         ( ![B:$i]:
% 0.80/1.00           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.80/1.00             ( ![C:$i]:
% 0.80/1.00               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.80/1.00                 ( ( k1_lattices @ A @ ( k2_lattices @ A @ B @ C ) @ C ) =
% 0.80/1.00                   ( C ) ) ) ) ) ) ) ))).
% 0.80/1.00  thf('47', plain,
% 0.80/1.00      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.80/1.00         (~ (v8_lattices @ X1)
% 0.80/1.00          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.80/1.00          | ((k1_lattices @ X1 @ (k2_lattices @ X1 @ X3 @ X2) @ X2) = (X2))
% 0.80/1.00          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.80/1.00          | ~ (l3_lattices @ X1)
% 0.80/1.00          | (v2_struct_0 @ X1))),
% 0.80/1.00      inference('cnf', [status(esa)], [d8_lattices])).
% 0.80/1.00  thf('48', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         ((v2_struct_0 @ sk_A)
% 0.80/1.00          | ~ (l3_lattices @ sk_A)
% 0.80/1.00          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.80/1.00          | ((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_C_1) @ sk_C_1)
% 0.80/1.00              = (sk_C_1))
% 0.80/1.00          | ~ (v8_lattices @ sk_A))),
% 0.80/1.00      inference('sup-', [status(thm)], ['46', '47'])).
% 0.80/1.00  thf('49', plain, ((l3_lattices @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('50', plain, ((v8_lattices @ sk_A)),
% 0.80/1.00      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.80/1.00  thf('51', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         ((v2_struct_0 @ sk_A)
% 0.80/1.00          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.80/1.00          | ((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_C_1) @ sk_C_1)
% 0.80/1.00              = (sk_C_1)))),
% 0.80/1.00      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.80/1.00  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('53', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         (((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_C_1) @ sk_C_1)
% 0.80/1.00            = (sk_C_1))
% 0.80/1.00          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.00      inference('clc', [status(thm)], ['51', '52'])).
% 0.80/1.00  thf('54', plain,
% 0.80/1.00      (((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_B_1 @ sk_C_1) @ sk_C_1)
% 0.80/1.00         = (sk_C_1))),
% 0.80/1.00      inference('sup-', [status(thm)], ['45', '53'])).
% 0.80/1.00  thf('55', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('56', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf(t21_lattices, axiom,
% 0.80/1.00    (![A:$i]:
% 0.80/1.00     ( ( ( ~( v2_struct_0 @ A ) ) & ( v8_lattices @ A ) & 
% 0.80/1.00         ( v9_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.80/1.00       ( ![B:$i]:
% 0.80/1.00         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.80/1.00           ( ![C:$i]:
% 0.80/1.00             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.80/1.00               ( ( r1_lattices @ A @ B @ C ) <=>
% 0.80/1.00                 ( ( k2_lattices @ A @ B @ C ) = ( B ) ) ) ) ) ) ) ))).
% 0.80/1.00  thf('57', plain,
% 0.80/1.00      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.80/1.00         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.80/1.00          | ~ (r1_lattices @ X14 @ X13 @ X15)
% 0.80/1.00          | ((k2_lattices @ X14 @ X13 @ X15) = (X13))
% 0.80/1.00          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.80/1.00          | ~ (l3_lattices @ X14)
% 0.80/1.00          | ~ (v9_lattices @ X14)
% 0.80/1.00          | ~ (v8_lattices @ X14)
% 0.80/1.00          | (v2_struct_0 @ X14))),
% 0.80/1.00      inference('cnf', [status(esa)], [t21_lattices])).
% 0.80/1.00  thf('58', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         ((v2_struct_0 @ sk_A)
% 0.80/1.00          | ~ (v8_lattices @ sk_A)
% 0.80/1.00          | ~ (v9_lattices @ sk_A)
% 0.80/1.00          | ~ (l3_lattices @ sk_A)
% 0.80/1.00          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.80/1.00          | ((k2_lattices @ sk_A @ sk_B_1 @ X0) = (sk_B_1))
% 0.80/1.00          | ~ (r1_lattices @ sk_A @ sk_B_1 @ X0))),
% 0.80/1.00      inference('sup-', [status(thm)], ['56', '57'])).
% 0.80/1.00  thf('59', plain, ((v8_lattices @ sk_A)),
% 0.80/1.00      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.80/1.00  thf('60', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         ((v2_struct_0 @ X0)
% 0.80/1.00          | ~ (v10_lattices @ X0)
% 0.80/1.00          | (v9_lattices @ X0)
% 0.80/1.00          | ~ (l3_lattices @ X0))),
% 0.80/1.00      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.80/1.00  thf('61', plain, (~ (v2_struct_0 @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('62', plain,
% 0.80/1.00      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.80/1.00      inference('sup-', [status(thm)], ['60', '61'])).
% 0.80/1.00  thf('63', plain, ((l3_lattices @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('64', plain, ((v10_lattices @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('65', plain, ((v9_lattices @ sk_A)),
% 0.80/1.00      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.80/1.00  thf('66', plain, ((l3_lattices @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('67', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         ((v2_struct_0 @ sk_A)
% 0.80/1.00          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.80/1.00          | ((k2_lattices @ sk_A @ sk_B_1 @ X0) = (sk_B_1))
% 0.80/1.00          | ~ (r1_lattices @ sk_A @ sk_B_1 @ X0))),
% 0.80/1.00      inference('demod', [status(thm)], ['58', '59', '65', '66'])).
% 0.80/1.00  thf('68', plain,
% 0.80/1.00      ((~ (r1_lattices @ sk_A @ sk_B_1 @ sk_C_1)
% 0.80/1.00        | ((k2_lattices @ sk_A @ sk_B_1 @ sk_C_1) = (sk_B_1))
% 0.80/1.00        | (v2_struct_0 @ sk_A))),
% 0.80/1.00      inference('sup-', [status(thm)], ['55', '67'])).
% 0.80/1.00  thf('69', plain, ((r3_lattices @ sk_A @ sk_B_1 @ sk_C_1)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('70', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf(redefinition_r3_lattices, axiom,
% 0.80/1.00    (![A:$i,B:$i,C:$i]:
% 0.80/1.00     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.80/1.00         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 0.80/1.00         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.80/1.00         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.80/1.00       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 0.80/1.00  thf('71', plain,
% 0.80/1.00      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.80/1.00         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.80/1.00          | ~ (l3_lattices @ X11)
% 0.80/1.00          | ~ (v9_lattices @ X11)
% 0.80/1.00          | ~ (v8_lattices @ X11)
% 0.80/1.00          | ~ (v6_lattices @ X11)
% 0.80/1.00          | (v2_struct_0 @ X11)
% 0.80/1.00          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 0.80/1.00          | (r1_lattices @ X11 @ X10 @ X12)
% 0.80/1.00          | ~ (r3_lattices @ X11 @ X10 @ X12))),
% 0.80/1.00      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.80/1.00  thf('72', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         (~ (r3_lattices @ sk_A @ sk_B_1 @ X0)
% 0.80/1.00          | (r1_lattices @ sk_A @ sk_B_1 @ X0)
% 0.80/1.00          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.80/1.00          | (v2_struct_0 @ sk_A)
% 0.80/1.00          | ~ (v6_lattices @ sk_A)
% 0.80/1.00          | ~ (v8_lattices @ sk_A)
% 0.80/1.00          | ~ (v9_lattices @ sk_A)
% 0.80/1.00          | ~ (l3_lattices @ sk_A))),
% 0.80/1.00      inference('sup-', [status(thm)], ['70', '71'])).
% 0.80/1.00  thf('73', plain, ((v6_lattices @ sk_A)),
% 0.80/1.00      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.80/1.00  thf('74', plain, ((v8_lattices @ sk_A)),
% 0.80/1.00      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.80/1.00  thf('75', plain, ((v9_lattices @ sk_A)),
% 0.80/1.00      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.80/1.00  thf('76', plain, ((l3_lattices @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('77', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         (~ (r3_lattices @ sk_A @ sk_B_1 @ X0)
% 0.80/1.00          | (r1_lattices @ sk_A @ sk_B_1 @ X0)
% 0.80/1.00          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.80/1.00          | (v2_struct_0 @ sk_A))),
% 0.80/1.00      inference('demod', [status(thm)], ['72', '73', '74', '75', '76'])).
% 0.80/1.00  thf('78', plain,
% 0.80/1.00      (((v2_struct_0 @ sk_A)
% 0.80/1.00        | ~ (m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))
% 0.80/1.00        | (r1_lattices @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.80/1.00      inference('sup-', [status(thm)], ['69', '77'])).
% 0.80/1.00  thf('79', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('80', plain,
% 0.80/1.00      (((v2_struct_0 @ sk_A) | (r1_lattices @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.80/1.00      inference('demod', [status(thm)], ['78', '79'])).
% 0.80/1.00  thf('81', plain, (~ (v2_struct_0 @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('82', plain, ((r1_lattices @ sk_A @ sk_B_1 @ sk_C_1)),
% 0.80/1.00      inference('clc', [status(thm)], ['80', '81'])).
% 0.80/1.00  thf('83', plain,
% 0.80/1.00      ((((k2_lattices @ sk_A @ sk_B_1 @ sk_C_1) = (sk_B_1))
% 0.80/1.00        | (v2_struct_0 @ sk_A))),
% 0.80/1.00      inference('demod', [status(thm)], ['68', '82'])).
% 0.80/1.00  thf('84', plain, (~ (v2_struct_0 @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('85', plain, (((k2_lattices @ sk_A @ sk_B_1 @ sk_C_1) = (sk_B_1))),
% 0.80/1.00      inference('clc', [status(thm)], ['83', '84'])).
% 0.80/1.00  thf('86', plain, (((k1_lattices @ sk_A @ sk_B_1 @ sk_C_1) = (sk_C_1))),
% 0.80/1.00      inference('demod', [status(thm)], ['54', '85'])).
% 0.80/1.00  thf('87', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('88', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf(redefinition_k3_lattices, axiom,
% 0.80/1.00    (![A:$i,B:$i,C:$i]:
% 0.80/1.00     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.80/1.00         ( l2_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.80/1.00         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.80/1.00       ( ( k3_lattices @ A @ B @ C ) = ( k1_lattices @ A @ B @ C ) ) ))).
% 0.80/1.00  thf('89', plain,
% 0.80/1.00      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.80/1.00         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.80/1.00          | ~ (l2_lattices @ X8)
% 0.80/1.00          | ~ (v4_lattices @ X8)
% 0.80/1.00          | (v2_struct_0 @ X8)
% 0.80/1.00          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.80/1.00          | ((k3_lattices @ X8 @ X7 @ X9) = (k1_lattices @ X8 @ X7 @ X9)))),
% 0.80/1.00      inference('cnf', [status(esa)], [redefinition_k3_lattices])).
% 0.80/1.00  thf('90', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         (((k3_lattices @ sk_A @ sk_B_1 @ X0)
% 0.80/1.00            = (k1_lattices @ sk_A @ sk_B_1 @ X0))
% 0.80/1.00          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.80/1.00          | (v2_struct_0 @ sk_A)
% 0.80/1.00          | ~ (v4_lattices @ sk_A)
% 0.80/1.00          | ~ (l2_lattices @ sk_A))),
% 0.80/1.00      inference('sup-', [status(thm)], ['88', '89'])).
% 0.80/1.00  thf('91', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         ((v2_struct_0 @ X0)
% 0.80/1.00          | ~ (v10_lattices @ X0)
% 0.80/1.00          | (v4_lattices @ X0)
% 0.80/1.00          | ~ (l3_lattices @ X0))),
% 0.80/1.00      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.80/1.00  thf('92', plain, (~ (v2_struct_0 @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('93', plain,
% 0.80/1.00      ((~ (l3_lattices @ sk_A) | (v4_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.80/1.00      inference('sup-', [status(thm)], ['91', '92'])).
% 0.80/1.00  thf('94', plain, ((l3_lattices @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('95', plain, ((v10_lattices @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('96', plain, ((v4_lattices @ sk_A)),
% 0.80/1.00      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.80/1.00  thf('97', plain, ((l3_lattices @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf(dt_l3_lattices, axiom,
% 0.80/1.00    (![A:$i]:
% 0.80/1.00     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 0.80/1.00  thf('98', plain, (![X6 : $i]: ((l2_lattices @ X6) | ~ (l3_lattices @ X6))),
% 0.80/1.00      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.80/1.00  thf('99', plain, ((l2_lattices @ sk_A)),
% 0.80/1.00      inference('sup-', [status(thm)], ['97', '98'])).
% 0.80/1.00  thf('100', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         (((k3_lattices @ sk_A @ sk_B_1 @ X0)
% 0.80/1.00            = (k1_lattices @ sk_A @ sk_B_1 @ X0))
% 0.80/1.00          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.80/1.00          | (v2_struct_0 @ sk_A))),
% 0.80/1.00      inference('demod', [status(thm)], ['90', '96', '99'])).
% 0.80/1.00  thf('101', plain, (~ (v2_struct_0 @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('102', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.80/1.00          | ((k3_lattices @ sk_A @ sk_B_1 @ X0)
% 0.80/1.00              = (k1_lattices @ sk_A @ sk_B_1 @ X0)))),
% 0.80/1.00      inference('clc', [status(thm)], ['100', '101'])).
% 0.80/1.00  thf('103', plain,
% 0.80/1.00      (((k3_lattices @ sk_A @ sk_B_1 @ sk_C_1)
% 0.80/1.00         = (k1_lattices @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.80/1.00      inference('sup-', [status(thm)], ['87', '102'])).
% 0.80/1.00  thf('104', plain, (((k3_lattices @ sk_A @ sk_B_1 @ sk_C_1) = (sk_C_1))),
% 0.80/1.00      inference('sup+', [status(thm)], ['86', '103'])).
% 0.80/1.00  thf('105', plain,
% 0.80/1.00      (((k7_lattices @ sk_A @ sk_C_1)
% 0.80/1.00         = (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B_1) @ 
% 0.80/1.00            (k7_lattices @ sk_A @ sk_C_1)))),
% 0.80/1.00      inference('demod', [status(thm)], ['44', '104'])).
% 0.80/1.00  thf('106', plain,
% 0.80/1.00      ((r1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_1) @ 
% 0.80/1.00        (k7_lattices @ sk_A @ sk_B_1))),
% 0.80/1.00      inference('demod', [status(thm)], ['33', '105'])).
% 0.80/1.00  thf('107', plain,
% 0.80/1.00      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C_1) @ (u1_struct_0 @ sk_A))),
% 0.80/1.00      inference('clc', [status(thm)], ['5', '6'])).
% 0.80/1.00  thf('108', plain,
% 0.80/1.00      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.80/1.00         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.80/1.00          | ~ (l3_lattices @ X11)
% 0.80/1.00          | ~ (v9_lattices @ X11)
% 0.80/1.00          | ~ (v8_lattices @ X11)
% 0.80/1.00          | ~ (v6_lattices @ X11)
% 0.80/1.00          | (v2_struct_0 @ X11)
% 0.80/1.00          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 0.80/1.00          | (r3_lattices @ X11 @ X10 @ X12)
% 0.80/1.00          | ~ (r1_lattices @ X11 @ X10 @ X12))),
% 0.80/1.00      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.80/1.00  thf('109', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         (~ (r1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_1) @ X0)
% 0.80/1.00          | (r3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_1) @ X0)
% 0.80/1.00          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.80/1.00          | (v2_struct_0 @ sk_A)
% 0.80/1.00          | ~ (v6_lattices @ sk_A)
% 0.80/1.00          | ~ (v8_lattices @ sk_A)
% 0.80/1.00          | ~ (v9_lattices @ sk_A)
% 0.80/1.00          | ~ (l3_lattices @ sk_A))),
% 0.80/1.00      inference('sup-', [status(thm)], ['107', '108'])).
% 0.80/1.00  thf('110', plain, ((v6_lattices @ sk_A)),
% 0.80/1.00      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.80/1.00  thf('111', plain, ((v8_lattices @ sk_A)),
% 0.80/1.00      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.80/1.00  thf('112', plain, ((v9_lattices @ sk_A)),
% 0.80/1.00      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.80/1.00  thf('113', plain, ((l3_lattices @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('114', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         (~ (r1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_1) @ X0)
% 0.80/1.00          | (r3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_1) @ X0)
% 0.80/1.00          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.80/1.00          | (v2_struct_0 @ sk_A))),
% 0.80/1.00      inference('demod', [status(thm)], ['109', '110', '111', '112', '113'])).
% 0.80/1.00  thf('115', plain,
% 0.80/1.00      (((v2_struct_0 @ sk_A)
% 0.80/1.00        | ~ (m1_subset_1 @ (k7_lattices @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.80/1.00        | (r3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_1) @ 
% 0.80/1.00           (k7_lattices @ sk_A @ sk_B_1)))),
% 0.80/1.00      inference('sup-', [status(thm)], ['106', '114'])).
% 0.80/1.00  thf('116', plain,
% 0.80/1.00      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.80/1.00      inference('clc', [status(thm)], ['12', '13'])).
% 0.80/1.00  thf('117', plain,
% 0.80/1.00      (((v2_struct_0 @ sk_A)
% 0.80/1.00        | (r3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_1) @ 
% 0.80/1.00           (k7_lattices @ sk_A @ sk_B_1)))),
% 0.80/1.00      inference('demod', [status(thm)], ['115', '116'])).
% 0.80/1.00  thf('118', plain, (~ (v2_struct_0 @ sk_A)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('119', plain,
% 0.80/1.00      ((r3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_1) @ 
% 0.80/1.00        (k7_lattices @ sk_A @ sk_B_1))),
% 0.80/1.00      inference('clc', [status(thm)], ['117', '118'])).
% 0.80/1.00  thf('120', plain, ($false), inference('demod', [status(thm)], ['0', '119'])).
% 0.80/1.00  
% 0.80/1.00  % SZS output end Refutation
% 0.80/1.00  
% 0.80/1.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
