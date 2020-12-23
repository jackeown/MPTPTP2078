%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.U4pGSrNvWg

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:39 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 317 expanded)
%              Number of leaves         :   32 ( 107 expanded)
%              Depth                    :   15
%              Number of atoms          : 1085 (4977 expanded)
%              Number of equality atoms :   21 (  21 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(k4_lattices_type,type,(
    k4_lattices: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(v17_lattices_type,type,(
    v17_lattices: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_lattices_type,type,(
    k7_lattices: $i > $i > $i )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_lattices_type,type,(
    k3_lattices: $i > $i > $i > $i )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(k1_lattices_type,type,(
    k1_lattices: $i > $i > $i > $i )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

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
    ~ ( r3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ ( k7_lattices @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
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
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l3_lattices @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( m1_subset_1 @ ( k7_lattices @ X4 @ X5 ) @ ( u1_struct_0 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattices])).

thf('10',plain,
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ( r1_lattices @ X14 @ ( k4_lattices @ X14 @ X13 @ X15 ) @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l3_lattices @ X14 )
      | ~ ( v8_lattices @ X14 )
      | ~ ( v6_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t23_lattices])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 ) @ ( k7_lattices @ sk_A @ sk_B ) ) ) ),
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
      | ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 ) @ ( k7_lattices @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['16','22','28','29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 ) @ ( k7_lattices @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ ( k7_lattices @ sk_A @ sk_C ) ) @ ( k7_lattices @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['7','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ( ( k7_lattices @ X17 @ ( k3_lattices @ X17 @ X16 @ X18 ) )
        = ( k4_lattices @ X17 @ ( k7_lattices @ X17 @ X16 ) @ ( k7_lattices @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l3_lattices @ X17 )
      | ~ ( v17_lattices @ X17 )
      | ~ ( v10_lattices @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t51_lattices])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v17_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k7_lattices @ sk_A @ ( k3_lattices @ sk_A @ sk_B @ X0 ) )
        = ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ ( k7_lattices @ sk_A @ X0 ) ) ) ) ),
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
      | ( ( k7_lattices @ sk_A @ ( k3_lattices @ sk_A @ sk_B @ X0 ) )
        = ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ ( k7_lattices @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k7_lattices @ sk_A @ ( k3_lattices @ sk_A @ sk_B @ X0 ) )
        = ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ ( k7_lattices @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k7_lattices @ sk_A @ ( k3_lattices @ sk_A @ sk_B @ sk_C ) )
    = ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ ( k7_lattices @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['34','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
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

thf('47',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( r1_lattices @ X2 @ X1 @ X3 )
      | ( ( k1_lattices @ X2 @ X1 @ X3 )
        = X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l2_lattices @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_lattices])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l2_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ sk_B @ X0 )
        = X0 )
      | ~ ( r1_lattices @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('50',plain,(
    ! [X6: $i] :
      ( ( l2_lattices @ X6 )
      | ~ ( l3_lattices @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('51',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ sk_B @ X0 )
        = X0 )
      | ~ ( r1_lattices @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['48','51'])).

thf('53',plain,
    ( ~ ( r1_lattices @ sk_A @ sk_B @ sk_C )
    | ( ( k1_lattices @ sk_A @ sk_B @ sk_C )
      = sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ( k1_lattices @ sk_A @ sk_B @ sk_C )
      = sk_C )
    | ~ ( r1_lattices @ sk_A @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
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

thf('58',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l2_lattices @ X8 )
      | ~ ( v4_lattices @ X8 )
      | ( v2_struct_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ( ( k3_lattices @ X8 @ X7 @ X9 )
        = ( k1_lattices @ X8 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_lattices])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B @ X0 )
        = ( k1_lattices @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v4_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v4_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['49','50'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B @ X0 )
        = ( k1_lattices @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_B @ X0 )
        = ( k1_lattices @ sk_A @ sk_B @ X0 ) ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k3_lattices @ sk_A @ sk_B @ sk_C )
    = ( k1_lattices @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['56','69'])).

thf('71',plain,
    ( ( ( k3_lattices @ sk_A @ sk_B @ sk_C )
      = sk_C )
    | ~ ( r1_lattices @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['55','70'])).

thf('72',plain,(
    r3_lattices @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
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

thf('74',plain,(
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

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattices @ sk_A @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('77',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattices @ sk_A @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','76','77','83','84'])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( r1_lattices @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['72','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    r1_lattices @ sk_A @ sk_B @ sk_C ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k3_lattices @ sk_A @ sk_B @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['71','90'])).

thf('92',plain,
    ( ( k7_lattices @ sk_A @ sk_C )
    = ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ ( k7_lattices @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['44','91'])).

thf('93',plain,(
    r1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ ( k7_lattices @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['33','92'])).

thf('94',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('95',plain,(
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

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ X0 )
      | ( r3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('98',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('99',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('100',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ X0 )
      | ( r3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['96','97','98','99','100'])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( r3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ ( k7_lattices @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['93','101'])).

thf('103',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ ( k7_lattices @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    r3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ ( k7_lattices @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,(
    $false ),
    inference(demod,[status(thm)],['0','106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.U4pGSrNvWg
% 0.16/0.37  % Computer   : n007.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 13:50:06 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.45/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.65  % Solved by: fo/fo7.sh
% 0.45/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.65  % done 261 iterations in 0.162s
% 0.45/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.65  % SZS output start Refutation
% 0.45/0.65  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.45/0.65  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.45/0.65  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.45/0.65  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.45/0.65  thf(k4_lattices_type, type, k4_lattices: $i > $i > $i > $i).
% 0.45/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.65  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.45/0.65  thf(v17_lattices_type, type, v17_lattices: $i > $o).
% 0.45/0.65  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.65  thf(k7_lattices_type, type, k7_lattices: $i > $i > $i).
% 0.45/0.65  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 0.45/0.65  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 0.45/0.65  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.65  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.65  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.45/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.65  thf(k3_lattices_type, type, k3_lattices: $i > $i > $i > $i).
% 0.45/0.65  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.45/0.65  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.45/0.65  thf(k1_lattices_type, type, k1_lattices: $i > $i > $i > $i).
% 0.45/0.65  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.45/0.65  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 0.45/0.65  thf(t53_lattices, conjecture,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.45/0.65         ( v17_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.45/0.65       ( ![B:$i]:
% 0.45/0.65         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.65           ( ![C:$i]:
% 0.45/0.65             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.65               ( ( r3_lattices @ A @ B @ C ) =>
% 0.45/0.65                 ( r3_lattices @
% 0.45/0.65                   A @ ( k7_lattices @ A @ C ) @ ( k7_lattices @ A @ B ) ) ) ) ) ) ) ))).
% 0.45/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.65    (~( ![A:$i]:
% 0.45/0.65        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.45/0.65            ( v17_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.45/0.65          ( ![B:$i]:
% 0.45/0.65            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.65              ( ![C:$i]:
% 0.45/0.65                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.65                  ( ( r3_lattices @ A @ B @ C ) =>
% 0.45/0.65                    ( r3_lattices @
% 0.45/0.65                      A @ ( k7_lattices @ A @ C ) @ ( k7_lattices @ A @ B ) ) ) ) ) ) ) ) )),
% 0.45/0.65    inference('cnf.neg', [status(esa)], [t53_lattices])).
% 0.45/0.65  thf('0', plain,
% 0.45/0.65      (~ (r3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ 
% 0.45/0.65          (k7_lattices @ sk_A @ sk_B))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('1', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(dt_k7_lattices, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) & 
% 0.45/0.65         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.65       ( m1_subset_1 @ ( k7_lattices @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.45/0.65  thf('2', plain,
% 0.45/0.65      (![X4 : $i, X5 : $i]:
% 0.45/0.65         (~ (l3_lattices @ X4)
% 0.45/0.65          | (v2_struct_0 @ X4)
% 0.45/0.65          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.45/0.65          | (m1_subset_1 @ (k7_lattices @ X4 @ X5) @ (u1_struct_0 @ X4)))),
% 0.45/0.65      inference('cnf', [status(esa)], [dt_k7_lattices])).
% 0.45/0.65  thf('3', plain,
% 0.45/0.65      (((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.45/0.65        | (v2_struct_0 @ sk_A)
% 0.45/0.65        | ~ (l3_lattices @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.65  thf('4', plain, ((l3_lattices @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('5', plain,
% 0.45/0.65      (((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.45/0.65        | (v2_struct_0 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['3', '4'])).
% 0.45/0.65  thf('6', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('7', plain,
% 0.45/0.65      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('clc', [status(thm)], ['5', '6'])).
% 0.45/0.65  thf('8', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('9', plain,
% 0.45/0.65      (![X4 : $i, X5 : $i]:
% 0.45/0.65         (~ (l3_lattices @ X4)
% 0.45/0.65          | (v2_struct_0 @ X4)
% 0.45/0.65          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.45/0.65          | (m1_subset_1 @ (k7_lattices @ X4 @ X5) @ (u1_struct_0 @ X4)))),
% 0.45/0.65      inference('cnf', [status(esa)], [dt_k7_lattices])).
% 0.45/0.65  thf('10', plain,
% 0.45/0.65      (((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.45/0.65        | (v2_struct_0 @ sk_A)
% 0.45/0.65        | ~ (l3_lattices @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['8', '9'])).
% 0.45/0.65  thf('11', plain, ((l3_lattices @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('12', plain,
% 0.45/0.65      (((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.45/0.65        | (v2_struct_0 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['10', '11'])).
% 0.45/0.65  thf('13', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('14', plain,
% 0.45/0.65      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('clc', [status(thm)], ['12', '13'])).
% 0.45/0.65  thf(t23_lattices, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.45/0.65         ( v8_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.45/0.65       ( ![B:$i]:
% 0.45/0.65         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.65           ( ![C:$i]:
% 0.45/0.65             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.65               ( r1_lattices @ A @ ( k4_lattices @ A @ B @ C ) @ B ) ) ) ) ) ))).
% 0.45/0.65  thf('15', plain,
% 0.45/0.65      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.45/0.65          | (r1_lattices @ X14 @ (k4_lattices @ X14 @ X13 @ X15) @ X13)
% 0.45/0.65          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.45/0.65          | ~ (l3_lattices @ X14)
% 0.45/0.65          | ~ (v8_lattices @ X14)
% 0.45/0.65          | ~ (v6_lattices @ X14)
% 0.45/0.65          | (v2_struct_0 @ X14))),
% 0.45/0.65      inference('cnf', [status(esa)], [t23_lattices])).
% 0.45/0.65  thf('16', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((v2_struct_0 @ sk_A)
% 0.45/0.65          | ~ (v6_lattices @ sk_A)
% 0.45/0.65          | ~ (v8_lattices @ sk_A)
% 0.45/0.65          | ~ (l3_lattices @ sk_A)
% 0.45/0.65          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.65          | (r1_lattices @ sk_A @ 
% 0.45/0.65             (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0) @ 
% 0.45/0.65             (k7_lattices @ sk_A @ sk_B)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['14', '15'])).
% 0.45/0.65  thf(cc1_lattices, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( l3_lattices @ A ) =>
% 0.45/0.65       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.45/0.65         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.45/0.65           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.45/0.65           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.45/0.65  thf('17', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((v2_struct_0 @ X0)
% 0.45/0.65          | ~ (v10_lattices @ X0)
% 0.45/0.65          | (v6_lattices @ X0)
% 0.45/0.65          | ~ (l3_lattices @ X0))),
% 0.45/0.65      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.45/0.65  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('19', plain,
% 0.45/0.65      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['17', '18'])).
% 0.45/0.65  thf('20', plain, ((l3_lattices @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('21', plain, ((v10_lattices @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('22', plain, ((v6_lattices @ sk_A)),
% 0.45/0.65      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.45/0.65  thf('23', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((v2_struct_0 @ X0)
% 0.45/0.65          | ~ (v10_lattices @ X0)
% 0.45/0.65          | (v8_lattices @ X0)
% 0.45/0.65          | ~ (l3_lattices @ X0))),
% 0.45/0.65      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.45/0.65  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('25', plain,
% 0.45/0.65      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['23', '24'])).
% 0.45/0.65  thf('26', plain, ((l3_lattices @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('27', plain, ((v10_lattices @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('28', plain, ((v8_lattices @ sk_A)),
% 0.45/0.65      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.45/0.65  thf('29', plain, ((l3_lattices @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('30', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((v2_struct_0 @ sk_A)
% 0.45/0.65          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.65          | (r1_lattices @ sk_A @ 
% 0.45/0.65             (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0) @ 
% 0.45/0.65             (k7_lattices @ sk_A @ sk_B)))),
% 0.45/0.65      inference('demod', [status(thm)], ['16', '22', '28', '29'])).
% 0.45/0.65  thf('31', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('32', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((r1_lattices @ sk_A @ 
% 0.45/0.65           (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0) @ 
% 0.45/0.65           (k7_lattices @ sk_A @ sk_B))
% 0.45/0.65          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('clc', [status(thm)], ['30', '31'])).
% 0.45/0.65  thf('33', plain,
% 0.45/0.65      ((r1_lattices @ sk_A @ 
% 0.45/0.65        (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ 
% 0.45/0.65         (k7_lattices @ sk_A @ sk_C)) @ 
% 0.45/0.65        (k7_lattices @ sk_A @ sk_B))),
% 0.45/0.65      inference('sup-', [status(thm)], ['7', '32'])).
% 0.45/0.65  thf('34', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('35', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(t51_lattices, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.45/0.65         ( v17_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.45/0.65       ( ![B:$i]:
% 0.45/0.65         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.65           ( ![C:$i]:
% 0.45/0.65             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.65               ( ( k7_lattices @ A @ ( k3_lattices @ A @ B @ C ) ) =
% 0.45/0.65                 ( k4_lattices @
% 0.45/0.65                   A @ ( k7_lattices @ A @ B ) @ ( k7_lattices @ A @ C ) ) ) ) ) ) ) ))).
% 0.45/0.65  thf('36', plain,
% 0.45/0.65      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.45/0.65          | ((k7_lattices @ X17 @ (k3_lattices @ X17 @ X16 @ X18))
% 0.45/0.65              = (k4_lattices @ X17 @ (k7_lattices @ X17 @ X16) @ 
% 0.45/0.65                 (k7_lattices @ X17 @ X18)))
% 0.45/0.65          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.45/0.65          | ~ (l3_lattices @ X17)
% 0.45/0.65          | ~ (v17_lattices @ X17)
% 0.45/0.65          | ~ (v10_lattices @ X17)
% 0.45/0.65          | (v2_struct_0 @ X17))),
% 0.45/0.65      inference('cnf', [status(esa)], [t51_lattices])).
% 0.45/0.65  thf('37', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((v2_struct_0 @ sk_A)
% 0.45/0.65          | ~ (v10_lattices @ sk_A)
% 0.45/0.65          | ~ (v17_lattices @ sk_A)
% 0.45/0.65          | ~ (l3_lattices @ sk_A)
% 0.45/0.65          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.65          | ((k7_lattices @ sk_A @ (k3_lattices @ sk_A @ sk_B @ X0))
% 0.45/0.65              = (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ 
% 0.45/0.65                 (k7_lattices @ sk_A @ X0))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['35', '36'])).
% 0.45/0.65  thf('38', plain, ((v10_lattices @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('39', plain, ((v17_lattices @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('40', plain, ((l3_lattices @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('41', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((v2_struct_0 @ sk_A)
% 0.45/0.65          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.65          | ((k7_lattices @ sk_A @ (k3_lattices @ sk_A @ sk_B @ X0))
% 0.45/0.65              = (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ 
% 0.45/0.65                 (k7_lattices @ sk_A @ X0))))),
% 0.45/0.65      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 0.45/0.65  thf('42', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('43', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (((k7_lattices @ sk_A @ (k3_lattices @ sk_A @ sk_B @ X0))
% 0.45/0.65            = (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ 
% 0.45/0.65               (k7_lattices @ sk_A @ X0)))
% 0.45/0.65          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('clc', [status(thm)], ['41', '42'])).
% 0.45/0.65  thf('44', plain,
% 0.45/0.65      (((k7_lattices @ sk_A @ (k3_lattices @ sk_A @ sk_B @ sk_C))
% 0.45/0.65         = (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ 
% 0.45/0.65            (k7_lattices @ sk_A @ sk_C)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['34', '43'])).
% 0.45/0.65  thf('45', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('46', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(d3_lattices, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( l2_lattices @ A ) ) =>
% 0.45/0.65       ( ![B:$i]:
% 0.45/0.65         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.65           ( ![C:$i]:
% 0.45/0.65             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.65               ( ( r1_lattices @ A @ B @ C ) <=>
% 0.45/0.65                 ( ( k1_lattices @ A @ B @ C ) = ( C ) ) ) ) ) ) ) ))).
% 0.45/0.65  thf('47', plain,
% 0.45/0.65      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.45/0.65          | ~ (r1_lattices @ X2 @ X1 @ X3)
% 0.45/0.65          | ((k1_lattices @ X2 @ X1 @ X3) = (X3))
% 0.45/0.65          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.45/0.65          | ~ (l2_lattices @ X2)
% 0.45/0.65          | (v2_struct_0 @ X2))),
% 0.45/0.65      inference('cnf', [status(esa)], [d3_lattices])).
% 0.45/0.65  thf('48', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((v2_struct_0 @ sk_A)
% 0.45/0.65          | ~ (l2_lattices @ sk_A)
% 0.45/0.65          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.65          | ((k1_lattices @ sk_A @ sk_B @ X0) = (X0))
% 0.45/0.65          | ~ (r1_lattices @ sk_A @ sk_B @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['46', '47'])).
% 0.45/0.65  thf('49', plain, ((l3_lattices @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(dt_l3_lattices, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 0.45/0.65  thf('50', plain, (![X6 : $i]: ((l2_lattices @ X6) | ~ (l3_lattices @ X6))),
% 0.45/0.65      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.45/0.65  thf('51', plain, ((l2_lattices @ sk_A)),
% 0.45/0.65      inference('sup-', [status(thm)], ['49', '50'])).
% 0.45/0.65  thf('52', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((v2_struct_0 @ sk_A)
% 0.45/0.65          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.65          | ((k1_lattices @ sk_A @ sk_B @ X0) = (X0))
% 0.45/0.65          | ~ (r1_lattices @ sk_A @ sk_B @ X0))),
% 0.45/0.65      inference('demod', [status(thm)], ['48', '51'])).
% 0.45/0.65  thf('53', plain,
% 0.45/0.65      ((~ (r1_lattices @ sk_A @ sk_B @ sk_C)
% 0.45/0.65        | ((k1_lattices @ sk_A @ sk_B @ sk_C) = (sk_C))
% 0.45/0.65        | (v2_struct_0 @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['45', '52'])).
% 0.45/0.65  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('55', plain,
% 0.45/0.65      ((((k1_lattices @ sk_A @ sk_B @ sk_C) = (sk_C))
% 0.45/0.65        | ~ (r1_lattices @ sk_A @ sk_B @ sk_C))),
% 0.45/0.65      inference('clc', [status(thm)], ['53', '54'])).
% 0.45/0.65  thf('56', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('57', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(redefinition_k3_lattices, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.45/0.65         ( l2_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.45/0.65         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.65       ( ( k3_lattices @ A @ B @ C ) = ( k1_lattices @ A @ B @ C ) ) ))).
% 0.45/0.65  thf('58', plain,
% 0.45/0.65      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.45/0.65          | ~ (l2_lattices @ X8)
% 0.45/0.65          | ~ (v4_lattices @ X8)
% 0.45/0.65          | (v2_struct_0 @ X8)
% 0.45/0.65          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.45/0.65          | ((k3_lattices @ X8 @ X7 @ X9) = (k1_lattices @ X8 @ X7 @ X9)))),
% 0.45/0.65      inference('cnf', [status(esa)], [redefinition_k3_lattices])).
% 0.45/0.65  thf('59', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (((k3_lattices @ sk_A @ sk_B @ X0) = (k1_lattices @ sk_A @ sk_B @ X0))
% 0.45/0.65          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.65          | (v2_struct_0 @ sk_A)
% 0.45/0.65          | ~ (v4_lattices @ sk_A)
% 0.45/0.65          | ~ (l2_lattices @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['57', '58'])).
% 0.45/0.65  thf('60', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((v2_struct_0 @ X0)
% 0.45/0.65          | ~ (v10_lattices @ X0)
% 0.45/0.65          | (v4_lattices @ X0)
% 0.45/0.65          | ~ (l3_lattices @ X0))),
% 0.45/0.65      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.45/0.65  thf('61', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('62', plain,
% 0.45/0.65      ((~ (l3_lattices @ sk_A) | (v4_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['60', '61'])).
% 0.45/0.65  thf('63', plain, ((l3_lattices @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('64', plain, ((v10_lattices @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('65', plain, ((v4_lattices @ sk_A)),
% 0.45/0.65      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.45/0.65  thf('66', plain, ((l2_lattices @ sk_A)),
% 0.45/0.65      inference('sup-', [status(thm)], ['49', '50'])).
% 0.45/0.65  thf('67', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (((k3_lattices @ sk_A @ sk_B @ X0) = (k1_lattices @ sk_A @ sk_B @ X0))
% 0.45/0.65          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.65          | (v2_struct_0 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['59', '65', '66'])).
% 0.45/0.65  thf('68', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('69', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.65          | ((k3_lattices @ sk_A @ sk_B @ X0)
% 0.45/0.65              = (k1_lattices @ sk_A @ sk_B @ X0)))),
% 0.45/0.65      inference('clc', [status(thm)], ['67', '68'])).
% 0.45/0.65  thf('70', plain,
% 0.45/0.65      (((k3_lattices @ sk_A @ sk_B @ sk_C) = (k1_lattices @ sk_A @ sk_B @ sk_C))),
% 0.45/0.65      inference('sup-', [status(thm)], ['56', '69'])).
% 0.45/0.65  thf('71', plain,
% 0.45/0.65      ((((k3_lattices @ sk_A @ sk_B @ sk_C) = (sk_C))
% 0.45/0.65        | ~ (r1_lattices @ sk_A @ sk_B @ sk_C))),
% 0.45/0.65      inference('demod', [status(thm)], ['55', '70'])).
% 0.45/0.65  thf('72', plain, ((r3_lattices @ sk_A @ sk_B @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('73', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(redefinition_r3_lattices, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.45/0.65         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 0.45/0.65         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.45/0.65         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.65       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 0.45/0.65  thf('74', plain,
% 0.45/0.65      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.45/0.65          | ~ (l3_lattices @ X11)
% 0.45/0.65          | ~ (v9_lattices @ X11)
% 0.45/0.65          | ~ (v8_lattices @ X11)
% 0.45/0.65          | ~ (v6_lattices @ X11)
% 0.45/0.65          | (v2_struct_0 @ X11)
% 0.45/0.65          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 0.45/0.65          | (r1_lattices @ X11 @ X10 @ X12)
% 0.45/0.65          | ~ (r3_lattices @ X11 @ X10 @ X12))),
% 0.45/0.65      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.45/0.65  thf('75', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (r3_lattices @ sk_A @ sk_B @ X0)
% 0.45/0.65          | (r1_lattices @ sk_A @ sk_B @ X0)
% 0.45/0.65          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.65          | (v2_struct_0 @ sk_A)
% 0.45/0.65          | ~ (v6_lattices @ sk_A)
% 0.45/0.65          | ~ (v8_lattices @ sk_A)
% 0.45/0.65          | ~ (v9_lattices @ sk_A)
% 0.45/0.65          | ~ (l3_lattices @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['73', '74'])).
% 0.45/0.65  thf('76', plain, ((v6_lattices @ sk_A)),
% 0.45/0.65      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.45/0.65  thf('77', plain, ((v8_lattices @ sk_A)),
% 0.45/0.65      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.45/0.65  thf('78', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((v2_struct_0 @ X0)
% 0.45/0.65          | ~ (v10_lattices @ X0)
% 0.45/0.65          | (v9_lattices @ X0)
% 0.45/0.65          | ~ (l3_lattices @ X0))),
% 0.45/0.65      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.45/0.65  thf('79', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('80', plain,
% 0.45/0.65      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['78', '79'])).
% 0.45/0.65  thf('81', plain, ((l3_lattices @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('82', plain, ((v10_lattices @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('83', plain, ((v9_lattices @ sk_A)),
% 0.45/0.65      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.45/0.65  thf('84', plain, ((l3_lattices @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('85', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (r3_lattices @ sk_A @ sk_B @ X0)
% 0.45/0.65          | (r1_lattices @ sk_A @ sk_B @ X0)
% 0.45/0.65          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.65          | (v2_struct_0 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['75', '76', '77', '83', '84'])).
% 0.45/0.65  thf('86', plain,
% 0.45/0.65      (((v2_struct_0 @ sk_A)
% 0.45/0.65        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.45/0.65        | (r1_lattices @ sk_A @ sk_B @ sk_C))),
% 0.45/0.65      inference('sup-', [status(thm)], ['72', '85'])).
% 0.45/0.65  thf('87', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('88', plain,
% 0.45/0.65      (((v2_struct_0 @ sk_A) | (r1_lattices @ sk_A @ sk_B @ sk_C))),
% 0.45/0.65      inference('demod', [status(thm)], ['86', '87'])).
% 0.45/0.65  thf('89', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('90', plain, ((r1_lattices @ sk_A @ sk_B @ sk_C)),
% 0.45/0.65      inference('clc', [status(thm)], ['88', '89'])).
% 0.45/0.65  thf('91', plain, (((k3_lattices @ sk_A @ sk_B @ sk_C) = (sk_C))),
% 0.45/0.65      inference('demod', [status(thm)], ['71', '90'])).
% 0.45/0.65  thf('92', plain,
% 0.45/0.65      (((k7_lattices @ sk_A @ sk_C)
% 0.45/0.65         = (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ 
% 0.45/0.65            (k7_lattices @ sk_A @ sk_C)))),
% 0.45/0.65      inference('demod', [status(thm)], ['44', '91'])).
% 0.45/0.65  thf('93', plain,
% 0.45/0.65      ((r1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ 
% 0.45/0.65        (k7_lattices @ sk_A @ sk_B))),
% 0.45/0.65      inference('demod', [status(thm)], ['33', '92'])).
% 0.45/0.65  thf('94', plain,
% 0.45/0.65      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('clc', [status(thm)], ['5', '6'])).
% 0.45/0.65  thf('95', plain,
% 0.45/0.65      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.45/0.65          | ~ (l3_lattices @ X11)
% 0.45/0.65          | ~ (v9_lattices @ X11)
% 0.45/0.65          | ~ (v8_lattices @ X11)
% 0.45/0.65          | ~ (v6_lattices @ X11)
% 0.45/0.65          | (v2_struct_0 @ X11)
% 0.45/0.65          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 0.45/0.65          | (r3_lattices @ X11 @ X10 @ X12)
% 0.45/0.65          | ~ (r1_lattices @ X11 @ X10 @ X12))),
% 0.45/0.65      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.45/0.65  thf('96', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (r1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ X0)
% 0.45/0.65          | (r3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ X0)
% 0.45/0.65          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.65          | (v2_struct_0 @ sk_A)
% 0.45/0.65          | ~ (v6_lattices @ sk_A)
% 0.45/0.65          | ~ (v8_lattices @ sk_A)
% 0.45/0.65          | ~ (v9_lattices @ sk_A)
% 0.45/0.65          | ~ (l3_lattices @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['94', '95'])).
% 0.45/0.65  thf('97', plain, ((v6_lattices @ sk_A)),
% 0.45/0.65      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.45/0.65  thf('98', plain, ((v8_lattices @ sk_A)),
% 0.45/0.65      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.45/0.65  thf('99', plain, ((v9_lattices @ sk_A)),
% 0.45/0.65      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.45/0.65  thf('100', plain, ((l3_lattices @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('101', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (r1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ X0)
% 0.45/0.65          | (r3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ X0)
% 0.45/0.65          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.65          | (v2_struct_0 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['96', '97', '98', '99', '100'])).
% 0.45/0.65  thf('102', plain,
% 0.45/0.65      (((v2_struct_0 @ sk_A)
% 0.45/0.65        | ~ (m1_subset_1 @ (k7_lattices @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.45/0.65        | (r3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ 
% 0.45/0.65           (k7_lattices @ sk_A @ sk_B)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['93', '101'])).
% 0.45/0.65  thf('103', plain,
% 0.45/0.65      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('clc', [status(thm)], ['12', '13'])).
% 0.45/0.65  thf('104', plain,
% 0.45/0.65      (((v2_struct_0 @ sk_A)
% 0.45/0.65        | (r3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ 
% 0.45/0.65           (k7_lattices @ sk_A @ sk_B)))),
% 0.45/0.65      inference('demod', [status(thm)], ['102', '103'])).
% 0.45/0.65  thf('105', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('106', plain,
% 0.45/0.65      ((r3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ 
% 0.45/0.65        (k7_lattices @ sk_A @ sk_B))),
% 0.45/0.65      inference('clc', [status(thm)], ['104', '105'])).
% 0.45/0.65  thf('107', plain, ($false), inference('demod', [status(thm)], ['0', '106'])).
% 0.45/0.65  
% 0.45/0.65  % SZS output end Refutation
% 0.45/0.65  
% 0.45/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
