%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bdOdtAtyh2

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:37 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 466 expanded)
%              Number of leaves         :   22 ( 143 expanded)
%              Depth                    :   17
%              Number of atoms          : 1255 (6252 expanded)
%              Number of equality atoms :   64 ( 277 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(v11_lattices_type,type,(
    v11_lattices: $i > $o )).

thf(v17_lattices_type,type,(
    v17_lattices: $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(k7_lattices_type,type,(
    k7_lattices: $i > $i > $i )).

thf(k5_lattices_type,type,(
    k5_lattices: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_lattices_type,type,(
    k1_lattices: $i > $i > $i > $i )).

thf(k6_lattices_type,type,(
    k6_lattices: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v16_lattices_type,type,(
    v16_lattices: $i > $o )).

thf(r2_lattices_type,type,(
    r2_lattices: $i > $i > $i > $o )).

thf(v15_lattices_type,type,(
    v15_lattices: $i > $o )).

thf(t49_lattices,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v17_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k7_lattices @ A @ ( k7_lattices @ A @ B ) )
            = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v17_lattices @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( k7_lattices @ A @ ( k7_lattices @ A @ B ) )
              = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t49_lattices])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_lattices,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k7_lattices @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l3_lattices @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( m1_subset_1 @ ( k7_lattices @ X7 @ X8 ) @ ( u1_struct_0 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattices])).

thf('3',plain,
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d18_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_lattices @ A @ B @ C )
              <=> ( ( ( k1_lattices @ A @ B @ C )
                    = ( k6_lattices @ A ) )
                  & ( ( k1_lattices @ A @ C @ B )
                    = ( k6_lattices @ A ) )
                  & ( ( k2_lattices @ A @ B @ C )
                    = ( k5_lattices @ A ) )
                  & ( ( k2_lattices @ A @ C @ B )
                    = ( k5_lattices @ A ) ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ( ( k1_lattices @ X2 @ X1 @ X3 )
       != ( k6_lattices @ X2 ) )
      | ( ( k1_lattices @ X2 @ X3 @ X1 )
       != ( k6_lattices @ X2 ) )
      | ( ( k2_lattices @ X2 @ X1 @ X3 )
       != ( k5_lattices @ X2 ) )
      | ( ( k2_lattices @ X2 @ X3 @ X1 )
       != ( k5_lattices @ X2 ) )
      | ( r2_lattices @ X2 @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l3_lattices @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d18_lattices])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattices @ sk_A @ sk_B @ X0 )
      | ( ( k2_lattices @ sk_A @ X0 @ sk_B )
       != ( k5_lattices @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ sk_B @ X0 )
       != ( k5_lattices @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ X0 @ sk_B )
       != ( k6_lattices @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ sk_B @ X0 )
       != ( k6_lattices @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattices @ sk_A @ sk_B @ X0 )
      | ( ( k2_lattices @ sk_A @ X0 @ sk_B )
       != ( k5_lattices @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ sk_B @ X0 )
       != ( k5_lattices @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ X0 @ sk_B )
       != ( k6_lattices @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ sk_B @ X0 )
       != ( k6_lattices @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( ( k1_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_B ) )
     != ( k6_lattices @ sk_A ) )
    | ( ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ sk_B )
     != ( k6_lattices @ sk_A ) )
    | ( ( k2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_B ) )
     != ( k5_lattices @ sk_A ) )
    | ( ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ sk_B )
     != ( k5_lattices @ sk_A ) )
    | ( r2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf(d21_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( ~ ( v2_struct_0 @ A )
              & ( v10_lattices @ A )
              & ( v11_lattices @ A )
              & ( v16_lattices @ A )
              & ( l3_lattices @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( C
                    = ( k7_lattices @ A @ B ) )
                <=> ( r2_lattices @ A @ C @ B ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( X6
       != ( k7_lattices @ X5 @ X4 ) )
      | ( r2_lattices @ X5 @ X6 @ X4 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l3_lattices @ X5 )
      | ~ ( v16_lattices @ X5 )
      | ~ ( v11_lattices @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d21_lattices])).

thf('16',plain,(
    ! [X4: $i,X5: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ~ ( v11_lattices @ X5 )
      | ~ ( v16_lattices @ X5 )
      | ~ ( l3_lattices @ X5 )
      | ~ ( m1_subset_1 @ ( k7_lattices @ X5 @ X4 ) @ ( u1_struct_0 @ X5 ) )
      | ( r2_lattices @ X5 @ ( k7_lattices @ X5 @ X4 ) @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ sk_B )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v16_lattices @ sk_A )
    | ~ ( v11_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc5_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v17_lattices @ A ) )
       => ( ~ ( v2_struct_0 @ A )
          & ( v11_lattices @ A )
          & ( v15_lattices @ A )
          & ( v16_lattices @ A ) ) ) ) )).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v17_lattices @ X0 )
      | ( v16_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc5_lattices])).

thf('21',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v16_lattices @ sk_A )
    | ~ ( v17_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v17_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v16_lattices @ sk_A ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v17_lattices @ X0 )
      | ( v11_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc5_lattices])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v11_lattices @ sk_A )
    | ~ ( v17_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v17_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v11_lattices @ sk_A ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( r2_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18','19','25','31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r2_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('37',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( r2_lattices @ X2 @ X1 @ X3 )
      | ( ( k1_lattices @ X2 @ X1 @ X3 )
        = ( k6_lattices @ X2 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l3_lattices @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d18_lattices])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 )
        = ( k6_lattices @ sk_A ) )
      | ~ ( r2_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 )
        = ( k6_lattices @ sk_A ) )
      | ~ ( r2_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ sk_B )
      = ( k6_lattices @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ sk_B )
      = ( k6_lattices @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ sk_B )
    = ( k6_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( k1_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_B ) )
     != ( k6_lattices @ sk_A ) )
    | ( ( k6_lattices @ sk_A )
     != ( k6_lattices @ sk_A ) )
    | ( ( k2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_B ) )
     != ( k5_lattices @ sk_A ) )
    | ( ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ sk_B )
     != ( k5_lattices @ sk_A ) )
    | ( r2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['13','45'])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_B ) )
    | ( ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ sk_B )
     != ( k5_lattices @ sk_A ) )
    | ( ( k2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_B ) )
     != ( k5_lattices @ sk_A ) )
    | ( ( k1_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_B ) )
     != ( k6_lattices @ sk_A ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    r2_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['33','34'])).

thf('49',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('50',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( r2_lattices @ X2 @ X1 @ X3 )
      | ( ( k2_lattices @ X2 @ X1 @ X3 )
        = ( k5_lattices @ X2 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l3_lattices @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d18_lattices])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 )
        = ( k5_lattices @ sk_A ) )
      | ~ ( r2_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 )
        = ( k5_lattices @ sk_A ) )
      | ~ ( r2_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ sk_B )
      = ( k5_lattices @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ sk_B )
      = ( k5_lattices @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ sk_B )
    = ( k5_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    r2_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['33','34'])).

thf('60',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('61',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( r2_lattices @ X2 @ X1 @ X3 )
      | ( ( k2_lattices @ X2 @ X3 @ X1 )
        = ( k5_lattices @ X2 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l3_lattices @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d18_lattices])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k7_lattices @ sk_A @ sk_B ) )
        = ( k5_lattices @ sk_A ) )
      | ~ ( r2_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k7_lattices @ sk_A @ sk_B ) )
        = ( k5_lattices @ sk_A ) )
      | ~ ( r2_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( k2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_B ) )
      = ( k5_lattices @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['59','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( ( k2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_B ) )
      = ( k5_lattices @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( k2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_B ) )
    = ( k5_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    r2_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['33','34'])).

thf('71',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('72',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( r2_lattices @ X2 @ X1 @ X3 )
      | ( ( k1_lattices @ X2 @ X3 @ X1 )
        = ( k6_lattices @ X2 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l3_lattices @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d18_lattices])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ X0 @ ( k7_lattices @ sk_A @ sk_B ) )
        = ( k6_lattices @ sk_A ) )
      | ~ ( r2_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ X0 @ ( k7_lattices @ sk_A @ sk_B ) )
        = ( k6_lattices @ sk_A ) )
      | ~ ( r2_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( k1_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_B ) )
      = ( k6_lattices @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['70','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( ( k1_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_B ) )
      = ( k6_lattices @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( k1_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_B ) )
    = ( k6_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_B ) )
    | ( ( k5_lattices @ sk_A )
     != ( k5_lattices @ sk_A ) )
    | ( ( k5_lattices @ sk_A )
     != ( k5_lattices @ sk_A ) )
    | ( ( k6_lattices @ sk_A )
     != ( k6_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','58','69','80'])).

thf('82',plain,
    ( ( r2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('84',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r2_lattices @ X5 @ X6 @ X4 )
      | ( X6
        = ( k7_lattices @ X5 @ X4 ) )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l3_lattices @ X5 )
      | ~ ( v16_lattices @ X5 )
      | ~ ( v11_lattices @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d21_lattices])).

thf('86',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ~ ( v11_lattices @ X5 )
      | ~ ( v16_lattices @ X5 )
      | ~ ( l3_lattices @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ( X6
        = ( k7_lattices @ X5 @ X4 ) )
      | ~ ( r2_lattices @ X5 @ X6 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_lattices @ sk_A @ sk_B @ X0 )
      | ( sk_B
        = ( k7_lattices @ sk_A @ X0 ) )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v16_lattices @ sk_A )
      | ~ ( v11_lattices @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','86'])).

thf('88',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v16_lattices @ sk_A ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('90',plain,(
    v11_lattices @ sk_A ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('91',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_lattices @ sk_A @ sk_B @ X0 )
      | ( sk_B
        = ( k7_lattices @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','88','89','90','91'])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) ) )
    | ~ ( r2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['83','92'])).

thf('94',plain,(
    ( k7_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( r2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ~ ( r2_lattices @ sk_A @ sk_B @ ( k7_lattices @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['82','97'])).

thf('99',plain,(
    $false ),
    inference(demod,[status(thm)],['0','98'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bdOdtAtyh2
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:56:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.49/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.49/0.68  % Solved by: fo/fo7.sh
% 0.49/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.68  % done 200 iterations in 0.227s
% 0.49/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.49/0.68  % SZS output start Refutation
% 0.49/0.68  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.49/0.68  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 0.49/0.68  thf(v11_lattices_type, type, v11_lattices: $i > $o).
% 0.49/0.68  thf(v17_lattices_type, type, v17_lattices: $i > $o).
% 0.49/0.68  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.49/0.68  thf(k7_lattices_type, type, k7_lattices: $i > $i > $i).
% 0.49/0.68  thf(k5_lattices_type, type, k5_lattices: $i > $i).
% 0.49/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.68  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.49/0.68  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.49/0.68  thf(k1_lattices_type, type, k1_lattices: $i > $i > $i > $i).
% 0.49/0.68  thf(k6_lattices_type, type, k6_lattices: $i > $i).
% 0.49/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.49/0.68  thf(v16_lattices_type, type, v16_lattices: $i > $o).
% 0.49/0.68  thf(r2_lattices_type, type, r2_lattices: $i > $i > $i > $o).
% 0.49/0.68  thf(v15_lattices_type, type, v15_lattices: $i > $o).
% 0.49/0.68  thf(t49_lattices, conjecture,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.49/0.68         ( v17_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.49/0.68       ( ![B:$i]:
% 0.49/0.68         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.49/0.68           ( ( k7_lattices @ A @ ( k7_lattices @ A @ B ) ) = ( B ) ) ) ) ))).
% 0.49/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.68    (~( ![A:$i]:
% 0.49/0.68        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.49/0.68            ( v17_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.49/0.68          ( ![B:$i]:
% 0.49/0.68            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.49/0.68              ( ( k7_lattices @ A @ ( k7_lattices @ A @ B ) ) = ( B ) ) ) ) ) )),
% 0.49/0.68    inference('cnf.neg', [status(esa)], [t49_lattices])).
% 0.49/0.68  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf(dt_k7_lattices, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) & 
% 0.49/0.68         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.68       ( m1_subset_1 @ ( k7_lattices @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.49/0.68  thf('2', plain,
% 0.49/0.68      (![X7 : $i, X8 : $i]:
% 0.49/0.68         (~ (l3_lattices @ X7)
% 0.49/0.68          | (v2_struct_0 @ X7)
% 0.49/0.68          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.49/0.68          | (m1_subset_1 @ (k7_lattices @ X7 @ X8) @ (u1_struct_0 @ X7)))),
% 0.49/0.68      inference('cnf', [status(esa)], [dt_k7_lattices])).
% 0.49/0.68  thf('3', plain,
% 0.49/0.68      (((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.49/0.68        | (v2_struct_0 @ sk_A)
% 0.49/0.68        | ~ (l3_lattices @ sk_A))),
% 0.49/0.68      inference('sup-', [status(thm)], ['1', '2'])).
% 0.49/0.68  thf('4', plain, ((l3_lattices @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('5', plain,
% 0.49/0.68      (((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.49/0.68        | (v2_struct_0 @ sk_A))),
% 0.49/0.68      inference('demod', [status(thm)], ['3', '4'])).
% 0.49/0.68  thf('6', plain, (~ (v2_struct_0 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('7', plain,
% 0.49/0.68      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.49/0.68      inference('clc', [status(thm)], ['5', '6'])).
% 0.49/0.68  thf('8', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf(d18_lattices, axiom,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.49/0.68       ( ![B:$i]:
% 0.49/0.68         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.49/0.68           ( ![C:$i]:
% 0.49/0.68             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.49/0.68               ( ( r2_lattices @ A @ B @ C ) <=>
% 0.49/0.68                 ( ( ( k1_lattices @ A @ B @ C ) = ( k6_lattices @ A ) ) & 
% 0.49/0.68                   ( ( k1_lattices @ A @ C @ B ) = ( k6_lattices @ A ) ) & 
% 0.49/0.68                   ( ( k2_lattices @ A @ B @ C ) = ( k5_lattices @ A ) ) & 
% 0.49/0.68                   ( ( k2_lattices @ A @ C @ B ) = ( k5_lattices @ A ) ) ) ) ) ) ) ) ))).
% 0.49/0.68  thf('9', plain,
% 0.49/0.68      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.49/0.68          | ((k1_lattices @ X2 @ X1 @ X3) != (k6_lattices @ X2))
% 0.49/0.68          | ((k1_lattices @ X2 @ X3 @ X1) != (k6_lattices @ X2))
% 0.49/0.68          | ((k2_lattices @ X2 @ X1 @ X3) != (k5_lattices @ X2))
% 0.49/0.68          | ((k2_lattices @ X2 @ X3 @ X1) != (k5_lattices @ X2))
% 0.49/0.68          | (r2_lattices @ X2 @ X1 @ X3)
% 0.49/0.68          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.49/0.68          | ~ (l3_lattices @ X2)
% 0.49/0.68          | (v2_struct_0 @ X2))),
% 0.49/0.68      inference('cnf', [status(esa)], [d18_lattices])).
% 0.49/0.68  thf('10', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         ((v2_struct_0 @ sk_A)
% 0.49/0.68          | ~ (l3_lattices @ sk_A)
% 0.49/0.68          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.49/0.68          | (r2_lattices @ sk_A @ sk_B @ X0)
% 0.49/0.68          | ((k2_lattices @ sk_A @ X0 @ sk_B) != (k5_lattices @ sk_A))
% 0.49/0.68          | ((k2_lattices @ sk_A @ sk_B @ X0) != (k5_lattices @ sk_A))
% 0.49/0.68          | ((k1_lattices @ sk_A @ X0 @ sk_B) != (k6_lattices @ sk_A))
% 0.49/0.68          | ((k1_lattices @ sk_A @ sk_B @ X0) != (k6_lattices @ sk_A)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['8', '9'])).
% 0.49/0.68  thf('11', plain, ((l3_lattices @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('12', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         ((v2_struct_0 @ sk_A)
% 0.49/0.68          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.49/0.68          | (r2_lattices @ sk_A @ sk_B @ X0)
% 0.49/0.68          | ((k2_lattices @ sk_A @ X0 @ sk_B) != (k5_lattices @ sk_A))
% 0.49/0.68          | ((k2_lattices @ sk_A @ sk_B @ X0) != (k5_lattices @ sk_A))
% 0.49/0.68          | ((k1_lattices @ sk_A @ X0 @ sk_B) != (k6_lattices @ sk_A))
% 0.49/0.68          | ((k1_lattices @ sk_A @ sk_B @ X0) != (k6_lattices @ sk_A)))),
% 0.49/0.68      inference('demod', [status(thm)], ['10', '11'])).
% 0.49/0.68  thf('13', plain,
% 0.49/0.68      ((((k1_lattices @ sk_A @ sk_B @ (k7_lattices @ sk_A @ sk_B))
% 0.49/0.68          != (k6_lattices @ sk_A))
% 0.49/0.68        | ((k1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ sk_B)
% 0.49/0.68            != (k6_lattices @ sk_A))
% 0.49/0.68        | ((k2_lattices @ sk_A @ sk_B @ (k7_lattices @ sk_A @ sk_B))
% 0.49/0.68            != (k5_lattices @ sk_A))
% 0.49/0.68        | ((k2_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ sk_B)
% 0.49/0.68            != (k5_lattices @ sk_A))
% 0.49/0.68        | (r2_lattices @ sk_A @ sk_B @ (k7_lattices @ sk_A @ sk_B))
% 0.49/0.68        | (v2_struct_0 @ sk_A))),
% 0.49/0.68      inference('sup-', [status(thm)], ['7', '12'])).
% 0.49/0.68  thf('14', plain,
% 0.49/0.68      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.49/0.68      inference('clc', [status(thm)], ['5', '6'])).
% 0.49/0.68  thf(d21_lattices, axiom,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.49/0.68       ( ![B:$i]:
% 0.49/0.68         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.49/0.68           ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.49/0.68               ( v11_lattices @ A ) & ( v16_lattices @ A ) & 
% 0.49/0.68               ( l3_lattices @ A ) ) =>
% 0.49/0.68             ( ![C:$i]:
% 0.49/0.68               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.49/0.68                 ( ( ( C ) = ( k7_lattices @ A @ B ) ) <=>
% 0.49/0.68                   ( r2_lattices @ A @ C @ B ) ) ) ) ) ) ) ))).
% 0.49/0.68  thf('15', plain,
% 0.49/0.68      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.49/0.68          | ((X6) != (k7_lattices @ X5 @ X4))
% 0.49/0.68          | (r2_lattices @ X5 @ X6 @ X4)
% 0.49/0.68          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.49/0.68          | ~ (l3_lattices @ X5)
% 0.49/0.68          | ~ (v16_lattices @ X5)
% 0.49/0.68          | ~ (v11_lattices @ X5)
% 0.49/0.68          | ~ (v10_lattices @ X5)
% 0.49/0.68          | (v2_struct_0 @ X5)
% 0.49/0.68          | ~ (l3_lattices @ X5)
% 0.49/0.68          | (v2_struct_0 @ X5))),
% 0.49/0.68      inference('cnf', [status(esa)], [d21_lattices])).
% 0.49/0.68  thf('16', plain,
% 0.49/0.68      (![X4 : $i, X5 : $i]:
% 0.49/0.68         ((v2_struct_0 @ X5)
% 0.49/0.68          | ~ (v10_lattices @ X5)
% 0.49/0.68          | ~ (v11_lattices @ X5)
% 0.49/0.68          | ~ (v16_lattices @ X5)
% 0.49/0.68          | ~ (l3_lattices @ X5)
% 0.49/0.68          | ~ (m1_subset_1 @ (k7_lattices @ X5 @ X4) @ (u1_struct_0 @ X5))
% 0.49/0.68          | (r2_lattices @ X5 @ (k7_lattices @ X5 @ X4) @ X4)
% 0.49/0.68          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5)))),
% 0.49/0.68      inference('simplify', [status(thm)], ['15'])).
% 0.49/0.68  thf('17', plain,
% 0.49/0.68      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.49/0.68        | (r2_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ sk_B)
% 0.49/0.68        | ~ (l3_lattices @ sk_A)
% 0.49/0.68        | ~ (v16_lattices @ sk_A)
% 0.49/0.68        | ~ (v11_lattices @ sk_A)
% 0.49/0.68        | ~ (v10_lattices @ sk_A)
% 0.49/0.68        | (v2_struct_0 @ sk_A))),
% 0.49/0.68      inference('sup-', [status(thm)], ['14', '16'])).
% 0.49/0.68  thf('18', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('19', plain, ((l3_lattices @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf(cc5_lattices, axiom,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( l3_lattices @ A ) =>
% 0.49/0.68       ( ( ( ~( v2_struct_0 @ A ) ) & ( v17_lattices @ A ) ) =>
% 0.49/0.68         ( ( ~( v2_struct_0 @ A ) ) & ( v11_lattices @ A ) & 
% 0.49/0.68           ( v15_lattices @ A ) & ( v16_lattices @ A ) ) ) ))).
% 0.49/0.68  thf('20', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         ((v2_struct_0 @ X0)
% 0.49/0.68          | ~ (v17_lattices @ X0)
% 0.49/0.68          | (v16_lattices @ X0)
% 0.49/0.68          | ~ (l3_lattices @ X0))),
% 0.49/0.68      inference('cnf', [status(esa)], [cc5_lattices])).
% 0.49/0.68  thf('21', plain, (~ (v2_struct_0 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('22', plain,
% 0.49/0.68      ((~ (l3_lattices @ sk_A)
% 0.49/0.68        | (v16_lattices @ sk_A)
% 0.49/0.68        | ~ (v17_lattices @ sk_A))),
% 0.49/0.68      inference('sup-', [status(thm)], ['20', '21'])).
% 0.49/0.68  thf('23', plain, ((l3_lattices @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('24', plain, ((v17_lattices @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('25', plain, ((v16_lattices @ sk_A)),
% 0.49/0.68      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.49/0.68  thf('26', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         ((v2_struct_0 @ X0)
% 0.49/0.68          | ~ (v17_lattices @ X0)
% 0.49/0.68          | (v11_lattices @ X0)
% 0.49/0.68          | ~ (l3_lattices @ X0))),
% 0.49/0.68      inference('cnf', [status(esa)], [cc5_lattices])).
% 0.49/0.68  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('28', plain,
% 0.49/0.68      ((~ (l3_lattices @ sk_A)
% 0.49/0.68        | (v11_lattices @ sk_A)
% 0.49/0.68        | ~ (v17_lattices @ sk_A))),
% 0.49/0.68      inference('sup-', [status(thm)], ['26', '27'])).
% 0.49/0.68  thf('29', plain, ((l3_lattices @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('30', plain, ((v17_lattices @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('31', plain, ((v11_lattices @ sk_A)),
% 0.49/0.68      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.49/0.68  thf('32', plain, ((v10_lattices @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('33', plain,
% 0.49/0.68      (((r2_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ sk_B)
% 0.49/0.68        | (v2_struct_0 @ sk_A))),
% 0.49/0.68      inference('demod', [status(thm)], ['17', '18', '19', '25', '31', '32'])).
% 0.49/0.68  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('35', plain, ((r2_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ sk_B)),
% 0.49/0.68      inference('clc', [status(thm)], ['33', '34'])).
% 0.49/0.68  thf('36', plain,
% 0.49/0.68      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.49/0.68      inference('clc', [status(thm)], ['5', '6'])).
% 0.49/0.68  thf('37', plain,
% 0.49/0.68      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.49/0.68          | ~ (r2_lattices @ X2 @ X1 @ X3)
% 0.49/0.68          | ((k1_lattices @ X2 @ X1 @ X3) = (k6_lattices @ X2))
% 0.49/0.68          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.49/0.68          | ~ (l3_lattices @ X2)
% 0.49/0.68          | (v2_struct_0 @ X2))),
% 0.49/0.68      inference('cnf', [status(esa)], [d18_lattices])).
% 0.49/0.68  thf('38', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         ((v2_struct_0 @ sk_A)
% 0.49/0.68          | ~ (l3_lattices @ sk_A)
% 0.49/0.68          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.49/0.68          | ((k1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0)
% 0.49/0.68              = (k6_lattices @ sk_A))
% 0.49/0.68          | ~ (r2_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0))),
% 0.49/0.68      inference('sup-', [status(thm)], ['36', '37'])).
% 0.49/0.68  thf('39', plain, ((l3_lattices @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('40', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         ((v2_struct_0 @ sk_A)
% 0.49/0.68          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.49/0.68          | ((k1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0)
% 0.49/0.68              = (k6_lattices @ sk_A))
% 0.49/0.68          | ~ (r2_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0))),
% 0.49/0.68      inference('demod', [status(thm)], ['38', '39'])).
% 0.49/0.68  thf('41', plain,
% 0.49/0.68      ((((k1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ sk_B)
% 0.49/0.68          = (k6_lattices @ sk_A))
% 0.49/0.68        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.49/0.68        | (v2_struct_0 @ sk_A))),
% 0.49/0.68      inference('sup-', [status(thm)], ['35', '40'])).
% 0.49/0.68  thf('42', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('43', plain,
% 0.49/0.68      ((((k1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ sk_B)
% 0.49/0.68          = (k6_lattices @ sk_A))
% 0.49/0.68        | (v2_struct_0 @ sk_A))),
% 0.49/0.68      inference('demod', [status(thm)], ['41', '42'])).
% 0.49/0.68  thf('44', plain, (~ (v2_struct_0 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('45', plain,
% 0.49/0.68      (((k1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ sk_B)
% 0.49/0.68         = (k6_lattices @ sk_A))),
% 0.49/0.68      inference('clc', [status(thm)], ['43', '44'])).
% 0.49/0.68  thf('46', plain,
% 0.49/0.68      ((((k1_lattices @ sk_A @ sk_B @ (k7_lattices @ sk_A @ sk_B))
% 0.49/0.68          != (k6_lattices @ sk_A))
% 0.49/0.68        | ((k6_lattices @ sk_A) != (k6_lattices @ sk_A))
% 0.49/0.68        | ((k2_lattices @ sk_A @ sk_B @ (k7_lattices @ sk_A @ sk_B))
% 0.49/0.68            != (k5_lattices @ sk_A))
% 0.49/0.68        | ((k2_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ sk_B)
% 0.49/0.68            != (k5_lattices @ sk_A))
% 0.49/0.68        | (r2_lattices @ sk_A @ sk_B @ (k7_lattices @ sk_A @ sk_B))
% 0.49/0.68        | (v2_struct_0 @ sk_A))),
% 0.49/0.68      inference('demod', [status(thm)], ['13', '45'])).
% 0.49/0.68  thf('47', plain,
% 0.49/0.68      (((v2_struct_0 @ sk_A)
% 0.49/0.68        | (r2_lattices @ sk_A @ sk_B @ (k7_lattices @ sk_A @ sk_B))
% 0.49/0.68        | ((k2_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ sk_B)
% 0.49/0.68            != (k5_lattices @ sk_A))
% 0.49/0.68        | ((k2_lattices @ sk_A @ sk_B @ (k7_lattices @ sk_A @ sk_B))
% 0.49/0.68            != (k5_lattices @ sk_A))
% 0.49/0.68        | ((k1_lattices @ sk_A @ sk_B @ (k7_lattices @ sk_A @ sk_B))
% 0.49/0.68            != (k6_lattices @ sk_A)))),
% 0.49/0.68      inference('simplify', [status(thm)], ['46'])).
% 0.49/0.68  thf('48', plain, ((r2_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ sk_B)),
% 0.49/0.68      inference('clc', [status(thm)], ['33', '34'])).
% 0.49/0.68  thf('49', plain,
% 0.49/0.68      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.49/0.68      inference('clc', [status(thm)], ['5', '6'])).
% 0.49/0.68  thf('50', plain,
% 0.49/0.68      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.49/0.68          | ~ (r2_lattices @ X2 @ X1 @ X3)
% 0.49/0.68          | ((k2_lattices @ X2 @ X1 @ X3) = (k5_lattices @ X2))
% 0.49/0.68          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.49/0.68          | ~ (l3_lattices @ X2)
% 0.49/0.68          | (v2_struct_0 @ X2))),
% 0.49/0.68      inference('cnf', [status(esa)], [d18_lattices])).
% 0.49/0.68  thf('51', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         ((v2_struct_0 @ sk_A)
% 0.49/0.68          | ~ (l3_lattices @ sk_A)
% 0.49/0.68          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.49/0.68          | ((k2_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0)
% 0.49/0.68              = (k5_lattices @ sk_A))
% 0.49/0.68          | ~ (r2_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0))),
% 0.49/0.68      inference('sup-', [status(thm)], ['49', '50'])).
% 0.49/0.68  thf('52', plain, ((l3_lattices @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('53', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         ((v2_struct_0 @ sk_A)
% 0.49/0.68          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.49/0.68          | ((k2_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0)
% 0.49/0.68              = (k5_lattices @ sk_A))
% 0.49/0.68          | ~ (r2_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0))),
% 0.49/0.68      inference('demod', [status(thm)], ['51', '52'])).
% 0.49/0.68  thf('54', plain,
% 0.49/0.68      ((((k2_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ sk_B)
% 0.49/0.68          = (k5_lattices @ sk_A))
% 0.49/0.68        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.49/0.68        | (v2_struct_0 @ sk_A))),
% 0.49/0.68      inference('sup-', [status(thm)], ['48', '53'])).
% 0.49/0.68  thf('55', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('56', plain,
% 0.49/0.68      ((((k2_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ sk_B)
% 0.49/0.68          = (k5_lattices @ sk_A))
% 0.49/0.68        | (v2_struct_0 @ sk_A))),
% 0.49/0.68      inference('demod', [status(thm)], ['54', '55'])).
% 0.49/0.68  thf('57', plain, (~ (v2_struct_0 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('58', plain,
% 0.49/0.68      (((k2_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ sk_B)
% 0.49/0.68         = (k5_lattices @ sk_A))),
% 0.49/0.68      inference('clc', [status(thm)], ['56', '57'])).
% 0.49/0.68  thf('59', plain, ((r2_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ sk_B)),
% 0.49/0.68      inference('clc', [status(thm)], ['33', '34'])).
% 0.49/0.68  thf('60', plain,
% 0.49/0.68      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.49/0.68      inference('clc', [status(thm)], ['5', '6'])).
% 0.49/0.68  thf('61', plain,
% 0.49/0.68      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.49/0.68          | ~ (r2_lattices @ X2 @ X1 @ X3)
% 0.49/0.68          | ((k2_lattices @ X2 @ X3 @ X1) = (k5_lattices @ X2))
% 0.49/0.68          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.49/0.68          | ~ (l3_lattices @ X2)
% 0.49/0.68          | (v2_struct_0 @ X2))),
% 0.49/0.68      inference('cnf', [status(esa)], [d18_lattices])).
% 0.49/0.68  thf('62', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         ((v2_struct_0 @ sk_A)
% 0.49/0.68          | ~ (l3_lattices @ sk_A)
% 0.49/0.68          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.49/0.68          | ((k2_lattices @ sk_A @ X0 @ (k7_lattices @ sk_A @ sk_B))
% 0.49/0.68              = (k5_lattices @ sk_A))
% 0.49/0.68          | ~ (r2_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0))),
% 0.49/0.68      inference('sup-', [status(thm)], ['60', '61'])).
% 0.49/0.68  thf('63', plain, ((l3_lattices @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('64', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         ((v2_struct_0 @ sk_A)
% 0.49/0.68          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.49/0.68          | ((k2_lattices @ sk_A @ X0 @ (k7_lattices @ sk_A @ sk_B))
% 0.49/0.68              = (k5_lattices @ sk_A))
% 0.49/0.68          | ~ (r2_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0))),
% 0.49/0.68      inference('demod', [status(thm)], ['62', '63'])).
% 0.49/0.68  thf('65', plain,
% 0.49/0.68      ((((k2_lattices @ sk_A @ sk_B @ (k7_lattices @ sk_A @ sk_B))
% 0.49/0.68          = (k5_lattices @ sk_A))
% 0.49/0.68        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.49/0.68        | (v2_struct_0 @ sk_A))),
% 0.49/0.68      inference('sup-', [status(thm)], ['59', '64'])).
% 0.49/0.68  thf('66', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('67', plain,
% 0.49/0.68      ((((k2_lattices @ sk_A @ sk_B @ (k7_lattices @ sk_A @ sk_B))
% 0.49/0.68          = (k5_lattices @ sk_A))
% 0.49/0.68        | (v2_struct_0 @ sk_A))),
% 0.49/0.68      inference('demod', [status(thm)], ['65', '66'])).
% 0.49/0.68  thf('68', plain, (~ (v2_struct_0 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('69', plain,
% 0.49/0.68      (((k2_lattices @ sk_A @ sk_B @ (k7_lattices @ sk_A @ sk_B))
% 0.49/0.68         = (k5_lattices @ sk_A))),
% 0.49/0.68      inference('clc', [status(thm)], ['67', '68'])).
% 0.49/0.68  thf('70', plain, ((r2_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ sk_B)),
% 0.49/0.68      inference('clc', [status(thm)], ['33', '34'])).
% 0.49/0.68  thf('71', plain,
% 0.49/0.68      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.49/0.68      inference('clc', [status(thm)], ['5', '6'])).
% 0.49/0.68  thf('72', plain,
% 0.49/0.68      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.49/0.68          | ~ (r2_lattices @ X2 @ X1 @ X3)
% 0.49/0.68          | ((k1_lattices @ X2 @ X3 @ X1) = (k6_lattices @ X2))
% 0.49/0.68          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.49/0.68          | ~ (l3_lattices @ X2)
% 0.49/0.68          | (v2_struct_0 @ X2))),
% 0.49/0.68      inference('cnf', [status(esa)], [d18_lattices])).
% 0.49/0.68  thf('73', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         ((v2_struct_0 @ sk_A)
% 0.49/0.68          | ~ (l3_lattices @ sk_A)
% 0.49/0.68          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.49/0.68          | ((k1_lattices @ sk_A @ X0 @ (k7_lattices @ sk_A @ sk_B))
% 0.49/0.68              = (k6_lattices @ sk_A))
% 0.49/0.68          | ~ (r2_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0))),
% 0.49/0.68      inference('sup-', [status(thm)], ['71', '72'])).
% 0.49/0.68  thf('74', plain, ((l3_lattices @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('75', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         ((v2_struct_0 @ sk_A)
% 0.49/0.68          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.49/0.68          | ((k1_lattices @ sk_A @ X0 @ (k7_lattices @ sk_A @ sk_B))
% 0.49/0.68              = (k6_lattices @ sk_A))
% 0.49/0.68          | ~ (r2_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0))),
% 0.49/0.68      inference('demod', [status(thm)], ['73', '74'])).
% 0.49/0.68  thf('76', plain,
% 0.49/0.68      ((((k1_lattices @ sk_A @ sk_B @ (k7_lattices @ sk_A @ sk_B))
% 0.49/0.68          = (k6_lattices @ sk_A))
% 0.49/0.68        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.49/0.68        | (v2_struct_0 @ sk_A))),
% 0.49/0.68      inference('sup-', [status(thm)], ['70', '75'])).
% 0.49/0.68  thf('77', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('78', plain,
% 0.49/0.68      ((((k1_lattices @ sk_A @ sk_B @ (k7_lattices @ sk_A @ sk_B))
% 0.49/0.68          = (k6_lattices @ sk_A))
% 0.49/0.68        | (v2_struct_0 @ sk_A))),
% 0.49/0.68      inference('demod', [status(thm)], ['76', '77'])).
% 0.49/0.68  thf('79', plain, (~ (v2_struct_0 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('80', plain,
% 0.49/0.68      (((k1_lattices @ sk_A @ sk_B @ (k7_lattices @ sk_A @ sk_B))
% 0.49/0.68         = (k6_lattices @ sk_A))),
% 0.49/0.68      inference('clc', [status(thm)], ['78', '79'])).
% 0.49/0.68  thf('81', plain,
% 0.49/0.68      (((v2_struct_0 @ sk_A)
% 0.49/0.68        | (r2_lattices @ sk_A @ sk_B @ (k7_lattices @ sk_A @ sk_B))
% 0.49/0.68        | ((k5_lattices @ sk_A) != (k5_lattices @ sk_A))
% 0.49/0.68        | ((k5_lattices @ sk_A) != (k5_lattices @ sk_A))
% 0.49/0.68        | ((k6_lattices @ sk_A) != (k6_lattices @ sk_A)))),
% 0.49/0.68      inference('demod', [status(thm)], ['47', '58', '69', '80'])).
% 0.49/0.68  thf('82', plain,
% 0.49/0.68      (((r2_lattices @ sk_A @ sk_B @ (k7_lattices @ sk_A @ sk_B))
% 0.49/0.68        | (v2_struct_0 @ sk_A))),
% 0.49/0.68      inference('simplify', [status(thm)], ['81'])).
% 0.49/0.68  thf('83', plain,
% 0.49/0.68      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.49/0.68      inference('clc', [status(thm)], ['5', '6'])).
% 0.49/0.68  thf('84', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('85', plain,
% 0.49/0.68      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.49/0.68          | ~ (r2_lattices @ X5 @ X6 @ X4)
% 0.49/0.68          | ((X6) = (k7_lattices @ X5 @ X4))
% 0.49/0.68          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.49/0.68          | ~ (l3_lattices @ X5)
% 0.49/0.68          | ~ (v16_lattices @ X5)
% 0.49/0.68          | ~ (v11_lattices @ X5)
% 0.49/0.68          | ~ (v10_lattices @ X5)
% 0.49/0.68          | (v2_struct_0 @ X5)
% 0.49/0.68          | ~ (l3_lattices @ X5)
% 0.49/0.68          | (v2_struct_0 @ X5))),
% 0.49/0.68      inference('cnf', [status(esa)], [d21_lattices])).
% 0.49/0.68  thf('86', plain,
% 0.49/0.68      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.49/0.68         ((v2_struct_0 @ X5)
% 0.49/0.68          | ~ (v10_lattices @ X5)
% 0.49/0.68          | ~ (v11_lattices @ X5)
% 0.49/0.68          | ~ (v16_lattices @ X5)
% 0.49/0.68          | ~ (l3_lattices @ X5)
% 0.49/0.68          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.49/0.68          | ((X6) = (k7_lattices @ X5 @ X4))
% 0.49/0.68          | ~ (r2_lattices @ X5 @ X6 @ X4)
% 0.49/0.68          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5)))),
% 0.49/0.68      inference('simplify', [status(thm)], ['85'])).
% 0.49/0.68  thf('87', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.49/0.68          | ~ (r2_lattices @ sk_A @ sk_B @ X0)
% 0.49/0.68          | ((sk_B) = (k7_lattices @ sk_A @ X0))
% 0.49/0.68          | ~ (l3_lattices @ sk_A)
% 0.49/0.68          | ~ (v16_lattices @ sk_A)
% 0.49/0.68          | ~ (v11_lattices @ sk_A)
% 0.49/0.68          | ~ (v10_lattices @ sk_A)
% 0.49/0.68          | (v2_struct_0 @ sk_A))),
% 0.49/0.68      inference('sup-', [status(thm)], ['84', '86'])).
% 0.49/0.68  thf('88', plain, ((l3_lattices @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('89', plain, ((v16_lattices @ sk_A)),
% 0.49/0.68      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.49/0.68  thf('90', plain, ((v11_lattices @ sk_A)),
% 0.49/0.68      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.49/0.68  thf('91', plain, ((v10_lattices @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('92', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.49/0.68          | ~ (r2_lattices @ sk_A @ sk_B @ X0)
% 0.49/0.68          | ((sk_B) = (k7_lattices @ sk_A @ X0))
% 0.49/0.68          | (v2_struct_0 @ sk_A))),
% 0.49/0.68      inference('demod', [status(thm)], ['87', '88', '89', '90', '91'])).
% 0.49/0.68  thf('93', plain,
% 0.49/0.68      (((v2_struct_0 @ sk_A)
% 0.49/0.68        | ((sk_B) = (k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B)))
% 0.49/0.68        | ~ (r2_lattices @ sk_A @ sk_B @ (k7_lattices @ sk_A @ sk_B)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['83', '92'])).
% 0.49/0.68  thf('94', plain,
% 0.49/0.68      (((k7_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B)) != (sk_B))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('95', plain,
% 0.49/0.68      (((v2_struct_0 @ sk_A)
% 0.49/0.68        | ~ (r2_lattices @ sk_A @ sk_B @ (k7_lattices @ sk_A @ sk_B)))),
% 0.49/0.68      inference('simplify_reflect-', [status(thm)], ['93', '94'])).
% 0.49/0.68  thf('96', plain, (~ (v2_struct_0 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('97', plain,
% 0.49/0.68      (~ (r2_lattices @ sk_A @ sk_B @ (k7_lattices @ sk_A @ sk_B))),
% 0.49/0.68      inference('clc', [status(thm)], ['95', '96'])).
% 0.49/0.68  thf('98', plain, ((v2_struct_0 @ sk_A)),
% 0.49/0.68      inference('clc', [status(thm)], ['82', '97'])).
% 0.49/0.68  thf('99', plain, ($false), inference('demod', [status(thm)], ['0', '98'])).
% 0.49/0.68  
% 0.49/0.68  % SZS output end Refutation
% 0.49/0.68  
% 0.49/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
