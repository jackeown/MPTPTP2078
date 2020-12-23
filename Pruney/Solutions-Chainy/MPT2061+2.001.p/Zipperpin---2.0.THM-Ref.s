%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AuBKsnput1

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:55 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 124 expanded)
%              Number of leaves         :   18 (  45 expanded)
%              Depth                    :   18
%              Number of atoms          :  528 (1824 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_waybel_0_type,type,(
    r2_waybel_0: $i > $i > $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(m2_yellow_6_type,type,(
    m2_yellow_6: $i > $i > $i > $o )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t21_yellow19,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( v2_struct_0 @ C )
            & ( v4_orders_2 @ C )
            & ( v7_waybel_0 @ C )
            & ( l1_waybel_0 @ C @ A ) )
         => ( ( r1_waybel_0 @ A @ C @ B )
           => ! [D: $i] :
                ( ( m2_yellow_6 @ D @ A @ C )
               => ( r1_waybel_0 @ A @ D @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_struct_0 @ A ) )
       => ! [B: $i,C: $i] :
            ( ( ~ ( v2_struct_0 @ C )
              & ( v4_orders_2 @ C )
              & ( v7_waybel_0 @ C )
              & ( l1_waybel_0 @ C @ A ) )
           => ( ( r1_waybel_0 @ A @ C @ B )
             => ! [D: $i] :
                  ( ( m2_yellow_6 @ D @ A @ C )
                 => ( r1_waybel_0 @ A @ D @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t21_yellow19])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_waybel_0 @ sk_A @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m2_yellow_6 @ sk_D @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m2_yellow_6,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ~ ( v2_struct_0 @ B )
        & ( v4_orders_2 @ B )
        & ( v7_waybel_0 @ B )
        & ( l1_waybel_0 @ B @ A ) )
     => ! [C: $i] :
          ( ( m2_yellow_6 @ C @ A @ B )
         => ( ~ ( v2_struct_0 @ C )
            & ( v4_orders_2 @ C )
            & ( v7_waybel_0 @ C )
            & ( l1_waybel_0 @ C @ A ) ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( l1_struct_0 @ X4 )
      | ( v2_struct_0 @ X4 )
      | ( v2_struct_0 @ X5 )
      | ~ ( v4_orders_2 @ X5 )
      | ~ ( v7_waybel_0 @ X5 )
      | ~ ( l1_waybel_0 @ X5 @ X4 )
      | ( l1_waybel_0 @ X6 @ X4 )
      | ~ ( m2_yellow_6 @ X6 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('4',plain,
    ( ( l1_waybel_0 @ sk_D @ sk_A )
    | ~ ( l1_waybel_0 @ sk_C @ sk_A )
    | ~ ( v7_waybel_0 @ sk_C )
    | ~ ( v4_orders_2 @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v7_waybel_0 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v4_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( l1_waybel_0 @ sk_D @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6','7','8'])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( l1_waybel_0 @ sk_D @ sk_A ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_waybel_0 @ sk_D @ sk_A ),
    inference(clc,[status(thm)],['11','12'])).

thf(t9_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( r1_waybel_0 @ A @ B @ C )
            <=> ~ ( r2_waybel_0 @ A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( r2_waybel_0 @ X1 @ X0 @ ( k6_subset_1 @ ( u1_struct_0 @ X1 ) @ X2 ) )
      | ( r1_waybel_0 @ X1 @ X0 @ X2 )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t9_waybel_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_D @ X0 )
      | ( r2_waybel_0 @ sk_A @ sk_D @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_D @ X0 )
      | ( r2_waybel_0 @ sk_A @ sk_D @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    m2_yellow_6 @ sk_D @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t27_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m2_yellow_6 @ C @ A @ B )
             => ! [D: $i] :
                  ( ( r2_waybel_0 @ A @ C @ D )
                 => ( r2_waybel_0 @ A @ B @ D ) ) ) ) ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( v4_orders_2 @ X7 )
      | ~ ( v7_waybel_0 @ X7 )
      | ~ ( l1_waybel_0 @ X7 @ X8 )
      | ~ ( r2_waybel_0 @ X8 @ X9 @ X10 )
      | ( r2_waybel_0 @ X8 @ X7 @ X10 )
      | ~ ( m2_yellow_6 @ X9 @ X8 @ X7 )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t27_yellow_6])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_C @ X0 )
      | ~ ( r2_waybel_0 @ sk_A @ sk_D @ X0 )
      | ~ ( l1_waybel_0 @ sk_C @ sk_A )
      | ~ ( v7_waybel_0 @ sk_C )
      | ~ ( v4_orders_2 @ sk_C )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v7_waybel_0 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v4_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_C @ X0 )
      | ~ ( r2_waybel_0 @ sk_A @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['20','21','22','23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( r1_waybel_0 @ sk_A @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r2_waybel_0 @ sk_A @ sk_C @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_waybel_0 @ sk_A @ sk_C @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ~ ( r1_waybel_0 @ X1 @ X0 @ X3 )
      | ~ ( r2_waybel_0 @ X1 @ X0 @ ( k6_subset_1 @ ( u1_struct_0 @ X1 ) @ X3 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t9_waybel_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( r1_waybel_0 @ sk_A @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( r1_waybel_0 @ sk_A @ sk_C @ X0 )
      | ~ ( l1_waybel_0 @ sk_C @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( r1_waybel_0 @ sk_A @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r1_waybel_0 @ sk_A @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_0 @ sk_A @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( r1_waybel_0 @ sk_A @ sk_D @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['1','33'])).

thf('35',plain,(
    ~ ( r1_waybel_0 @ sk_A @ sk_D @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    m2_yellow_6 @ sk_D @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( l1_struct_0 @ X4 )
      | ( v2_struct_0 @ X4 )
      | ( v2_struct_0 @ X5 )
      | ~ ( v4_orders_2 @ X5 )
      | ~ ( v7_waybel_0 @ X5 )
      | ~ ( l1_waybel_0 @ X5 @ X4 )
      | ~ ( v2_struct_0 @ X6 )
      | ~ ( m2_yellow_6 @ X6 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('41',plain,
    ( ~ ( v2_struct_0 @ sk_D )
    | ~ ( l1_waybel_0 @ sk_C @ sk_A )
    | ~ ( v7_waybel_0 @ sk_C )
    | ~ ( v4_orders_2 @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v7_waybel_0 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v4_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ~ ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42','43','44','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['38','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['0','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AuBKsnput1
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:14:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 26 iterations in 0.019s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(r2_waybel_0_type, type, r2_waybel_0: $i > $i > $i > $o).
% 0.20/0.48  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.20/0.48  thf(m2_yellow_6_type, type, m2_yellow_6: $i > $i > $i > $o).
% 0.20/0.48  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.20/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.48  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.20/0.48  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(t21_yellow19, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.48       ( ![B:$i,C:$i]:
% 0.20/0.48         ( ( ( ~( v2_struct_0 @ C ) ) & ( v4_orders_2 @ C ) & 
% 0.20/0.48             ( v7_waybel_0 @ C ) & ( l1_waybel_0 @ C @ A ) ) =>
% 0.20/0.48           ( ( r1_waybel_0 @ A @ C @ B ) =>
% 0.20/0.48             ( ![D:$i]:
% 0.20/0.48               ( ( m2_yellow_6 @ D @ A @ C ) => ( r1_waybel_0 @ A @ D @ B ) ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.48          ( ![B:$i,C:$i]:
% 0.20/0.48            ( ( ( ~( v2_struct_0 @ C ) ) & ( v4_orders_2 @ C ) & 
% 0.20/0.48                ( v7_waybel_0 @ C ) & ( l1_waybel_0 @ C @ A ) ) =>
% 0.20/0.48              ( ( r1_waybel_0 @ A @ C @ B ) =>
% 0.20/0.48                ( ![D:$i]:
% 0.20/0.48                  ( ( m2_yellow_6 @ D @ A @ C ) => ( r1_waybel_0 @ A @ D @ B ) ) ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t21_yellow19])).
% 0.20/0.48  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain, ((r1_waybel_0 @ sk_A @ sk_C @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('2', plain, ((m2_yellow_6 @ sk_D @ sk_A @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(dt_m2_yellow_6, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.20/0.48         ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.20/0.48         ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.48       ( ![C:$i]:
% 0.20/0.48         ( ( m2_yellow_6 @ C @ A @ B ) =>
% 0.20/0.48           ( ( ~( v2_struct_0 @ C ) ) & ( v4_orders_2 @ C ) & 
% 0.20/0.48             ( v7_waybel_0 @ C ) & ( l1_waybel_0 @ C @ A ) ) ) ) ))).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.48         (~ (l1_struct_0 @ X4)
% 0.20/0.48          | (v2_struct_0 @ X4)
% 0.20/0.48          | (v2_struct_0 @ X5)
% 0.20/0.48          | ~ (v4_orders_2 @ X5)
% 0.20/0.48          | ~ (v7_waybel_0 @ X5)
% 0.20/0.48          | ~ (l1_waybel_0 @ X5 @ X4)
% 0.20/0.48          | (l1_waybel_0 @ X6 @ X4)
% 0.20/0.48          | ~ (m2_yellow_6 @ X6 @ X4 @ X5))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (((l1_waybel_0 @ sk_D @ sk_A)
% 0.20/0.48        | ~ (l1_waybel_0 @ sk_C @ sk_A)
% 0.20/0.48        | ~ (v7_waybel_0 @ sk_C)
% 0.20/0.48        | ~ (v4_orders_2 @ sk_C)
% 0.20/0.48        | (v2_struct_0 @ sk_C)
% 0.20/0.48        | (v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf('5', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('6', plain, ((v7_waybel_0 @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('7', plain, ((v4_orders_2 @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('8', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (((l1_waybel_0 @ sk_D @ sk_A)
% 0.20/0.48        | (v2_struct_0 @ sk_C)
% 0.20/0.48        | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['4', '5', '6', '7', '8'])).
% 0.20/0.48  thf('10', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('11', plain, (((v2_struct_0 @ sk_A) | (l1_waybel_0 @ sk_D @ sk_A))),
% 0.20/0.48      inference('clc', [status(thm)], ['9', '10'])).
% 0.20/0.48  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('13', plain, ((l1_waybel_0 @ sk_D @ sk_A)),
% 0.20/0.48      inference('clc', [status(thm)], ['11', '12'])).
% 0.20/0.48  thf(t9_waybel_0, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( r1_waybel_0 @ A @ B @ C ) <=>
% 0.20/0.48               ( ~( r2_waybel_0 @
% 0.20/0.48                    A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X0)
% 0.20/0.48          | ~ (l1_waybel_0 @ X0 @ X1)
% 0.20/0.48          | (r2_waybel_0 @ X1 @ X0 @ (k6_subset_1 @ (u1_struct_0 @ X1) @ X2))
% 0.20/0.48          | (r1_waybel_0 @ X1 @ X0 @ X2)
% 0.20/0.48          | ~ (l1_struct_0 @ X1)
% 0.20/0.48          | (v2_struct_0 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [t9_waybel_0])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_A)
% 0.20/0.48          | ~ (l1_struct_0 @ sk_A)
% 0.20/0.48          | (r1_waybel_0 @ sk_A @ sk_D @ X0)
% 0.20/0.48          | (r2_waybel_0 @ sk_A @ sk_D @ 
% 0.20/0.48             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.20/0.48          | (v2_struct_0 @ sk_D))),
% 0.20/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.48  thf('16', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_A)
% 0.20/0.48          | (r1_waybel_0 @ sk_A @ sk_D @ X0)
% 0.20/0.48          | (r2_waybel_0 @ sk_A @ sk_D @ 
% 0.20/0.48             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.20/0.48          | (v2_struct_0 @ sk_D))),
% 0.20/0.48      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.48  thf('18', plain, ((m2_yellow_6 @ sk_D @ sk_A @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t27_yellow_6, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.20/0.48             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( m2_yellow_6 @ C @ A @ B ) =>
% 0.20/0.48               ( ![D:$i]:
% 0.20/0.48                 ( ( r2_waybel_0 @ A @ C @ D ) => ( r2_waybel_0 @ A @ B @ D ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X7)
% 0.20/0.48          | ~ (v4_orders_2 @ X7)
% 0.20/0.48          | ~ (v7_waybel_0 @ X7)
% 0.20/0.48          | ~ (l1_waybel_0 @ X7 @ X8)
% 0.20/0.48          | ~ (r2_waybel_0 @ X8 @ X9 @ X10)
% 0.20/0.48          | (r2_waybel_0 @ X8 @ X7 @ X10)
% 0.20/0.48          | ~ (m2_yellow_6 @ X9 @ X8 @ X7)
% 0.20/0.48          | ~ (l1_struct_0 @ X8)
% 0.20/0.48          | (v2_struct_0 @ X8))),
% 0.20/0.48      inference('cnf', [status(esa)], [t27_yellow_6])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_A)
% 0.20/0.48          | ~ (l1_struct_0 @ sk_A)
% 0.20/0.48          | (r2_waybel_0 @ sk_A @ sk_C @ X0)
% 0.20/0.48          | ~ (r2_waybel_0 @ sk_A @ sk_D @ X0)
% 0.20/0.48          | ~ (l1_waybel_0 @ sk_C @ sk_A)
% 0.20/0.48          | ~ (v7_waybel_0 @ sk_C)
% 0.20/0.48          | ~ (v4_orders_2 @ sk_C)
% 0.20/0.48          | (v2_struct_0 @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.48  thf('21', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('22', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('23', plain, ((v7_waybel_0 @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('24', plain, ((v4_orders_2 @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_A)
% 0.20/0.48          | (r2_waybel_0 @ sk_A @ sk_C @ X0)
% 0.20/0.48          | ~ (r2_waybel_0 @ sk_A @ sk_D @ X0)
% 0.20/0.48          | (v2_struct_0 @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['20', '21', '22', '23', '24'])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_D)
% 0.20/0.48          | (r1_waybel_0 @ sk_A @ sk_D @ X0)
% 0.20/0.48          | (v2_struct_0 @ sk_A)
% 0.20/0.48          | (v2_struct_0 @ sk_C)
% 0.20/0.48          | (r2_waybel_0 @ sk_A @ sk_C @ 
% 0.20/0.48             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.20/0.48          | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['17', '25'])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((r2_waybel_0 @ sk_A @ sk_C @ 
% 0.20/0.48           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.20/0.48          | (v2_struct_0 @ sk_C)
% 0.20/0.48          | (v2_struct_0 @ sk_A)
% 0.20/0.48          | (r1_waybel_0 @ sk_A @ sk_D @ X0)
% 0.20/0.48          | (v2_struct_0 @ sk_D))),
% 0.20/0.48      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X0)
% 0.20/0.48          | ~ (l1_waybel_0 @ X0 @ X1)
% 0.20/0.48          | ~ (r1_waybel_0 @ X1 @ X0 @ X3)
% 0.20/0.48          | ~ (r2_waybel_0 @ X1 @ X0 @ (k6_subset_1 @ (u1_struct_0 @ X1) @ X3))
% 0.20/0.48          | ~ (l1_struct_0 @ X1)
% 0.20/0.48          | (v2_struct_0 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [t9_waybel_0])).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_D)
% 0.20/0.48          | (r1_waybel_0 @ sk_A @ sk_D @ X0)
% 0.20/0.48          | (v2_struct_0 @ sk_A)
% 0.20/0.48          | (v2_struct_0 @ sk_C)
% 0.20/0.48          | (v2_struct_0 @ sk_A)
% 0.20/0.48          | ~ (l1_struct_0 @ sk_A)
% 0.20/0.48          | ~ (r1_waybel_0 @ sk_A @ sk_C @ X0)
% 0.20/0.48          | ~ (l1_waybel_0 @ sk_C @ sk_A)
% 0.20/0.48          | (v2_struct_0 @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.48  thf('30', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('31', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_D)
% 0.20/0.48          | (r1_waybel_0 @ sk_A @ sk_D @ X0)
% 0.20/0.48          | (v2_struct_0 @ sk_A)
% 0.20/0.48          | (v2_struct_0 @ sk_C)
% 0.20/0.48          | (v2_struct_0 @ sk_A)
% 0.20/0.48          | ~ (r1_waybel_0 @ sk_A @ sk_C @ X0)
% 0.20/0.48          | (v2_struct_0 @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (r1_waybel_0 @ sk_A @ sk_C @ X0)
% 0.20/0.48          | (v2_struct_0 @ sk_C)
% 0.20/0.48          | (v2_struct_0 @ sk_A)
% 0.20/0.48          | (r1_waybel_0 @ sk_A @ sk_D @ X0)
% 0.20/0.48          | (v2_struct_0 @ sk_D))),
% 0.20/0.48      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.48  thf('34', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_D)
% 0.20/0.48        | (r1_waybel_0 @ sk_A @ sk_D @ sk_B)
% 0.20/0.48        | (v2_struct_0 @ sk_A)
% 0.20/0.48        | (v2_struct_0 @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '33'])).
% 0.20/0.48  thf('35', plain, (~ (r1_waybel_0 @ sk_A @ sk_D @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D))),
% 0.20/0.48      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.48  thf('37', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('38', plain, (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('clc', [status(thm)], ['36', '37'])).
% 0.20/0.48  thf('39', plain, ((m2_yellow_6 @ sk_D @ sk_A @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('40', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.48         (~ (l1_struct_0 @ X4)
% 0.20/0.48          | (v2_struct_0 @ X4)
% 0.20/0.48          | (v2_struct_0 @ X5)
% 0.20/0.48          | ~ (v4_orders_2 @ X5)
% 0.20/0.48          | ~ (v7_waybel_0 @ X5)
% 0.20/0.48          | ~ (l1_waybel_0 @ X5 @ X4)
% 0.20/0.48          | ~ (v2_struct_0 @ X6)
% 0.20/0.48          | ~ (m2_yellow_6 @ X6 @ X4 @ X5))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 0.20/0.48  thf('41', plain,
% 0.20/0.48      ((~ (v2_struct_0 @ sk_D)
% 0.20/0.48        | ~ (l1_waybel_0 @ sk_C @ sk_A)
% 0.20/0.48        | ~ (v7_waybel_0 @ sk_C)
% 0.20/0.48        | ~ (v4_orders_2 @ sk_C)
% 0.20/0.48        | (v2_struct_0 @ sk_C)
% 0.20/0.48        | (v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.48  thf('42', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('43', plain, ((v7_waybel_0 @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('44', plain, ((v4_orders_2 @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('45', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('46', plain,
% 0.20/0.48      ((~ (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['41', '42', '43', '44', '45'])).
% 0.20/0.48  thf('47', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('48', plain, (((v2_struct_0 @ sk_A) | ~ (v2_struct_0 @ sk_D))),
% 0.20/0.48      inference('clc', [status(thm)], ['46', '47'])).
% 0.20/0.48  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('50', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.48      inference('clc', [status(thm)], ['48', '49'])).
% 0.20/0.48  thf('51', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('clc', [status(thm)], ['38', '50'])).
% 0.20/0.48  thf('52', plain, ($false), inference('demod', [status(thm)], ['0', '51'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
