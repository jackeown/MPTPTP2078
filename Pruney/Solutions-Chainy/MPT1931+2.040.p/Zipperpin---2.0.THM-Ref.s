%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nNfHHzqwKq

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:02 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   69 (  97 expanded)
%              Number of leaves         :   28 (  42 expanded)
%              Depth                    :   14
%              Number of atoms          :  474 ( 978 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_waybel_0_type,type,(
    r2_waybel_0: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(o_2_2_yellow_6_type,type,(
    o_2_2_yellow_6: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('0',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t29_yellow_6,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_struct_0 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v4_orders_2 @ B )
              & ( v7_waybel_0 @ B )
              & ( l1_waybel_0 @ B @ A ) )
           => ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_yellow_6])).

thf('1',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( r2_waybel_0 @ A @ B @ C )
            <=> ~ ( r1_waybel_0 @ A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( l1_waybel_0 @ X12 @ X13 )
      | ( r1_waybel_0 @ X13 @ X12 @ ( k6_subset_1 @ ( u1_struct_0 @ X13 ) @ X14 ) )
      | ( r2_waybel_0 @ X13 @ X12 @ X14 )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t10_waybel_0])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k6_subset_1 @ X2 @ X3 )
      = ( k4_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( l1_waybel_0 @ X12 @ X13 )
      | ( r1_waybel_0 @ X13 @ X12 @ ( k4_xboole_0 @ ( u1_struct_0 @ X13 ) @ X14 ) )
      | ( r2_waybel_0 @ X13 @ X12 @ X14 )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( r1_waybel_0 @ sk_A @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_0 @ sk_A @ sk_B @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','7'])).

thf('9',plain,(
    ~ ( r1_waybel_0 @ sk_A @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_waybel_0 @ sk_A @ sk_B @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_waybel_0 @ sk_A @ sk_B @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r2_waybel_0 @ sk_A @ sk_B @ k1_xboole_0 ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_o_2_2_yellow_6,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ~ ( v2_struct_0 @ B )
        & ( v4_orders_2 @ B )
        & ( v7_waybel_0 @ B )
        & ( l1_waybel_0 @ B @ A ) )
     => ( m1_subset_1 @ ( o_2_2_yellow_6 @ A @ B ) @ ( u1_struct_0 @ B ) ) ) )).

thf('16',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v7_waybel_0 @ X17 )
      | ~ ( l1_waybel_0 @ X17 @ X16 )
      | ( m1_subset_1 @ ( o_2_2_yellow_6 @ X16 @ X17 ) @ ( u1_struct_0 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_o_2_2_yellow_6])).

thf('17',plain,
    ( ( m1_subset_1 @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( m1_subset_1 @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18','19','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['23','24'])).

thf(d12_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( r2_waybel_0 @ A @ B @ C )
            <=> ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) )
                 => ? [E: $i] :
                      ( ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C )
                      & ( r1_orders_2 @ B @ D @ E )
                      & ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) ) ) ) )).

thf('26',plain,(
    ! [X6: $i,X7: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( l1_waybel_0 @ X6 @ X7 )
      | ~ ( r2_waybel_0 @ X7 @ X6 @ X10 )
      | ( r2_hidden @ ( k2_waybel_0 @ X7 @ X6 @ ( sk_E @ X11 @ X10 @ X6 @ X7 ) ) @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( r2_hidden @ ( k2_waybel_0 @ X0 @ sk_B @ ( sk_E @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ X1 @ sk_B @ X0 ) ) @ X1 )
      | ~ ( r2_waybel_0 @ X0 @ sk_B @ X1 )
      | ~ ( l1_waybel_0 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B @ ( sk_E @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_B @ sk_A ) ) @ k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','27'])).

thf('29',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B @ ( sk_E @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_B @ sk_A ) ) @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B @ ( sk_E @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_B @ sk_A ) ) @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B @ ( sk_E @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_B @ sk_A ) ) @ k1_xboole_0 ),
    inference(clc,[status(thm)],['33','34'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('36',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('37',plain,(
    ~ ( r1_tarski @ k1_xboole_0 @ ( k2_waybel_0 @ sk_A @ sk_B @ ( sk_E @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['37','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nNfHHzqwKq
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:42:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.49  % Solved by: fo/fo7.sh
% 0.19/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.49  % done 40 iterations in 0.038s
% 0.19/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.49  % SZS output start Refutation
% 0.19/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.49  thf(r2_waybel_0_type, type, r2_waybel_0: $i > $i > $i > $o).
% 0.19/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.49  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.19/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.49  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.19/0.49  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.19/0.49  thf(o_2_2_yellow_6_type, type, o_2_2_yellow_6: $i > $i > $i).
% 0.19/0.49  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.19/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.49  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 0.19/0.49  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.19/0.49  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.19/0.49  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.19/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.19/0.49  thf(t3_boole, axiom,
% 0.19/0.49    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.49  thf('0', plain, (![X1 : $i]: ((k4_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.19/0.49      inference('cnf', [status(esa)], [t3_boole])).
% 0.19/0.49  thf(t29_yellow_6, conjecture,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.19/0.49             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.19/0.49           ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.19/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.49    (~( ![A:$i]:
% 0.19/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.49          ( ![B:$i]:
% 0.19/0.49            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.19/0.49                ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.19/0.49              ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ) )),
% 0.19/0.49    inference('cnf.neg', [status(esa)], [t29_yellow_6])).
% 0.19/0.49  thf('1', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(t10_waybel_0, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.19/0.49           ( ![C:$i]:
% 0.19/0.49             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.19/0.49               ( ~( r1_waybel_0 @
% 0.19/0.49                    A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ))).
% 0.19/0.49  thf('2', plain,
% 0.19/0.49      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.49         ((v2_struct_0 @ X12)
% 0.19/0.49          | ~ (l1_waybel_0 @ X12 @ X13)
% 0.19/0.49          | (r1_waybel_0 @ X13 @ X12 @ 
% 0.19/0.49             (k6_subset_1 @ (u1_struct_0 @ X13) @ X14))
% 0.19/0.49          | (r2_waybel_0 @ X13 @ X12 @ X14)
% 0.19/0.49          | ~ (l1_struct_0 @ X13)
% 0.19/0.49          | (v2_struct_0 @ X13))),
% 0.19/0.49      inference('cnf', [status(esa)], [t10_waybel_0])).
% 0.19/0.49  thf(redefinition_k6_subset_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.19/0.49  thf('3', plain,
% 0.19/0.49      (![X2 : $i, X3 : $i]: ((k6_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))),
% 0.19/0.49      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.19/0.49  thf('4', plain,
% 0.19/0.49      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.49         ((v2_struct_0 @ X12)
% 0.19/0.49          | ~ (l1_waybel_0 @ X12 @ X13)
% 0.19/0.49          | (r1_waybel_0 @ X13 @ X12 @ 
% 0.19/0.49             (k4_xboole_0 @ (u1_struct_0 @ X13) @ X14))
% 0.19/0.49          | (r2_waybel_0 @ X13 @ X12 @ X14)
% 0.19/0.49          | ~ (l1_struct_0 @ X13)
% 0.19/0.49          | (v2_struct_0 @ X13))),
% 0.19/0.49      inference('demod', [status(thm)], ['2', '3'])).
% 0.19/0.49  thf('5', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((v2_struct_0 @ sk_A)
% 0.19/0.49          | ~ (l1_struct_0 @ sk_A)
% 0.19/0.49          | (r2_waybel_0 @ sk_A @ sk_B @ X0)
% 0.19/0.49          | (r1_waybel_0 @ sk_A @ sk_B @ 
% 0.19/0.49             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))
% 0.19/0.49          | (v2_struct_0 @ sk_B))),
% 0.19/0.49      inference('sup-', [status(thm)], ['1', '4'])).
% 0.19/0.49  thf('6', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('7', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((v2_struct_0 @ sk_A)
% 0.19/0.49          | (r2_waybel_0 @ sk_A @ sk_B @ X0)
% 0.19/0.49          | (r1_waybel_0 @ sk_A @ sk_B @ 
% 0.19/0.49             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))
% 0.19/0.49          | (v2_struct_0 @ sk_B))),
% 0.19/0.49      inference('demod', [status(thm)], ['5', '6'])).
% 0.19/0.49  thf('8', plain,
% 0.19/0.49      (((r1_waybel_0 @ sk_A @ sk_B @ (u1_struct_0 @ sk_A))
% 0.19/0.49        | (v2_struct_0 @ sk_B)
% 0.19/0.49        | (r2_waybel_0 @ sk_A @ sk_B @ k1_xboole_0)
% 0.19/0.49        | (v2_struct_0 @ sk_A))),
% 0.19/0.49      inference('sup+', [status(thm)], ['0', '7'])).
% 0.19/0.49  thf('9', plain, (~ (r1_waybel_0 @ sk_A @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('10', plain,
% 0.19/0.49      (((v2_struct_0 @ sk_A)
% 0.19/0.49        | (r2_waybel_0 @ sk_A @ sk_B @ k1_xboole_0)
% 0.19/0.49        | (v2_struct_0 @ sk_B))),
% 0.19/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.49  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('12', plain,
% 0.19/0.49      (((v2_struct_0 @ sk_B) | (r2_waybel_0 @ sk_A @ sk_B @ k1_xboole_0))),
% 0.19/0.49      inference('clc', [status(thm)], ['10', '11'])).
% 0.19/0.49  thf('13', plain, (~ (v2_struct_0 @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('14', plain, ((r2_waybel_0 @ sk_A @ sk_B @ k1_xboole_0)),
% 0.19/0.49      inference('clc', [status(thm)], ['12', '13'])).
% 0.19/0.49  thf('15', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(dt_o_2_2_yellow_6, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.19/0.49         ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.19/0.49         ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.19/0.49       ( m1_subset_1 @ ( o_2_2_yellow_6 @ A @ B ) @ ( u1_struct_0 @ B ) ) ))).
% 0.19/0.49  thf('16', plain,
% 0.19/0.49      (![X16 : $i, X17 : $i]:
% 0.19/0.49         (~ (l1_struct_0 @ X16)
% 0.19/0.49          | (v2_struct_0 @ X16)
% 0.19/0.49          | (v2_struct_0 @ X17)
% 0.19/0.49          | ~ (v4_orders_2 @ X17)
% 0.19/0.49          | ~ (v7_waybel_0 @ X17)
% 0.19/0.49          | ~ (l1_waybel_0 @ X17 @ X16)
% 0.19/0.49          | (m1_subset_1 @ (o_2_2_yellow_6 @ X16 @ X17) @ (u1_struct_0 @ X17)))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_o_2_2_yellow_6])).
% 0.19/0.49  thf('17', plain,
% 0.19/0.49      (((m1_subset_1 @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.19/0.49        | ~ (v7_waybel_0 @ sk_B)
% 0.19/0.49        | ~ (v4_orders_2 @ sk_B)
% 0.19/0.49        | (v2_struct_0 @ sk_B)
% 0.19/0.49        | (v2_struct_0 @ sk_A)
% 0.19/0.49        | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.49  thf('18', plain, ((v7_waybel_0 @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('19', plain, ((v4_orders_2 @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('20', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('21', plain,
% 0.19/0.49      (((m1_subset_1 @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.19/0.49        | (v2_struct_0 @ sk_B)
% 0.19/0.49        | (v2_struct_0 @ sk_A))),
% 0.19/0.49      inference('demod', [status(thm)], ['17', '18', '19', '20'])).
% 0.19/0.49  thf('22', plain, (~ (v2_struct_0 @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('23', plain,
% 0.19/0.49      (((v2_struct_0 @ sk_A)
% 0.19/0.49        | (m1_subset_1 @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)))),
% 0.19/0.49      inference('clc', [status(thm)], ['21', '22'])).
% 0.19/0.49  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('25', plain,
% 0.19/0.49      ((m1_subset_1 @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))),
% 0.19/0.49      inference('clc', [status(thm)], ['23', '24'])).
% 0.19/0.49  thf(d12_waybel_0, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.19/0.49           ( ![C:$i]:
% 0.19/0.49             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.19/0.49               ( ![D:$i]:
% 0.19/0.49                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.19/0.49                   ( ?[E:$i]:
% 0.19/0.49                     ( ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) & 
% 0.19/0.49                       ( r1_orders_2 @ B @ D @ E ) & 
% 0.19/0.49                       ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.49  thf('26', plain,
% 0.19/0.49      (![X6 : $i, X7 : $i, X10 : $i, X11 : $i]:
% 0.19/0.49         ((v2_struct_0 @ X6)
% 0.19/0.49          | ~ (l1_waybel_0 @ X6 @ X7)
% 0.19/0.49          | ~ (r2_waybel_0 @ X7 @ X6 @ X10)
% 0.19/0.49          | (r2_hidden @ 
% 0.19/0.49             (k2_waybel_0 @ X7 @ X6 @ (sk_E @ X11 @ X10 @ X6 @ X7)) @ X10)
% 0.19/0.49          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X6))
% 0.19/0.49          | ~ (l1_struct_0 @ X7)
% 0.19/0.49          | (v2_struct_0 @ X7))),
% 0.19/0.49      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.19/0.49  thf('27', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         ((v2_struct_0 @ X0)
% 0.19/0.49          | ~ (l1_struct_0 @ X0)
% 0.19/0.49          | (r2_hidden @ 
% 0.19/0.49             (k2_waybel_0 @ X0 @ sk_B @ 
% 0.19/0.49              (sk_E @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ X1 @ sk_B @ X0)) @ 
% 0.19/0.49             X1)
% 0.19/0.49          | ~ (r2_waybel_0 @ X0 @ sk_B @ X1)
% 0.19/0.49          | ~ (l1_waybel_0 @ sk_B @ X0)
% 0.19/0.49          | (v2_struct_0 @ sk_B))),
% 0.19/0.49      inference('sup-', [status(thm)], ['25', '26'])).
% 0.19/0.49  thf('28', plain,
% 0.19/0.49      (((v2_struct_0 @ sk_B)
% 0.19/0.49        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.19/0.49        | (r2_hidden @ 
% 0.19/0.49           (k2_waybel_0 @ sk_A @ sk_B @ 
% 0.19/0.49            (sk_E @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ k1_xboole_0 @ sk_B @ sk_A)) @ 
% 0.19/0.49           k1_xboole_0)
% 0.19/0.49        | ~ (l1_struct_0 @ sk_A)
% 0.19/0.49        | (v2_struct_0 @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['14', '27'])).
% 0.19/0.49  thf('29', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('30', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('31', plain,
% 0.19/0.49      (((v2_struct_0 @ sk_B)
% 0.19/0.49        | (r2_hidden @ 
% 0.19/0.49           (k2_waybel_0 @ sk_A @ sk_B @ 
% 0.19/0.49            (sk_E @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ k1_xboole_0 @ sk_B @ sk_A)) @ 
% 0.19/0.49           k1_xboole_0)
% 0.19/0.49        | (v2_struct_0 @ sk_A))),
% 0.19/0.49      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.19/0.49  thf('32', plain, (~ (v2_struct_0 @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('33', plain,
% 0.19/0.49      (((v2_struct_0 @ sk_A)
% 0.19/0.49        | (r2_hidden @ 
% 0.19/0.49           (k2_waybel_0 @ sk_A @ sk_B @ 
% 0.19/0.49            (sk_E @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ k1_xboole_0 @ sk_B @ sk_A)) @ 
% 0.19/0.49           k1_xboole_0))),
% 0.19/0.49      inference('clc', [status(thm)], ['31', '32'])).
% 0.19/0.49  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('35', plain,
% 0.19/0.49      ((r2_hidden @ 
% 0.19/0.49        (k2_waybel_0 @ sk_A @ sk_B @ 
% 0.19/0.49         (sk_E @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ k1_xboole_0 @ sk_B @ sk_A)) @ 
% 0.19/0.49        k1_xboole_0)),
% 0.19/0.49      inference('clc', [status(thm)], ['33', '34'])).
% 0.19/0.49  thf(t7_ordinal1, axiom,
% 0.19/0.49    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.49  thf('36', plain,
% 0.19/0.49      (![X4 : $i, X5 : $i]: (~ (r2_hidden @ X4 @ X5) | ~ (r1_tarski @ X5 @ X4))),
% 0.19/0.49      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.19/0.49  thf('37', plain,
% 0.19/0.49      (~ (r1_tarski @ k1_xboole_0 @ 
% 0.19/0.49          (k2_waybel_0 @ sk_A @ sk_B @ 
% 0.19/0.49           (sk_E @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ k1_xboole_0 @ sk_B @ sk_A)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['35', '36'])).
% 0.19/0.49  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.19/0.49  thf('38', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.19/0.49      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.49  thf('39', plain, ($false), inference('demod', [status(thm)], ['37', '38'])).
% 0.19/0.49  
% 0.19/0.49  % SZS output end Refutation
% 0.19/0.49  
% 0.19/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
