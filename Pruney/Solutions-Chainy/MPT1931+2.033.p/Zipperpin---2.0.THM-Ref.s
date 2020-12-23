%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3pUgkzczn8

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:01 EST 2020

% Result     : Theorem 0.84s
% Output     : Refutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :   61 (  82 expanded)
%              Number of leaves         :   26 (  37 expanded)
%              Depth                    :   13
%              Number of atoms          :  407 ( 726 expanded)
%              Number of equality atoms :    9 (  14 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r2_waybel_0_type,type,(
    r2_waybel_0: $i > $i > $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('2',plain,(
    ! [X6: $i] :
      ( ( k6_subset_1 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(demod,[status(thm)],['0','1'])).

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

thf('3',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
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

thf('4',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( l1_waybel_0 @ X19 @ X20 )
      | ( r1_waybel_0 @ X20 @ X19 @ ( k6_subset_1 @ ( u1_struct_0 @ X20 ) @ X21 ) )
      | ( r2_waybel_0 @ X20 @ X19 @ X21 )
      | ~ ( l1_struct_0 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t10_waybel_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['2','7'])).

thf('9',plain,(
    ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['12','13'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('15',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ ( sk_B @ X10 ) @ X10 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

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

thf('16',plain,(
    ! [X13: $i,X14: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( l1_waybel_0 @ X13 @ X14 )
      | ~ ( r2_waybel_0 @ X14 @ X13 @ X17 )
      | ( r2_hidden @ ( k2_waybel_0 @ X14 @ X13 @ ( sk_E @ X18 @ X17 @ X13 @ X14 ) ) @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ X0 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X2 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r2_waybel_0 @ X1 @ X0 @ X2 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
    | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ k1_xboole_0 @ sk_B_1 @ sk_A ) ) @ k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ k1_xboole_0 @ sk_B_1 @ sk_A ) ) @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ k1_xboole_0 @ sk_B_1 @ sk_A ) ) @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ k1_xboole_0 @ sk_B_1 @ sk_A ) ) @ k1_xboole_0 ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X6: $i] :
      ( ( k6_subset_1 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('27',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('28',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('30',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k6_subset_1 @ X1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['31'])).

thf('33',plain,(
    $false ),
    inference('sup-',[status(thm)],['25','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3pUgkzczn8
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:00:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.84/1.03  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.84/1.03  % Solved by: fo/fo7.sh
% 0.84/1.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.84/1.03  % done 861 iterations in 0.539s
% 0.84/1.03  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.84/1.03  % SZS output start Refutation
% 0.84/1.03  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.84/1.03  thf(r2_waybel_0_type, type, r2_waybel_0: $i > $i > $i > $o).
% 0.84/1.03  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.84/1.03  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.84/1.03  thf(sk_A_type, type, sk_A: $i).
% 0.84/1.03  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.84/1.03  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.84/1.03  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 0.84/1.03  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.84/1.03  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.84/1.03  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.84/1.03  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.84/1.03  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.84/1.03  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.84/1.03  thf(sk_B_type, type, sk_B: $i > $i).
% 0.84/1.03  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.84/1.03  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.84/1.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.84/1.03  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.84/1.03  thf(t3_boole, axiom,
% 0.84/1.03    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.84/1.03  thf('0', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.84/1.03      inference('cnf', [status(esa)], [t3_boole])).
% 0.84/1.03  thf(redefinition_k6_subset_1, axiom,
% 0.84/1.03    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.84/1.03  thf('1', plain,
% 0.84/1.03      (![X11 : $i, X12 : $i]:
% 0.84/1.03         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.84/1.03      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.84/1.03  thf('2', plain, (![X6 : $i]: ((k6_subset_1 @ X6 @ k1_xboole_0) = (X6))),
% 0.84/1.03      inference('demod', [status(thm)], ['0', '1'])).
% 0.84/1.03  thf(t29_yellow_6, conjecture,
% 0.84/1.03    (![A:$i]:
% 0.84/1.03     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.84/1.03       ( ![B:$i]:
% 0.84/1.03         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.84/1.03             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.84/1.03           ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.84/1.03  thf(zf_stmt_0, negated_conjecture,
% 0.84/1.03    (~( ![A:$i]:
% 0.84/1.03        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.84/1.03          ( ![B:$i]:
% 0.84/1.03            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.84/1.03                ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.84/1.03              ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ) )),
% 0.84/1.03    inference('cnf.neg', [status(esa)], [t29_yellow_6])).
% 0.84/1.03  thf('3', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf(t10_waybel_0, axiom,
% 0.84/1.03    (![A:$i]:
% 0.84/1.03     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.84/1.03       ( ![B:$i]:
% 0.84/1.03         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.84/1.03           ( ![C:$i]:
% 0.84/1.03             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.84/1.03               ( ~( r1_waybel_0 @
% 0.84/1.03                    A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ))).
% 0.84/1.03  thf('4', plain,
% 0.84/1.03      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.84/1.03         ((v2_struct_0 @ X19)
% 0.84/1.03          | ~ (l1_waybel_0 @ X19 @ X20)
% 0.84/1.03          | (r1_waybel_0 @ X20 @ X19 @ 
% 0.84/1.03             (k6_subset_1 @ (u1_struct_0 @ X20) @ X21))
% 0.84/1.03          | (r2_waybel_0 @ X20 @ X19 @ X21)
% 0.84/1.03          | ~ (l1_struct_0 @ X20)
% 0.84/1.03          | (v2_struct_0 @ X20))),
% 0.84/1.03      inference('cnf', [status(esa)], [t10_waybel_0])).
% 0.84/1.03  thf('5', plain,
% 0.84/1.03      (![X0 : $i]:
% 0.84/1.03         ((v2_struct_0 @ sk_A)
% 0.84/1.03          | ~ (l1_struct_0 @ sk_A)
% 0.84/1.03          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.84/1.03          | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.84/1.03             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.84/1.03          | (v2_struct_0 @ sk_B_1))),
% 0.84/1.03      inference('sup-', [status(thm)], ['3', '4'])).
% 0.84/1.03  thf('6', plain, ((l1_struct_0 @ sk_A)),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf('7', plain,
% 0.84/1.03      (![X0 : $i]:
% 0.84/1.03         ((v2_struct_0 @ sk_A)
% 0.84/1.03          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.84/1.03          | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.84/1.03             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.84/1.03          | (v2_struct_0 @ sk_B_1))),
% 0.84/1.03      inference('demod', [status(thm)], ['5', '6'])).
% 0.84/1.03  thf('8', plain,
% 0.84/1.03      (((r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.84/1.03        | (v2_struct_0 @ sk_B_1)
% 0.84/1.03        | (r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0)
% 0.84/1.03        | (v2_struct_0 @ sk_A))),
% 0.84/1.03      inference('sup+', [status(thm)], ['2', '7'])).
% 0.84/1.03  thf('9', plain, (~ (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf('10', plain,
% 0.84/1.03      (((v2_struct_0 @ sk_A)
% 0.84/1.03        | (r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0)
% 0.84/1.03        | (v2_struct_0 @ sk_B_1))),
% 0.84/1.03      inference('sup-', [status(thm)], ['8', '9'])).
% 0.84/1.03  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf('12', plain,
% 0.84/1.03      (((v2_struct_0 @ sk_B_1) | (r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0))),
% 0.84/1.03      inference('clc', [status(thm)], ['10', '11'])).
% 0.84/1.03  thf('13', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf('14', plain, ((r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0)),
% 0.84/1.03      inference('clc', [status(thm)], ['12', '13'])).
% 0.84/1.03  thf(existence_m1_subset_1, axiom,
% 0.84/1.03    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.84/1.03  thf('15', plain, (![X10 : $i]: (m1_subset_1 @ (sk_B @ X10) @ X10)),
% 0.84/1.03      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.84/1.03  thf(d12_waybel_0, axiom,
% 0.84/1.03    (![A:$i]:
% 0.84/1.03     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.84/1.03       ( ![B:$i]:
% 0.84/1.03         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.84/1.03           ( ![C:$i]:
% 0.84/1.03             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.84/1.03               ( ![D:$i]:
% 0.84/1.03                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.84/1.03                   ( ?[E:$i]:
% 0.84/1.03                     ( ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) & 
% 0.84/1.03                       ( r1_orders_2 @ B @ D @ E ) & 
% 0.84/1.03                       ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.84/1.03  thf('16', plain,
% 0.84/1.03      (![X13 : $i, X14 : $i, X17 : $i, X18 : $i]:
% 0.84/1.03         ((v2_struct_0 @ X13)
% 0.84/1.03          | ~ (l1_waybel_0 @ X13 @ X14)
% 0.84/1.03          | ~ (r2_waybel_0 @ X14 @ X13 @ X17)
% 0.84/1.03          | (r2_hidden @ 
% 0.84/1.03             (k2_waybel_0 @ X14 @ X13 @ (sk_E @ X18 @ X17 @ X13 @ X14)) @ X17)
% 0.84/1.03          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X13))
% 0.84/1.03          | ~ (l1_struct_0 @ X14)
% 0.84/1.03          | (v2_struct_0 @ X14))),
% 0.84/1.03      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.84/1.03  thf('17', plain,
% 0.84/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.03         ((v2_struct_0 @ X1)
% 0.84/1.03          | ~ (l1_struct_0 @ X1)
% 0.84/1.03          | (r2_hidden @ 
% 0.84/1.03             (k2_waybel_0 @ X1 @ X0 @ 
% 0.84/1.03              (sk_E @ (sk_B @ (u1_struct_0 @ X0)) @ X2 @ X0 @ X1)) @ 
% 0.84/1.03             X2)
% 0.84/1.03          | ~ (r2_waybel_0 @ X1 @ X0 @ X2)
% 0.84/1.03          | ~ (l1_waybel_0 @ X0 @ X1)
% 0.84/1.03          | (v2_struct_0 @ X0))),
% 0.84/1.03      inference('sup-', [status(thm)], ['15', '16'])).
% 0.84/1.03  thf('18', plain,
% 0.84/1.03      (((v2_struct_0 @ sk_B_1)
% 0.84/1.03        | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.84/1.03        | (r2_hidden @ 
% 0.84/1.03           (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.84/1.03            (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ k1_xboole_0 @ sk_B_1 @ 
% 0.84/1.03             sk_A)) @ 
% 0.84/1.03           k1_xboole_0)
% 0.84/1.03        | ~ (l1_struct_0 @ sk_A)
% 0.84/1.03        | (v2_struct_0 @ sk_A))),
% 0.84/1.03      inference('sup-', [status(thm)], ['14', '17'])).
% 0.84/1.03  thf('19', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf('20', plain, ((l1_struct_0 @ sk_A)),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf('21', plain,
% 0.84/1.03      (((v2_struct_0 @ sk_B_1)
% 0.84/1.03        | (r2_hidden @ 
% 0.84/1.03           (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.84/1.03            (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ k1_xboole_0 @ sk_B_1 @ 
% 0.84/1.03             sk_A)) @ 
% 0.84/1.03           k1_xboole_0)
% 0.84/1.03        | (v2_struct_0 @ sk_A))),
% 0.84/1.03      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.84/1.03  thf('22', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf('23', plain,
% 0.84/1.03      (((v2_struct_0 @ sk_A)
% 0.84/1.03        | (r2_hidden @ 
% 0.84/1.03           (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.84/1.03            (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ k1_xboole_0 @ sk_B_1 @ 
% 0.84/1.03             sk_A)) @ 
% 0.84/1.03           k1_xboole_0))),
% 0.84/1.03      inference('clc', [status(thm)], ['21', '22'])).
% 0.84/1.03  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf('25', plain,
% 0.84/1.03      ((r2_hidden @ 
% 0.84/1.03        (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.84/1.03         (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ k1_xboole_0 @ sk_B_1 @ sk_A)) @ 
% 0.84/1.03        k1_xboole_0)),
% 0.84/1.03      inference('clc', [status(thm)], ['23', '24'])).
% 0.84/1.03  thf('26', plain, (![X6 : $i]: ((k6_subset_1 @ X6 @ k1_xboole_0) = (X6))),
% 0.84/1.03      inference('demod', [status(thm)], ['0', '1'])).
% 0.84/1.03  thf(d5_xboole_0, axiom,
% 0.84/1.03    (![A:$i,B:$i,C:$i]:
% 0.84/1.03     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.84/1.03       ( ![D:$i]:
% 0.84/1.03         ( ( r2_hidden @ D @ C ) <=>
% 0.84/1.03           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.84/1.03  thf('27', plain,
% 0.84/1.03      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.84/1.03         (~ (r2_hidden @ X4 @ X3)
% 0.84/1.03          | ~ (r2_hidden @ X4 @ X2)
% 0.84/1.03          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.84/1.03      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.84/1.03  thf('28', plain,
% 0.84/1.03      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.84/1.03         (~ (r2_hidden @ X4 @ X2)
% 0.84/1.03          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.84/1.03      inference('simplify', [status(thm)], ['27'])).
% 0.84/1.03  thf('29', plain,
% 0.84/1.03      (![X11 : $i, X12 : $i]:
% 0.84/1.03         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.84/1.03      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.84/1.03  thf('30', plain,
% 0.84/1.03      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.84/1.03         (~ (r2_hidden @ X4 @ X2)
% 0.84/1.03          | ~ (r2_hidden @ X4 @ (k6_subset_1 @ X1 @ X2)))),
% 0.84/1.03      inference('demod', [status(thm)], ['28', '29'])).
% 0.84/1.03  thf('31', plain,
% 0.84/1.03      (![X0 : $i, X1 : $i]:
% 0.84/1.03         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.84/1.03      inference('sup-', [status(thm)], ['26', '30'])).
% 0.84/1.03  thf('32', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.84/1.03      inference('condensation', [status(thm)], ['31'])).
% 0.84/1.03  thf('33', plain, ($false), inference('sup-', [status(thm)], ['25', '32'])).
% 0.84/1.03  
% 0.84/1.03  % SZS output end Refutation
% 0.84/1.03  
% 0.84/1.03  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
