%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ig24Srn8WA

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:59 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   64 (  77 expanded)
%              Number of leaves         :   31 (  38 expanded)
%              Depth                    :   14
%              Number of atoms          :  437 ( 658 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_waybel_0_type,type,(
    r2_waybel_0: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('0',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

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

thf('6',plain,(
    l1_waybel_0 @ sk_B_2 @ sk_A ),
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

thf('7',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( l1_waybel_0 @ X19 @ X20 )
      | ( r1_waybel_0 @ X20 @ X19 @ ( k6_subset_1 @ ( u1_struct_0 @ X20 ) @ X21 ) )
      | ( r2_waybel_0 @ X20 @ X19 @ X21 )
      | ~ ( l1_struct_0 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t10_waybel_0])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('9',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( l1_waybel_0 @ X19 @ X20 )
      | ( r1_waybel_0 @ X20 @ X19 @ ( k4_xboole_0 @ ( u1_struct_0 @ X20 ) @ X21 ) )
      | ( r2_waybel_0 @ X20 @ X19 @ X21 )
      | ~ ( l1_struct_0 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B_2 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B_2 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_0 @ sk_A @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_B_2 )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','12'])).

thf('14',plain,(
    ~ ( r1_waybel_0 @ sk_A @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_B_2 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('16',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X10 ) @ X10 ) ),
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

thf('17',plain,(
    ! [X13: $i,X14: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( l1_waybel_0 @ X13 @ X14 )
      | ~ ( r2_waybel_0 @ X14 @ X13 @ X17 )
      | ( r2_hidden @ ( k2_waybel_0 @ X14 @ X13 @ ( sk_E @ X18 @ X17 @ X13 @ X14 ) ) @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ X0 @ ( sk_E @ ( sk_B_1 @ ( u1_struct_0 @ X0 ) ) @ X2 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r2_waybel_0 @ X1 @ X0 @ X2 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_2 )
      | ~ ( l1_waybel_0 @ sk_B_2 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_2 @ ( sk_E @ ( sk_B_1 @ ( u1_struct_0 @ sk_B_2 ) ) @ X0 @ sk_B_2 @ sk_A ) ) @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    l1_waybel_0 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_2 )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_2 @ ( sk_E @ ( sk_B_1 @ ( u1_struct_0 @ sk_B_2 ) ) @ X0 @ sk_B_2 @ sk_A ) ) @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_2 @ ( sk_E @ ( sk_B_1 @ ( u1_struct_0 @ sk_B_2 ) ) @ X0 @ sk_B_2 @ sk_A ) ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_2 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_2 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ X0 ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ig24Srn8WA
% 0.14/0.33  % Computer   : n003.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 11:14:57 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  % Running portfolio for 600 s
% 0.14/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.33  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 60 iterations in 0.039s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.49  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.20/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.49  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.20/0.49  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.20/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.49  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.20/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.49  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.20/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(r2_waybel_0_type, type, r2_waybel_0: $i > $i > $i > $o).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.49  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.20/0.49  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.20/0.49  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.49  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.49      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.49  thf(t3_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.49            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.49       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.49            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.49  thf(d1_xboole_0, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf(t83_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X7 : $i, X8 : $i]:
% 0.20/0.49         (((k4_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_xboole_0 @ X7 @ X8))),
% 0.20/0.49      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (v1_xboole_0 @ X0) | ((k4_xboole_0 @ X1 @ X0) = (X1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.49  thf(t29_yellow_6, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.20/0.49             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.49           ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.49          ( ![B:$i]:
% 0.20/0.49            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.20/0.49                ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.49              ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t29_yellow_6])).
% 0.20/0.49  thf('6', plain, ((l1_waybel_0 @ sk_B_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t10_waybel_0, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.20/0.49               ( ~( r1_waybel_0 @
% 0.20/0.49                    A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.49         ((v2_struct_0 @ X19)
% 0.20/0.49          | ~ (l1_waybel_0 @ X19 @ X20)
% 0.20/0.49          | (r1_waybel_0 @ X20 @ X19 @ 
% 0.20/0.49             (k6_subset_1 @ (u1_struct_0 @ X20) @ X21))
% 0.20/0.49          | (r2_waybel_0 @ X20 @ X19 @ X21)
% 0.20/0.49          | ~ (l1_struct_0 @ X20)
% 0.20/0.49          | (v2_struct_0 @ X20))),
% 0.20/0.49      inference('cnf', [status(esa)], [t10_waybel_0])).
% 0.20/0.49  thf(redefinition_k6_subset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X11 : $i, X12 : $i]:
% 0.20/0.49         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.49         ((v2_struct_0 @ X19)
% 0.20/0.49          | ~ (l1_waybel_0 @ X19 @ X20)
% 0.20/0.49          | (r1_waybel_0 @ X20 @ X19 @ 
% 0.20/0.49             (k4_xboole_0 @ (u1_struct_0 @ X20) @ X21))
% 0.20/0.49          | (r2_waybel_0 @ X20 @ X19 @ X21)
% 0.20/0.49          | ~ (l1_struct_0 @ X20)
% 0.20/0.49          | (v2_struct_0 @ X20))),
% 0.20/0.49      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_A)
% 0.20/0.49          | ~ (l1_struct_0 @ sk_A)
% 0.20/0.49          | (r2_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.20/0.49          | (r1_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.20/0.49             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))
% 0.20/0.49          | (v2_struct_0 @ sk_B_2))),
% 0.20/0.49      inference('sup-', [status(thm)], ['6', '9'])).
% 0.20/0.49  thf('11', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_A)
% 0.20/0.49          | (r2_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.20/0.49          | (r1_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.20/0.49             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))
% 0.20/0.49          | (v2_struct_0 @ sk_B_2))),
% 0.20/0.49      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r1_waybel_0 @ sk_A @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.20/0.49          | ~ (v1_xboole_0 @ X0)
% 0.20/0.49          | (v2_struct_0 @ sk_B_2)
% 0.20/0.49          | (r2_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.20/0.49          | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('sup+', [status(thm)], ['5', '12'])).
% 0.20/0.49  thf('14', plain, (~ (r1_waybel_0 @ sk_A @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_A)
% 0.20/0.49          | (r2_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.20/0.49          | (v2_struct_0 @ sk_B_2)
% 0.20/0.49          | ~ (v1_xboole_0 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf(existence_m1_subset_1, axiom,
% 0.20/0.49    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.20/0.49  thf('16', plain, (![X10 : $i]: (m1_subset_1 @ (sk_B_1 @ X10) @ X10)),
% 0.20/0.49      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.20/0.49  thf(d12_waybel_0, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.20/0.49               ( ![D:$i]:
% 0.20/0.49                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.49                   ( ?[E:$i]:
% 0.20/0.49                     ( ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) & 
% 0.20/0.49                       ( r1_orders_2 @ B @ D @ E ) & 
% 0.20/0.49                       ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X13 : $i, X14 : $i, X17 : $i, X18 : $i]:
% 0.20/0.49         ((v2_struct_0 @ X13)
% 0.20/0.49          | ~ (l1_waybel_0 @ X13 @ X14)
% 0.20/0.49          | ~ (r2_waybel_0 @ X14 @ X13 @ X17)
% 0.20/0.49          | (r2_hidden @ 
% 0.20/0.49             (k2_waybel_0 @ X14 @ X13 @ (sk_E @ X18 @ X17 @ X13 @ X14)) @ X17)
% 0.20/0.49          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X13))
% 0.20/0.49          | ~ (l1_struct_0 @ X14)
% 0.20/0.49          | (v2_struct_0 @ X14))),
% 0.20/0.49      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         ((v2_struct_0 @ X1)
% 0.20/0.49          | ~ (l1_struct_0 @ X1)
% 0.20/0.49          | (r2_hidden @ 
% 0.20/0.49             (k2_waybel_0 @ X1 @ X0 @ 
% 0.20/0.49              (sk_E @ (sk_B_1 @ (u1_struct_0 @ X0)) @ X2 @ X0 @ X1)) @ 
% 0.20/0.49             X2)
% 0.20/0.49          | ~ (r2_waybel_0 @ X1 @ X0 @ X2)
% 0.20/0.49          | ~ (l1_waybel_0 @ X0 @ X1)
% 0.20/0.49          | (v2_struct_0 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_xboole_0 @ X0)
% 0.20/0.49          | (v2_struct_0 @ sk_B_2)
% 0.20/0.49          | (v2_struct_0 @ sk_A)
% 0.20/0.49          | (v2_struct_0 @ sk_B_2)
% 0.20/0.49          | ~ (l1_waybel_0 @ sk_B_2 @ sk_A)
% 0.20/0.49          | (r2_hidden @ 
% 0.20/0.49             (k2_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.20/0.49              (sk_E @ (sk_B_1 @ (u1_struct_0 @ sk_B_2)) @ X0 @ sk_B_2 @ sk_A)) @ 
% 0.20/0.49             X0)
% 0.20/0.49          | ~ (l1_struct_0 @ sk_A)
% 0.20/0.49          | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['15', '18'])).
% 0.20/0.49  thf('20', plain, ((l1_waybel_0 @ sk_B_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('21', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_xboole_0 @ X0)
% 0.20/0.49          | (v2_struct_0 @ sk_B_2)
% 0.20/0.49          | (v2_struct_0 @ sk_A)
% 0.20/0.49          | (v2_struct_0 @ sk_B_2)
% 0.20/0.49          | (r2_hidden @ 
% 0.20/0.49             (k2_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.20/0.49              (sk_E @ (sk_B_1 @ (u1_struct_0 @ sk_B_2)) @ X0 @ sk_B_2 @ sk_A)) @ 
% 0.20/0.49             X0)
% 0.20/0.49          | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r2_hidden @ 
% 0.20/0.49           (k2_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.20/0.49            (sk_E @ (sk_B_1 @ (u1_struct_0 @ sk_B_2)) @ X0 @ sk_B_2 @ sk_A)) @ 
% 0.20/0.49           X0)
% 0.20/0.49          | (v2_struct_0 @ sk_A)
% 0.20/0.49          | (v2_struct_0 @ sk_B_2)
% 0.20/0.49          | ~ (v1_xboole_0 @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_xboole_0 @ X0)
% 0.20/0.49          | (v2_struct_0 @ sk_B_2)
% 0.20/0.49          | (v2_struct_0 @ sk_A)
% 0.20/0.49          | ~ (v1_xboole_0 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B_2) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.49  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v2_struct_0 @ sk_B_2))),
% 0.20/0.49      inference('clc', [status(thm)], ['26', '27'])).
% 0.20/0.49  thf('29', plain, (~ (v2_struct_0 @ sk_B_2)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('30', plain, (![X0 : $i]: ~ (v1_xboole_0 @ X0)),
% 0.20/0.49      inference('clc', [status(thm)], ['28', '29'])).
% 0.20/0.49  thf('31', plain, ($false), inference('sup-', [status(thm)], ['0', '30'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
