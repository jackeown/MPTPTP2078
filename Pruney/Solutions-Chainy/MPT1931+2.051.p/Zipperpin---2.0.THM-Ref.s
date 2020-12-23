%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0vHuqHuRTO

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   68 (  86 expanded)
%              Number of leaves         :   31 (  41 expanded)
%              Depth                    :   14
%              Number of atoms          :  447 ( 744 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r2_waybel_0_type,type,(
    r2_waybel_0: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

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
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_C @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

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

thf('7',plain,(
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

thf('8',plain,(
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

thf('9',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ X9 @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('10',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( l1_waybel_0 @ X19 @ X20 )
      | ( r1_waybel_0 @ X20 @ X19 @ ( k4_xboole_0 @ ( u1_struct_0 @ X20 ) @ X21 ) )
      | ( r2_waybel_0 @ X20 @ X19 @ X21 )
      | ~ ( l1_struct_0 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['6','13'])).

thf('15',plain,(
    ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['18','19'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('21',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ ( sk_B @ X8 ) @ X8 ) ),
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

thf('22',plain,(
    ! [X13: $i,X14: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( l1_waybel_0 @ X13 @ X14 )
      | ~ ( r2_waybel_0 @ X14 @ X13 @ X17 )
      | ( r2_hidden @ ( k2_waybel_0 @ X14 @ X13 @ ( sk_E @ X18 @ X17 @ X13 @ X14 ) ) @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ X0 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X2 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r2_waybel_0 @ X1 @ X0 @ X2 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
    | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ k1_xboole_0 @ sk_B_1 @ sk_A ) ) @ k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ k1_xboole_0 @ sk_B_1 @ sk_A ) ) @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ k1_xboole_0 @ sk_B_1 @ sk_A ) ) @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ k1_xboole_0 @ sk_B_1 @ sk_A ) ) @ k1_xboole_0 ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('33',plain,(
    ~ ( r1_tarski @ k1_xboole_0 @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ k1_xboole_0 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['33','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0vHuqHuRTO
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:03:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 55 iterations in 0.036s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(r2_waybel_0_type, type, r2_waybel_0: $i > $i > $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.20/0.49  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.49  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.20/0.49  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 0.20/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.49  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.20/0.49  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.49  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.20/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.49  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.49  thf('0', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.20/0.49      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.49  thf(t3_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.49            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.49       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.49            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.49  thf(t7_ordinal1, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X11 : $i, X12 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X11 @ X12) | ~ (r1_tarski @ X12 @ X11))),
% 0.20/0.49      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_tarski @ X0 @ (sk_C @ X0 @ X1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf('4', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.49  thf(t83_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i]:
% 0.20/0.49         (((k4_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_xboole_0 @ X5 @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.49  thf('6', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '5'])).
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
% 0.20/0.49  thf('7', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
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
% 0.20/0.49  thf('8', plain,
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
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X9 : $i, X10 : $i]:
% 0.20/0.49         ((k6_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.49         ((v2_struct_0 @ X19)
% 0.20/0.49          | ~ (l1_waybel_0 @ X19 @ X20)
% 0.20/0.49          | (r1_waybel_0 @ X20 @ X19 @ 
% 0.20/0.49             (k4_xboole_0 @ (u1_struct_0 @ X20) @ X21))
% 0.20/0.49          | (r2_waybel_0 @ X20 @ X19 @ X21)
% 0.20/0.49          | ~ (l1_struct_0 @ X20)
% 0.20/0.49          | (v2_struct_0 @ X20))),
% 0.20/0.49      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_A)
% 0.20/0.49          | ~ (l1_struct_0 @ sk_A)
% 0.20/0.49          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.20/0.49          | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.20/0.49             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))
% 0.20/0.49          | (v2_struct_0 @ sk_B_1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['7', '10'])).
% 0.20/0.49  thf('12', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_A)
% 0.20/0.49          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.20/0.49          | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.20/0.49             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))
% 0.20/0.49          | (v2_struct_0 @ sk_B_1))),
% 0.20/0.49      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (((r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.49        | (v2_struct_0 @ sk_B_1)
% 0.20/0.49        | (r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0)
% 0.20/0.49        | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('sup+', [status(thm)], ['6', '13'])).
% 0.20/0.49  thf('15', plain, (~ (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | (r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0)
% 0.20/0.49        | (v2_struct_0 @ sk_B_1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.49  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_B_1) | (r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0))),
% 0.20/0.49      inference('clc', [status(thm)], ['16', '17'])).
% 0.20/0.49  thf('19', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('20', plain, ((r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0)),
% 0.20/0.49      inference('clc', [status(thm)], ['18', '19'])).
% 0.20/0.49  thf(existence_m1_subset_1, axiom,
% 0.20/0.49    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.20/0.49  thf('21', plain, (![X8 : $i]: (m1_subset_1 @ (sk_B @ X8) @ X8)),
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
% 0.20/0.49  thf('22', plain,
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
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         ((v2_struct_0 @ X1)
% 0.20/0.49          | ~ (l1_struct_0 @ X1)
% 0.20/0.49          | (r2_hidden @ 
% 0.20/0.49             (k2_waybel_0 @ X1 @ X0 @ 
% 0.20/0.49              (sk_E @ (sk_B @ (u1_struct_0 @ X0)) @ X2 @ X0 @ X1)) @ 
% 0.20/0.49             X2)
% 0.20/0.49          | ~ (r2_waybel_0 @ X1 @ X0 @ X2)
% 0.20/0.49          | ~ (l1_waybel_0 @ X0 @ X1)
% 0.20/0.49          | (v2_struct_0 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_B_1)
% 0.20/0.49        | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.20/0.49        | (r2_hidden @ 
% 0.20/0.49           (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.20/0.49            (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ k1_xboole_0 @ sk_B_1 @ 
% 0.20/0.49             sk_A)) @ 
% 0.20/0.49           k1_xboole_0)
% 0.20/0.49        | ~ (l1_struct_0 @ sk_A)
% 0.20/0.49        | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['20', '23'])).
% 0.20/0.49  thf('25', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('26', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_B_1)
% 0.20/0.49        | (r2_hidden @ 
% 0.20/0.49           (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.20/0.49            (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ k1_xboole_0 @ sk_B_1 @ 
% 0.20/0.49             sk_A)) @ 
% 0.20/0.49           k1_xboole_0)
% 0.20/0.49        | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.20/0.49  thf('28', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | (r2_hidden @ 
% 0.20/0.49           (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.20/0.49            (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ k1_xboole_0 @ sk_B_1 @ 
% 0.20/0.49             sk_A)) @ 
% 0.20/0.49           k1_xboole_0))),
% 0.20/0.49      inference('clc', [status(thm)], ['27', '28'])).
% 0.20/0.49  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      ((r2_hidden @ 
% 0.20/0.49        (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.20/0.49         (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ k1_xboole_0 @ sk_B_1 @ sk_A)) @ 
% 0.20/0.49        k1_xboole_0)),
% 0.20/0.49      inference('clc', [status(thm)], ['29', '30'])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (![X11 : $i, X12 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X11 @ X12) | ~ (r1_tarski @ X12 @ X11))),
% 0.20/0.49      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (~ (r1_tarski @ k1_xboole_0 @ 
% 0.20/0.49          (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.20/0.49           (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ k1_xboole_0 @ sk_B_1 @ 
% 0.20/0.49            sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.49  thf('34', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.20/0.49      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.49  thf('35', plain, ($false), inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
