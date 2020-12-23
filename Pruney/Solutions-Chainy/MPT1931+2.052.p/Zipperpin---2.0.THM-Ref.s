%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.byA5QLhtfK

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 129 expanded)
%              Number of leaves         :   30 (  52 expanded)
%              Depth                    :   19
%              Number of atoms          :  547 (1364 expanded)
%              Number of equality atoms :    5 (  10 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_waybel_0_type,type,(
    r2_waybel_0: $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('0',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ X1 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X3 )
        = X2 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( l1_waybel_0 @ X16 @ X17 )
      | ( r1_waybel_0 @ X17 @ X16 @ ( k6_subset_1 @ ( u1_struct_0 @ X17 ) @ X18 ) )
      | ( r2_waybel_0 @ X17 @ X16 @ X18 )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t10_waybel_0])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k6_subset_1 @ X6 @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('6',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( l1_waybel_0 @ X16 @ X17 )
      | ( r1_waybel_0 @ X17 @ X16 @ ( k4_xboole_0 @ ( u1_struct_0 @ X17 ) @ X18 ) )
      | ( r2_waybel_0 @ X17 @ X16 @ X18 )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf('11',plain,(
    ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['14','15'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('18',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ ( sk_B @ X5 ) @ X5 ) ),
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

thf('19',plain,(
    ! [X10: $i,X11: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( l1_waybel_0 @ X10 @ X11 )
      | ~ ( r2_waybel_0 @ X11 @ X10 @ X14 )
      | ( m1_subset_1 @ ( sk_E @ X15 @ X14 @ X10 @ X11 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X2 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_waybel_0 @ X1 @ X0 @ X2 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ k1_xboole_0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ k1_xboole_0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ k1_xboole_0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ k1_xboole_0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X10: $i,X11: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( l1_waybel_0 @ X10 @ X11 )
      | ~ ( r2_waybel_0 @ X11 @ X10 @ X14 )
      | ( r2_hidden @ ( k2_waybel_0 @ X11 @ X10 @ ( sk_E @ X15 @ X14 @ X10 @ X11 ) ) @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( r2_hidden @ ( k2_waybel_0 @ X0 @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ k1_xboole_0 @ sk_B_1 @ sk_A ) @ X1 @ sk_B_1 @ X0 ) ) @ X1 )
      | ~ ( r2_waybel_0 @ X0 @ sk_B_1 @ X1 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
    | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ k1_xboole_0 @ sk_B_1 @ sk_A ) @ k1_xboole_0 @ sk_B_1 @ sk_A ) ) @ k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','30'])).

thf('32',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ k1_xboole_0 @ sk_B_1 @ sk_A ) @ k1_xboole_0 @ sk_B_1 @ sk_A ) ) @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ k1_xboole_0 @ sk_B_1 @ sk_A ) @ k1_xboole_0 @ sk_B_1 @ sk_A ) ) @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ k1_xboole_0 @ sk_B_1 @ sk_A ) @ k1_xboole_0 @ sk_B_1 @ sk_A ) ) @ k1_xboole_0 ),
    inference(clc,[status(thm)],['36','37'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('39',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('40',plain,(
    ~ ( r1_tarski @ k1_xboole_0 @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ k1_xboole_0 @ sk_B_1 @ sk_A ) @ k1_xboole_0 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['40','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.byA5QLhtfK
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:08:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 40 iterations in 0.028s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.21/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.48  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 0.21/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.48  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.48  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.21/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(r2_waybel_0_type, type, r2_waybel_0: $i > $i > $i > $o).
% 0.21/0.48  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.48  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.21/0.48  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.21/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.48  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.21/0.48  thf('0', plain, (![X1 : $i]: (r1_xboole_0 @ X1 @ k1_xboole_0)),
% 0.21/0.48      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.48  thf(t83_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X2 : $i, X3 : $i]:
% 0.21/0.48         (((k4_xboole_0 @ X2 @ X3) = (X2)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.21/0.48      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.48  thf('2', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.48  thf(t29_yellow_6, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.48             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.48           ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.48          ( ![B:$i]:
% 0.21/0.48            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.48                ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.48              ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t29_yellow_6])).
% 0.21/0.48  thf('3', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t10_waybel_0, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.48           ( ![C:$i]:
% 0.21/0.48             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.21/0.48               ( ~( r1_waybel_0 @
% 0.21/0.48                    A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ))).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.48         ((v2_struct_0 @ X16)
% 0.21/0.48          | ~ (l1_waybel_0 @ X16 @ X17)
% 0.21/0.48          | (r1_waybel_0 @ X17 @ X16 @ 
% 0.21/0.48             (k6_subset_1 @ (u1_struct_0 @ X17) @ X18))
% 0.21/0.48          | (r2_waybel_0 @ X17 @ X16 @ X18)
% 0.21/0.48          | ~ (l1_struct_0 @ X17)
% 0.21/0.48          | (v2_struct_0 @ X17))),
% 0.21/0.48      inference('cnf', [status(esa)], [t10_waybel_0])).
% 0.21/0.48  thf(redefinition_k6_subset_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i]: ((k6_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.48         ((v2_struct_0 @ X16)
% 0.21/0.48          | ~ (l1_waybel_0 @ X16 @ X17)
% 0.21/0.48          | (r1_waybel_0 @ X17 @ X16 @ 
% 0.21/0.48             (k4_xboole_0 @ (u1_struct_0 @ X17) @ X18))
% 0.21/0.48          | (r2_waybel_0 @ X17 @ X16 @ X18)
% 0.21/0.48          | ~ (l1_struct_0 @ X17)
% 0.21/0.48          | (v2_struct_0 @ X17))),
% 0.21/0.48      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((v2_struct_0 @ sk_A)
% 0.21/0.48          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.48          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.48          | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.21/0.48             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))
% 0.21/0.48          | (v2_struct_0 @ sk_B_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['3', '6'])).
% 0.21/0.48  thf('8', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((v2_struct_0 @ sk_A)
% 0.21/0.48          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.48          | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.21/0.48             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))
% 0.21/0.48          | (v2_struct_0 @ sk_B_1))),
% 0.21/0.48      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (((r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.48        | (v2_struct_0 @ sk_B_1)
% 0.21/0.48        | (r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0)
% 0.21/0.48        | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('sup+', [status(thm)], ['2', '9'])).
% 0.21/0.48  thf('11', plain, (~ (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_A)
% 0.21/0.48        | (r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0)
% 0.21/0.48        | (v2_struct_0 @ sk_B_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.48  thf('13', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_B_1) | (r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0))),
% 0.21/0.48      inference('clc', [status(thm)], ['12', '13'])).
% 0.21/0.48  thf('15', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('16', plain, ((r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0)),
% 0.21/0.48      inference('clc', [status(thm)], ['14', '15'])).
% 0.21/0.48  thf('17', plain, ((r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0)),
% 0.21/0.48      inference('clc', [status(thm)], ['14', '15'])).
% 0.21/0.48  thf(existence_m1_subset_1, axiom,
% 0.21/0.48    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.21/0.48  thf('18', plain, (![X5 : $i]: (m1_subset_1 @ (sk_B @ X5) @ X5)),
% 0.21/0.48      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.21/0.48  thf(d12_waybel_0, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.48           ( ![C:$i]:
% 0.21/0.48             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.21/0.48               ( ![D:$i]:
% 0.21/0.48                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.48                   ( ?[E:$i]:
% 0.21/0.48                     ( ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) & 
% 0.21/0.48                       ( r1_orders_2 @ B @ D @ E ) & 
% 0.21/0.48                       ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (![X10 : $i, X11 : $i, X14 : $i, X15 : $i]:
% 0.21/0.48         ((v2_struct_0 @ X10)
% 0.21/0.48          | ~ (l1_waybel_0 @ X10 @ X11)
% 0.21/0.48          | ~ (r2_waybel_0 @ X11 @ X10 @ X14)
% 0.21/0.48          | (m1_subset_1 @ (sk_E @ X15 @ X14 @ X10 @ X11) @ (u1_struct_0 @ X10))
% 0.21/0.48          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X10))
% 0.21/0.48          | ~ (l1_struct_0 @ X11)
% 0.21/0.48          | (v2_struct_0 @ X11))),
% 0.21/0.48      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         ((v2_struct_0 @ X1)
% 0.21/0.48          | ~ (l1_struct_0 @ X1)
% 0.21/0.48          | (m1_subset_1 @ 
% 0.21/0.48             (sk_E @ (sk_B @ (u1_struct_0 @ X0)) @ X2 @ X0 @ X1) @ 
% 0.21/0.48             (u1_struct_0 @ X0))
% 0.21/0.48          | ~ (r2_waybel_0 @ X1 @ X0 @ X2)
% 0.21/0.48          | ~ (l1_waybel_0 @ X0 @ X1)
% 0.21/0.48          | (v2_struct_0 @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_B_1)
% 0.21/0.48        | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.21/0.48        | (m1_subset_1 @ 
% 0.21/0.48           (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ k1_xboole_0 @ sk_B_1 @ 
% 0.21/0.48            sk_A) @ 
% 0.21/0.48           (u1_struct_0 @ sk_B_1))
% 0.21/0.48        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.48        | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['17', '20'])).
% 0.21/0.48  thf('22', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('23', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_B_1)
% 0.21/0.48        | (m1_subset_1 @ 
% 0.21/0.48           (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ k1_xboole_0 @ sk_B_1 @ 
% 0.21/0.48            sk_A) @ 
% 0.21/0.48           (u1_struct_0 @ sk_B_1))
% 0.21/0.48        | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.21/0.48  thf('25', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_A)
% 0.21/0.48        | (m1_subset_1 @ 
% 0.21/0.48           (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ k1_xboole_0 @ sk_B_1 @ 
% 0.21/0.48            sk_A) @ 
% 0.21/0.48           (u1_struct_0 @ sk_B_1)))),
% 0.21/0.48      inference('clc', [status(thm)], ['24', '25'])).
% 0.21/0.48  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      ((m1_subset_1 @ 
% 0.21/0.48        (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ k1_xboole_0 @ sk_B_1 @ sk_A) @ 
% 0.21/0.48        (u1_struct_0 @ sk_B_1))),
% 0.21/0.48      inference('clc', [status(thm)], ['26', '27'])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      (![X10 : $i, X11 : $i, X14 : $i, X15 : $i]:
% 0.21/0.48         ((v2_struct_0 @ X10)
% 0.21/0.48          | ~ (l1_waybel_0 @ X10 @ X11)
% 0.21/0.48          | ~ (r2_waybel_0 @ X11 @ X10 @ X14)
% 0.21/0.48          | (r2_hidden @ 
% 0.21/0.48             (k2_waybel_0 @ X11 @ X10 @ (sk_E @ X15 @ X14 @ X10 @ X11)) @ X14)
% 0.21/0.48          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X10))
% 0.21/0.48          | ~ (l1_struct_0 @ X11)
% 0.21/0.48          | (v2_struct_0 @ X11))),
% 0.21/0.48      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.21/0.48  thf('30', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((v2_struct_0 @ X0)
% 0.21/0.48          | ~ (l1_struct_0 @ X0)
% 0.21/0.48          | (r2_hidden @ 
% 0.21/0.48             (k2_waybel_0 @ X0 @ sk_B_1 @ 
% 0.21/0.48              (sk_E @ 
% 0.21/0.48               (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ k1_xboole_0 @ 
% 0.21/0.48                sk_B_1 @ sk_A) @ 
% 0.21/0.48               X1 @ sk_B_1 @ X0)) @ 
% 0.21/0.48             X1)
% 0.21/0.48          | ~ (r2_waybel_0 @ X0 @ sk_B_1 @ X1)
% 0.21/0.48          | ~ (l1_waybel_0 @ sk_B_1 @ X0)
% 0.21/0.48          | (v2_struct_0 @ sk_B_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.48  thf('31', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_B_1)
% 0.21/0.48        | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.21/0.48        | (r2_hidden @ 
% 0.21/0.48           (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.21/0.48            (sk_E @ 
% 0.21/0.48             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ k1_xboole_0 @ sk_B_1 @ 
% 0.21/0.48              sk_A) @ 
% 0.21/0.48             k1_xboole_0 @ sk_B_1 @ sk_A)) @ 
% 0.21/0.48           k1_xboole_0)
% 0.21/0.48        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.48        | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['16', '30'])).
% 0.21/0.48  thf('32', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('33', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('34', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_B_1)
% 0.21/0.48        | (r2_hidden @ 
% 0.21/0.48           (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.21/0.48            (sk_E @ 
% 0.21/0.48             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ k1_xboole_0 @ sk_B_1 @ 
% 0.21/0.48              sk_A) @ 
% 0.21/0.48             k1_xboole_0 @ sk_B_1 @ sk_A)) @ 
% 0.21/0.48           k1_xboole_0)
% 0.21/0.48        | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.21/0.48  thf('35', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('36', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_A)
% 0.21/0.48        | (r2_hidden @ 
% 0.21/0.48           (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.21/0.48            (sk_E @ 
% 0.21/0.48             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ k1_xboole_0 @ sk_B_1 @ 
% 0.21/0.48              sk_A) @ 
% 0.21/0.48             k1_xboole_0 @ sk_B_1 @ sk_A)) @ 
% 0.21/0.48           k1_xboole_0))),
% 0.21/0.48      inference('clc', [status(thm)], ['34', '35'])).
% 0.21/0.48  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('38', plain,
% 0.21/0.48      ((r2_hidden @ 
% 0.21/0.48        (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.21/0.48         (sk_E @ 
% 0.21/0.48          (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ k1_xboole_0 @ sk_B_1 @ sk_A) @ 
% 0.21/0.48          k1_xboole_0 @ sk_B_1 @ sk_A)) @ 
% 0.21/0.48        k1_xboole_0)),
% 0.21/0.48      inference('clc', [status(thm)], ['36', '37'])).
% 0.21/0.48  thf(t7_ordinal1, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.48  thf('39', plain,
% 0.21/0.48      (![X8 : $i, X9 : $i]: (~ (r2_hidden @ X8 @ X9) | ~ (r1_tarski @ X9 @ X8))),
% 0.21/0.48      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.48  thf('40', plain,
% 0.21/0.48      (~ (r1_tarski @ k1_xboole_0 @ 
% 0.21/0.48          (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.21/0.48           (sk_E @ 
% 0.21/0.48            (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ k1_xboole_0 @ sk_B_1 @ 
% 0.21/0.48             sk_A) @ 
% 0.21/0.48            k1_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.48  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.48  thf('41', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.48      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.48  thf('42', plain, ($false), inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
