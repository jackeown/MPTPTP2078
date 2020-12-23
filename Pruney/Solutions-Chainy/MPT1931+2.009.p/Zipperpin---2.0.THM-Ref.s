%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AwzijEiYP2

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 125 expanded)
%              Number of leaves         :   22 (  46 expanded)
%              Depth                    :   24
%              Number of atoms          :  613 (1521 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(o_2_2_yellow_6_type,type,(
    o_2_2_yellow_6: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

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

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
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

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ( v2_struct_0 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v7_waybel_0 @ X13 )
      | ~ ( l1_waybel_0 @ X13 @ X12 )
      | ( m1_subset_1 @ ( o_2_2_yellow_6 @ X12 @ X13 ) @ ( u1_struct_0 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_o_2_2_yellow_6])).

thf('5',plain,
    ( ( m1_subset_1 @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( m1_subset_1 @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['5','6','7','8'])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['11','12'])).

thf(d11_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( r1_waybel_0 @ A @ B @ C )
            <=> ? [D: $i] :
                  ( ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                     => ( ( r1_orders_2 @ B @ D @ E )
                       => ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) ) )
                  & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( l1_waybel_0 @ X3 @ X4 )
      | ( m1_subset_1 @ ( sk_E @ X5 @ X6 @ X3 @ X4 ) @ ( u1_struct_0 @ X3 ) )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X3 ) )
      | ( r1_waybel_0 @ X4 @ X3 @ X6 )
      | ~ ( l1_struct_0 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d11_waybel_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( r1_waybel_0 @ X0 @ sk_B @ X1 )
      | ( m1_subset_1 @ ( sk_E @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ X1 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_waybel_0 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','15'])).

thf('17',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(dt_k2_waybel_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ~ ( v2_struct_0 @ B )
        & ( l1_waybel_0 @ B @ A )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) )
     => ( m1_subset_1 @ ( k2_waybel_0 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ) )).

thf('19',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( l1_waybel_0 @ X9 @ X10 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l1_struct_0 @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X9 ) )
      | ( m1_subset_1 @ ( k2_waybel_0 @ X10 @ X9 @ X11 ) @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_waybel_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( k2_waybel_0 @ X1 @ sk_B @ ( sk_E @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ X0 @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ X1 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_waybel_0 @ sk_B @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( m1_subset_1 @ ( k2_waybel_0 @ X1 @ sk_B @ ( sk_E @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ X0 @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ X1 ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( k2_waybel_0 @ sk_A @ sk_B @ ( sk_E @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ X0 @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','21'])).

thf('23',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( k2_waybel_0 @ sk_A @ sk_B @ ( sk_E @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ X0 @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_waybel_0 @ sk_A @ sk_B @ ( sk_E @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ X0 @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B @ ( sk_E @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ X0 @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( l1_waybel_0 @ X3 @ X4 )
      | ~ ( r2_hidden @ ( k2_waybel_0 @ X4 @ X3 @ ( sk_E @ X5 @ X6 @ X3 @ X4 ) ) @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X3 ) )
      | ( r1_waybel_0 @ X4 @ X3 @ X6 )
      | ~ ( l1_struct_0 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d11_waybel_0])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_0 @ sk_A @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('32',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_0 @ sk_A @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ~ ( r1_waybel_0 @ sk_A @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['38','39'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('41',plain,(
    ! [X2: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['0','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AwzijEiYP2
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:25:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.36  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 33 iterations in 0.024s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.48  thf(o_2_2_yellow_6_type, type, o_2_2_yellow_6: $i > $i > $i).
% 0.20/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.48  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.20/0.48  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.20/0.48  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.20/0.48  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.48  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.20/0.48  thf(t29_yellow_6, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.20/0.48             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.48           ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.48          ( ![B:$i]:
% 0.20/0.48            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.20/0.48                ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.48              ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t29_yellow_6])).
% 0.20/0.48  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('2', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('3', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(dt_o_2_2_yellow_6, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.20/0.48         ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.20/0.48         ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.48       ( m1_subset_1 @ ( o_2_2_yellow_6 @ A @ B ) @ ( u1_struct_0 @ B ) ) ))).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X12 : $i, X13 : $i]:
% 0.20/0.48         (~ (l1_struct_0 @ X12)
% 0.20/0.48          | (v2_struct_0 @ X12)
% 0.20/0.48          | (v2_struct_0 @ X13)
% 0.20/0.48          | ~ (v4_orders_2 @ X13)
% 0.20/0.48          | ~ (v7_waybel_0 @ X13)
% 0.20/0.48          | ~ (l1_waybel_0 @ X13 @ X12)
% 0.20/0.48          | (m1_subset_1 @ (o_2_2_yellow_6 @ X12 @ X13) @ (u1_struct_0 @ X13)))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_o_2_2_yellow_6])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (((m1_subset_1 @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.20/0.48        | ~ (v7_waybel_0 @ sk_B)
% 0.20/0.48        | ~ (v4_orders_2 @ sk_B)
% 0.20/0.48        | (v2_struct_0 @ sk_B)
% 0.20/0.48        | (v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.48  thf('6', plain, ((v7_waybel_0 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('7', plain, ((v4_orders_2 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('8', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (((m1_subset_1 @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.20/0.48        | (v2_struct_0 @ sk_B)
% 0.20/0.48        | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['5', '6', '7', '8'])).
% 0.20/0.48  thf('10', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | (m1_subset_1 @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)))),
% 0.20/0.48      inference('clc', [status(thm)], ['9', '10'])).
% 0.20/0.48  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      ((m1_subset_1 @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))),
% 0.20/0.48      inference('clc', [status(thm)], ['11', '12'])).
% 0.20/0.48  thf(d11_waybel_0, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( r1_waybel_0 @ A @ B @ C ) <=>
% 0.20/0.48               ( ?[D:$i]:
% 0.20/0.48                 ( ( ![E:$i]:
% 0.20/0.48                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.48                       ( ( r1_orders_2 @ B @ D @ E ) =>
% 0.20/0.48                         ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) ) ) ) & 
% 0.20/0.48                   ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X3)
% 0.20/0.48          | ~ (l1_waybel_0 @ X3 @ X4)
% 0.20/0.48          | (m1_subset_1 @ (sk_E @ X5 @ X6 @ X3 @ X4) @ (u1_struct_0 @ X3))
% 0.20/0.48          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X3))
% 0.20/0.48          | (r1_waybel_0 @ X4 @ X3 @ X6)
% 0.20/0.48          | ~ (l1_struct_0 @ X4)
% 0.20/0.48          | (v2_struct_0 @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [d11_waybel_0])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X0)
% 0.20/0.48          | ~ (l1_struct_0 @ X0)
% 0.20/0.48          | (r1_waybel_0 @ X0 @ sk_B @ X1)
% 0.20/0.48          | (m1_subset_1 @ 
% 0.20/0.48             (sk_E @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ X1 @ sk_B @ X0) @ 
% 0.20/0.48             (u1_struct_0 @ sk_B))
% 0.20/0.48          | ~ (l1_waybel_0 @ sk_B @ X0)
% 0.20/0.48          | (v2_struct_0 @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_B)
% 0.20/0.48          | (m1_subset_1 @ 
% 0.20/0.48             (sk_E @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ X0 @ sk_B @ sk_A) @ 
% 0.20/0.48             (u1_struct_0 @ sk_B))
% 0.20/0.48          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.20/0.48          | ~ (l1_struct_0 @ sk_A)
% 0.20/0.48          | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '15'])).
% 0.20/0.48  thf('17', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_B)
% 0.20/0.48          | (m1_subset_1 @ 
% 0.20/0.48             (sk_E @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ X0 @ sk_B @ sk_A) @ 
% 0.20/0.48             (u1_struct_0 @ sk_B))
% 0.20/0.48          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.20/0.48          | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.48  thf(dt_k2_waybel_0, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.20/0.48         ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) & 
% 0.20/0.48         ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.48       ( m1_subset_1 @ ( k2_waybel_0 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ))).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.48         (~ (l1_waybel_0 @ X9 @ X10)
% 0.20/0.48          | (v2_struct_0 @ X9)
% 0.20/0.48          | ~ (l1_struct_0 @ X10)
% 0.20/0.48          | (v2_struct_0 @ X10)
% 0.20/0.48          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X9))
% 0.20/0.48          | (m1_subset_1 @ (k2_waybel_0 @ X10 @ X9 @ X11) @ (u1_struct_0 @ X10)))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k2_waybel_0])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_A)
% 0.20/0.48          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.20/0.48          | (v2_struct_0 @ sk_B)
% 0.20/0.48          | (m1_subset_1 @ 
% 0.20/0.48             (k2_waybel_0 @ X1 @ sk_B @ 
% 0.20/0.48              (sk_E @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ X0 @ sk_B @ sk_A)) @ 
% 0.20/0.48             (u1_struct_0 @ X1))
% 0.20/0.48          | (v2_struct_0 @ X1)
% 0.20/0.48          | ~ (l1_struct_0 @ X1)
% 0.20/0.48          | (v2_struct_0 @ sk_B)
% 0.20/0.48          | ~ (l1_waybel_0 @ sk_B @ X1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (l1_waybel_0 @ sk_B @ X1)
% 0.20/0.48          | ~ (l1_struct_0 @ X1)
% 0.20/0.48          | (v2_struct_0 @ X1)
% 0.20/0.48          | (m1_subset_1 @ 
% 0.20/0.48             (k2_waybel_0 @ X1 @ sk_B @ 
% 0.20/0.48              (sk_E @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ X0 @ sk_B @ sk_A)) @ 
% 0.20/0.48             (u1_struct_0 @ X1))
% 0.20/0.48          | (v2_struct_0 @ sk_B)
% 0.20/0.48          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.20/0.48          | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_A)
% 0.20/0.48          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.20/0.48          | (v2_struct_0 @ sk_B)
% 0.20/0.48          | (m1_subset_1 @ 
% 0.20/0.48             (k2_waybel_0 @ sk_A @ sk_B @ 
% 0.20/0.48              (sk_E @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ X0 @ sk_B @ sk_A)) @ 
% 0.20/0.48             (u1_struct_0 @ sk_A))
% 0.20/0.48          | (v2_struct_0 @ sk_A)
% 0.20/0.48          | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '21'])).
% 0.20/0.48  thf('23', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_A)
% 0.20/0.48          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.20/0.48          | (v2_struct_0 @ sk_B)
% 0.20/0.48          | (m1_subset_1 @ 
% 0.20/0.48             (k2_waybel_0 @ sk_A @ sk_B @ 
% 0.20/0.48              (sk_E @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ X0 @ sk_B @ sk_A)) @ 
% 0.20/0.48             (u1_struct_0 @ sk_A))
% 0.20/0.48          | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((m1_subset_1 @ 
% 0.20/0.48           (k2_waybel_0 @ sk_A @ sk_B @ 
% 0.20/0.48            (sk_E @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ X0 @ sk_B @ sk_A)) @ 
% 0.20/0.48           (u1_struct_0 @ sk_A))
% 0.20/0.48          | (v2_struct_0 @ sk_B)
% 0.20/0.48          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.20/0.48          | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.48  thf(t2_subset, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.48       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((r2_hidden @ X0 @ X1)
% 0.20/0.48          | (v1_xboole_0 @ X1)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_A)
% 0.20/0.48          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.20/0.48          | (v2_struct_0 @ sk_B)
% 0.20/0.48          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.48          | (r2_hidden @ 
% 0.20/0.48             (k2_waybel_0 @ sk_A @ sk_B @ 
% 0.20/0.48              (sk_E @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ X0 @ sk_B @ sk_A)) @ 
% 0.20/0.48             (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X3)
% 0.20/0.48          | ~ (l1_waybel_0 @ X3 @ X4)
% 0.20/0.48          | ~ (r2_hidden @ 
% 0.20/0.48               (k2_waybel_0 @ X4 @ X3 @ (sk_E @ X5 @ X6 @ X3 @ X4)) @ X6)
% 0.20/0.48          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X3))
% 0.20/0.48          | (r1_waybel_0 @ X4 @ X3 @ X6)
% 0.20/0.48          | ~ (l1_struct_0 @ X4)
% 0.20/0.48          | (v2_struct_0 @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [d11_waybel_0])).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.48        | (v2_struct_0 @ sk_B)
% 0.20/0.48        | (r1_waybel_0 @ sk_A @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.48        | (v2_struct_0 @ sk_A)
% 0.20/0.48        | (v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (l1_struct_0 @ sk_A)
% 0.20/0.48        | (r1_waybel_0 @ sk_A @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.48        | ~ (m1_subset_1 @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ 
% 0.20/0.48             (u1_struct_0 @ sk_B))
% 0.20/0.48        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.20/0.48        | (v2_struct_0 @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.48  thf('30', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      ((m1_subset_1 @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))),
% 0.20/0.48      inference('clc', [status(thm)], ['11', '12'])).
% 0.20/0.48  thf('32', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.48        | (v2_struct_0 @ sk_B)
% 0.20/0.48        | (r1_waybel_0 @ sk_A @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.48        | (v2_struct_0 @ sk_A)
% 0.20/0.48        | (v2_struct_0 @ sk_A)
% 0.20/0.48        | (r1_waybel_0 @ sk_A @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.48        | (v2_struct_0 @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.20/0.48  thf('34', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | (r1_waybel_0 @ sk_A @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.48        | (v2_struct_0 @ sk_B)
% 0.20/0.48        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['33'])).
% 0.20/0.48  thf('35', plain, (~ (r1_waybel_0 @ sk_A @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.48        | (v2_struct_0 @ sk_B)
% 0.20/0.48        | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.48  thf('37', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('clc', [status(thm)], ['36', '37'])).
% 0.20/0.48  thf('39', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('40', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('clc', [status(thm)], ['38', '39'])).
% 0.20/0.48  thf(fc2_struct_0, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.48       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.48  thf('41', plain,
% 0.20/0.48      (![X2 : $i]:
% 0.20/0.48         (~ (v1_xboole_0 @ (u1_struct_0 @ X2))
% 0.20/0.48          | ~ (l1_struct_0 @ X2)
% 0.20/0.48          | (v2_struct_0 @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.48  thf('42', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.48  thf('43', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('44', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['42', '43'])).
% 0.20/0.48  thf('45', plain, ($false), inference('demod', [status(thm)], ['0', '44'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
