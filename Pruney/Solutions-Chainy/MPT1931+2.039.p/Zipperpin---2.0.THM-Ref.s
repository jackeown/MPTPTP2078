%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Gu1fGeqbo1

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 108 expanded)
%              Number of leaves         :   33 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :  528 (1032 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(r2_waybel_0_type,type,(
    r2_waybel_0: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(o_2_2_yellow_6_type,type,(
    o_2_2_yellow_6: $i > $i > $i )).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('0',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('5',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
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
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('8',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( l1_waybel_0 @ X18 @ X19 )
      | ( r2_waybel_0 @ X19 @ X18 @ ( k6_subset_1 @ ( u1_struct_0 @ X19 ) @ X20 ) )
      | ( r1_waybel_0 @ X19 @ X18 @ X20 )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t9_waybel_0])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k6_subset_1 @ X8 @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('10',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( l1_waybel_0 @ X18 @ X19 )
      | ( r2_waybel_0 @ X19 @ X18 @ ( k4_xboole_0 @ ( u1_struct_0 @ X19 ) @ X20 ) )
      | ( r1_waybel_0 @ X19 @ X18 @ X20 )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( r2_waybel_0 @ sk_A @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( r2_waybel_0 @ sk_A @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r2_waybel_0 @ sk_A @ sk_B @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_0 @ sk_A @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['6','13'])).

thf('15',plain,(
    ~ ( r1_waybel_0 @ sk_A @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_0 @ sk_A @ sk_B @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( r2_waybel_0 @ sk_A @ sk_B @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r2_waybel_0 @ sk_A @ sk_B @ k1_xboole_0 ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
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

thf('22',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_struct_0 @ X22 )
      | ( v2_struct_0 @ X22 )
      | ( v2_struct_0 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ~ ( v7_waybel_0 @ X23 )
      | ~ ( l1_waybel_0 @ X23 @ X22 )
      | ( m1_subset_1 @ ( o_2_2_yellow_6 @ X22 @ X23 ) @ ( u1_struct_0 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_o_2_2_yellow_6])).

thf('23',plain,
    ( ( m1_subset_1 @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( m1_subset_1 @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['29','30'])).

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

thf('32',plain,(
    ! [X12: $i,X13: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( l1_waybel_0 @ X12 @ X13 )
      | ~ ( r2_waybel_0 @ X13 @ X12 @ X16 )
      | ( r2_hidden @ ( k2_waybel_0 @ X13 @ X12 @ ( sk_E @ X17 @ X16 @ X12 @ X13 ) ) @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( r2_hidden @ ( k2_waybel_0 @ X0 @ sk_B @ ( sk_E @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ X1 @ sk_B @ X0 ) ) @ X1 )
      | ~ ( r2_waybel_0 @ X0 @ sk_B @ X1 )
      | ~ ( l1_waybel_0 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B @ ( sk_E @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_B @ sk_A ) ) @ k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','33'])).

thf('35',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B @ ( sk_E @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_B @ sk_A ) ) @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B @ ( sk_E @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_B @ sk_A ) ) @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B @ ( sk_E @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_B @ sk_A ) ) @ k1_xboole_0 ),
    inference(clc,[status(thm)],['39','40'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('42',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('43',plain,(
    ~ ( r1_tarski @ k1_xboole_0 @ ( k2_waybel_0 @ sk_A @ sk_B @ ( sk_E @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('44',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['43','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Gu1fGeqbo1
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:32:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.57  % Solved by: fo/fo7.sh
% 0.21/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.57  % done 126 iterations in 0.110s
% 0.21/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.57  % SZS output start Refutation
% 0.21/0.57  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.57  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 0.21/0.57  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.21/0.57  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.21/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.57  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.21/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.57  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.57  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.21/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.57  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.21/0.57  thf(r2_waybel_0_type, type, r2_waybel_0: $i > $i > $i > $o).
% 0.21/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.57  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.21/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.57  thf(o_2_2_yellow_6_type, type, o_2_2_yellow_6: $i > $i > $i).
% 0.21/0.57  thf(t36_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.57  thf('0', plain,
% 0.21/0.57      (![X2 : $i, X3 : $i]: (r1_tarski @ (k4_xboole_0 @ X2 @ X3) @ X2)),
% 0.21/0.57      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.21/0.57  thf(t79_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.21/0.57  thf('1', plain,
% 0.21/0.57      (![X6 : $i, X7 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X7)),
% 0.21/0.57      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.21/0.57  thf(t69_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.57       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.21/0.57  thf('2', plain,
% 0.21/0.57      (![X4 : $i, X5 : $i]:
% 0.21/0.57         (~ (r1_xboole_0 @ X4 @ X5)
% 0.21/0.57          | ~ (r1_tarski @ X4 @ X5)
% 0.21/0.57          | (v1_xboole_0 @ X4))),
% 0.21/0.57      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.21/0.57  thf('3', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((v1_xboole_0 @ (k4_xboole_0 @ X1 @ X0))
% 0.21/0.57          | ~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.57  thf('4', plain, (![X0 : $i]: (v1_xboole_0 @ (k4_xboole_0 @ X0 @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['0', '3'])).
% 0.21/0.57  thf(l13_xboole_0, axiom,
% 0.21/0.57    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.57  thf('5', plain,
% 0.21/0.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.57  thf('6', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.57  thf(t29_yellow_6, conjecture,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.57             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.57           ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.57    (~( ![A:$i]:
% 0.21/0.57        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.57          ( ![B:$i]:
% 0.21/0.57            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.57                ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.57              ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ) )),
% 0.21/0.57    inference('cnf.neg', [status(esa)], [t29_yellow_6])).
% 0.21/0.57  thf('7', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(t9_waybel_0, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.57           ( ![C:$i]:
% 0.21/0.57             ( ( r1_waybel_0 @ A @ B @ C ) <=>
% 0.21/0.57               ( ~( r2_waybel_0 @
% 0.21/0.57                    A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ))).
% 0.21/0.57  thf('8', plain,
% 0.21/0.57      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.57         ((v2_struct_0 @ X18)
% 0.21/0.57          | ~ (l1_waybel_0 @ X18 @ X19)
% 0.21/0.57          | (r2_waybel_0 @ X19 @ X18 @ 
% 0.21/0.57             (k6_subset_1 @ (u1_struct_0 @ X19) @ X20))
% 0.21/0.57          | (r1_waybel_0 @ X19 @ X18 @ X20)
% 0.21/0.57          | ~ (l1_struct_0 @ X19)
% 0.21/0.57          | (v2_struct_0 @ X19))),
% 0.21/0.57      inference('cnf', [status(esa)], [t9_waybel_0])).
% 0.21/0.57  thf(redefinition_k6_subset_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.21/0.57  thf('9', plain,
% 0.21/0.57      (![X8 : $i, X9 : $i]: ((k6_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))),
% 0.21/0.57      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.57  thf('10', plain,
% 0.21/0.57      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.57         ((v2_struct_0 @ X18)
% 0.21/0.57          | ~ (l1_waybel_0 @ X18 @ X19)
% 0.21/0.57          | (r2_waybel_0 @ X19 @ X18 @ 
% 0.21/0.57             (k4_xboole_0 @ (u1_struct_0 @ X19) @ X20))
% 0.21/0.57          | (r1_waybel_0 @ X19 @ X18 @ X20)
% 0.21/0.57          | ~ (l1_struct_0 @ X19)
% 0.21/0.57          | (v2_struct_0 @ X19))),
% 0.21/0.57      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.57  thf('11', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v2_struct_0 @ sk_A)
% 0.21/0.57          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.57          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.21/0.57          | (r2_waybel_0 @ sk_A @ sk_B @ 
% 0.21/0.57             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))
% 0.21/0.57          | (v2_struct_0 @ sk_B))),
% 0.21/0.57      inference('sup-', [status(thm)], ['7', '10'])).
% 0.21/0.57  thf('12', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('13', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v2_struct_0 @ sk_A)
% 0.21/0.57          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.21/0.57          | (r2_waybel_0 @ sk_A @ sk_B @ 
% 0.21/0.57             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))
% 0.21/0.57          | (v2_struct_0 @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.57  thf('14', plain,
% 0.21/0.57      (((r2_waybel_0 @ sk_A @ sk_B @ k1_xboole_0)
% 0.21/0.57        | (v2_struct_0 @ sk_B)
% 0.21/0.57        | (r1_waybel_0 @ sk_A @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.57        | (v2_struct_0 @ sk_A))),
% 0.21/0.57      inference('sup+', [status(thm)], ['6', '13'])).
% 0.21/0.57  thf('15', plain, (~ (r1_waybel_0 @ sk_A @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('16', plain,
% 0.21/0.57      (((v2_struct_0 @ sk_A)
% 0.21/0.57        | (v2_struct_0 @ sk_B)
% 0.21/0.57        | (r2_waybel_0 @ sk_A @ sk_B @ k1_xboole_0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.57  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('18', plain,
% 0.21/0.57      (((r2_waybel_0 @ sk_A @ sk_B @ k1_xboole_0) | (v2_struct_0 @ sk_B))),
% 0.21/0.57      inference('clc', [status(thm)], ['16', '17'])).
% 0.21/0.57  thf('19', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('20', plain, ((r2_waybel_0 @ sk_A @ sk_B @ k1_xboole_0)),
% 0.21/0.57      inference('clc', [status(thm)], ['18', '19'])).
% 0.21/0.57  thf('21', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(dt_o_2_2_yellow_6, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.21/0.57         ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.57         ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.57       ( m1_subset_1 @ ( o_2_2_yellow_6 @ A @ B ) @ ( u1_struct_0 @ B ) ) ))).
% 0.21/0.57  thf('22', plain,
% 0.21/0.57      (![X22 : $i, X23 : $i]:
% 0.21/0.57         (~ (l1_struct_0 @ X22)
% 0.21/0.57          | (v2_struct_0 @ X22)
% 0.21/0.57          | (v2_struct_0 @ X23)
% 0.21/0.57          | ~ (v4_orders_2 @ X23)
% 0.21/0.57          | ~ (v7_waybel_0 @ X23)
% 0.21/0.57          | ~ (l1_waybel_0 @ X23 @ X22)
% 0.21/0.57          | (m1_subset_1 @ (o_2_2_yellow_6 @ X22 @ X23) @ (u1_struct_0 @ X23)))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_o_2_2_yellow_6])).
% 0.21/0.57  thf('23', plain,
% 0.21/0.57      (((m1_subset_1 @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.21/0.57        | ~ (v7_waybel_0 @ sk_B)
% 0.21/0.57        | ~ (v4_orders_2 @ sk_B)
% 0.21/0.57        | (v2_struct_0 @ sk_B)
% 0.21/0.57        | (v2_struct_0 @ sk_A)
% 0.21/0.57        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.57  thf('24', plain, ((v7_waybel_0 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('25', plain, ((v4_orders_2 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('26', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('27', plain,
% 0.21/0.57      (((m1_subset_1 @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.21/0.57        | (v2_struct_0 @ sk_B)
% 0.21/0.57        | (v2_struct_0 @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['23', '24', '25', '26'])).
% 0.21/0.57  thf('28', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('29', plain,
% 0.21/0.57      (((v2_struct_0 @ sk_A)
% 0.21/0.57        | (m1_subset_1 @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)))),
% 0.21/0.57      inference('clc', [status(thm)], ['27', '28'])).
% 0.21/0.57  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('31', plain,
% 0.21/0.57      ((m1_subset_1 @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))),
% 0.21/0.57      inference('clc', [status(thm)], ['29', '30'])).
% 0.21/0.57  thf(d12_waybel_0, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.57           ( ![C:$i]:
% 0.21/0.57             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.21/0.57               ( ![D:$i]:
% 0.21/0.57                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.57                   ( ?[E:$i]:
% 0.21/0.57                     ( ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) & 
% 0.21/0.57                       ( r1_orders_2 @ B @ D @ E ) & 
% 0.21/0.57                       ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.57  thf('32', plain,
% 0.21/0.57      (![X12 : $i, X13 : $i, X16 : $i, X17 : $i]:
% 0.21/0.57         ((v2_struct_0 @ X12)
% 0.21/0.57          | ~ (l1_waybel_0 @ X12 @ X13)
% 0.21/0.57          | ~ (r2_waybel_0 @ X13 @ X12 @ X16)
% 0.21/0.57          | (r2_hidden @ 
% 0.21/0.57             (k2_waybel_0 @ X13 @ X12 @ (sk_E @ X17 @ X16 @ X12 @ X13)) @ X16)
% 0.21/0.57          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X12))
% 0.21/0.57          | ~ (l1_struct_0 @ X13)
% 0.21/0.57          | (v2_struct_0 @ X13))),
% 0.21/0.57      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.21/0.57  thf('33', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((v2_struct_0 @ X0)
% 0.21/0.57          | ~ (l1_struct_0 @ X0)
% 0.21/0.57          | (r2_hidden @ 
% 0.21/0.57             (k2_waybel_0 @ X0 @ sk_B @ 
% 0.21/0.57              (sk_E @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ X1 @ sk_B @ X0)) @ 
% 0.21/0.57             X1)
% 0.21/0.57          | ~ (r2_waybel_0 @ X0 @ sk_B @ X1)
% 0.21/0.57          | ~ (l1_waybel_0 @ sk_B @ X0)
% 0.21/0.57          | (v2_struct_0 @ sk_B))),
% 0.21/0.57      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.57  thf('34', plain,
% 0.21/0.57      (((v2_struct_0 @ sk_B)
% 0.21/0.57        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.21/0.57        | (r2_hidden @ 
% 0.21/0.57           (k2_waybel_0 @ sk_A @ sk_B @ 
% 0.21/0.57            (sk_E @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ k1_xboole_0 @ sk_B @ sk_A)) @ 
% 0.21/0.57           k1_xboole_0)
% 0.21/0.57        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.57        | (v2_struct_0 @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['20', '33'])).
% 0.21/0.57  thf('35', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('36', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('37', plain,
% 0.21/0.57      (((v2_struct_0 @ sk_B)
% 0.21/0.57        | (r2_hidden @ 
% 0.21/0.57           (k2_waybel_0 @ sk_A @ sk_B @ 
% 0.21/0.57            (sk_E @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ k1_xboole_0 @ sk_B @ sk_A)) @ 
% 0.21/0.57           k1_xboole_0)
% 0.21/0.57        | (v2_struct_0 @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.21/0.57  thf('38', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('39', plain,
% 0.21/0.57      (((v2_struct_0 @ sk_A)
% 0.21/0.57        | (r2_hidden @ 
% 0.21/0.57           (k2_waybel_0 @ sk_A @ sk_B @ 
% 0.21/0.57            (sk_E @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ k1_xboole_0 @ sk_B @ sk_A)) @ 
% 0.21/0.57           k1_xboole_0))),
% 0.21/0.57      inference('clc', [status(thm)], ['37', '38'])).
% 0.21/0.57  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('41', plain,
% 0.21/0.57      ((r2_hidden @ 
% 0.21/0.57        (k2_waybel_0 @ sk_A @ sk_B @ 
% 0.21/0.57         (sk_E @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ k1_xboole_0 @ sk_B @ sk_A)) @ 
% 0.21/0.57        k1_xboole_0)),
% 0.21/0.57      inference('clc', [status(thm)], ['39', '40'])).
% 0.21/0.57  thf(t7_ordinal1, axiom,
% 0.21/0.57    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.57  thf('42', plain,
% 0.21/0.57      (![X10 : $i, X11 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X10 @ X11) | ~ (r1_tarski @ X11 @ X10))),
% 0.21/0.57      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.57  thf('43', plain,
% 0.21/0.57      (~ (r1_tarski @ k1_xboole_0 @ 
% 0.21/0.57          (k2_waybel_0 @ sk_A @ sk_B @ 
% 0.21/0.57           (sk_E @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ k1_xboole_0 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.57  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.57  thf('44', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.21/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.57  thf('45', plain, ($false), inference('demod', [status(thm)], ['43', '44'])).
% 0.21/0.57  
% 0.21/0.57  % SZS output end Refutation
% 0.21/0.57  
% 0.42/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
