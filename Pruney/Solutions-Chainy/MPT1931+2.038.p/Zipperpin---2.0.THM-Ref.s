%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mwJbMJvPKK

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:01 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 111 expanded)
%              Number of leaves         :   34 (  48 expanded)
%              Depth                    :   14
%              Number of atoms          :  541 (1045 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(o_2_2_yellow_6_type,type,(
    o_2_2_yellow_6: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(r2_waybel_0_type,type,(
    r2_waybel_0: $i > $i > $i > $o )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('0',plain,(
    ! [X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X2 ) @ X1 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( v1_xboole_0 @ X3 ) ) ),
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

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('5',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_xboole_0 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ( X7 = X8 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

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

thf('9',plain,(
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

thf('10',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( l1_waybel_0 @ X19 @ X20 )
      | ( r2_waybel_0 @ X20 @ X19 @ ( k6_subset_1 @ ( u1_struct_0 @ X20 ) @ X21 ) )
      | ( r1_waybel_0 @ X20 @ X19 @ X21 )
      | ~ ( l1_struct_0 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t9_waybel_0])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ X9 @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('12',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( l1_waybel_0 @ X19 @ X20 )
      | ( r2_waybel_0 @ X20 @ X19 @ ( k4_xboole_0 @ ( u1_struct_0 @ X20 ) @ X21 ) )
      | ( r1_waybel_0 @ X20 @ X19 @ X21 )
      | ~ ( l1_struct_0 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( r2_waybel_0 @ sk_A @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( r2_waybel_0 @ sk_A @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r2_waybel_0 @ sk_A @ sk_B @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_0 @ sk_A @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['8','15'])).

thf('17',plain,(
    ~ ( r1_waybel_0 @ sk_A @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_0 @ sk_A @ sk_B @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( r2_waybel_0 @ sk_A @ sk_B @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    r2_waybel_0 @ sk_A @ sk_B @ k1_xboole_0 ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
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

thf('24',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ~ ( v7_waybel_0 @ X24 )
      | ~ ( l1_waybel_0 @ X24 @ X23 )
      | ( m1_subset_1 @ ( o_2_2_yellow_6 @ X23 @ X24 ) @ ( u1_struct_0 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_o_2_2_yellow_6])).

thf('25',plain,
    ( ( m1_subset_1 @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( m1_subset_1 @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['31','32'])).

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

thf('34',plain,(
    ! [X13: $i,X14: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( l1_waybel_0 @ X13 @ X14 )
      | ~ ( r2_waybel_0 @ X14 @ X13 @ X17 )
      | ( r2_hidden @ ( k2_waybel_0 @ X14 @ X13 @ ( sk_E @ X18 @ X17 @ X13 @ X14 ) ) @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( r2_hidden @ ( k2_waybel_0 @ X0 @ sk_B @ ( sk_E @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ X1 @ sk_B @ X0 ) ) @ X1 )
      | ~ ( r2_waybel_0 @ X0 @ sk_B @ X1 )
      | ~ ( l1_waybel_0 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B @ ( sk_E @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_B @ sk_A ) ) @ k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','35'])).

thf('37',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B @ ( sk_E @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_B @ sk_A ) ) @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B @ ( sk_E @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_B @ sk_A ) ) @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B @ ( sk_E @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_B @ sk_A ) ) @ k1_xboole_0 ),
    inference(clc,[status(thm)],['41','42'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('44',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('45',plain,(
    ~ ( r1_tarski @ k1_xboole_0 @ ( k2_waybel_0 @ sk_A @ sk_B @ ( sk_E @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['45','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mwJbMJvPKK
% 0.12/0.32  % Computer   : n021.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 13:58:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.18/0.33  % Number of cores: 8
% 0.18/0.33  % Python version: Python 3.6.8
% 0.18/0.33  % Running in FO mode
% 0.43/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.62  % Solved by: fo/fo7.sh
% 0.43/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.62  % done 323 iterations in 0.186s
% 0.43/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.62  % SZS output start Refutation
% 0.43/0.62  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.43/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.62  thf(o_2_2_yellow_6_type, type, o_2_2_yellow_6: $i > $i > $i).
% 0.43/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.43/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.43/0.62  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.43/0.62  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.43/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.43/0.62  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.43/0.62  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.43/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.43/0.62  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.43/0.62  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.43/0.62  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.43/0.62  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.43/0.62  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.43/0.62  thf(r2_waybel_0_type, type, r2_waybel_0: $i > $i > $i > $o).
% 0.43/0.62  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 0.43/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.43/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.62  thf(t36_xboole_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.43/0.62  thf('0', plain,
% 0.43/0.62      (![X1 : $i, X2 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X2) @ X1)),
% 0.43/0.62      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.43/0.62  thf(t79_xboole_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.43/0.62  thf('1', plain,
% 0.43/0.62      (![X5 : $i, X6 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X6)),
% 0.43/0.62      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.43/0.62  thf(t69_xboole_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.43/0.62       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.43/0.62  thf('2', plain,
% 0.43/0.62      (![X3 : $i, X4 : $i]:
% 0.43/0.62         (~ (r1_xboole_0 @ X3 @ X4)
% 0.43/0.62          | ~ (r1_tarski @ X3 @ X4)
% 0.43/0.62          | (v1_xboole_0 @ X3))),
% 0.43/0.62      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.43/0.62  thf('3', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((v1_xboole_0 @ (k4_xboole_0 @ X1 @ X0))
% 0.43/0.62          | ~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.43/0.62  thf('4', plain, (![X0 : $i]: (v1_xboole_0 @ (k4_xboole_0 @ X0 @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['0', '3'])).
% 0.43/0.62  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.43/0.62  thf('5', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.43/0.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.43/0.62  thf(t8_boole, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.43/0.62  thf('6', plain,
% 0.43/0.62      (![X7 : $i, X8 : $i]:
% 0.43/0.62         (~ (v1_xboole_0 @ X7) | ~ (v1_xboole_0 @ X8) | ((X7) = (X8)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t8_boole])).
% 0.43/0.62  thf('7', plain,
% 0.43/0.62      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['5', '6'])).
% 0.43/0.62  thf('8', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['4', '7'])).
% 0.43/0.62  thf(t29_yellow_6, conjecture,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.43/0.62       ( ![B:$i]:
% 0.43/0.62         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.43/0.62             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.43/0.62           ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.43/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.62    (~( ![A:$i]:
% 0.43/0.62        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.43/0.62          ( ![B:$i]:
% 0.43/0.62            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.43/0.62                ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.43/0.62              ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ) )),
% 0.43/0.62    inference('cnf.neg', [status(esa)], [t29_yellow_6])).
% 0.43/0.62  thf('9', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(t9_waybel_0, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.43/0.62       ( ![B:$i]:
% 0.43/0.62         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.43/0.62           ( ![C:$i]:
% 0.43/0.62             ( ( r1_waybel_0 @ A @ B @ C ) <=>
% 0.43/0.62               ( ~( r2_waybel_0 @
% 0.43/0.62                    A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ))).
% 0.43/0.62  thf('10', plain,
% 0.43/0.62      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.43/0.62         ((v2_struct_0 @ X19)
% 0.43/0.62          | ~ (l1_waybel_0 @ X19 @ X20)
% 0.43/0.62          | (r2_waybel_0 @ X20 @ X19 @ 
% 0.43/0.62             (k6_subset_1 @ (u1_struct_0 @ X20) @ X21))
% 0.43/0.62          | (r1_waybel_0 @ X20 @ X19 @ X21)
% 0.43/0.62          | ~ (l1_struct_0 @ X20)
% 0.43/0.62          | (v2_struct_0 @ X20))),
% 0.43/0.62      inference('cnf', [status(esa)], [t9_waybel_0])).
% 0.43/0.62  thf(redefinition_k6_subset_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.43/0.62  thf('11', plain,
% 0.43/0.62      (![X9 : $i, X10 : $i]:
% 0.43/0.62         ((k6_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))),
% 0.43/0.62      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.43/0.62  thf('12', plain,
% 0.43/0.62      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.43/0.62         ((v2_struct_0 @ X19)
% 0.43/0.62          | ~ (l1_waybel_0 @ X19 @ X20)
% 0.43/0.62          | (r2_waybel_0 @ X20 @ X19 @ 
% 0.43/0.62             (k4_xboole_0 @ (u1_struct_0 @ X20) @ X21))
% 0.43/0.62          | (r1_waybel_0 @ X20 @ X19 @ X21)
% 0.43/0.62          | ~ (l1_struct_0 @ X20)
% 0.43/0.62          | (v2_struct_0 @ X20))),
% 0.43/0.62      inference('demod', [status(thm)], ['10', '11'])).
% 0.43/0.62  thf('13', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((v2_struct_0 @ sk_A)
% 0.43/0.62          | ~ (l1_struct_0 @ sk_A)
% 0.43/0.62          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.43/0.62          | (r2_waybel_0 @ sk_A @ sk_B @ 
% 0.43/0.62             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))
% 0.43/0.62          | (v2_struct_0 @ sk_B))),
% 0.43/0.62      inference('sup-', [status(thm)], ['9', '12'])).
% 0.43/0.62  thf('14', plain, ((l1_struct_0 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('15', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((v2_struct_0 @ sk_A)
% 0.43/0.62          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.43/0.62          | (r2_waybel_0 @ sk_A @ sk_B @ 
% 0.43/0.62             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))
% 0.43/0.62          | (v2_struct_0 @ sk_B))),
% 0.43/0.62      inference('demod', [status(thm)], ['13', '14'])).
% 0.43/0.62  thf('16', plain,
% 0.43/0.62      (((r2_waybel_0 @ sk_A @ sk_B @ k1_xboole_0)
% 0.43/0.62        | (v2_struct_0 @ sk_B)
% 0.43/0.62        | (r1_waybel_0 @ sk_A @ sk_B @ (u1_struct_0 @ sk_A))
% 0.43/0.62        | (v2_struct_0 @ sk_A))),
% 0.43/0.62      inference('sup+', [status(thm)], ['8', '15'])).
% 0.43/0.62  thf('17', plain, (~ (r1_waybel_0 @ sk_A @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('18', plain,
% 0.43/0.62      (((v2_struct_0 @ sk_A)
% 0.43/0.62        | (v2_struct_0 @ sk_B)
% 0.43/0.62        | (r2_waybel_0 @ sk_A @ sk_B @ k1_xboole_0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['16', '17'])).
% 0.43/0.62  thf('19', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('20', plain,
% 0.43/0.62      (((r2_waybel_0 @ sk_A @ sk_B @ k1_xboole_0) | (v2_struct_0 @ sk_B))),
% 0.43/0.62      inference('clc', [status(thm)], ['18', '19'])).
% 0.43/0.62  thf('21', plain, (~ (v2_struct_0 @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('22', plain, ((r2_waybel_0 @ sk_A @ sk_B @ k1_xboole_0)),
% 0.43/0.62      inference('clc', [status(thm)], ['20', '21'])).
% 0.43/0.62  thf('23', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(dt_o_2_2_yellow_6, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.43/0.62         ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.43/0.62         ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.43/0.62       ( m1_subset_1 @ ( o_2_2_yellow_6 @ A @ B ) @ ( u1_struct_0 @ B ) ) ))).
% 0.43/0.62  thf('24', plain,
% 0.43/0.62      (![X23 : $i, X24 : $i]:
% 0.43/0.62         (~ (l1_struct_0 @ X23)
% 0.43/0.62          | (v2_struct_0 @ X23)
% 0.43/0.62          | (v2_struct_0 @ X24)
% 0.43/0.62          | ~ (v4_orders_2 @ X24)
% 0.43/0.62          | ~ (v7_waybel_0 @ X24)
% 0.43/0.62          | ~ (l1_waybel_0 @ X24 @ X23)
% 0.43/0.62          | (m1_subset_1 @ (o_2_2_yellow_6 @ X23 @ X24) @ (u1_struct_0 @ X24)))),
% 0.43/0.62      inference('cnf', [status(esa)], [dt_o_2_2_yellow_6])).
% 0.43/0.62  thf('25', plain,
% 0.43/0.62      (((m1_subset_1 @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.43/0.62        | ~ (v7_waybel_0 @ sk_B)
% 0.43/0.62        | ~ (v4_orders_2 @ sk_B)
% 0.43/0.62        | (v2_struct_0 @ sk_B)
% 0.43/0.62        | (v2_struct_0 @ sk_A)
% 0.43/0.62        | ~ (l1_struct_0 @ sk_A))),
% 0.43/0.62      inference('sup-', [status(thm)], ['23', '24'])).
% 0.43/0.62  thf('26', plain, ((v7_waybel_0 @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('27', plain, ((v4_orders_2 @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('28', plain, ((l1_struct_0 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('29', plain,
% 0.43/0.62      (((m1_subset_1 @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.43/0.62        | (v2_struct_0 @ sk_B)
% 0.43/0.62        | (v2_struct_0 @ sk_A))),
% 0.43/0.62      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 0.43/0.62  thf('30', plain, (~ (v2_struct_0 @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('31', plain,
% 0.43/0.62      (((v2_struct_0 @ sk_A)
% 0.43/0.62        | (m1_subset_1 @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)))),
% 0.43/0.62      inference('clc', [status(thm)], ['29', '30'])).
% 0.43/0.62  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('33', plain,
% 0.43/0.62      ((m1_subset_1 @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))),
% 0.43/0.62      inference('clc', [status(thm)], ['31', '32'])).
% 0.43/0.62  thf(d12_waybel_0, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.43/0.62       ( ![B:$i]:
% 0.43/0.62         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.43/0.62           ( ![C:$i]:
% 0.43/0.62             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.43/0.62               ( ![D:$i]:
% 0.43/0.62                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.43/0.62                   ( ?[E:$i]:
% 0.43/0.62                     ( ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) & 
% 0.43/0.62                       ( r1_orders_2 @ B @ D @ E ) & 
% 0.43/0.62                       ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.43/0.62  thf('34', plain,
% 0.43/0.62      (![X13 : $i, X14 : $i, X17 : $i, X18 : $i]:
% 0.43/0.62         ((v2_struct_0 @ X13)
% 0.43/0.62          | ~ (l1_waybel_0 @ X13 @ X14)
% 0.43/0.62          | ~ (r2_waybel_0 @ X14 @ X13 @ X17)
% 0.43/0.62          | (r2_hidden @ 
% 0.43/0.62             (k2_waybel_0 @ X14 @ X13 @ (sk_E @ X18 @ X17 @ X13 @ X14)) @ X17)
% 0.43/0.62          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X13))
% 0.43/0.62          | ~ (l1_struct_0 @ X14)
% 0.43/0.62          | (v2_struct_0 @ X14))),
% 0.43/0.62      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.43/0.62  thf('35', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((v2_struct_0 @ X0)
% 0.43/0.62          | ~ (l1_struct_0 @ X0)
% 0.43/0.62          | (r2_hidden @ 
% 0.43/0.62             (k2_waybel_0 @ X0 @ sk_B @ 
% 0.43/0.62              (sk_E @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ X1 @ sk_B @ X0)) @ 
% 0.43/0.62             X1)
% 0.43/0.62          | ~ (r2_waybel_0 @ X0 @ sk_B @ X1)
% 0.43/0.62          | ~ (l1_waybel_0 @ sk_B @ X0)
% 0.43/0.62          | (v2_struct_0 @ sk_B))),
% 0.43/0.62      inference('sup-', [status(thm)], ['33', '34'])).
% 0.43/0.62  thf('36', plain,
% 0.43/0.62      (((v2_struct_0 @ sk_B)
% 0.43/0.62        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.43/0.62        | (r2_hidden @ 
% 0.43/0.62           (k2_waybel_0 @ sk_A @ sk_B @ 
% 0.43/0.62            (sk_E @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ k1_xboole_0 @ sk_B @ sk_A)) @ 
% 0.43/0.62           k1_xboole_0)
% 0.43/0.62        | ~ (l1_struct_0 @ sk_A)
% 0.43/0.62        | (v2_struct_0 @ sk_A))),
% 0.43/0.62      inference('sup-', [status(thm)], ['22', '35'])).
% 0.43/0.62  thf('37', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('38', plain, ((l1_struct_0 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('39', plain,
% 0.43/0.62      (((v2_struct_0 @ sk_B)
% 0.43/0.62        | (r2_hidden @ 
% 0.43/0.62           (k2_waybel_0 @ sk_A @ sk_B @ 
% 0.43/0.62            (sk_E @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ k1_xboole_0 @ sk_B @ sk_A)) @ 
% 0.43/0.62           k1_xboole_0)
% 0.43/0.62        | (v2_struct_0 @ sk_A))),
% 0.43/0.62      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.43/0.62  thf('40', plain, (~ (v2_struct_0 @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('41', plain,
% 0.43/0.62      (((v2_struct_0 @ sk_A)
% 0.43/0.62        | (r2_hidden @ 
% 0.43/0.62           (k2_waybel_0 @ sk_A @ sk_B @ 
% 0.43/0.62            (sk_E @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ k1_xboole_0 @ sk_B @ sk_A)) @ 
% 0.43/0.62           k1_xboole_0))),
% 0.43/0.62      inference('clc', [status(thm)], ['39', '40'])).
% 0.43/0.62  thf('42', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('43', plain,
% 0.43/0.62      ((r2_hidden @ 
% 0.43/0.62        (k2_waybel_0 @ sk_A @ sk_B @ 
% 0.43/0.62         (sk_E @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ k1_xboole_0 @ sk_B @ sk_A)) @ 
% 0.43/0.62        k1_xboole_0)),
% 0.43/0.62      inference('clc', [status(thm)], ['41', '42'])).
% 0.43/0.62  thf(t7_ordinal1, axiom,
% 0.43/0.62    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.43/0.62  thf('44', plain,
% 0.43/0.62      (![X11 : $i, X12 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X11 @ X12) | ~ (r1_tarski @ X12 @ X11))),
% 0.43/0.62      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.43/0.62  thf('45', plain,
% 0.43/0.62      (~ (r1_tarski @ k1_xboole_0 @ 
% 0.43/0.62          (k2_waybel_0 @ sk_A @ sk_B @ 
% 0.43/0.62           (sk_E @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ k1_xboole_0 @ sk_B @ sk_A)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['43', '44'])).
% 0.43/0.62  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.43/0.62  thf('46', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.43/0.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.43/0.62  thf('47', plain, ($false), inference('demod', [status(thm)], ['45', '46'])).
% 0.43/0.62  
% 0.43/0.62  % SZS output end Refutation
% 0.43/0.62  
% 0.49/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
