%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.88ftDatTlj

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 176 expanded)
%              Number of leaves         :   25 (  65 expanded)
%              Depth                    :   13
%              Number of atoms          :  578 (2794 expanded)
%              Number of equality atoms :    7 (  85 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_yellow_6_type,type,(
    k4_yellow_6: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(k11_yellow_6_type,type,(
    k11_yellow_6: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_yellow_6_type,type,(
    v1_yellow_6: $i > $i > $o )).

thf(v3_yellow_6_type,type,(
    v3_yellow_6: $i > $i > $o )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t45_yellow_6,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v8_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( v1_yellow_6 @ B @ A )
            & ( l1_waybel_0 @ B @ A ) )
         => ( ( k11_yellow_6 @ A @ B )
            = ( k4_yellow_6 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v8_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v4_orders_2 @ B )
              & ( v7_waybel_0 @ B )
              & ( v1_yellow_6 @ B @ A )
              & ( l1_waybel_0 @ B @ A ) )
           => ( ( k11_yellow_6 @ A @ B )
              = ( k4_yellow_6 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t45_yellow_6])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_yellow_6 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t42_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( v1_yellow_6 @ B @ A )
            & ( l1_waybel_0 @ B @ A ) )
         => ( r2_hidden @ ( k4_yellow_6 @ A @ B ) @ ( k10_yellow_6 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v7_waybel_0 @ X12 )
      | ~ ( v1_yellow_6 @ X12 @ X13 )
      | ~ ( l1_waybel_0 @ X12 @ X13 )
      | ( r2_hidden @ ( k4_yellow_6 @ X13 @ X12 ) @ ( k10_yellow_6 @ X13 @ X12 ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_6])).

thf('3',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6','7','8'])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['11','12'])).

thf(d20_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v8_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( v3_yellow_6 @ B @ A )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( C
                  = ( k11_yellow_6 @ A @ B ) )
              <=> ( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( v4_orders_2 @ X7 )
      | ~ ( v7_waybel_0 @ X7 )
      | ~ ( v3_yellow_6 @ X7 @ X8 )
      | ~ ( l1_waybel_0 @ X7 @ X8 )
      | ~ ( r2_hidden @ X9 @ ( k10_yellow_6 @ X8 @ X7 ) )
      | ( X9
        = ( k11_yellow_6 @ X8 @ X7 ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v8_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d20_yellow_6])).

thf('15',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_subset_1 @ ( k4_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k4_yellow_6 @ sk_A @ sk_B )
      = ( k11_yellow_6 @ sk_A @ sk_B ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v3_yellow_6 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('20',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k10_yellow_6,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( v4_orders_2 @ B )
        & ( v7_waybel_0 @ B )
        & ( l1_waybel_0 @ B @ A ) )
     => ( m1_subset_1 @ ( k10_yellow_6 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('21',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v7_waybel_0 @ X11 )
      | ~ ( l1_waybel_0 @ X11 @ X10 )
      | ( m1_subset_1 @ ( k10_yellow_6 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_yellow_6])).

thf('22',plain,
    ( ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23','24','25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','33'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('35',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('36',plain,(
    m1_subset_1 @ ( k4_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ( ( ~ ( v2_struct_0 @ B )
              & ( v4_orders_2 @ B )
              & ( v7_waybel_0 @ B )
              & ( v1_yellow_6 @ B @ A ) )
           => ( ~ ( v2_struct_0 @ B )
              & ( v4_orders_2 @ B )
              & ( v7_waybel_0 @ B )
              & ( v3_yellow_6 @ B @ A ) ) ) ) ) )).

thf('39',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_waybel_0 @ X5 @ X6 )
      | ( v3_yellow_6 @ X5 @ X6 )
      | ~ ( v1_yellow_6 @ X5 @ X6 )
      | ~ ( v7_waybel_0 @ X5 )
      | ~ ( v4_orders_2 @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc4_yellow_6])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v1_yellow_6 @ sk_B @ sk_A )
    | ( v3_yellow_6 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_yellow_6 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v3_yellow_6 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['40','41','42','43','44','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v3_yellow_6 @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v3_yellow_6 @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_yellow_6 @ sk_A @ sk_B )
      = ( k11_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['15','16','17','18','36','37','50','51','52'])).

thf('54',plain,(
    ( k11_yellow_6 @ sk_A @ sk_B )
 != ( k4_yellow_6 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v2_struct_0 @ sk_B ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['0','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.88ftDatTlj
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:58:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.45  % Solved by: fo/fo7.sh
% 0.21/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.45  % done 26 iterations in 0.015s
% 0.21/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.45  % SZS output start Refutation
% 0.21/0.45  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.45  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.45  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.21/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.45  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.45  thf(k4_yellow_6_type, type, k4_yellow_6: $i > $i > $i).
% 0.21/0.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.45  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.21/0.45  thf(k11_yellow_6_type, type, k11_yellow_6: $i > $i > $i).
% 0.21/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.45  thf(v1_yellow_6_type, type, v1_yellow_6: $i > $i > $o).
% 0.21/0.45  thf(v3_yellow_6_type, type, v3_yellow_6: $i > $i > $o).
% 0.21/0.45  thf(k10_yellow_6_type, type, k10_yellow_6: $i > $i > $i).
% 0.21/0.45  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.45  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.45  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.21/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.45  thf(t45_yellow_6, conjecture,
% 0.21/0.45    (![A:$i]:
% 0.21/0.45     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.45         ( v8_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.45       ( ![B:$i]:
% 0.21/0.45         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.45             ( v7_waybel_0 @ B ) & ( v1_yellow_6 @ B @ A ) & 
% 0.21/0.45             ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.45           ( ( k11_yellow_6 @ A @ B ) = ( k4_yellow_6 @ A @ B ) ) ) ) ))).
% 0.21/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.45    (~( ![A:$i]:
% 0.21/0.45        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.45            ( v8_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.45          ( ![B:$i]:
% 0.21/0.45            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.45                ( v7_waybel_0 @ B ) & ( v1_yellow_6 @ B @ A ) & 
% 0.21/0.45                ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.45              ( ( k11_yellow_6 @ A @ B ) = ( k4_yellow_6 @ A @ B ) ) ) ) ) )),
% 0.21/0.45    inference('cnf.neg', [status(esa)], [t45_yellow_6])).
% 0.21/0.45  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('1', plain, ((v1_yellow_6 @ sk_B @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf(t42_yellow_6, axiom,
% 0.21/0.45    (![A:$i]:
% 0.21/0.45     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.45       ( ![B:$i]:
% 0.21/0.45         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.45             ( v7_waybel_0 @ B ) & ( v1_yellow_6 @ B @ A ) & 
% 0.21/0.45             ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.45           ( r2_hidden @ ( k4_yellow_6 @ A @ B ) @ ( k10_yellow_6 @ A @ B ) ) ) ) ))).
% 0.21/0.45  thf('2', plain,
% 0.21/0.45      (![X12 : $i, X13 : $i]:
% 0.21/0.45         ((v2_struct_0 @ X12)
% 0.21/0.45          | ~ (v4_orders_2 @ X12)
% 0.21/0.45          | ~ (v7_waybel_0 @ X12)
% 0.21/0.45          | ~ (v1_yellow_6 @ X12 @ X13)
% 0.21/0.45          | ~ (l1_waybel_0 @ X12 @ X13)
% 0.21/0.45          | (r2_hidden @ (k4_yellow_6 @ X13 @ X12) @ (k10_yellow_6 @ X13 @ X12))
% 0.21/0.45          | ~ (l1_pre_topc @ X13)
% 0.21/0.45          | ~ (v2_pre_topc @ X13)
% 0.21/0.45          | (v2_struct_0 @ X13))),
% 0.21/0.45      inference('cnf', [status(esa)], [t42_yellow_6])).
% 0.21/0.45  thf('3', plain,
% 0.21/0.45      (((v2_struct_0 @ sk_A)
% 0.21/0.45        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.45        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.45        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B) @ 
% 0.21/0.45           (k10_yellow_6 @ sk_A @ sk_B))
% 0.21/0.45        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.21/0.45        | ~ (v7_waybel_0 @ sk_B)
% 0.21/0.45        | ~ (v4_orders_2 @ sk_B)
% 0.21/0.45        | (v2_struct_0 @ sk_B))),
% 0.21/0.45      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.45  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('6', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('7', plain, ((v7_waybel_0 @ sk_B)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('8', plain, ((v4_orders_2 @ sk_B)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('9', plain,
% 0.21/0.45      (((v2_struct_0 @ sk_A)
% 0.21/0.45        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B) @ 
% 0.21/0.45           (k10_yellow_6 @ sk_A @ sk_B))
% 0.21/0.45        | (v2_struct_0 @ sk_B))),
% 0.21/0.45      inference('demod', [status(thm)], ['3', '4', '5', '6', '7', '8'])).
% 0.21/0.45  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('11', plain,
% 0.21/0.45      (((v2_struct_0 @ sk_B)
% 0.21/0.45        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B) @ 
% 0.21/0.45           (k10_yellow_6 @ sk_A @ sk_B)))),
% 0.21/0.45      inference('clc', [status(thm)], ['9', '10'])).
% 0.21/0.45  thf('12', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('13', plain,
% 0.21/0.45      ((r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B) @ (k10_yellow_6 @ sk_A @ sk_B))),
% 0.21/0.45      inference('clc', [status(thm)], ['11', '12'])).
% 0.21/0.45  thf(d20_yellow_6, axiom,
% 0.21/0.45    (![A:$i]:
% 0.21/0.45     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.45         ( v8_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.45       ( ![B:$i]:
% 0.21/0.45         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.45             ( v7_waybel_0 @ B ) & ( v3_yellow_6 @ B @ A ) & 
% 0.21/0.45             ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.45           ( ![C:$i]:
% 0.21/0.45             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.45               ( ( ( C ) = ( k11_yellow_6 @ A @ B ) ) <=>
% 0.21/0.45                 ( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) ) ) ) ) ) ) ))).
% 0.21/0.45  thf('14', plain,
% 0.21/0.45      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.45         ((v2_struct_0 @ X7)
% 0.21/0.45          | ~ (v4_orders_2 @ X7)
% 0.21/0.45          | ~ (v7_waybel_0 @ X7)
% 0.21/0.45          | ~ (v3_yellow_6 @ X7 @ X8)
% 0.21/0.45          | ~ (l1_waybel_0 @ X7 @ X8)
% 0.21/0.45          | ~ (r2_hidden @ X9 @ (k10_yellow_6 @ X8 @ X7))
% 0.21/0.45          | ((X9) = (k11_yellow_6 @ X8 @ X7))
% 0.21/0.45          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.21/0.45          | ~ (l1_pre_topc @ X8)
% 0.21/0.45          | ~ (v8_pre_topc @ X8)
% 0.21/0.45          | ~ (v2_pre_topc @ X8)
% 0.21/0.45          | (v2_struct_0 @ X8))),
% 0.21/0.45      inference('cnf', [status(esa)], [d20_yellow_6])).
% 0.21/0.45  thf('15', plain,
% 0.21/0.45      (((v2_struct_0 @ sk_A)
% 0.21/0.45        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.45        | ~ (v8_pre_topc @ sk_A)
% 0.21/0.45        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.45        | ~ (m1_subset_1 @ (k4_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.45        | ((k4_yellow_6 @ sk_A @ sk_B) = (k11_yellow_6 @ sk_A @ sk_B))
% 0.21/0.45        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.21/0.45        | ~ (v3_yellow_6 @ sk_B @ sk_A)
% 0.21/0.45        | ~ (v7_waybel_0 @ sk_B)
% 0.21/0.45        | ~ (v4_orders_2 @ sk_B)
% 0.21/0.45        | (v2_struct_0 @ sk_B))),
% 0.21/0.45      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.45  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('17', plain, ((v8_pre_topc @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('19', plain,
% 0.21/0.45      ((r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B) @ (k10_yellow_6 @ sk_A @ sk_B))),
% 0.21/0.45      inference('clc', [status(thm)], ['11', '12'])).
% 0.21/0.45  thf('20', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf(dt_k10_yellow_6, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.45         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 0.21/0.45         ( v4_orders_2 @ B ) & ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.45       ( m1_subset_1 @
% 0.21/0.45         ( k10_yellow_6 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.45  thf('21', plain,
% 0.21/0.45      (![X10 : $i, X11 : $i]:
% 0.21/0.45         (~ (l1_pre_topc @ X10)
% 0.21/0.45          | ~ (v2_pre_topc @ X10)
% 0.21/0.45          | (v2_struct_0 @ X10)
% 0.21/0.45          | (v2_struct_0 @ X11)
% 0.21/0.45          | ~ (v4_orders_2 @ X11)
% 0.21/0.45          | ~ (v7_waybel_0 @ X11)
% 0.21/0.45          | ~ (l1_waybel_0 @ X11 @ X10)
% 0.21/0.45          | (m1_subset_1 @ (k10_yellow_6 @ X10 @ X11) @ 
% 0.21/0.45             (k1_zfmisc_1 @ (u1_struct_0 @ X10))))),
% 0.21/0.45      inference('cnf', [status(esa)], [dt_k10_yellow_6])).
% 0.21/0.45  thf('22', plain,
% 0.21/0.45      (((m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_B) @ 
% 0.21/0.45         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.45        | ~ (v7_waybel_0 @ sk_B)
% 0.21/0.45        | ~ (v4_orders_2 @ sk_B)
% 0.21/0.45        | (v2_struct_0 @ sk_B)
% 0.21/0.45        | (v2_struct_0 @ sk_A)
% 0.21/0.45        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.45        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.45      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.45  thf('23', plain, ((v7_waybel_0 @ sk_B)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('24', plain, ((v4_orders_2 @ sk_B)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('27', plain,
% 0.21/0.45      (((m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_B) @ 
% 0.21/0.45         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.45        | (v2_struct_0 @ sk_B)
% 0.21/0.45        | (v2_struct_0 @ sk_A))),
% 0.21/0.45      inference('demod', [status(thm)], ['22', '23', '24', '25', '26'])).
% 0.21/0.45  thf('28', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('29', plain,
% 0.21/0.45      (((v2_struct_0 @ sk_A)
% 0.21/0.45        | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_B) @ 
% 0.21/0.45           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.45      inference('clc', [status(thm)], ['27', '28'])).
% 0.21/0.45  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('31', plain,
% 0.21/0.45      ((m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_B) @ 
% 0.21/0.45        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.45      inference('clc', [status(thm)], ['29', '30'])).
% 0.21/0.45  thf(l3_subset_1, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.45       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.21/0.45  thf('32', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.45         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.45          | (r2_hidden @ X0 @ X2)
% 0.21/0.45          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.21/0.45      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.21/0.45  thf('33', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.45          | ~ (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ sk_B)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.45  thf('34', plain,
% 0.21/0.45      ((r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.45      inference('sup-', [status(thm)], ['19', '33'])).
% 0.21/0.45  thf(t1_subset, axiom,
% 0.21/0.45    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.21/0.45  thf('35', plain,
% 0.21/0.45      (![X3 : $i, X4 : $i]: ((m1_subset_1 @ X3 @ X4) | ~ (r2_hidden @ X3 @ X4))),
% 0.21/0.45      inference('cnf', [status(esa)], [t1_subset])).
% 0.21/0.45  thf('36', plain,
% 0.21/0.45      ((m1_subset_1 @ (k4_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.45      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.45  thf('37', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('38', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf(cc4_yellow_6, axiom,
% 0.21/0.45    (![A:$i]:
% 0.21/0.45     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.45       ( ![B:$i]:
% 0.21/0.45         ( ( l1_waybel_0 @ B @ A ) =>
% 0.21/0.45           ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.45               ( v7_waybel_0 @ B ) & ( v1_yellow_6 @ B @ A ) ) =>
% 0.21/0.45             ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.45               ( v7_waybel_0 @ B ) & ( v3_yellow_6 @ B @ A ) ) ) ) ) ))).
% 0.21/0.45  thf('39', plain,
% 0.21/0.45      (![X5 : $i, X6 : $i]:
% 0.21/0.45         (~ (l1_waybel_0 @ X5 @ X6)
% 0.21/0.45          | (v3_yellow_6 @ X5 @ X6)
% 0.21/0.45          | ~ (v1_yellow_6 @ X5 @ X6)
% 0.21/0.45          | ~ (v7_waybel_0 @ X5)
% 0.21/0.45          | ~ (v4_orders_2 @ X5)
% 0.21/0.45          | (v2_struct_0 @ X5)
% 0.21/0.45          | ~ (l1_pre_topc @ X6)
% 0.21/0.45          | ~ (v2_pre_topc @ X6)
% 0.21/0.45          | (v2_struct_0 @ X6))),
% 0.21/0.45      inference('cnf', [status(esa)], [cc4_yellow_6])).
% 0.21/0.45  thf('40', plain,
% 0.21/0.45      (((v2_struct_0 @ sk_A)
% 0.21/0.45        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.45        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.45        | (v2_struct_0 @ sk_B)
% 0.21/0.45        | ~ (v4_orders_2 @ sk_B)
% 0.21/0.45        | ~ (v7_waybel_0 @ sk_B)
% 0.21/0.45        | ~ (v1_yellow_6 @ sk_B @ sk_A)
% 0.21/0.45        | (v3_yellow_6 @ sk_B @ sk_A))),
% 0.21/0.45      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.45  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('43', plain, ((v4_orders_2 @ sk_B)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('44', plain, ((v7_waybel_0 @ sk_B)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('45', plain, ((v1_yellow_6 @ sk_B @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('46', plain,
% 0.21/0.45      (((v2_struct_0 @ sk_A)
% 0.21/0.45        | (v2_struct_0 @ sk_B)
% 0.21/0.45        | (v3_yellow_6 @ sk_B @ sk_A))),
% 0.21/0.45      inference('demod', [status(thm)], ['40', '41', '42', '43', '44', '45'])).
% 0.21/0.45  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('48', plain, (((v3_yellow_6 @ sk_B @ sk_A) | (v2_struct_0 @ sk_B))),
% 0.21/0.45      inference('clc', [status(thm)], ['46', '47'])).
% 0.21/0.45  thf('49', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('50', plain, ((v3_yellow_6 @ sk_B @ sk_A)),
% 0.21/0.45      inference('clc', [status(thm)], ['48', '49'])).
% 0.21/0.45  thf('51', plain, ((v7_waybel_0 @ sk_B)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('52', plain, ((v4_orders_2 @ sk_B)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('53', plain,
% 0.21/0.45      (((v2_struct_0 @ sk_A)
% 0.21/0.45        | ((k4_yellow_6 @ sk_A @ sk_B) = (k11_yellow_6 @ sk_A @ sk_B))
% 0.21/0.45        | (v2_struct_0 @ sk_B))),
% 0.21/0.45      inference('demod', [status(thm)],
% 0.21/0.45                ['15', '16', '17', '18', '36', '37', '50', '51', '52'])).
% 0.21/0.45  thf('54', plain,
% 0.21/0.45      (((k11_yellow_6 @ sk_A @ sk_B) != (k4_yellow_6 @ sk_A @ sk_B))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('55', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B))),
% 0.21/0.45      inference('simplify_reflect-', [status(thm)], ['53', '54'])).
% 0.21/0.45  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('57', plain, ((v2_struct_0 @ sk_B)),
% 0.21/0.45      inference('clc', [status(thm)], ['55', '56'])).
% 0.21/0.45  thf('58', plain, ($false), inference('demod', [status(thm)], ['0', '57'])).
% 0.21/0.45  
% 0.21/0.45  % SZS output end Refutation
% 0.21/0.45  
% 0.21/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
