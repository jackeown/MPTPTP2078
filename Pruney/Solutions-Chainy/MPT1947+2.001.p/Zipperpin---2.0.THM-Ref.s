%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.flFkHYQfsr

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 694 expanded)
%              Number of leaves         :   33 ( 220 expanded)
%              Depth                    :   25
%              Number of atoms          : 1123 (10883 expanded)
%              Number of equality atoms :   25 ( 342 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_yellow_6_type,type,(
    v3_yellow_6: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_yellow_6_type,type,(
    v1_yellow_6: $i > $i > $o )).

thf(k4_yellow_6_type,type,(
    k4_yellow_6: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k11_yellow_6_type,type,(
    k11_yellow_6: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

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
    l1_waybel_0 @ sk_B_1 @ sk_A ),
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

thf('1',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_waybel_0 @ X16 @ X17 )
      | ( v3_yellow_6 @ X16 @ X17 )
      | ~ ( v1_yellow_6 @ X16 @ X17 )
      | ~ ( v7_waybel_0 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc4_yellow_6])).

thf('2',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( v4_orders_2 @ sk_B_1 )
    | ~ ( v7_waybel_0 @ sk_B_1 )
    | ~ ( v1_yellow_6 @ sk_B_1 @ sk_A )
    | ( v3_yellow_6 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v4_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v7_waybel_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_yellow_6 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v3_yellow_6 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','4','5','6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v3_yellow_6 @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v3_yellow_6 @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['10','11'])).

thf(dt_k11_yellow_6,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v8_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( v4_orders_2 @ B )
        & ( v7_waybel_0 @ B )
        & ( v3_yellow_6 @ B @ A )
        & ( l1_waybel_0 @ B @ A ) )
     => ( m1_subset_1 @ ( k11_yellow_6 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('13',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( v8_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ( v2_struct_0 @ X22 )
      | ~ ( v4_orders_2 @ X22 )
      | ~ ( v7_waybel_0 @ X22 )
      | ~ ( v3_yellow_6 @ X22 @ X21 )
      | ~ ( l1_waybel_0 @ X22 @ X21 )
      | ( m1_subset_1 @ ( k11_yellow_6 @ X21 @ X22 ) @ ( u1_struct_0 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k11_yellow_6])).

thf('14',plain,
    ( ( m1_subset_1 @ ( k11_yellow_6 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B_1 )
    | ~ ( v4_orders_2 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v7_waybel_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v4_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( m1_subset_1 @ ( k11_yellow_6 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','15','16','17','18','19','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k11_yellow_6 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ ( k11_yellow_6 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

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

thf('26',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v7_waybel_0 @ X18 )
      | ~ ( v3_yellow_6 @ X18 @ X19 )
      | ~ ( l1_waybel_0 @ X18 @ X19 )
      | ( X20
       != ( k11_yellow_6 @ X19 @ X18 ) )
      | ( r2_hidden @ X20 @ ( k10_yellow_6 @ X19 @ X18 ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v8_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d20_yellow_6])).

thf('27',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ~ ( v8_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ ( k11_yellow_6 @ X19 @ X18 ) @ ( u1_struct_0 @ X19 ) )
      | ( r2_hidden @ ( k11_yellow_6 @ X19 @ X18 ) @ ( k10_yellow_6 @ X19 @ X18 ) )
      | ~ ( l1_waybel_0 @ X18 @ X19 )
      | ~ ( v3_yellow_6 @ X18 @ X19 )
      | ~ ( v7_waybel_0 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ~ ( v4_orders_2 @ sk_B_1 )
    | ~ ( v7_waybel_0 @ sk_B_1 )
    | ~ ( v3_yellow_6 @ sk_B_1 @ sk_A )
    | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
    | ( r2_hidden @ ( k11_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    v4_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v7_waybel_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v3_yellow_6 @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['10','11'])).

thf('32',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( k11_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29','30','31','32','33','34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k11_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    r2_hidden @ ( k11_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['38','39'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('41',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X11 ) @ X13 )
      | ~ ( r2_hidden @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('42',plain,(
    r1_tarski @ ( k1_tarski @ ( k11_yellow_6 @ sk_A @ sk_B_1 ) ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('43',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ~ ( v1_zfmisc_1 @ X14 )
      | ( X15 = X14 )
      | ~ ( r1_tarski @ X15 @ X14 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ ( k11_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( ( k1_tarski @ ( k11_yellow_6 @ sk_A @ sk_B_1 ) )
      = ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_zfmisc_1 @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc22_yellow_6,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v8_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( v4_orders_2 @ B )
        & ( v7_waybel_0 @ B )
        & ( l1_waybel_0 @ B @ A ) )
     => ( v1_zfmisc_1 @ ( k10_yellow_6 @ A @ B ) ) ) )).

thf('46',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( v8_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ~ ( v7_waybel_0 @ X24 )
      | ~ ( l1_waybel_0 @ X24 @ X23 )
      | ( v1_zfmisc_1 @ ( k10_yellow_6 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[fc22_yellow_6])).

thf('47',plain,
    ( ( v1_zfmisc_1 @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ~ ( v7_waybel_0 @ sk_B_1 )
    | ~ ( v4_orders_2 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v7_waybel_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v4_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v1_zfmisc_1 @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['47','48','49','50','51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_zfmisc_1 @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_zfmisc_1 @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ ( k11_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( ( k1_tarski @ ( k11_yellow_6 @ sk_A @ sk_B_1 ) )
      = ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['44','57'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('59',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('60',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_tarski @ ( k1_tarski @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('64',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( ( k1_tarski @ ( k11_yellow_6 @ sk_A @ sk_B_1 ) )
      = ( k10_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['58','64'])).

thf('66',plain,(
    v1_yellow_6 @ sk_B_1 @ sk_A ),
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

thf('67',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v4_orders_2 @ X25 )
      | ~ ( v7_waybel_0 @ X25 )
      | ~ ( v1_yellow_6 @ X25 @ X26 )
      | ~ ( l1_waybel_0 @ X25 @ X26 )
      | ( r2_hidden @ ( k4_yellow_6 @ X26 @ X25 ) @ ( k10_yellow_6 @ X26 @ X25 ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_6])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B_1 )
    | ~ ( v4_orders_2 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v7_waybel_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v4_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['68','69','70','71','72','73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('80',plain,(
    ~ ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k1_tarski @ ( k11_yellow_6 @ sk_A @ sk_B_1 ) )
    = ( k10_yellow_6 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['65','80'])).

thf('82',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['59'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('83',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X8 )
      | ( X8
       != ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('84',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','84'])).

thf('86',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X11 ) @ X13 )
      | ~ ( r2_hidden @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    r1_tarski @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k11_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['81','87'])).

thf('89',plain,(
    r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('90',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X11 ) @ X13 )
      | ~ ( r2_hidden @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('91',plain,(
    r1_tarski @ ( k1_tarski @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ~ ( v1_zfmisc_1 @ X14 )
      | ( X15 = X14 )
      | ~ ( r1_tarski @ X15 @ X14 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('93',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( ( k1_tarski @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) )
      = ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_zfmisc_1 @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v1_zfmisc_1 @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('95',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( ( k1_tarski @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) )
      = ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('97',plain,
    ( ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( ( k1_tarski @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) )
      = ( k10_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('99',plain,
    ( ( k1_tarski @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) )
    = ( k10_yellow_6 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_tarski @ ( k1_tarski @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) @ X0 )
      | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k11_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['88','101'])).

thf('103',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ( r1_tarski @ X9 @ X7 )
      | ( X8
       != ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('104',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r1_tarski @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    r1_tarski @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k11_yellow_6 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['102','104'])).

thf('106',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('107',plain,
    ( ~ ( r1_tarski @ ( k11_yellow_6 @ sk_A @ sk_B_1 ) @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( ( k11_yellow_6 @ sk_A @ sk_B_1 )
      = ( k4_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ( k11_yellow_6 @ sk_A @ sk_B_1 )
 != ( k4_yellow_6 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ~ ( r1_tarski @ ( k11_yellow_6 @ sk_A @ sk_B_1 ) @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( k1_tarski @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) )
    = ( k10_yellow_6 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('111',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('112',plain,(
    r1_tarski @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( k1_tarski @ ( k11_yellow_6 @ sk_A @ sk_B_1 ) )
    = ( k10_yellow_6 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['65','80'])).

thf('114',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_tarski @ ( k1_tarski @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) @ X0 )
      | ( r2_hidden @ ( k11_yellow_6 @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    r2_hidden @ ( k11_yellow_6 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['112','115'])).

thf('117',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r1_tarski @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('118',plain,(
    r1_tarski @ ( k11_yellow_6 @ sk_A @ sk_B_1 ) @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    $false ),
    inference(demod,[status(thm)],['109','118'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.flFkHYQfsr
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:37:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 159 iterations in 0.079s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.54  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.21/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.54  thf(v3_yellow_6_type, type, v3_yellow_6: $i > $i > $o).
% 0.21/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.54  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.21/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.54  thf(v1_yellow_6_type, type, v1_yellow_6: $i > $i > $o).
% 0.21/0.54  thf(k4_yellow_6_type, type, k4_yellow_6: $i > $i > $i).
% 0.21/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(k10_yellow_6_type, type, k10_yellow_6: $i > $i > $i).
% 0.21/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.54  thf(k11_yellow_6_type, type, k11_yellow_6: $i > $i > $i).
% 0.21/0.54  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.54  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.21/0.54  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.21/0.54  thf(t45_yellow_6, conjecture,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.54         ( v8_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.54             ( v7_waybel_0 @ B ) & ( v1_yellow_6 @ B @ A ) & 
% 0.21/0.54             ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.54           ( ( k11_yellow_6 @ A @ B ) = ( k4_yellow_6 @ A @ B ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i]:
% 0.21/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.54            ( v8_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54          ( ![B:$i]:
% 0.21/0.54            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.54                ( v7_waybel_0 @ B ) & ( v1_yellow_6 @ B @ A ) & 
% 0.21/0.54                ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.54              ( ( k11_yellow_6 @ A @ B ) = ( k4_yellow_6 @ A @ B ) ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t45_yellow_6])).
% 0.21/0.54  thf('0', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(cc4_yellow_6, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( l1_waybel_0 @ B @ A ) =>
% 0.21/0.54           ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.54               ( v7_waybel_0 @ B ) & ( v1_yellow_6 @ B @ A ) ) =>
% 0.21/0.54             ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.54               ( v7_waybel_0 @ B ) & ( v3_yellow_6 @ B @ A ) ) ) ) ) ))).
% 0.21/0.54  thf('1', plain,
% 0.21/0.54      (![X16 : $i, X17 : $i]:
% 0.21/0.54         (~ (l1_waybel_0 @ X16 @ X17)
% 0.21/0.54          | (v3_yellow_6 @ X16 @ X17)
% 0.21/0.54          | ~ (v1_yellow_6 @ X16 @ X17)
% 0.21/0.54          | ~ (v7_waybel_0 @ X16)
% 0.21/0.54          | ~ (v4_orders_2 @ X16)
% 0.21/0.54          | (v2_struct_0 @ X16)
% 0.21/0.54          | ~ (l1_pre_topc @ X17)
% 0.21/0.54          | ~ (v2_pre_topc @ X17)
% 0.21/0.54          | (v2_struct_0 @ X17))),
% 0.21/0.54      inference('cnf', [status(esa)], [cc4_yellow_6])).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_A)
% 0.21/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54        | (v2_struct_0 @ sk_B_1)
% 0.21/0.54        | ~ (v4_orders_2 @ sk_B_1)
% 0.21/0.54        | ~ (v7_waybel_0 @ sk_B_1)
% 0.21/0.54        | ~ (v1_yellow_6 @ sk_B_1 @ sk_A)
% 0.21/0.54        | (v3_yellow_6 @ sk_B_1 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.54  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('5', plain, ((v4_orders_2 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('6', plain, ((v7_waybel_0 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('7', plain, ((v1_yellow_6 @ sk_B_1 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_A)
% 0.21/0.54        | (v2_struct_0 @ sk_B_1)
% 0.21/0.54        | (v3_yellow_6 @ sk_B_1 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['2', '3', '4', '5', '6', '7'])).
% 0.21/0.54  thf('9', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('10', plain, (((v3_yellow_6 @ sk_B_1 @ sk_A) | (v2_struct_0 @ sk_B_1))),
% 0.21/0.54      inference('clc', [status(thm)], ['8', '9'])).
% 0.21/0.54  thf('11', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('12', plain, ((v3_yellow_6 @ sk_B_1 @ sk_A)),
% 0.21/0.54      inference('clc', [status(thm)], ['10', '11'])).
% 0.21/0.54  thf(dt_k11_yellow_6, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.54         ( v8_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.21/0.54         ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.54         ( v7_waybel_0 @ B ) & ( v3_yellow_6 @ B @ A ) & 
% 0.21/0.54         ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.54       ( m1_subset_1 @ ( k11_yellow_6 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.21/0.54  thf('13', plain,
% 0.21/0.54      (![X21 : $i, X22 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X21)
% 0.21/0.54          | ~ (v8_pre_topc @ X21)
% 0.21/0.54          | ~ (v2_pre_topc @ X21)
% 0.21/0.54          | (v2_struct_0 @ X21)
% 0.21/0.54          | (v2_struct_0 @ X22)
% 0.21/0.54          | ~ (v4_orders_2 @ X22)
% 0.21/0.54          | ~ (v7_waybel_0 @ X22)
% 0.21/0.54          | ~ (v3_yellow_6 @ X22 @ X21)
% 0.21/0.54          | ~ (l1_waybel_0 @ X22 @ X21)
% 0.21/0.54          | (m1_subset_1 @ (k11_yellow_6 @ X21 @ X22) @ (u1_struct_0 @ X21)))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k11_yellow_6])).
% 0.21/0.54  thf('14', plain,
% 0.21/0.54      (((m1_subset_1 @ (k11_yellow_6 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.21/0.54        | ~ (v7_waybel_0 @ sk_B_1)
% 0.21/0.54        | ~ (v4_orders_2 @ sk_B_1)
% 0.21/0.54        | (v2_struct_0 @ sk_B_1)
% 0.21/0.54        | (v2_struct_0 @ sk_A)
% 0.21/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.54        | ~ (v8_pre_topc @ sk_A)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.54  thf('15', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('16', plain, ((v7_waybel_0 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('17', plain, ((v4_orders_2 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('18', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('19', plain, ((v8_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('21', plain,
% 0.21/0.54      (((m1_subset_1 @ (k11_yellow_6 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | (v2_struct_0 @ sk_B_1)
% 0.21/0.54        | (v2_struct_0 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)],
% 0.21/0.54                ['14', '15', '16', '17', '18', '19', '20'])).
% 0.21/0.54  thf('22', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('23', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_A)
% 0.21/0.54        | (m1_subset_1 @ (k11_yellow_6 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('clc', [status(thm)], ['21', '22'])).
% 0.21/0.54  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      ((m1_subset_1 @ (k11_yellow_6 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('clc', [status(thm)], ['23', '24'])).
% 0.21/0.54  thf(d20_yellow_6, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.54         ( v8_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.54             ( v7_waybel_0 @ B ) & ( v3_yellow_6 @ B @ A ) & 
% 0.21/0.54             ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.54           ( ![C:$i]:
% 0.21/0.54             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.54               ( ( ( C ) = ( k11_yellow_6 @ A @ B ) ) <=>
% 0.21/0.54                 ( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.54         ((v2_struct_0 @ X18)
% 0.21/0.54          | ~ (v4_orders_2 @ X18)
% 0.21/0.54          | ~ (v7_waybel_0 @ X18)
% 0.21/0.54          | ~ (v3_yellow_6 @ X18 @ X19)
% 0.21/0.54          | ~ (l1_waybel_0 @ X18 @ X19)
% 0.21/0.54          | ((X20) != (k11_yellow_6 @ X19 @ X18))
% 0.21/0.54          | (r2_hidden @ X20 @ (k10_yellow_6 @ X19 @ X18))
% 0.21/0.54          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 0.21/0.54          | ~ (l1_pre_topc @ X19)
% 0.21/0.54          | ~ (v8_pre_topc @ X19)
% 0.21/0.54          | ~ (v2_pre_topc @ X19)
% 0.21/0.54          | (v2_struct_0 @ X19))),
% 0.21/0.54      inference('cnf', [status(esa)], [d20_yellow_6])).
% 0.21/0.54  thf('27', plain,
% 0.21/0.54      (![X18 : $i, X19 : $i]:
% 0.21/0.54         ((v2_struct_0 @ X19)
% 0.21/0.54          | ~ (v2_pre_topc @ X19)
% 0.21/0.54          | ~ (v8_pre_topc @ X19)
% 0.21/0.54          | ~ (l1_pre_topc @ X19)
% 0.21/0.54          | ~ (m1_subset_1 @ (k11_yellow_6 @ X19 @ X18) @ (u1_struct_0 @ X19))
% 0.21/0.54          | (r2_hidden @ (k11_yellow_6 @ X19 @ X18) @ 
% 0.21/0.54             (k10_yellow_6 @ X19 @ X18))
% 0.21/0.54          | ~ (l1_waybel_0 @ X18 @ X19)
% 0.21/0.54          | ~ (v3_yellow_6 @ X18 @ X19)
% 0.21/0.54          | ~ (v7_waybel_0 @ X18)
% 0.21/0.54          | ~ (v4_orders_2 @ X18)
% 0.21/0.54          | (v2_struct_0 @ X18))),
% 0.21/0.54      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_B_1)
% 0.21/0.54        | ~ (v4_orders_2 @ sk_B_1)
% 0.21/0.54        | ~ (v7_waybel_0 @ sk_B_1)
% 0.21/0.54        | ~ (v3_yellow_6 @ sk_B_1 @ sk_A)
% 0.21/0.54        | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.21/0.54        | (r2_hidden @ (k11_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.21/0.54           (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54        | ~ (v8_pre_topc @ sk_A)
% 0.21/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.54        | (v2_struct_0 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['25', '27'])).
% 0.21/0.54  thf('29', plain, ((v4_orders_2 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('30', plain, ((v7_waybel_0 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('31', plain, ((v3_yellow_6 @ sk_B_1 @ sk_A)),
% 0.21/0.54      inference('clc', [status(thm)], ['10', '11'])).
% 0.21/0.54  thf('32', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('34', plain, ((v8_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('36', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_B_1)
% 0.21/0.54        | (r2_hidden @ (k11_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.21/0.54           (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.54        | (v2_struct_0 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)],
% 0.21/0.54                ['28', '29', '30', '31', '32', '33', '34', '35'])).
% 0.21/0.54  thf('37', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('38', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_A)
% 0.21/0.54        | (r2_hidden @ (k11_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.21/0.54           (k10_yellow_6 @ sk_A @ sk_B_1)))),
% 0.21/0.54      inference('clc', [status(thm)], ['36', '37'])).
% 0.21/0.54  thf('39', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('40', plain,
% 0.21/0.54      ((r2_hidden @ (k11_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.21/0.54        (k10_yellow_6 @ sk_A @ sk_B_1))),
% 0.21/0.54      inference('clc', [status(thm)], ['38', '39'])).
% 0.21/0.54  thf(l1_zfmisc_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.21/0.54  thf('41', plain,
% 0.21/0.54      (![X11 : $i, X13 : $i]:
% 0.21/0.54         ((r1_tarski @ (k1_tarski @ X11) @ X13) | ~ (r2_hidden @ X11 @ X13))),
% 0.21/0.54      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.54  thf('42', plain,
% 0.21/0.54      ((r1_tarski @ (k1_tarski @ (k11_yellow_6 @ sk_A @ sk_B_1)) @ 
% 0.21/0.54        (k10_yellow_6 @ sk_A @ sk_B_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.54  thf(t1_tex_2, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.21/0.54           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.21/0.54  thf('43', plain,
% 0.21/0.54      (![X14 : $i, X15 : $i]:
% 0.21/0.54         ((v1_xboole_0 @ X14)
% 0.21/0.54          | ~ (v1_zfmisc_1 @ X14)
% 0.21/0.54          | ((X15) = (X14))
% 0.21/0.54          | ~ (r1_tarski @ X15 @ X14)
% 0.21/0.54          | (v1_xboole_0 @ X15))),
% 0.21/0.54      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.21/0.54  thf('44', plain,
% 0.21/0.54      (((v1_xboole_0 @ (k1_tarski @ (k11_yellow_6 @ sk_A @ sk_B_1)))
% 0.21/0.54        | ((k1_tarski @ (k11_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.54            = (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.54        | ~ (v1_zfmisc_1 @ (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.54        | (v1_xboole_0 @ (k10_yellow_6 @ sk_A @ sk_B_1)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.54  thf('45', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(fc22_yellow_6, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.54         ( v8_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.21/0.54         ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.54         ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.54       ( v1_zfmisc_1 @ ( k10_yellow_6 @ A @ B ) ) ))).
% 0.21/0.54  thf('46', plain,
% 0.21/0.54      (![X23 : $i, X24 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X23)
% 0.21/0.54          | ~ (v8_pre_topc @ X23)
% 0.21/0.54          | ~ (v2_pre_topc @ X23)
% 0.21/0.54          | (v2_struct_0 @ X23)
% 0.21/0.54          | (v2_struct_0 @ X24)
% 0.21/0.54          | ~ (v4_orders_2 @ X24)
% 0.21/0.54          | ~ (v7_waybel_0 @ X24)
% 0.21/0.54          | ~ (l1_waybel_0 @ X24 @ X23)
% 0.21/0.54          | (v1_zfmisc_1 @ (k10_yellow_6 @ X23 @ X24)))),
% 0.21/0.54      inference('cnf', [status(esa)], [fc22_yellow_6])).
% 0.21/0.54  thf('47', plain,
% 0.21/0.54      (((v1_zfmisc_1 @ (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.54        | ~ (v7_waybel_0 @ sk_B_1)
% 0.21/0.54        | ~ (v4_orders_2 @ sk_B_1)
% 0.21/0.54        | (v2_struct_0 @ sk_B_1)
% 0.21/0.54        | (v2_struct_0 @ sk_A)
% 0.21/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.54        | ~ (v8_pre_topc @ sk_A)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.54  thf('48', plain, ((v7_waybel_0 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('49', plain, ((v4_orders_2 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('50', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('51', plain, ((v8_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('53', plain,
% 0.21/0.54      (((v1_zfmisc_1 @ (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.54        | (v2_struct_0 @ sk_B_1)
% 0.21/0.54        | (v2_struct_0 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['47', '48', '49', '50', '51', '52'])).
% 0.21/0.54  thf('54', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('55', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_A) | (v1_zfmisc_1 @ (k10_yellow_6 @ sk_A @ sk_B_1)))),
% 0.21/0.54      inference('clc', [status(thm)], ['53', '54'])).
% 0.21/0.54  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('57', plain, ((v1_zfmisc_1 @ (k10_yellow_6 @ sk_A @ sk_B_1))),
% 0.21/0.54      inference('clc', [status(thm)], ['55', '56'])).
% 0.21/0.54  thf('58', plain,
% 0.21/0.54      (((v1_xboole_0 @ (k1_tarski @ (k11_yellow_6 @ sk_A @ sk_B_1)))
% 0.21/0.54        | ((k1_tarski @ (k11_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.54            = (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.54        | (v1_xboole_0 @ (k10_yellow_6 @ sk_A @ sk_B_1)))),
% 0.21/0.54      inference('demod', [status(thm)], ['44', '57'])).
% 0.21/0.54  thf(d10_xboole_0, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.54  thf('59', plain,
% 0.21/0.54      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.54  thf('60', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.21/0.54      inference('simplify', [status(thm)], ['59'])).
% 0.21/0.54  thf('61', plain,
% 0.21/0.54      (![X11 : $i, X12 : $i]:
% 0.21/0.54         ((r2_hidden @ X11 @ X12) | ~ (r1_tarski @ (k1_tarski @ X11) @ X12))),
% 0.21/0.54      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.54  thf('62', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['60', '61'])).
% 0.21/0.54  thf(d1_xboole_0, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.54  thf('63', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.54  thf('64', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['62', '63'])).
% 0.21/0.54  thf('65', plain,
% 0.21/0.54      (((v1_xboole_0 @ (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.54        | ((k1_tarski @ (k11_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.54            = (k10_yellow_6 @ sk_A @ sk_B_1)))),
% 0.21/0.54      inference('clc', [status(thm)], ['58', '64'])).
% 0.21/0.54  thf('66', plain, ((v1_yellow_6 @ sk_B_1 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t42_yellow_6, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.54             ( v7_waybel_0 @ B ) & ( v1_yellow_6 @ B @ A ) & 
% 0.21/0.54             ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.54           ( r2_hidden @ ( k4_yellow_6 @ A @ B ) @ ( k10_yellow_6 @ A @ B ) ) ) ) ))).
% 0.21/0.54  thf('67', plain,
% 0.21/0.54      (![X25 : $i, X26 : $i]:
% 0.21/0.54         ((v2_struct_0 @ X25)
% 0.21/0.54          | ~ (v4_orders_2 @ X25)
% 0.21/0.54          | ~ (v7_waybel_0 @ X25)
% 0.21/0.54          | ~ (v1_yellow_6 @ X25 @ X26)
% 0.21/0.54          | ~ (l1_waybel_0 @ X25 @ X26)
% 0.21/0.54          | (r2_hidden @ (k4_yellow_6 @ X26 @ X25) @ (k10_yellow_6 @ X26 @ X25))
% 0.21/0.54          | ~ (l1_pre_topc @ X26)
% 0.21/0.54          | ~ (v2_pre_topc @ X26)
% 0.21/0.54          | (v2_struct_0 @ X26))),
% 0.21/0.54      inference('cnf', [status(esa)], [t42_yellow_6])).
% 0.21/0.54  thf('68', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_A)
% 0.21/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.21/0.54           (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.54        | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.21/0.54        | ~ (v7_waybel_0 @ sk_B_1)
% 0.21/0.54        | ~ (v4_orders_2 @ sk_B_1)
% 0.21/0.54        | (v2_struct_0 @ sk_B_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['66', '67'])).
% 0.21/0.54  thf('69', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('71', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('72', plain, ((v7_waybel_0 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('73', plain, ((v4_orders_2 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('74', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_A)
% 0.21/0.54        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.21/0.54           (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.54        | (v2_struct_0 @ sk_B_1))),
% 0.21/0.54      inference('demod', [status(thm)], ['68', '69', '70', '71', '72', '73'])).
% 0.21/0.54  thf('75', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('76', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_B_1)
% 0.21/0.54        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.21/0.54           (k10_yellow_6 @ sk_A @ sk_B_1)))),
% 0.21/0.54      inference('clc', [status(thm)], ['74', '75'])).
% 0.21/0.54  thf('77', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('78', plain,
% 0.21/0.54      ((r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.21/0.54        (k10_yellow_6 @ sk_A @ sk_B_1))),
% 0.21/0.54      inference('clc', [status(thm)], ['76', '77'])).
% 0.21/0.54  thf('79', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.54  thf('80', plain, (~ (v1_xboole_0 @ (k10_yellow_6 @ sk_A @ sk_B_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['78', '79'])).
% 0.21/0.54  thf('81', plain,
% 0.21/0.54      (((k1_tarski @ (k11_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.54         = (k10_yellow_6 @ sk_A @ sk_B_1))),
% 0.21/0.54      inference('clc', [status(thm)], ['65', '80'])).
% 0.21/0.54  thf('82', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.21/0.54      inference('simplify', [status(thm)], ['59'])).
% 0.21/0.54  thf(d1_zfmisc_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.21/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.21/0.54  thf('83', plain,
% 0.21/0.54      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.54         (~ (r1_tarski @ X6 @ X7)
% 0.21/0.54          | (r2_hidden @ X6 @ X8)
% 0.21/0.54          | ((X8) != (k1_zfmisc_1 @ X7)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.54  thf('84', plain,
% 0.21/0.54      (![X6 : $i, X7 : $i]:
% 0.21/0.54         ((r2_hidden @ X6 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X6 @ X7))),
% 0.21/0.54      inference('simplify', [status(thm)], ['83'])).
% 0.21/0.54  thf('85', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['82', '84'])).
% 0.21/0.54  thf('86', plain,
% 0.21/0.54      (![X11 : $i, X13 : $i]:
% 0.21/0.54         ((r1_tarski @ (k1_tarski @ X11) @ X13) | ~ (r2_hidden @ X11 @ X13))),
% 0.21/0.54      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.54  thf('87', plain,
% 0.21/0.54      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['85', '86'])).
% 0.21/0.54  thf('88', plain,
% 0.21/0.54      ((r1_tarski @ (k10_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.21/0.54        (k1_zfmisc_1 @ (k11_yellow_6 @ sk_A @ sk_B_1)))),
% 0.21/0.54      inference('sup+', [status(thm)], ['81', '87'])).
% 0.21/0.54  thf('89', plain,
% 0.21/0.54      ((r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.21/0.54        (k10_yellow_6 @ sk_A @ sk_B_1))),
% 0.21/0.54      inference('clc', [status(thm)], ['76', '77'])).
% 0.21/0.54  thf('90', plain,
% 0.21/0.54      (![X11 : $i, X13 : $i]:
% 0.21/0.54         ((r1_tarski @ (k1_tarski @ X11) @ X13) | ~ (r2_hidden @ X11 @ X13))),
% 0.21/0.54      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.54  thf('91', plain,
% 0.21/0.54      ((r1_tarski @ (k1_tarski @ (k4_yellow_6 @ sk_A @ sk_B_1)) @ 
% 0.21/0.54        (k10_yellow_6 @ sk_A @ sk_B_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['89', '90'])).
% 0.21/0.54  thf('92', plain,
% 0.21/0.54      (![X14 : $i, X15 : $i]:
% 0.21/0.54         ((v1_xboole_0 @ X14)
% 0.21/0.54          | ~ (v1_zfmisc_1 @ X14)
% 0.21/0.54          | ((X15) = (X14))
% 0.21/0.54          | ~ (r1_tarski @ X15 @ X14)
% 0.21/0.54          | (v1_xboole_0 @ X15))),
% 0.21/0.54      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.21/0.54  thf('93', plain,
% 0.21/0.54      (((v1_xboole_0 @ (k1_tarski @ (k4_yellow_6 @ sk_A @ sk_B_1)))
% 0.21/0.54        | ((k1_tarski @ (k4_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.54            = (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.54        | ~ (v1_zfmisc_1 @ (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.54        | (v1_xboole_0 @ (k10_yellow_6 @ sk_A @ sk_B_1)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['91', '92'])).
% 0.21/0.54  thf('94', plain, ((v1_zfmisc_1 @ (k10_yellow_6 @ sk_A @ sk_B_1))),
% 0.21/0.54      inference('clc', [status(thm)], ['55', '56'])).
% 0.21/0.54  thf('95', plain,
% 0.21/0.54      (((v1_xboole_0 @ (k1_tarski @ (k4_yellow_6 @ sk_A @ sk_B_1)))
% 0.21/0.54        | ((k1_tarski @ (k4_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.54            = (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.54        | (v1_xboole_0 @ (k10_yellow_6 @ sk_A @ sk_B_1)))),
% 0.21/0.54      inference('demod', [status(thm)], ['93', '94'])).
% 0.21/0.54  thf('96', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['62', '63'])).
% 0.21/0.54  thf('97', plain,
% 0.21/0.54      (((v1_xboole_0 @ (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.54        | ((k1_tarski @ (k4_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.54            = (k10_yellow_6 @ sk_A @ sk_B_1)))),
% 0.21/0.54      inference('clc', [status(thm)], ['95', '96'])).
% 0.21/0.54  thf('98', plain, (~ (v1_xboole_0 @ (k10_yellow_6 @ sk_A @ sk_B_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['78', '79'])).
% 0.21/0.54  thf('99', plain,
% 0.21/0.54      (((k1_tarski @ (k4_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.54         = (k10_yellow_6 @ sk_A @ sk_B_1))),
% 0.21/0.54      inference('clc', [status(thm)], ['97', '98'])).
% 0.21/0.54  thf('100', plain,
% 0.21/0.54      (![X11 : $i, X12 : $i]:
% 0.21/0.54         ((r2_hidden @ X11 @ X12) | ~ (r1_tarski @ (k1_tarski @ X11) @ X12))),
% 0.21/0.54      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.54  thf('101', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (r1_tarski @ (k10_yellow_6 @ sk_A @ sk_B_1) @ X0)
% 0.21/0.54          | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['99', '100'])).
% 0.21/0.54  thf('102', plain,
% 0.21/0.54      ((r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.21/0.54        (k1_zfmisc_1 @ (k11_yellow_6 @ sk_A @ sk_B_1)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['88', '101'])).
% 0.21/0.54  thf('103', plain,
% 0.21/0.54      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X9 @ X8)
% 0.21/0.54          | (r1_tarski @ X9 @ X7)
% 0.21/0.54          | ((X8) != (k1_zfmisc_1 @ X7)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.54  thf('104', plain,
% 0.21/0.54      (![X7 : $i, X9 : $i]:
% 0.21/0.54         ((r1_tarski @ X9 @ X7) | ~ (r2_hidden @ X9 @ (k1_zfmisc_1 @ X7)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['103'])).
% 0.21/0.54  thf('105', plain,
% 0.21/0.54      ((r1_tarski @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.21/0.54        (k11_yellow_6 @ sk_A @ sk_B_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['102', '104'])).
% 0.21/0.54  thf('106', plain,
% 0.21/0.54      (![X3 : $i, X5 : $i]:
% 0.21/0.54         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 0.21/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.54  thf('107', plain,
% 0.21/0.54      ((~ (r1_tarski @ (k11_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.21/0.54           (k4_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.54        | ((k11_yellow_6 @ sk_A @ sk_B_1) = (k4_yellow_6 @ sk_A @ sk_B_1)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['105', '106'])).
% 0.21/0.54  thf('108', plain,
% 0.21/0.54      (((k11_yellow_6 @ sk_A @ sk_B_1) != (k4_yellow_6 @ sk_A @ sk_B_1))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('109', plain,
% 0.21/0.54      (~ (r1_tarski @ (k11_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.21/0.54          (k4_yellow_6 @ sk_A @ sk_B_1))),
% 0.21/0.54      inference('simplify_reflect-', [status(thm)], ['107', '108'])).
% 0.21/0.54  thf('110', plain,
% 0.21/0.54      (((k1_tarski @ (k4_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.54         = (k10_yellow_6 @ sk_A @ sk_B_1))),
% 0.21/0.54      inference('clc', [status(thm)], ['97', '98'])).
% 0.21/0.54  thf('111', plain,
% 0.21/0.54      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['85', '86'])).
% 0.21/0.54  thf('112', plain,
% 0.21/0.54      ((r1_tarski @ (k10_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.21/0.54        (k1_zfmisc_1 @ (k4_yellow_6 @ sk_A @ sk_B_1)))),
% 0.21/0.54      inference('sup+', [status(thm)], ['110', '111'])).
% 0.21/0.54  thf('113', plain,
% 0.21/0.54      (((k1_tarski @ (k11_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.54         = (k10_yellow_6 @ sk_A @ sk_B_1))),
% 0.21/0.54      inference('clc', [status(thm)], ['65', '80'])).
% 0.21/0.54  thf('114', plain,
% 0.21/0.54      (![X11 : $i, X12 : $i]:
% 0.21/0.54         ((r2_hidden @ X11 @ X12) | ~ (r1_tarski @ (k1_tarski @ X11) @ X12))),
% 0.21/0.54      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.54  thf('115', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (r1_tarski @ (k10_yellow_6 @ sk_A @ sk_B_1) @ X0)
% 0.21/0.54          | (r2_hidden @ (k11_yellow_6 @ sk_A @ sk_B_1) @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['113', '114'])).
% 0.21/0.54  thf('116', plain,
% 0.21/0.54      ((r2_hidden @ (k11_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.21/0.54        (k1_zfmisc_1 @ (k4_yellow_6 @ sk_A @ sk_B_1)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['112', '115'])).
% 0.21/0.54  thf('117', plain,
% 0.21/0.54      (![X7 : $i, X9 : $i]:
% 0.21/0.54         ((r1_tarski @ X9 @ X7) | ~ (r2_hidden @ X9 @ (k1_zfmisc_1 @ X7)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['103'])).
% 0.21/0.54  thf('118', plain,
% 0.21/0.54      ((r1_tarski @ (k11_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.21/0.54        (k4_yellow_6 @ sk_A @ sk_B_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['116', '117'])).
% 0.21/0.54  thf('119', plain, ($false), inference('demod', [status(thm)], ['109', '118'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
