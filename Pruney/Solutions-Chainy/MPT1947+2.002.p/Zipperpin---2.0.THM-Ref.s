%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5X9hJz40nj

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 346 expanded)
%              Number of leaves         :   32 ( 117 expanded)
%              Depth                    :   22
%              Number of atoms          :  839 (5734 expanded)
%              Number of equality atoms :   18 ( 180 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_yellow_6_type,type,(
    k4_yellow_6: $i > $i > $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_yellow_6_type,type,(
    v1_yellow_6: $i > $i > $o )).

thf(k11_yellow_6_type,type,(
    k11_yellow_6: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_yellow_6_type,type,(
    v3_yellow_6: $i > $i > $o )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

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

thf('1',plain,(
    ! [X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ~ ( v7_waybel_0 @ X24 )
      | ~ ( v1_yellow_6 @ X24 @ X25 )
      | ~ ( l1_waybel_0 @ X24 @ X25 )
      | ( r2_hidden @ ( k4_yellow_6 @ X25 @ X24 ) @ ( k10_yellow_6 @ X25 @ X24 ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_6])).

thf('2',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B_1 )
    | ~ ( v4_orders_2 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v7_waybel_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v4_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['2','3','4','5','6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
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

thf('14',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_waybel_0 @ X15 @ X16 )
      | ( v3_yellow_6 @ X15 @ X16 )
      | ~ ( v1_yellow_6 @ X15 @ X16 )
      | ~ ( v7_waybel_0 @ X15 )
      | ~ ( v4_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc4_yellow_6])).

thf('15',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( v4_orders_2 @ sk_B_1 )
    | ~ ( v7_waybel_0 @ sk_B_1 )
    | ~ ( v1_yellow_6 @ sk_B_1 @ sk_A )
    | ( v3_yellow_6 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v4_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v7_waybel_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_yellow_6 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v3_yellow_6 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16','17','18','19','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v3_yellow_6 @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v3_yellow_6 @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['23','24'])).

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

thf('26',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v8_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v7_waybel_0 @ X21 )
      | ~ ( v3_yellow_6 @ X21 @ X20 )
      | ~ ( l1_waybel_0 @ X21 @ X20 )
      | ( m1_subset_1 @ ( k11_yellow_6 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k11_yellow_6])).

thf('27',plain,
    ( ( m1_subset_1 @ ( k11_yellow_6 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B_1 )
    | ~ ( v4_orders_2 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v7_waybel_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v4_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( m1_subset_1 @ ( k11_yellow_6 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28','29','30','31','32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k11_yellow_6 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ ( k11_yellow_6 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['36','37'])).

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

thf('39',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v7_waybel_0 @ X17 )
      | ~ ( v3_yellow_6 @ X17 @ X18 )
      | ~ ( l1_waybel_0 @ X17 @ X18 )
      | ( X19
       != ( k11_yellow_6 @ X18 @ X17 ) )
      | ( r2_hidden @ X19 @ ( k10_yellow_6 @ X18 @ X17 ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v8_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d20_yellow_6])).

thf('40',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( v8_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ ( k11_yellow_6 @ X18 @ X17 ) @ ( u1_struct_0 @ X18 ) )
      | ( r2_hidden @ ( k11_yellow_6 @ X18 @ X17 ) @ ( k10_yellow_6 @ X18 @ X17 ) )
      | ~ ( l1_waybel_0 @ X17 @ X18 )
      | ~ ( v3_yellow_6 @ X17 @ X18 )
      | ~ ( v7_waybel_0 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
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
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    v4_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v7_waybel_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v3_yellow_6 @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['23','24'])).

thf('45',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( k11_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42','43','44','45','46','47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k11_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    r2_hidden @ ( k11_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['51','52'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('54',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X10 ) @ X12 )
      | ~ ( r2_hidden @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('55',plain,(
    r1_tarski @ ( k1_tarski @ ( k11_yellow_6 @ sk_A @ sk_B_1 ) ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('56',plain,(
    ! [X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X13 )
      | ~ ( v1_zfmisc_1 @ X13 )
      | ( X14 = X13 )
      | ~ ( r1_tarski @ X14 @ X13 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('57',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ ( k11_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( ( k1_tarski @ ( k11_yellow_6 @ sk_A @ sk_B_1 ) )
      = ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_zfmisc_1 @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
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

thf('59',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( v8_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ( v2_struct_0 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ~ ( v7_waybel_0 @ X23 )
      | ~ ( l1_waybel_0 @ X23 @ X22 )
      | ( v1_zfmisc_1 @ ( k10_yellow_6 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[fc22_yellow_6])).

thf('60',plain,
    ( ( v1_zfmisc_1 @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ~ ( v7_waybel_0 @ sk_B_1 )
    | ~ ( v4_orders_2 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v7_waybel_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v4_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v1_zfmisc_1 @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','62','63','64','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_zfmisc_1 @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_zfmisc_1 @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ ( k11_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( ( k1_tarski @ ( k11_yellow_6 @ sk_A @ sk_B_1 ) )
      = ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['57','70'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('72',plain,(
    ! [X9: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('73',plain,
    ( ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( ( k1_tarski @ ( k11_yellow_6 @ sk_A @ sk_B_1 ) )
      = ( k10_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,(
    r2_hidden @ ( k11_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['51','52'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('76',plain,(
    ~ ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k1_tarski @ ( k11_yellow_6 @ sk_A @ sk_B_1 ) )
    = ( k10_yellow_6 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['73','76'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('78',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( X6 = X3 )
      | ( X5
       != ( k1_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('79',plain,(
    ! [X3: $i,X6: $i] :
      ( ( X6 = X3 )
      | ~ ( r2_hidden @ X6 @ ( k1_tarski @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
      | ( X0
        = ( k11_yellow_6 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['77','79'])).

thf('81',plain,
    ( ( k4_yellow_6 @ sk_A @ sk_B_1 )
    = ( k11_yellow_6 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['12','80'])).

thf('82',plain,(
    ( k11_yellow_6 @ sk_A @ sk_B_1 )
 != ( k4_yellow_6 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['81','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5X9hJz40nj
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:36:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 88 iterations in 0.034s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.49  thf(k4_yellow_6_type, type, k4_yellow_6: $i > $i > $i).
% 0.21/0.49  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.21/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.49  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.49  thf(v1_yellow_6_type, type, v1_yellow_6: $i > $i > $o).
% 0.21/0.49  thf(k11_yellow_6_type, type, k11_yellow_6: $i > $i > $i).
% 0.21/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.49  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.21/0.49  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(v3_yellow_6_type, type, v3_yellow_6: $i > $i > $o).
% 0.21/0.49  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.21/0.49  thf(k10_yellow_6_type, type, k10_yellow_6: $i > $i > $i).
% 0.21/0.49  thf(t45_yellow_6, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.49         ( v8_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.49             ( v7_waybel_0 @ B ) & ( v1_yellow_6 @ B @ A ) & 
% 0.21/0.49             ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.49           ( ( k11_yellow_6 @ A @ B ) = ( k4_yellow_6 @ A @ B ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.49            ( v8_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.49                ( v7_waybel_0 @ B ) & ( v1_yellow_6 @ B @ A ) & 
% 0.21/0.49                ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.49              ( ( k11_yellow_6 @ A @ B ) = ( k4_yellow_6 @ A @ B ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t45_yellow_6])).
% 0.21/0.49  thf('0', plain, ((v1_yellow_6 @ sk_B_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t42_yellow_6, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.49             ( v7_waybel_0 @ B ) & ( v1_yellow_6 @ B @ A ) & 
% 0.21/0.49             ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.49           ( r2_hidden @ ( k4_yellow_6 @ A @ B ) @ ( k10_yellow_6 @ A @ B ) ) ) ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X24 : $i, X25 : $i]:
% 0.21/0.49         ((v2_struct_0 @ X24)
% 0.21/0.49          | ~ (v4_orders_2 @ X24)
% 0.21/0.49          | ~ (v7_waybel_0 @ X24)
% 0.21/0.49          | ~ (v1_yellow_6 @ X24 @ X25)
% 0.21/0.49          | ~ (l1_waybel_0 @ X24 @ X25)
% 0.21/0.49          | (r2_hidden @ (k4_yellow_6 @ X25 @ X24) @ (k10_yellow_6 @ X25 @ X24))
% 0.21/0.49          | ~ (l1_pre_topc @ X25)
% 0.21/0.49          | ~ (v2_pre_topc @ X25)
% 0.21/0.49          | (v2_struct_0 @ X25))),
% 0.21/0.49      inference('cnf', [status(esa)], [t42_yellow_6])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A)
% 0.21/0.49        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.49        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.21/0.49           (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.49        | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.21/0.49        | ~ (v7_waybel_0 @ sk_B_1)
% 0.21/0.49        | ~ (v4_orders_2 @ sk_B_1)
% 0.21/0.49        | (v2_struct_0 @ sk_B_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('5', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('6', plain, ((v7_waybel_0 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('7', plain, ((v4_orders_2 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A)
% 0.21/0.49        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.21/0.49           (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.49        | (v2_struct_0 @ sk_B_1))),
% 0.21/0.49      inference('demod', [status(thm)], ['2', '3', '4', '5', '6', '7'])).
% 0.21/0.49  thf('9', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_B_1)
% 0.21/0.49        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.21/0.49           (k10_yellow_6 @ sk_A @ sk_B_1)))),
% 0.21/0.49      inference('clc', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf('11', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      ((r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.21/0.49        (k10_yellow_6 @ sk_A @ sk_B_1))),
% 0.21/0.49      inference('clc', [status(thm)], ['10', '11'])).
% 0.21/0.49  thf('13', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(cc4_yellow_6, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( l1_waybel_0 @ B @ A ) =>
% 0.21/0.49           ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.49               ( v7_waybel_0 @ B ) & ( v1_yellow_6 @ B @ A ) ) =>
% 0.21/0.49             ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.49               ( v7_waybel_0 @ B ) & ( v3_yellow_6 @ B @ A ) ) ) ) ) ))).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X15 : $i, X16 : $i]:
% 0.21/0.49         (~ (l1_waybel_0 @ X15 @ X16)
% 0.21/0.49          | (v3_yellow_6 @ X15 @ X16)
% 0.21/0.49          | ~ (v1_yellow_6 @ X15 @ X16)
% 0.21/0.49          | ~ (v7_waybel_0 @ X15)
% 0.21/0.49          | ~ (v4_orders_2 @ X15)
% 0.21/0.49          | (v2_struct_0 @ X15)
% 0.21/0.49          | ~ (l1_pre_topc @ X16)
% 0.21/0.49          | ~ (v2_pre_topc @ X16)
% 0.21/0.49          | (v2_struct_0 @ X16))),
% 0.21/0.49      inference('cnf', [status(esa)], [cc4_yellow_6])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A)
% 0.21/0.49        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.49        | (v2_struct_0 @ sk_B_1)
% 0.21/0.49        | ~ (v4_orders_2 @ sk_B_1)
% 0.21/0.49        | ~ (v7_waybel_0 @ sk_B_1)
% 0.21/0.49        | ~ (v1_yellow_6 @ sk_B_1 @ sk_A)
% 0.21/0.49        | (v3_yellow_6 @ sk_B_1 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.49  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('18', plain, ((v4_orders_2 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('19', plain, ((v7_waybel_0 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('20', plain, ((v1_yellow_6 @ sk_B_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A)
% 0.21/0.49        | (v2_struct_0 @ sk_B_1)
% 0.21/0.49        | (v3_yellow_6 @ sk_B_1 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['15', '16', '17', '18', '19', '20'])).
% 0.21/0.49  thf('22', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('23', plain, (((v3_yellow_6 @ sk_B_1 @ sk_A) | (v2_struct_0 @ sk_B_1))),
% 0.21/0.49      inference('clc', [status(thm)], ['21', '22'])).
% 0.21/0.49  thf('24', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('25', plain, ((v3_yellow_6 @ sk_B_1 @ sk_A)),
% 0.21/0.49      inference('clc', [status(thm)], ['23', '24'])).
% 0.21/0.49  thf(dt_k11_yellow_6, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.49         ( v8_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.21/0.49         ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.49         ( v7_waybel_0 @ B ) & ( v3_yellow_6 @ B @ A ) & 
% 0.21/0.49         ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.49       ( m1_subset_1 @ ( k11_yellow_6 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (![X20 : $i, X21 : $i]:
% 0.21/0.49         (~ (l1_pre_topc @ X20)
% 0.21/0.49          | ~ (v8_pre_topc @ X20)
% 0.21/0.49          | ~ (v2_pre_topc @ X20)
% 0.21/0.49          | (v2_struct_0 @ X20)
% 0.21/0.49          | (v2_struct_0 @ X21)
% 0.21/0.49          | ~ (v4_orders_2 @ X21)
% 0.21/0.49          | ~ (v7_waybel_0 @ X21)
% 0.21/0.49          | ~ (v3_yellow_6 @ X21 @ X20)
% 0.21/0.49          | ~ (l1_waybel_0 @ X21 @ X20)
% 0.21/0.49          | (m1_subset_1 @ (k11_yellow_6 @ X20 @ X21) @ (u1_struct_0 @ X20)))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k11_yellow_6])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      (((m1_subset_1 @ (k11_yellow_6 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.21/0.49        | ~ (v7_waybel_0 @ sk_B_1)
% 0.21/0.49        | ~ (v4_orders_2 @ sk_B_1)
% 0.21/0.49        | (v2_struct_0 @ sk_B_1)
% 0.21/0.49        | (v2_struct_0 @ sk_A)
% 0.21/0.49        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.49        | ~ (v8_pre_topc @ sk_A)
% 0.21/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.49  thf('28', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('29', plain, ((v7_waybel_0 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('30', plain, ((v4_orders_2 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('32', plain, ((v8_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      (((m1_subset_1 @ (k11_yellow_6 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | (v2_struct_0 @ sk_B_1)
% 0.21/0.49        | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)],
% 0.21/0.49                ['27', '28', '29', '30', '31', '32', '33'])).
% 0.21/0.49  thf('35', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A)
% 0.21/0.49        | (m1_subset_1 @ (k11_yellow_6 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('clc', [status(thm)], ['34', '35'])).
% 0.21/0.49  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      ((m1_subset_1 @ (k11_yellow_6 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('clc', [status(thm)], ['36', '37'])).
% 0.21/0.49  thf(d20_yellow_6, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.49         ( v8_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.49             ( v7_waybel_0 @ B ) & ( v3_yellow_6 @ B @ A ) & 
% 0.21/0.49             ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.49               ( ( ( C ) = ( k11_yellow_6 @ A @ B ) ) <=>
% 0.21/0.49                 ( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('39', plain,
% 0.21/0.49      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.49         ((v2_struct_0 @ X17)
% 0.21/0.49          | ~ (v4_orders_2 @ X17)
% 0.21/0.49          | ~ (v7_waybel_0 @ X17)
% 0.21/0.49          | ~ (v3_yellow_6 @ X17 @ X18)
% 0.21/0.49          | ~ (l1_waybel_0 @ X17 @ X18)
% 0.21/0.49          | ((X19) != (k11_yellow_6 @ X18 @ X17))
% 0.21/0.49          | (r2_hidden @ X19 @ (k10_yellow_6 @ X18 @ X17))
% 0.21/0.49          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 0.21/0.49          | ~ (l1_pre_topc @ X18)
% 0.21/0.49          | ~ (v8_pre_topc @ X18)
% 0.21/0.49          | ~ (v2_pre_topc @ X18)
% 0.21/0.49          | (v2_struct_0 @ X18))),
% 0.21/0.49      inference('cnf', [status(esa)], [d20_yellow_6])).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      (![X17 : $i, X18 : $i]:
% 0.21/0.49         ((v2_struct_0 @ X18)
% 0.21/0.49          | ~ (v2_pre_topc @ X18)
% 0.21/0.49          | ~ (v8_pre_topc @ X18)
% 0.21/0.49          | ~ (l1_pre_topc @ X18)
% 0.21/0.49          | ~ (m1_subset_1 @ (k11_yellow_6 @ X18 @ X17) @ (u1_struct_0 @ X18))
% 0.21/0.49          | (r2_hidden @ (k11_yellow_6 @ X18 @ X17) @ 
% 0.21/0.49             (k10_yellow_6 @ X18 @ X17))
% 0.21/0.49          | ~ (l1_waybel_0 @ X17 @ X18)
% 0.21/0.49          | ~ (v3_yellow_6 @ X17 @ X18)
% 0.21/0.49          | ~ (v7_waybel_0 @ X17)
% 0.21/0.49          | ~ (v4_orders_2 @ X17)
% 0.21/0.49          | (v2_struct_0 @ X17))),
% 0.21/0.49      inference('simplify', [status(thm)], ['39'])).
% 0.21/0.49  thf('41', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_B_1)
% 0.21/0.49        | ~ (v4_orders_2 @ sk_B_1)
% 0.21/0.49        | ~ (v7_waybel_0 @ sk_B_1)
% 0.21/0.49        | ~ (v3_yellow_6 @ sk_B_1 @ sk_A)
% 0.21/0.49        | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.21/0.49        | (r2_hidden @ (k11_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.21/0.49           (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.49        | ~ (v8_pre_topc @ sk_A)
% 0.21/0.49        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.49        | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['38', '40'])).
% 0.21/0.49  thf('42', plain, ((v4_orders_2 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('43', plain, ((v7_waybel_0 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('44', plain, ((v3_yellow_6 @ sk_B_1 @ sk_A)),
% 0.21/0.49      inference('clc', [status(thm)], ['23', '24'])).
% 0.21/0.49  thf('45', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('47', plain, ((v8_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('48', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('49', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_B_1)
% 0.21/0.49        | (r2_hidden @ (k11_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.21/0.49           (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.49        | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)],
% 0.21/0.49                ['41', '42', '43', '44', '45', '46', '47', '48'])).
% 0.21/0.49  thf('50', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('51', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A)
% 0.21/0.49        | (r2_hidden @ (k11_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.21/0.49           (k10_yellow_6 @ sk_A @ sk_B_1)))),
% 0.21/0.49      inference('clc', [status(thm)], ['49', '50'])).
% 0.21/0.49  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('53', plain,
% 0.21/0.49      ((r2_hidden @ (k11_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.21/0.49        (k10_yellow_6 @ sk_A @ sk_B_1))),
% 0.21/0.49      inference('clc', [status(thm)], ['51', '52'])).
% 0.21/0.49  thf(l1_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.21/0.49  thf('54', plain,
% 0.21/0.49      (![X10 : $i, X12 : $i]:
% 0.21/0.49         ((r1_tarski @ (k1_tarski @ X10) @ X12) | ~ (r2_hidden @ X10 @ X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.49  thf('55', plain,
% 0.21/0.49      ((r1_tarski @ (k1_tarski @ (k11_yellow_6 @ sk_A @ sk_B_1)) @ 
% 0.21/0.49        (k10_yellow_6 @ sk_A @ sk_B_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.49  thf(t1_tex_2, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.21/0.49           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.21/0.49  thf('56', plain,
% 0.21/0.49      (![X13 : $i, X14 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ X13)
% 0.21/0.49          | ~ (v1_zfmisc_1 @ X13)
% 0.21/0.49          | ((X14) = (X13))
% 0.21/0.49          | ~ (r1_tarski @ X14 @ X13)
% 0.21/0.49          | (v1_xboole_0 @ X14))),
% 0.21/0.49      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.21/0.49  thf('57', plain,
% 0.21/0.49      (((v1_xboole_0 @ (k1_tarski @ (k11_yellow_6 @ sk_A @ sk_B_1)))
% 0.21/0.49        | ((k1_tarski @ (k11_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.49            = (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.49        | ~ (v1_zfmisc_1 @ (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.49        | (v1_xboole_0 @ (k10_yellow_6 @ sk_A @ sk_B_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.49  thf('58', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(fc22_yellow_6, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.49         ( v8_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.21/0.49         ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.49         ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.49       ( v1_zfmisc_1 @ ( k10_yellow_6 @ A @ B ) ) ))).
% 0.21/0.49  thf('59', plain,
% 0.21/0.49      (![X22 : $i, X23 : $i]:
% 0.21/0.49         (~ (l1_pre_topc @ X22)
% 0.21/0.49          | ~ (v8_pre_topc @ X22)
% 0.21/0.49          | ~ (v2_pre_topc @ X22)
% 0.21/0.49          | (v2_struct_0 @ X22)
% 0.21/0.49          | (v2_struct_0 @ X23)
% 0.21/0.49          | ~ (v4_orders_2 @ X23)
% 0.21/0.49          | ~ (v7_waybel_0 @ X23)
% 0.21/0.49          | ~ (l1_waybel_0 @ X23 @ X22)
% 0.21/0.49          | (v1_zfmisc_1 @ (k10_yellow_6 @ X22 @ X23)))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc22_yellow_6])).
% 0.21/0.49  thf('60', plain,
% 0.21/0.49      (((v1_zfmisc_1 @ (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.49        | ~ (v7_waybel_0 @ sk_B_1)
% 0.21/0.49        | ~ (v4_orders_2 @ sk_B_1)
% 0.21/0.49        | (v2_struct_0 @ sk_B_1)
% 0.21/0.49        | (v2_struct_0 @ sk_A)
% 0.21/0.49        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.49        | ~ (v8_pre_topc @ sk_A)
% 0.21/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['58', '59'])).
% 0.21/0.49  thf('61', plain, ((v7_waybel_0 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('62', plain, ((v4_orders_2 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('63', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('64', plain, ((v8_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('66', plain,
% 0.21/0.49      (((v1_zfmisc_1 @ (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.49        | (v2_struct_0 @ sk_B_1)
% 0.21/0.49        | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['60', '61', '62', '63', '64', '65'])).
% 0.21/0.49  thf('67', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('68', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A) | (v1_zfmisc_1 @ (k10_yellow_6 @ sk_A @ sk_B_1)))),
% 0.21/0.49      inference('clc', [status(thm)], ['66', '67'])).
% 0.21/0.49  thf('69', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('70', plain, ((v1_zfmisc_1 @ (k10_yellow_6 @ sk_A @ sk_B_1))),
% 0.21/0.49      inference('clc', [status(thm)], ['68', '69'])).
% 0.21/0.49  thf('71', plain,
% 0.21/0.49      (((v1_xboole_0 @ (k1_tarski @ (k11_yellow_6 @ sk_A @ sk_B_1)))
% 0.21/0.49        | ((k1_tarski @ (k11_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.49            = (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.49        | (v1_xboole_0 @ (k10_yellow_6 @ sk_A @ sk_B_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['57', '70'])).
% 0.21/0.49  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.21/0.49  thf('72', plain, (![X9 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X9))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.21/0.49  thf('73', plain,
% 0.21/0.49      (((v1_xboole_0 @ (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.49        | ((k1_tarski @ (k11_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.49            = (k10_yellow_6 @ sk_A @ sk_B_1)))),
% 0.21/0.49      inference('clc', [status(thm)], ['71', '72'])).
% 0.21/0.49  thf('74', plain,
% 0.21/0.49      ((r2_hidden @ (k11_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.21/0.49        (k10_yellow_6 @ sk_A @ sk_B_1))),
% 0.21/0.49      inference('clc', [status(thm)], ['51', '52'])).
% 0.21/0.49  thf(d1_xboole_0, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.49  thf('75', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.49  thf('76', plain, (~ (v1_xboole_0 @ (k10_yellow_6 @ sk_A @ sk_B_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['74', '75'])).
% 0.21/0.49  thf('77', plain,
% 0.21/0.49      (((k1_tarski @ (k11_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.49         = (k10_yellow_6 @ sk_A @ sk_B_1))),
% 0.21/0.49      inference('clc', [status(thm)], ['73', '76'])).
% 0.21/0.49  thf(d1_tarski, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.49  thf('78', plain,
% 0.21/0.49      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X6 @ X5) | ((X6) = (X3)) | ((X5) != (k1_tarski @ X3)))),
% 0.21/0.49      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.49  thf('79', plain,
% 0.21/0.49      (![X3 : $i, X6 : $i]:
% 0.21/0.49         (((X6) = (X3)) | ~ (r2_hidden @ X6 @ (k1_tarski @ X3)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['78'])).
% 0.21/0.49  thf('80', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.21/0.49          | ((X0) = (k11_yellow_6 @ sk_A @ sk_B_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['77', '79'])).
% 0.21/0.49  thf('81', plain,
% 0.21/0.49      (((k4_yellow_6 @ sk_A @ sk_B_1) = (k11_yellow_6 @ sk_A @ sk_B_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['12', '80'])).
% 0.21/0.49  thf('82', plain,
% 0.21/0.49      (((k11_yellow_6 @ sk_A @ sk_B_1) != (k4_yellow_6 @ sk_A @ sk_B_1))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('83', plain, ($false),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['81', '82'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
