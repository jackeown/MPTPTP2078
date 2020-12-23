%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IdJADYPkDp

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  191 (1520 expanded)
%              Number of leaves         :   31 ( 461 expanded)
%              Depth                    :   28
%              Number of atoms          : 1954 (24242 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_waybel_0_type,type,(
    r2_waybel_0: $i > $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(m2_yellow_6_type,type,(
    m2_yellow_6: $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(t41_yellow_6,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m2_yellow_6 @ C @ A @ B )
             => ( r1_tarski @ ( k10_yellow_6 @ A @ B ) @ ( k10_yellow_6 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v4_orders_2 @ B )
              & ( v7_waybel_0 @ B )
              & ( l1_waybel_0 @ B @ A ) )
           => ! [C: $i] :
                ( ( m2_yellow_6 @ C @ A @ B )
               => ( r1_tarski @ ( k10_yellow_6 @ A @ B ) @ ( k10_yellow_6 @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t41_yellow_6])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
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

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ( v2_struct_0 @ X15 )
      | ~ ( v4_orders_2 @ X15 )
      | ~ ( v7_waybel_0 @ X15 )
      | ~ ( l1_waybel_0 @ X15 @ X14 )
      | ( m1_subset_1 @ ( k10_yellow_6 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_yellow_6])).

thf('3',plain,
    ( ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','5','6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    m2_yellow_6 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m2_yellow_6,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ~ ( v2_struct_0 @ B )
        & ( v4_orders_2 @ B )
        & ( v7_waybel_0 @ B )
        & ( l1_waybel_0 @ B @ A ) )
     => ! [C: $i] :
          ( ( m2_yellow_6 @ C @ A @ B )
         => ( ~ ( v2_struct_0 @ C )
            & ( v4_orders_2 @ C )
            & ( v7_waybel_0 @ C )
            & ( l1_waybel_0 @ C @ A ) ) ) ) )).

thf('14',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v7_waybel_0 @ X17 )
      | ~ ( l1_waybel_0 @ X17 @ X16 )
      | ( l1_waybel_0 @ X18 @ X16 )
      | ~ ( m2_yellow_6 @ X18 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('15',plain,
    ( ( l1_waybel_0 @ sk_C @ sk_A )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('20',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('21',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( l1_waybel_0 @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16','17','18','21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( l1_waybel_0 @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ( v2_struct_0 @ X15 )
      | ~ ( v4_orders_2 @ X15 )
      | ~ ( v7_waybel_0 @ X15 )
      | ~ ( l1_waybel_0 @ X15 @ X14 )
      | ( m1_subset_1 @ ( k10_yellow_6 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_yellow_6])).

thf('28',plain,
    ( ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v7_waybel_0 @ sk_C )
    | ~ ( v4_orders_2 @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m2_yellow_6 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v7_waybel_0 @ X17 )
      | ~ ( l1_waybel_0 @ X17 @ X16 )
      | ( v7_waybel_0 @ X18 )
      | ~ ( m2_yellow_6 @ X18 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('31',plain,
    ( ( v7_waybel_0 @ sk_C )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('36',plain,
    ( ( v7_waybel_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33','34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v7_waybel_0 @ sk_C ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v7_waybel_0 @ sk_C ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    m2_yellow_6 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v7_waybel_0 @ X17 )
      | ~ ( l1_waybel_0 @ X17 @ X16 )
      | ( v4_orders_2 @ X18 )
      | ~ ( m2_yellow_6 @ X18 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('43',plain,
    ( ( v4_orders_2 @ sk_C )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('48',plain,
    ( ( v4_orders_2 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','44','45','46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v4_orders_2 @ sk_C ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v4_orders_2 @ sk_C ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','40','52','53','54'])).

thf('56',plain,(
    m2_yellow_6 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v7_waybel_0 @ X17 )
      | ~ ( l1_waybel_0 @ X17 @ X16 )
      | ~ ( v2_struct_0 @ X18 )
      | ~ ( m2_yellow_6 @ X18 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('58',plain,
    ( ~ ( v2_struct_0 @ sk_C )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('63',plain,
    ( ~ ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['58','59','60','61','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['55','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf(t7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                 => ( r2_hidden @ D @ C ) ) )
           => ( r1_tarski @ B @ C ) ) ) ) )).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( r1_tarski @ X2 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ X2 @ X1 ) @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m1_subset_1 @ ( sk_D @ ( k10_yellow_6 @ sk_A @ sk_C ) @ X0 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ X0 @ ( k10_yellow_6 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( r1_tarski @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_C ) )
    | ( m1_subset_1 @ ( sk_D @ ( k10_yellow_6 @ sk_A @ sk_C ) @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','72'])).

thf('74',plain,(
    ~ ( r1_tarski @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_subset_1 @ ( sk_D @ ( k10_yellow_6 @ sk_A @ sk_C ) @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf(d18_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( k10_yellow_6 @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_hidden @ D @ C )
                    <=> ! [E: $i] :
                          ( ( m1_connsp_2 @ E @ A @ D )
                         => ( r1_waybel_0 @ A @ B @ E ) ) ) ) ) ) ) ) )).

thf('77',plain,(
    ! [X8: $i,X9: $i,X10: $i,X12: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v4_orders_2 @ X8 )
      | ~ ( v7_waybel_0 @ X8 )
      | ~ ( l1_waybel_0 @ X8 @ X9 )
      | ( X10
       != ( k10_yellow_6 @ X9 @ X8 ) )
      | ( r2_hidden @ X12 @ X10 )
      | ( m1_connsp_2 @ ( sk_E_1 @ X12 @ X8 @ X9 ) @ X9 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d18_yellow_6])).

thf('78',plain,(
    ! [X8: $i,X9: $i,X12: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ ( k10_yellow_6 @ X9 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X9 ) )
      | ( m1_connsp_2 @ ( sk_E_1 @ X12 @ X8 @ X9 ) @ X9 @ X12 )
      | ( r2_hidden @ X12 @ ( k10_yellow_6 @ X9 @ X8 ) )
      | ~ ( l1_waybel_0 @ X8 @ X9 )
      | ~ ( v7_waybel_0 @ X8 )
      | ~ ( v4_orders_2 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( v4_orders_2 @ sk_C )
      | ~ ( v7_waybel_0 @ sk_C )
      | ~ ( l1_waybel_0 @ sk_C @ sk_A )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ sk_C ) )
      | ( m1_connsp_2 @ ( sk_E_1 @ X0 @ sk_C @ sk_A ) @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','78'])).

thf('80',plain,(
    v4_orders_2 @ sk_C ),
    inference(clc,[status(thm)],['50','51'])).

thf('81',plain,(
    v7_waybel_0 @ sk_C ),
    inference(clc,[status(thm)],['38','39'])).

thf('82',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(clc,[status(thm)],['24','25'])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ sk_C ) )
      | ( m1_connsp_2 @ ( sk_E_1 @ X0 @ sk_C @ sk_A ) @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['79','80','81','82','83','84'])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_connsp_2 @ ( sk_E_1 @ ( sk_D @ ( k10_yellow_6 @ sk_A @ sk_C ) @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C @ sk_A ) @ sk_A @ ( sk_D @ ( k10_yellow_6 @ sk_A @ sk_C ) @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ ( sk_D @ ( k10_yellow_6 @ sk_A @ sk_C ) @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k10_yellow_6 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['75','85'])).

thf('87',plain,(
    m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('88',plain,(
    m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( r1_tarski @ X2 @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ ( k10_yellow_6 @ sk_A @ sk_C ) @ X0 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ( r1_tarski @ X0 @ ( k10_yellow_6 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( r1_tarski @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_C ) )
    | ( r2_hidden @ ( sk_D @ ( k10_yellow_6 @ sk_A @ sk_C ) @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['87','90'])).

thf('92',plain,(
    ~ ( r1_tarski @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    r2_hidden @ ( sk_D @ ( k10_yellow_6 @ sk_A @ sk_C ) @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('95',plain,(
    ! [X8: $i,X9: $i,X10: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v4_orders_2 @ X8 )
      | ~ ( v7_waybel_0 @ X8 )
      | ~ ( l1_waybel_0 @ X8 @ X9 )
      | ( X10
       != ( k10_yellow_6 @ X9 @ X8 ) )
      | ~ ( m1_connsp_2 @ X13 @ X9 @ X12 )
      | ( r1_waybel_0 @ X9 @ X8 @ X13 )
      | ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d18_yellow_6])).

thf('96',plain,(
    ! [X8: $i,X9: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ ( k10_yellow_6 @ X9 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X9 ) )
      | ~ ( r2_hidden @ X12 @ ( k10_yellow_6 @ X9 @ X8 ) )
      | ( r1_waybel_0 @ X9 @ X8 @ X13 )
      | ~ ( m1_connsp_2 @ X13 @ X9 @ X12 )
      | ~ ( l1_waybel_0 @ X8 @ X9 )
      | ~ ( v7_waybel_0 @ X8 )
      | ~ ( v4_orders_2 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ~ ( m1_connsp_2 @ X1 @ sk_A @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['94','96'])).

thf('98',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_connsp_2 @ X1 @ sk_A @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['97','98','99','100','101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k10_yellow_6 @ sk_A @ sk_C ) @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ ( sk_D @ ( k10_yellow_6 @ sk_A @ sk_C ) @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['93','103'])).

thf('105',plain,(
    m1_subset_1 @ ( sk_D @ ( k10_yellow_6 @ sk_A @ sk_C ) @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ ( sk_D @ ( k10_yellow_6 @ sk_A @ sk_C ) @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ ( sk_D @ ( k10_yellow_6 @ sk_A @ sk_C ) @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k10_yellow_6 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_0 @ sk_A @ sk_B @ ( sk_E_1 @ ( sk_D @ ( k10_yellow_6 @ sk_A @ sk_C ) @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['86','106'])).

thf('108',plain,
    ( ( r1_waybel_0 @ sk_A @ sk_B @ ( sk_E_1 @ ( sk_D @ ( k10_yellow_6 @ sk_A @ sk_C ) @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ ( k10_yellow_6 @ sk_A @ sk_C ) @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k10_yellow_6 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(clc,[status(thm)],['24','25'])).

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

thf('110',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( l1_waybel_0 @ X4 @ X5 )
      | ( r2_waybel_0 @ X5 @ X4 @ ( k6_subset_1 @ ( u1_struct_0 @ X5 ) @ X6 ) )
      | ( r1_waybel_0 @ X5 @ X4 @ X6 )
      | ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t9_waybel_0])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_C @ X0 )
      | ( r2_waybel_0 @ sk_A @ sk_C @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_C @ X0 )
      | ( r2_waybel_0 @ sk_A @ sk_C @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    m2_yellow_6 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t27_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m2_yellow_6 @ C @ A @ B )
             => ! [D: $i] :
                  ( ( r2_waybel_0 @ A @ C @ D )
                 => ( r2_waybel_0 @ A @ B @ D ) ) ) ) ) )).

thf('115',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v7_waybel_0 @ X19 )
      | ~ ( l1_waybel_0 @ X19 @ X20 )
      | ~ ( r2_waybel_0 @ X20 @ X21 @ X22 )
      | ( r2_waybel_0 @ X20 @ X19 @ X22 )
      | ~ ( m2_yellow_6 @ X21 @ X20 @ X19 )
      | ~ ( l1_struct_0 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t27_yellow_6])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_waybel_0 @ sk_A @ sk_C @ X0 )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('118',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_waybel_0 @ sk_A @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['116','117','118','119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( r1_waybel_0 @ sk_A @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r2_waybel_0 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['113','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( r2_waybel_0 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( l1_waybel_0 @ X4 @ X5 )
      | ~ ( r1_waybel_0 @ X5 @ X4 @ X7 )
      | ~ ( r2_waybel_0 @ X5 @ X4 @ ( k6_subset_1 @ ( u1_struct_0 @ X5 ) @ X7 ) )
      | ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t9_waybel_0])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( r1_waybel_0 @ sk_A @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('127',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( r1_waybel_0 @ sk_A @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['125','126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ ( sk_D @ ( k10_yellow_6 @ sk_A @ sk_C ) @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k10_yellow_6 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( r1_waybel_0 @ sk_A @ sk_C @ ( sk_E_1 @ ( sk_D @ ( k10_yellow_6 @ sk_A @ sk_C ) @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['108','129'])).

thf('131',plain,
    ( ( r1_waybel_0 @ sk_A @ sk_C @ ( sk_E_1 @ ( sk_D @ ( k10_yellow_6 @ sk_A @ sk_C ) @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ ( k10_yellow_6 @ sk_A @ sk_C ) @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k10_yellow_6 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('133',plain,(
    ! [X8: $i,X9: $i,X10: $i,X12: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v4_orders_2 @ X8 )
      | ~ ( v7_waybel_0 @ X8 )
      | ~ ( l1_waybel_0 @ X8 @ X9 )
      | ( X10
       != ( k10_yellow_6 @ X9 @ X8 ) )
      | ( r2_hidden @ X12 @ X10 )
      | ~ ( r1_waybel_0 @ X9 @ X8 @ ( sk_E_1 @ X12 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d18_yellow_6])).

thf('134',plain,(
    ! [X8: $i,X9: $i,X12: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ ( k10_yellow_6 @ X9 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X9 ) )
      | ~ ( r1_waybel_0 @ X9 @ X8 @ ( sk_E_1 @ X12 @ X8 @ X9 ) )
      | ( r2_hidden @ X12 @ ( k10_yellow_6 @ X9 @ X8 ) )
      | ~ ( l1_waybel_0 @ X8 @ X9 )
      | ~ ( v7_waybel_0 @ X8 )
      | ~ ( v4_orders_2 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( v4_orders_2 @ sk_C )
      | ~ ( v7_waybel_0 @ sk_C )
      | ~ ( l1_waybel_0 @ sk_C @ sk_A )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ sk_C ) )
      | ~ ( r1_waybel_0 @ sk_A @ sk_C @ ( sk_E_1 @ X0 @ sk_C @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['132','134'])).

thf('136',plain,(
    v4_orders_2 @ sk_C ),
    inference(clc,[status(thm)],['50','51'])).

thf('137',plain,(
    v7_waybel_0 @ sk_C ),
    inference(clc,[status(thm)],['38','39'])).

thf('138',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(clc,[status(thm)],['24','25'])).

thf('139',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ sk_C ) )
      | ~ ( r1_waybel_0 @ sk_A @ sk_C @ ( sk_E_1 @ X0 @ sk_C @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['135','136','137','138','139','140'])).

thf('142',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ ( sk_D @ ( k10_yellow_6 @ sk_A @ sk_C ) @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k10_yellow_6 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_D @ ( k10_yellow_6 @ sk_A @ sk_C ) @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( k10_yellow_6 @ sk_A @ sk_C ) @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k10_yellow_6 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['131','141'])).

thf('143',plain,(
    m1_subset_1 @ ( sk_D @ ( k10_yellow_6 @ sk_A @ sk_C ) @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('144',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ ( sk_D @ ( k10_yellow_6 @ sk_A @ sk_C ) @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k10_yellow_6 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ ( k10_yellow_6 @ sk_A @ sk_C ) @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k10_yellow_6 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ ( k10_yellow_6 @ sk_A @ sk_C ) @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k10_yellow_6 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,(
    m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('147',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( r1_tarski @ X2 @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('148',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k10_yellow_6 @ sk_A @ sk_C ) @ X0 @ ( u1_struct_0 @ sk_A ) ) @ ( k10_yellow_6 @ sk_A @ sk_C ) )
      | ( r1_tarski @ X0 @ ( k10_yellow_6 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_C ) )
    | ~ ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['145','148'])).

thf('150',plain,(
    m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('151',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,(
    ~ ( r1_tarski @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['153','154'])).

thf('156',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('157',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['155','156'])).

thf('158',plain,(
    $false ),
    inference(demod,[status(thm)],['0','157'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IdJADYPkDp
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:21:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 109 iterations in 0.058s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.20/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.20/0.51  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.20/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.51  thf(r2_waybel_0_type, type, r2_waybel_0: $i > $i > $i > $o).
% 0.20/0.51  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.51  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.20/0.51  thf(m2_yellow_6_type, type, m2_yellow_6: $i > $i > $i > $o).
% 0.20/0.51  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.51  thf(k10_yellow_6_type, type, k10_yellow_6: $i > $i > $i).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.51  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.20/0.51  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.51  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.20/0.51  thf(t41_yellow_6, conjecture,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.20/0.51             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( m2_yellow_6 @ C @ A @ B ) =>
% 0.20/0.51               ( r1_tarski @
% 0.20/0.51                 ( k10_yellow_6 @ A @ B ) @ ( k10_yellow_6 @ A @ C ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i]:
% 0.20/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.51            ( l1_pre_topc @ A ) ) =>
% 0.20/0.51          ( ![B:$i]:
% 0.20/0.51            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.20/0.51                ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.51              ( ![C:$i]:
% 0.20/0.51                ( ( m2_yellow_6 @ C @ A @ B ) =>
% 0.20/0.51                  ( r1_tarski @
% 0.20/0.51                    ( k10_yellow_6 @ A @ B ) @ ( k10_yellow_6 @ A @ C ) ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t41_yellow_6])).
% 0.20/0.51  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(dt_k10_yellow_6, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.51         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 0.20/0.51         ( v4_orders_2 @ B ) & ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.51       ( m1_subset_1 @
% 0.20/0.51         ( k10_yellow_6 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ X14)
% 0.20/0.51          | ~ (v2_pre_topc @ X14)
% 0.20/0.51          | (v2_struct_0 @ X14)
% 0.20/0.51          | (v2_struct_0 @ X15)
% 0.20/0.51          | ~ (v4_orders_2 @ X15)
% 0.20/0.51          | ~ (v7_waybel_0 @ X15)
% 0.20/0.51          | ~ (l1_waybel_0 @ X15 @ X14)
% 0.20/0.51          | (m1_subset_1 @ (k10_yellow_6 @ X14 @ X15) @ 
% 0.20/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k10_yellow_6])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (((m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_B) @ 
% 0.20/0.51         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51        | ~ (v7_waybel_0 @ sk_B)
% 0.20/0.51        | ~ (v4_orders_2 @ sk_B)
% 0.20/0.51        | (v2_struct_0 @ sk_B)
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.51  thf('4', plain, ((v7_waybel_0 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('5', plain, ((v4_orders_2 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('6', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (((m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_B) @ 
% 0.20/0.51         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51        | (v2_struct_0 @ sk_B)
% 0.20/0.51        | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['3', '4', '5', '6', '7'])).
% 0.20/0.51  thf('9', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_B) @ 
% 0.20/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('clc', [status(thm)], ['8', '9'])).
% 0.20/0.51  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      ((m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_B) @ 
% 0.20/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('clc', [status(thm)], ['10', '11'])).
% 0.20/0.51  thf('13', plain, ((m2_yellow_6 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(dt_m2_yellow_6, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.20/0.51         ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.20/0.51         ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.51       ( ![C:$i]:
% 0.20/0.51         ( ( m2_yellow_6 @ C @ A @ B ) =>
% 0.20/0.51           ( ( ~( v2_struct_0 @ C ) ) & ( v4_orders_2 @ C ) & 
% 0.20/0.51             ( v7_waybel_0 @ C ) & ( l1_waybel_0 @ C @ A ) ) ) ) ))).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.51         (~ (l1_struct_0 @ X16)
% 0.20/0.51          | (v2_struct_0 @ X16)
% 0.20/0.51          | (v2_struct_0 @ X17)
% 0.20/0.51          | ~ (v4_orders_2 @ X17)
% 0.20/0.51          | ~ (v7_waybel_0 @ X17)
% 0.20/0.51          | ~ (l1_waybel_0 @ X17 @ X16)
% 0.20/0.51          | (l1_waybel_0 @ X18 @ X16)
% 0.20/0.51          | ~ (m2_yellow_6 @ X18 @ X16 @ X17))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (((l1_waybel_0 @ sk_C @ sk_A)
% 0.20/0.51        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.20/0.51        | ~ (v7_waybel_0 @ sk_B)
% 0.20/0.51        | ~ (v4_orders_2 @ sk_B)
% 0.20/0.51        | (v2_struct_0 @ sk_B)
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.51  thf('16', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('17', plain, ((v7_waybel_0 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('18', plain, ((v4_orders_2 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(dt_l1_pre_topc, axiom,
% 0.20/0.51    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.51  thf('20', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.51  thf('21', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (((l1_waybel_0 @ sk_C @ sk_A)
% 0.20/0.51        | (v2_struct_0 @ sk_B)
% 0.20/0.51        | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['15', '16', '17', '18', '21'])).
% 0.20/0.51  thf('23', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('24', plain, (((v2_struct_0 @ sk_A) | (l1_waybel_0 @ sk_C @ sk_A))),
% 0.20/0.51      inference('clc', [status(thm)], ['22', '23'])).
% 0.20/0.51  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('26', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 0.20/0.51      inference('clc', [status(thm)], ['24', '25'])).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ X14)
% 0.20/0.51          | ~ (v2_pre_topc @ X14)
% 0.20/0.51          | (v2_struct_0 @ X14)
% 0.20/0.51          | (v2_struct_0 @ X15)
% 0.20/0.51          | ~ (v4_orders_2 @ X15)
% 0.20/0.51          | ~ (v7_waybel_0 @ X15)
% 0.20/0.51          | ~ (l1_waybel_0 @ X15 @ X14)
% 0.20/0.51          | (m1_subset_1 @ (k10_yellow_6 @ X14 @ X15) @ 
% 0.20/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k10_yellow_6])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      (((m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_C) @ 
% 0.20/0.51         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51        | ~ (v7_waybel_0 @ sk_C)
% 0.20/0.51        | ~ (v4_orders_2 @ sk_C)
% 0.20/0.51        | (v2_struct_0 @ sk_C)
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.51  thf('29', plain, ((m2_yellow_6 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.51         (~ (l1_struct_0 @ X16)
% 0.20/0.51          | (v2_struct_0 @ X16)
% 0.20/0.51          | (v2_struct_0 @ X17)
% 0.20/0.51          | ~ (v4_orders_2 @ X17)
% 0.20/0.51          | ~ (v7_waybel_0 @ X17)
% 0.20/0.51          | ~ (l1_waybel_0 @ X17 @ X16)
% 0.20/0.51          | (v7_waybel_0 @ X18)
% 0.20/0.51          | ~ (m2_yellow_6 @ X18 @ X16 @ X17))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      (((v7_waybel_0 @ sk_C)
% 0.20/0.51        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.20/0.51        | ~ (v7_waybel_0 @ sk_B)
% 0.20/0.51        | ~ (v4_orders_2 @ sk_B)
% 0.20/0.51        | (v2_struct_0 @ sk_B)
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.51  thf('32', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('33', plain, ((v7_waybel_0 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('34', plain, ((v4_orders_2 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('35', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      (((v7_waybel_0 @ sk_C) | (v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['31', '32', '33', '34', '35'])).
% 0.20/0.51  thf('37', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('38', plain, (((v2_struct_0 @ sk_A) | (v7_waybel_0 @ sk_C))),
% 0.20/0.51      inference('clc', [status(thm)], ['36', '37'])).
% 0.20/0.51  thf('39', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('40', plain, ((v7_waybel_0 @ sk_C)),
% 0.20/0.51      inference('clc', [status(thm)], ['38', '39'])).
% 0.20/0.51  thf('41', plain, ((m2_yellow_6 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.51         (~ (l1_struct_0 @ X16)
% 0.20/0.51          | (v2_struct_0 @ X16)
% 0.20/0.51          | (v2_struct_0 @ X17)
% 0.20/0.51          | ~ (v4_orders_2 @ X17)
% 0.20/0.51          | ~ (v7_waybel_0 @ X17)
% 0.20/0.51          | ~ (l1_waybel_0 @ X17 @ X16)
% 0.20/0.51          | (v4_orders_2 @ X18)
% 0.20/0.51          | ~ (m2_yellow_6 @ X18 @ X16 @ X17))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      (((v4_orders_2 @ sk_C)
% 0.20/0.51        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.20/0.51        | ~ (v7_waybel_0 @ sk_B)
% 0.20/0.51        | ~ (v4_orders_2 @ sk_B)
% 0.20/0.51        | (v2_struct_0 @ sk_B)
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.51  thf('44', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('45', plain, ((v7_waybel_0 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('46', plain, ((v4_orders_2 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('47', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.51  thf('48', plain,
% 0.20/0.51      (((v4_orders_2 @ sk_C) | (v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['43', '44', '45', '46', '47'])).
% 0.20/0.51  thf('49', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('50', plain, (((v2_struct_0 @ sk_A) | (v4_orders_2 @ sk_C))),
% 0.20/0.51      inference('clc', [status(thm)], ['48', '49'])).
% 0.20/0.51  thf('51', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('52', plain, ((v4_orders_2 @ sk_C)),
% 0.20/0.51      inference('clc', [status(thm)], ['50', '51'])).
% 0.20/0.51  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('55', plain,
% 0.20/0.51      (((m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_C) @ 
% 0.20/0.51         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51        | (v2_struct_0 @ sk_C)
% 0.20/0.51        | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['28', '40', '52', '53', '54'])).
% 0.20/0.51  thf('56', plain, ((m2_yellow_6 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('57', plain,
% 0.20/0.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.51         (~ (l1_struct_0 @ X16)
% 0.20/0.51          | (v2_struct_0 @ X16)
% 0.20/0.51          | (v2_struct_0 @ X17)
% 0.20/0.51          | ~ (v4_orders_2 @ X17)
% 0.20/0.51          | ~ (v7_waybel_0 @ X17)
% 0.20/0.51          | ~ (l1_waybel_0 @ X17 @ X16)
% 0.20/0.51          | ~ (v2_struct_0 @ X18)
% 0.20/0.51          | ~ (m2_yellow_6 @ X18 @ X16 @ X17))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 0.20/0.51  thf('58', plain,
% 0.20/0.51      ((~ (v2_struct_0 @ sk_C)
% 0.20/0.51        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.20/0.51        | ~ (v7_waybel_0 @ sk_B)
% 0.20/0.51        | ~ (v4_orders_2 @ sk_B)
% 0.20/0.51        | (v2_struct_0 @ sk_B)
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['56', '57'])).
% 0.20/0.51  thf('59', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('60', plain, ((v7_waybel_0 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('61', plain, ((v4_orders_2 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('62', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.51  thf('63', plain,
% 0.20/0.51      ((~ (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['58', '59', '60', '61', '62'])).
% 0.20/0.51  thf('64', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('65', plain, (((v2_struct_0 @ sk_A) | ~ (v2_struct_0 @ sk_C))),
% 0.20/0.51      inference('clc', [status(thm)], ['63', '64'])).
% 0.20/0.51  thf('66', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('67', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.51      inference('clc', [status(thm)], ['65', '66'])).
% 0.20/0.51  thf('68', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_C) @ 
% 0.20/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('clc', [status(thm)], ['55', '67'])).
% 0.20/0.51  thf('69', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('70', plain,
% 0.20/0.51      ((m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_C) @ 
% 0.20/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('clc', [status(thm)], ['68', '69'])).
% 0.20/0.51  thf(t7_subset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.51       ( ![C:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.51           ( ( ![D:$i]:
% 0.20/0.51               ( ( m1_subset_1 @ D @ A ) =>
% 0.20/0.51                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 0.20/0.51             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.20/0.51  thf('71', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.20/0.51          | (r1_tarski @ X2 @ X0)
% 0.20/0.51          | (m1_subset_1 @ (sk_D @ X0 @ X2 @ X1) @ X1)
% 0.20/0.51          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.20/0.51  thf('72', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51          | (m1_subset_1 @ 
% 0.20/0.51             (sk_D @ (k10_yellow_6 @ sk_A @ sk_C) @ X0 @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.51             (u1_struct_0 @ sk_A))
% 0.20/0.51          | (r1_tarski @ X0 @ (k10_yellow_6 @ sk_A @ sk_C)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['70', '71'])).
% 0.20/0.51  thf('73', plain,
% 0.20/0.51      (((r1_tarski @ (k10_yellow_6 @ sk_A @ sk_B) @ 
% 0.20/0.51         (k10_yellow_6 @ sk_A @ sk_C))
% 0.20/0.51        | (m1_subset_1 @ 
% 0.20/0.51           (sk_D @ (k10_yellow_6 @ sk_A @ sk_C) @ 
% 0.20/0.51            (k10_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.51           (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['12', '72'])).
% 0.20/0.51  thf('74', plain,
% 0.20/0.51      (~ (r1_tarski @ (k10_yellow_6 @ sk_A @ sk_B) @ 
% 0.20/0.51          (k10_yellow_6 @ sk_A @ sk_C))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('75', plain,
% 0.20/0.51      ((m1_subset_1 @ 
% 0.20/0.51        (sk_D @ (k10_yellow_6 @ sk_A @ sk_C) @ (k10_yellow_6 @ sk_A @ sk_B) @ 
% 0.20/0.51         (u1_struct_0 @ sk_A)) @ 
% 0.20/0.51        (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('clc', [status(thm)], ['73', '74'])).
% 0.20/0.51  thf('76', plain,
% 0.20/0.51      ((m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_C) @ 
% 0.20/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('clc', [status(thm)], ['68', '69'])).
% 0.20/0.51  thf(d18_yellow_6, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.20/0.51             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51               ( ( ( C ) = ( k10_yellow_6 @ A @ B ) ) <=>
% 0.20/0.51                 ( ![D:$i]:
% 0.20/0.51                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.51                     ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.51                       ( ![E:$i]:
% 0.20/0.51                         ( ( m1_connsp_2 @ E @ A @ D ) =>
% 0.20/0.51                           ( r1_waybel_0 @ A @ B @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('77', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i, X10 : $i, X12 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X8)
% 0.20/0.51          | ~ (v4_orders_2 @ X8)
% 0.20/0.51          | ~ (v7_waybel_0 @ X8)
% 0.20/0.51          | ~ (l1_waybel_0 @ X8 @ X9)
% 0.20/0.51          | ((X10) != (k10_yellow_6 @ X9 @ X8))
% 0.20/0.51          | (r2_hidden @ X12 @ X10)
% 0.20/0.51          | (m1_connsp_2 @ (sk_E_1 @ X12 @ X8 @ X9) @ X9 @ X12)
% 0.20/0.51          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X9))
% 0.20/0.51          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.51          | ~ (l1_pre_topc @ X9)
% 0.20/0.51          | ~ (v2_pre_topc @ X9)
% 0.20/0.51          | (v2_struct_0 @ X9))),
% 0.20/0.51      inference('cnf', [status(esa)], [d18_yellow_6])).
% 0.20/0.51  thf('78', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i, X12 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X9)
% 0.20/0.51          | ~ (v2_pre_topc @ X9)
% 0.20/0.51          | ~ (l1_pre_topc @ X9)
% 0.20/0.51          | ~ (m1_subset_1 @ (k10_yellow_6 @ X9 @ X8) @ 
% 0.20/0.51               (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.51          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X9))
% 0.20/0.51          | (m1_connsp_2 @ (sk_E_1 @ X12 @ X8 @ X9) @ X9 @ X12)
% 0.20/0.51          | (r2_hidden @ X12 @ (k10_yellow_6 @ X9 @ X8))
% 0.20/0.51          | ~ (l1_waybel_0 @ X8 @ X9)
% 0.20/0.51          | ~ (v7_waybel_0 @ X8)
% 0.20/0.51          | ~ (v4_orders_2 @ X8)
% 0.20/0.51          | (v2_struct_0 @ X8))),
% 0.20/0.51      inference('simplify', [status(thm)], ['77'])).
% 0.20/0.51  thf('79', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_C)
% 0.20/0.51          | ~ (v4_orders_2 @ sk_C)
% 0.20/0.51          | ~ (v7_waybel_0 @ sk_C)
% 0.20/0.51          | ~ (l1_waybel_0 @ sk_C @ sk_A)
% 0.20/0.51          | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ sk_C))
% 0.20/0.51          | (m1_connsp_2 @ (sk_E_1 @ X0 @ sk_C @ sk_A) @ sk_A @ X0)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51          | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['76', '78'])).
% 0.20/0.51  thf('80', plain, ((v4_orders_2 @ sk_C)),
% 0.20/0.51      inference('clc', [status(thm)], ['50', '51'])).
% 0.20/0.51  thf('81', plain, ((v7_waybel_0 @ sk_C)),
% 0.20/0.51      inference('clc', [status(thm)], ['38', '39'])).
% 0.20/0.51  thf('82', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 0.20/0.51      inference('clc', [status(thm)], ['24', '25'])).
% 0.20/0.51  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('84', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('85', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_C)
% 0.20/0.51          | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ sk_C))
% 0.20/0.51          | (m1_connsp_2 @ (sk_E_1 @ X0 @ sk_C @ sk_A) @ sk_A @ X0)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['79', '80', '81', '82', '83', '84'])).
% 0.20/0.51  thf('86', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | (m1_connsp_2 @ 
% 0.20/0.51           (sk_E_1 @ 
% 0.20/0.51            (sk_D @ (k10_yellow_6 @ sk_A @ sk_C) @ 
% 0.20/0.51             (k10_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.51            sk_C @ sk_A) @ 
% 0.20/0.51           sk_A @ 
% 0.20/0.51           (sk_D @ (k10_yellow_6 @ sk_A @ sk_C) @ 
% 0.20/0.51            (k10_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))
% 0.20/0.51        | (r2_hidden @ 
% 0.20/0.51           (sk_D @ (k10_yellow_6 @ sk_A @ sk_C) @ 
% 0.20/0.51            (k10_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.51           (k10_yellow_6 @ sk_A @ sk_C))
% 0.20/0.51        | (v2_struct_0 @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['75', '85'])).
% 0.20/0.51  thf('87', plain,
% 0.20/0.51      ((m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_B) @ 
% 0.20/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('clc', [status(thm)], ['10', '11'])).
% 0.20/0.51  thf('88', plain,
% 0.20/0.51      ((m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_C) @ 
% 0.20/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('clc', [status(thm)], ['68', '69'])).
% 0.20/0.51  thf('89', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.20/0.51          | (r1_tarski @ X2 @ X0)
% 0.20/0.51          | (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X2)
% 0.20/0.51          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.20/0.51  thf('90', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51          | (r2_hidden @ 
% 0.20/0.51             (sk_D @ (k10_yellow_6 @ sk_A @ sk_C) @ X0 @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.51             X0)
% 0.20/0.51          | (r1_tarski @ X0 @ (k10_yellow_6 @ sk_A @ sk_C)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['88', '89'])).
% 0.20/0.51  thf('91', plain,
% 0.20/0.51      (((r1_tarski @ (k10_yellow_6 @ sk_A @ sk_B) @ 
% 0.20/0.51         (k10_yellow_6 @ sk_A @ sk_C))
% 0.20/0.51        | (r2_hidden @ 
% 0.20/0.51           (sk_D @ (k10_yellow_6 @ sk_A @ sk_C) @ 
% 0.20/0.51            (k10_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.51           (k10_yellow_6 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['87', '90'])).
% 0.20/0.51  thf('92', plain,
% 0.20/0.51      (~ (r1_tarski @ (k10_yellow_6 @ sk_A @ sk_B) @ 
% 0.20/0.51          (k10_yellow_6 @ sk_A @ sk_C))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('93', plain,
% 0.20/0.51      ((r2_hidden @ 
% 0.20/0.51        (sk_D @ (k10_yellow_6 @ sk_A @ sk_C) @ (k10_yellow_6 @ sk_A @ sk_B) @ 
% 0.20/0.51         (u1_struct_0 @ sk_A)) @ 
% 0.20/0.51        (k10_yellow_6 @ sk_A @ sk_B))),
% 0.20/0.51      inference('clc', [status(thm)], ['91', '92'])).
% 0.20/0.51  thf('94', plain,
% 0.20/0.51      ((m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_B) @ 
% 0.20/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('clc', [status(thm)], ['10', '11'])).
% 0.20/0.51  thf('95', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i, X10 : $i, X12 : $i, X13 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X8)
% 0.20/0.51          | ~ (v4_orders_2 @ X8)
% 0.20/0.51          | ~ (v7_waybel_0 @ X8)
% 0.20/0.51          | ~ (l1_waybel_0 @ X8 @ X9)
% 0.20/0.51          | ((X10) != (k10_yellow_6 @ X9 @ X8))
% 0.20/0.51          | ~ (m1_connsp_2 @ X13 @ X9 @ X12)
% 0.20/0.51          | (r1_waybel_0 @ X9 @ X8 @ X13)
% 0.20/0.51          | ~ (r2_hidden @ X12 @ X10)
% 0.20/0.51          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X9))
% 0.20/0.51          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.51          | ~ (l1_pre_topc @ X9)
% 0.20/0.51          | ~ (v2_pre_topc @ X9)
% 0.20/0.51          | (v2_struct_0 @ X9))),
% 0.20/0.51      inference('cnf', [status(esa)], [d18_yellow_6])).
% 0.20/0.51  thf('96', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i, X12 : $i, X13 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X9)
% 0.20/0.51          | ~ (v2_pre_topc @ X9)
% 0.20/0.51          | ~ (l1_pre_topc @ X9)
% 0.20/0.51          | ~ (m1_subset_1 @ (k10_yellow_6 @ X9 @ X8) @ 
% 0.20/0.51               (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.51          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X9))
% 0.20/0.51          | ~ (r2_hidden @ X12 @ (k10_yellow_6 @ X9 @ X8))
% 0.20/0.51          | (r1_waybel_0 @ X9 @ X8 @ X13)
% 0.20/0.51          | ~ (m1_connsp_2 @ X13 @ X9 @ X12)
% 0.20/0.51          | ~ (l1_waybel_0 @ X8 @ X9)
% 0.20/0.51          | ~ (v7_waybel_0 @ X8)
% 0.20/0.51          | ~ (v4_orders_2 @ X8)
% 0.20/0.51          | (v2_struct_0 @ X8))),
% 0.20/0.51      inference('simplify', [status(thm)], ['95'])).
% 0.20/0.51  thf('97', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_B)
% 0.20/0.51          | ~ (v4_orders_2 @ sk_B)
% 0.20/0.51          | ~ (v7_waybel_0 @ sk_B)
% 0.20/0.51          | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.20/0.51          | ~ (m1_connsp_2 @ X1 @ sk_A @ X0)
% 0.20/0.51          | (r1_waybel_0 @ sk_A @ sk_B @ X1)
% 0.20/0.51          | ~ (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51          | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['94', '96'])).
% 0.20/0.51  thf('98', plain, ((v4_orders_2 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('99', plain, ((v7_waybel_0 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('100', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('102', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('103', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_B)
% 0.20/0.51          | ~ (m1_connsp_2 @ X1 @ sk_A @ X0)
% 0.20/0.51          | (r1_waybel_0 @ sk_A @ sk_B @ X1)
% 0.20/0.51          | ~ (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['97', '98', '99', '100', '101', '102'])).
% 0.20/0.51  thf('104', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | ~ (m1_subset_1 @ 
% 0.20/0.51               (sk_D @ (k10_yellow_6 @ sk_A @ sk_C) @ 
% 0.20/0.51                (k10_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.51               (u1_struct_0 @ sk_A))
% 0.20/0.51          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.20/0.51          | ~ (m1_connsp_2 @ X0 @ sk_A @ 
% 0.20/0.51               (sk_D @ (k10_yellow_6 @ sk_A @ sk_C) @ 
% 0.20/0.51                (k10_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))
% 0.20/0.51          | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['93', '103'])).
% 0.20/0.51  thf('105', plain,
% 0.20/0.51      ((m1_subset_1 @ 
% 0.20/0.51        (sk_D @ (k10_yellow_6 @ sk_A @ sk_C) @ (k10_yellow_6 @ sk_A @ sk_B) @ 
% 0.20/0.51         (u1_struct_0 @ sk_A)) @ 
% 0.20/0.51        (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('clc', [status(thm)], ['73', '74'])).
% 0.20/0.51  thf('106', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.20/0.51          | ~ (m1_connsp_2 @ X0 @ sk_A @ 
% 0.20/0.51               (sk_D @ (k10_yellow_6 @ sk_A @ sk_C) @ 
% 0.20/0.51                (k10_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))
% 0.20/0.51          | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['104', '105'])).
% 0.20/0.51  thf('107', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_C)
% 0.20/0.51        | (r2_hidden @ 
% 0.20/0.51           (sk_D @ (k10_yellow_6 @ sk_A @ sk_C) @ 
% 0.20/0.51            (k10_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.51           (k10_yellow_6 @ sk_A @ sk_C))
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | (v2_struct_0 @ sk_B)
% 0.20/0.51        | (r1_waybel_0 @ sk_A @ sk_B @ 
% 0.20/0.51           (sk_E_1 @ 
% 0.20/0.51            (sk_D @ (k10_yellow_6 @ sk_A @ sk_C) @ 
% 0.20/0.51             (k10_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.51            sk_C @ sk_A))
% 0.20/0.51        | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['86', '106'])).
% 0.20/0.51  thf('108', plain,
% 0.20/0.51      (((r1_waybel_0 @ sk_A @ sk_B @ 
% 0.20/0.51         (sk_E_1 @ 
% 0.20/0.51          (sk_D @ (k10_yellow_6 @ sk_A @ sk_C) @ 
% 0.20/0.51           (k10_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.51          sk_C @ sk_A))
% 0.20/0.51        | (v2_struct_0 @ sk_B)
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | (r2_hidden @ 
% 0.20/0.51           (sk_D @ (k10_yellow_6 @ sk_A @ sk_C) @ 
% 0.20/0.51            (k10_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.51           (k10_yellow_6 @ sk_A @ sk_C))
% 0.20/0.51        | (v2_struct_0 @ sk_C))),
% 0.20/0.51      inference('simplify', [status(thm)], ['107'])).
% 0.20/0.51  thf('109', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 0.20/0.51      inference('clc', [status(thm)], ['24', '25'])).
% 0.20/0.51  thf(t9_waybel_0, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( r1_waybel_0 @ A @ B @ C ) <=>
% 0.20/0.51               ( ~( r2_waybel_0 @
% 0.20/0.51                    A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('110', plain,
% 0.20/0.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X4)
% 0.20/0.51          | ~ (l1_waybel_0 @ X4 @ X5)
% 0.20/0.51          | (r2_waybel_0 @ X5 @ X4 @ (k6_subset_1 @ (u1_struct_0 @ X5) @ X6))
% 0.20/0.51          | (r1_waybel_0 @ X5 @ X4 @ X6)
% 0.20/0.51          | ~ (l1_struct_0 @ X5)
% 0.20/0.51          | (v2_struct_0 @ X5))),
% 0.20/0.51      inference('cnf', [status(esa)], [t9_waybel_0])).
% 0.20/0.51  thf('111', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | ~ (l1_struct_0 @ sk_A)
% 0.20/0.51          | (r1_waybel_0 @ sk_A @ sk_C @ X0)
% 0.20/0.51          | (r2_waybel_0 @ sk_A @ sk_C @ 
% 0.20/0.51             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.20/0.51          | (v2_struct_0 @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['109', '110'])).
% 0.20/0.51  thf('112', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.51  thf('113', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | (r1_waybel_0 @ sk_A @ sk_C @ X0)
% 0.20/0.51          | (r2_waybel_0 @ sk_A @ sk_C @ 
% 0.20/0.51             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.20/0.51          | (v2_struct_0 @ sk_C))),
% 0.20/0.51      inference('demod', [status(thm)], ['111', '112'])).
% 0.20/0.51  thf('114', plain, ((m2_yellow_6 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t27_yellow_6, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.20/0.51             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( m2_yellow_6 @ C @ A @ B ) =>
% 0.20/0.51               ( ![D:$i]:
% 0.20/0.51                 ( ( r2_waybel_0 @ A @ C @ D ) => ( r2_waybel_0 @ A @ B @ D ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('115', plain,
% 0.20/0.51      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X19)
% 0.20/0.51          | ~ (v4_orders_2 @ X19)
% 0.20/0.51          | ~ (v7_waybel_0 @ X19)
% 0.20/0.51          | ~ (l1_waybel_0 @ X19 @ X20)
% 0.20/0.51          | ~ (r2_waybel_0 @ X20 @ X21 @ X22)
% 0.20/0.51          | (r2_waybel_0 @ X20 @ X19 @ X22)
% 0.20/0.51          | ~ (m2_yellow_6 @ X21 @ X20 @ X19)
% 0.20/0.51          | ~ (l1_struct_0 @ X20)
% 0.20/0.51          | (v2_struct_0 @ X20))),
% 0.20/0.51      inference('cnf', [status(esa)], [t27_yellow_6])).
% 0.20/0.51  thf('116', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | ~ (l1_struct_0 @ sk_A)
% 0.20/0.51          | (r2_waybel_0 @ sk_A @ sk_B @ X0)
% 0.20/0.51          | ~ (r2_waybel_0 @ sk_A @ sk_C @ X0)
% 0.20/0.51          | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.20/0.51          | ~ (v7_waybel_0 @ sk_B)
% 0.20/0.51          | ~ (v4_orders_2 @ sk_B)
% 0.20/0.51          | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['114', '115'])).
% 0.20/0.51  thf('117', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.51  thf('118', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('119', plain, ((v7_waybel_0 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('120', plain, ((v4_orders_2 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('121', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | (r2_waybel_0 @ sk_A @ sk_B @ X0)
% 0.20/0.51          | ~ (r2_waybel_0 @ sk_A @ sk_C @ X0)
% 0.20/0.51          | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['116', '117', '118', '119', '120'])).
% 0.20/0.51  thf('122', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_C)
% 0.20/0.51          | (r1_waybel_0 @ sk_A @ sk_C @ X0)
% 0.20/0.51          | (v2_struct_0 @ sk_A)
% 0.20/0.51          | (v2_struct_0 @ sk_B)
% 0.20/0.51          | (r2_waybel_0 @ sk_A @ sk_B @ 
% 0.20/0.51             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.20/0.51          | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['113', '121'])).
% 0.20/0.51  thf('123', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r2_waybel_0 @ sk_A @ sk_B @ 
% 0.20/0.51           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.20/0.51          | (v2_struct_0 @ sk_B)
% 0.20/0.51          | (v2_struct_0 @ sk_A)
% 0.20/0.51          | (r1_waybel_0 @ sk_A @ sk_C @ X0)
% 0.20/0.51          | (v2_struct_0 @ sk_C))),
% 0.20/0.51      inference('simplify', [status(thm)], ['122'])).
% 0.20/0.51  thf('124', plain,
% 0.20/0.51      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X4)
% 0.20/0.51          | ~ (l1_waybel_0 @ X4 @ X5)
% 0.20/0.51          | ~ (r1_waybel_0 @ X5 @ X4 @ X7)
% 0.20/0.51          | ~ (r2_waybel_0 @ X5 @ X4 @ (k6_subset_1 @ (u1_struct_0 @ X5) @ X7))
% 0.20/0.51          | ~ (l1_struct_0 @ X5)
% 0.20/0.51          | (v2_struct_0 @ X5))),
% 0.20/0.51      inference('cnf', [status(esa)], [t9_waybel_0])).
% 0.20/0.51  thf('125', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_C)
% 0.20/0.51          | (r1_waybel_0 @ sk_A @ sk_C @ X0)
% 0.20/0.51          | (v2_struct_0 @ sk_A)
% 0.20/0.51          | (v2_struct_0 @ sk_B)
% 0.20/0.51          | (v2_struct_0 @ sk_A)
% 0.20/0.51          | ~ (l1_struct_0 @ sk_A)
% 0.20/0.51          | ~ (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.20/0.51          | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.20/0.51          | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['123', '124'])).
% 0.20/0.51  thf('126', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.51  thf('127', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('128', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_C)
% 0.20/0.51          | (r1_waybel_0 @ sk_A @ sk_C @ X0)
% 0.20/0.51          | (v2_struct_0 @ sk_A)
% 0.20/0.51          | (v2_struct_0 @ sk_B)
% 0.20/0.51          | (v2_struct_0 @ sk_A)
% 0.20/0.51          | ~ (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.20/0.51          | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['125', '126', '127'])).
% 0.20/0.51  thf('129', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.20/0.51          | (v2_struct_0 @ sk_B)
% 0.20/0.51          | (v2_struct_0 @ sk_A)
% 0.20/0.51          | (r1_waybel_0 @ sk_A @ sk_C @ X0)
% 0.20/0.51          | (v2_struct_0 @ sk_C))),
% 0.20/0.51      inference('simplify', [status(thm)], ['128'])).
% 0.20/0.51  thf('130', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_C)
% 0.20/0.51        | (r2_hidden @ 
% 0.20/0.51           (sk_D @ (k10_yellow_6 @ sk_A @ sk_C) @ 
% 0.20/0.51            (k10_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.51           (k10_yellow_6 @ sk_A @ sk_C))
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | (v2_struct_0 @ sk_B)
% 0.20/0.51        | (v2_struct_0 @ sk_C)
% 0.20/0.51        | (r1_waybel_0 @ sk_A @ sk_C @ 
% 0.20/0.51           (sk_E_1 @ 
% 0.20/0.51            (sk_D @ (k10_yellow_6 @ sk_A @ sk_C) @ 
% 0.20/0.51             (k10_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.51            sk_C @ sk_A))
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['108', '129'])).
% 0.20/0.51  thf('131', plain,
% 0.20/0.51      (((r1_waybel_0 @ sk_A @ sk_C @ 
% 0.20/0.51         (sk_E_1 @ 
% 0.20/0.51          (sk_D @ (k10_yellow_6 @ sk_A @ sk_C) @ 
% 0.20/0.51           (k10_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.51          sk_C @ sk_A))
% 0.20/0.51        | (v2_struct_0 @ sk_B)
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | (r2_hidden @ 
% 0.20/0.51           (sk_D @ (k10_yellow_6 @ sk_A @ sk_C) @ 
% 0.20/0.51            (k10_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.51           (k10_yellow_6 @ sk_A @ sk_C))
% 0.20/0.51        | (v2_struct_0 @ sk_C))),
% 0.20/0.51      inference('simplify', [status(thm)], ['130'])).
% 0.20/0.51  thf('132', plain,
% 0.20/0.51      ((m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_C) @ 
% 0.20/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('clc', [status(thm)], ['68', '69'])).
% 0.20/0.51  thf('133', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i, X10 : $i, X12 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X8)
% 0.20/0.51          | ~ (v4_orders_2 @ X8)
% 0.20/0.51          | ~ (v7_waybel_0 @ X8)
% 0.20/0.51          | ~ (l1_waybel_0 @ X8 @ X9)
% 0.20/0.51          | ((X10) != (k10_yellow_6 @ X9 @ X8))
% 0.20/0.51          | (r2_hidden @ X12 @ X10)
% 0.20/0.51          | ~ (r1_waybel_0 @ X9 @ X8 @ (sk_E_1 @ X12 @ X8 @ X9))
% 0.20/0.51          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X9))
% 0.20/0.51          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.51          | ~ (l1_pre_topc @ X9)
% 0.20/0.51          | ~ (v2_pre_topc @ X9)
% 0.20/0.51          | (v2_struct_0 @ X9))),
% 0.20/0.51      inference('cnf', [status(esa)], [d18_yellow_6])).
% 0.20/0.51  thf('134', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i, X12 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X9)
% 0.20/0.51          | ~ (v2_pre_topc @ X9)
% 0.20/0.51          | ~ (l1_pre_topc @ X9)
% 0.20/0.51          | ~ (m1_subset_1 @ (k10_yellow_6 @ X9 @ X8) @ 
% 0.20/0.51               (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.51          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X9))
% 0.20/0.51          | ~ (r1_waybel_0 @ X9 @ X8 @ (sk_E_1 @ X12 @ X8 @ X9))
% 0.20/0.51          | (r2_hidden @ X12 @ (k10_yellow_6 @ X9 @ X8))
% 0.20/0.51          | ~ (l1_waybel_0 @ X8 @ X9)
% 0.20/0.51          | ~ (v7_waybel_0 @ X8)
% 0.20/0.51          | ~ (v4_orders_2 @ X8)
% 0.20/0.51          | (v2_struct_0 @ X8))),
% 0.20/0.51      inference('simplify', [status(thm)], ['133'])).
% 0.20/0.51  thf('135', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_C)
% 0.20/0.51          | ~ (v4_orders_2 @ sk_C)
% 0.20/0.51          | ~ (v7_waybel_0 @ sk_C)
% 0.20/0.51          | ~ (l1_waybel_0 @ sk_C @ sk_A)
% 0.20/0.51          | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ sk_C))
% 0.20/0.51          | ~ (r1_waybel_0 @ sk_A @ sk_C @ (sk_E_1 @ X0 @ sk_C @ sk_A))
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51          | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['132', '134'])).
% 0.20/0.51  thf('136', plain, ((v4_orders_2 @ sk_C)),
% 0.20/0.51      inference('clc', [status(thm)], ['50', '51'])).
% 0.20/0.51  thf('137', plain, ((v7_waybel_0 @ sk_C)),
% 0.20/0.51      inference('clc', [status(thm)], ['38', '39'])).
% 0.20/0.51  thf('138', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 0.20/0.51      inference('clc', [status(thm)], ['24', '25'])).
% 0.20/0.51  thf('139', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('140', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('141', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_C)
% 0.20/0.51          | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ sk_C))
% 0.20/0.51          | ~ (r1_waybel_0 @ sk_A @ sk_C @ (sk_E_1 @ X0 @ sk_C @ sk_A))
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)],
% 0.20/0.51                ['135', '136', '137', '138', '139', '140'])).
% 0.20/0.51  thf('142', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_C)
% 0.20/0.51        | (r2_hidden @ 
% 0.20/0.51           (sk_D @ (k10_yellow_6 @ sk_A @ sk_C) @ 
% 0.20/0.51            (k10_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.51           (k10_yellow_6 @ sk_A @ sk_C))
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | (v2_struct_0 @ sk_B)
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | ~ (m1_subset_1 @ 
% 0.20/0.51             (sk_D @ (k10_yellow_6 @ sk_A @ sk_C) @ 
% 0.20/0.51              (k10_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.51             (u1_struct_0 @ sk_A))
% 0.20/0.51        | (r2_hidden @ 
% 0.20/0.51           (sk_D @ (k10_yellow_6 @ sk_A @ sk_C) @ 
% 0.20/0.51            (k10_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.51           (k10_yellow_6 @ sk_A @ sk_C))
% 0.20/0.51        | (v2_struct_0 @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['131', '141'])).
% 0.20/0.51  thf('143', plain,
% 0.20/0.51      ((m1_subset_1 @ 
% 0.20/0.51        (sk_D @ (k10_yellow_6 @ sk_A @ sk_C) @ (k10_yellow_6 @ sk_A @ sk_B) @ 
% 0.20/0.51         (u1_struct_0 @ sk_A)) @ 
% 0.20/0.51        (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('clc', [status(thm)], ['73', '74'])).
% 0.20/0.51  thf('144', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_C)
% 0.20/0.51        | (r2_hidden @ 
% 0.20/0.51           (sk_D @ (k10_yellow_6 @ sk_A @ sk_C) @ 
% 0.20/0.51            (k10_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.51           (k10_yellow_6 @ sk_A @ sk_C))
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | (v2_struct_0 @ sk_B)
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | (r2_hidden @ 
% 0.20/0.51           (sk_D @ (k10_yellow_6 @ sk_A @ sk_C) @ 
% 0.20/0.51            (k10_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.51           (k10_yellow_6 @ sk_A @ sk_C))
% 0.20/0.51        | (v2_struct_0 @ sk_C))),
% 0.20/0.51      inference('demod', [status(thm)], ['142', '143'])).
% 0.20/0.51  thf('145', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_B)
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | (r2_hidden @ 
% 0.20/0.51           (sk_D @ (k10_yellow_6 @ sk_A @ sk_C) @ 
% 0.20/0.51            (k10_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.51           (k10_yellow_6 @ sk_A @ sk_C))
% 0.20/0.51        | (v2_struct_0 @ sk_C))),
% 0.20/0.51      inference('simplify', [status(thm)], ['144'])).
% 0.20/0.51  thf('146', plain,
% 0.20/0.51      ((m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_C) @ 
% 0.20/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('clc', [status(thm)], ['68', '69'])).
% 0.20/0.51  thf('147', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.20/0.51          | (r1_tarski @ X2 @ X0)
% 0.20/0.51          | ~ (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X0)
% 0.20/0.51          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.20/0.51  thf('148', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51          | ~ (r2_hidden @ 
% 0.20/0.51               (sk_D @ (k10_yellow_6 @ sk_A @ sk_C) @ X0 @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.51               (k10_yellow_6 @ sk_A @ sk_C))
% 0.20/0.51          | (r1_tarski @ X0 @ (k10_yellow_6 @ sk_A @ sk_C)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['146', '147'])).
% 0.20/0.51  thf('149', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_C)
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | (v2_struct_0 @ sk_B)
% 0.20/0.51        | (r1_tarski @ (k10_yellow_6 @ sk_A @ sk_B) @ 
% 0.20/0.51           (k10_yellow_6 @ sk_A @ sk_C))
% 0.20/0.51        | ~ (m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_B) @ 
% 0.20/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['145', '148'])).
% 0.20/0.51  thf('150', plain,
% 0.20/0.51      ((m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_B) @ 
% 0.20/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('clc', [status(thm)], ['10', '11'])).
% 0.20/0.51  thf('151', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_C)
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | (v2_struct_0 @ sk_B)
% 0.20/0.51        | (r1_tarski @ (k10_yellow_6 @ sk_A @ sk_B) @ 
% 0.20/0.51           (k10_yellow_6 @ sk_A @ sk_C)))),
% 0.20/0.51      inference('demod', [status(thm)], ['149', '150'])).
% 0.20/0.51  thf('152', plain,
% 0.20/0.51      (~ (r1_tarski @ (k10_yellow_6 @ sk_A @ sk_B) @ 
% 0.20/0.51          (k10_yellow_6 @ sk_A @ sk_C))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('153', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['151', '152'])).
% 0.20/0.51  thf('154', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('155', plain, (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('clc', [status(thm)], ['153', '154'])).
% 0.20/0.51  thf('156', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.51      inference('clc', [status(thm)], ['65', '66'])).
% 0.20/0.51  thf('157', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('clc', [status(thm)], ['155', '156'])).
% 0.20/0.51  thf('158', plain, ($false), inference('demod', [status(thm)], ['0', '157'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
