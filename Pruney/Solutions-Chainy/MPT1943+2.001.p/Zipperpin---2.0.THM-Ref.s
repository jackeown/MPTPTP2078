%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KO44BvuQIL

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 780 expanded)
%              Number of leaves         :   32 ( 244 expanded)
%              Depth                    :   27
%              Number of atoms          : 1808 (12344 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_waybel_0_type,type,(
    r2_waybel_0: $i > $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m2_yellow_6_type,type,(
    m2_yellow_6: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

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

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( v2_struct_0 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v7_waybel_0 @ X19 )
      | ~ ( l1_waybel_0 @ X19 @ X18 )
      | ( m1_subset_1 @ ( k10_yellow_6 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_yellow_6])).

thf('4',plain,
    ( ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6','7','8'])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( m1_subset_1 @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_yellow_6 @ sk_A @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_yellow_6 @ sk_A @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','15'])).

thf('18',plain,(
    m2_yellow_6 @ sk_C_1 @ sk_A @ sk_B ),
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

thf('19',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( l1_struct_0 @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v7_waybel_0 @ X21 )
      | ~ ( l1_waybel_0 @ X21 @ X20 )
      | ( l1_waybel_0 @ X22 @ X20 )
      | ~ ( m2_yellow_6 @ X22 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('20',plain,
    ( ( l1_waybel_0 @ sk_C_1 @ sk_A )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('25',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('26',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( l1_waybel_0 @ sk_C_1 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22','23','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( l1_waybel_0 @ sk_C_1 @ sk_A ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_waybel_0 @ sk_C_1 @ sk_A ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( v2_struct_0 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v7_waybel_0 @ X19 )
      | ~ ( l1_waybel_0 @ X19 @ X18 )
      | ( m1_subset_1 @ ( k10_yellow_6 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_yellow_6])).

thf('33',plain,
    ( ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v7_waybel_0 @ sk_C_1 )
    | ~ ( v4_orders_2 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m2_yellow_6 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( l1_struct_0 @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v7_waybel_0 @ X21 )
      | ~ ( l1_waybel_0 @ X21 @ X20 )
      | ( v7_waybel_0 @ X22 )
      | ~ ( m2_yellow_6 @ X22 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('36',plain,
    ( ( v7_waybel_0 @ sk_C_1 )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['24','25'])).

thf('41',plain,
    ( ( v7_waybel_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37','38','39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v7_waybel_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v7_waybel_0 @ sk_C_1 ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    m2_yellow_6 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( l1_struct_0 @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v7_waybel_0 @ X21 )
      | ~ ( l1_waybel_0 @ X21 @ X20 )
      | ( v4_orders_2 @ X22 )
      | ~ ( m2_yellow_6 @ X22 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('48',plain,
    ( ( v4_orders_2 @ sk_C_1 )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['24','25'])).

thf('53',plain,
    ( ( v4_orders_2 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','49','50','51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v4_orders_2 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v4_orders_2 @ sk_C_1 ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','45','57','58','59'])).

thf('61',plain,(
    m2_yellow_6 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( l1_struct_0 @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v7_waybel_0 @ X21 )
      | ~ ( l1_waybel_0 @ X21 @ X20 )
      | ~ ( v2_struct_0 @ X22 )
      | ~ ( m2_yellow_6 @ X22 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('63',plain,
    ( ~ ( v2_struct_0 @ sk_C_1 )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['24','25'])).

thf('68',plain,
    ( ~ ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['63','64','65','66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['60','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['73','74'])).

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

thf('76',plain,(
    ! [X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v7_waybel_0 @ X12 )
      | ~ ( l1_waybel_0 @ X12 @ X13 )
      | ( X14
       != ( k10_yellow_6 @ X13 @ X12 ) )
      | ( r2_hidden @ X16 @ X14 )
      | ( m1_connsp_2 @ ( sk_E_1 @ X16 @ X12 @ X13 ) @ X13 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d18_yellow_6])).

thf('77',plain,(
    ! [X12: $i,X13: $i,X16: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ ( k10_yellow_6 @ X13 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X13 ) )
      | ( m1_connsp_2 @ ( sk_E_1 @ X16 @ X12 @ X13 ) @ X13 @ X16 )
      | ( r2_hidden @ X16 @ ( k10_yellow_6 @ X13 @ X12 ) )
      | ~ ( l1_waybel_0 @ X12 @ X13 )
      | ~ ( v7_waybel_0 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ~ ( v4_orders_2 @ sk_C_1 )
      | ~ ( v7_waybel_0 @ sk_C_1 )
      | ~ ( l1_waybel_0 @ sk_C_1 @ sk_A )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ sk_C_1 ) )
      | ( m1_connsp_2 @ ( sk_E_1 @ X0 @ sk_C_1 @ sk_A ) @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','77'])).

thf('79',plain,(
    v4_orders_2 @ sk_C_1 ),
    inference(clc,[status(thm)],['55','56'])).

thf('80',plain,(
    v7_waybel_0 @ sk_C_1 ),
    inference(clc,[status(thm)],['43','44'])).

thf('81',plain,(
    l1_waybel_0 @ sk_C_1 @ sk_A ),
    inference(clc,[status(thm)],['29','30'])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ sk_C_1 ) )
      | ( m1_connsp_2 @ ( sk_E_1 @ X0 @ sk_C_1 @ sk_A ) @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','79','80','81','82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_yellow_6 @ sk_A @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ ( sk_E_1 @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) @ sk_A @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B ) ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['17','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_yellow_6 @ sk_A @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','15'])).

thf('87',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('88',plain,(
    m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('89',plain,(
    ! [X12: $i,X13: $i,X14: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v7_waybel_0 @ X12 )
      | ~ ( l1_waybel_0 @ X12 @ X13 )
      | ( X14
       != ( k10_yellow_6 @ X13 @ X12 ) )
      | ~ ( m1_connsp_2 @ X17 @ X13 @ X16 )
      | ( r1_waybel_0 @ X13 @ X12 @ X17 )
      | ~ ( r2_hidden @ X16 @ X14 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d18_yellow_6])).

thf('90',plain,(
    ! [X12: $i,X13: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ ( k10_yellow_6 @ X13 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r2_hidden @ X16 @ ( k10_yellow_6 @ X13 @ X12 ) )
      | ( r1_waybel_0 @ X13 @ X12 @ X17 )
      | ~ ( m1_connsp_2 @ X17 @ X13 @ X16 )
      | ~ ( l1_waybel_0 @ X12 @ X13 )
      | ~ ( v7_waybel_0 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
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
    inference('sup-',[status(thm)],['88','90'])).

thf('92',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_connsp_2 @ X1 @ sk_A @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['91','92','93','94','95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_yellow_6 @ sk_A @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X1 )
      | ~ ( m1_connsp_2 @ X1 @ sk_A @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['87','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_yellow_6 @ sk_A @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_connsp_2 @ X1 @ sk_A @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B ) ) )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X1 )
      | ~ ( m1_connsp_2 @ X1 @ sk_A @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ ( sk_E_1 @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_0 @ sk_A @ sk_B @ ( sk_E_1 @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    l1_waybel_0 @ sk_C_1 @ sk_A ),
    inference(clc,[status(thm)],['29','30'])).

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

thf('104',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( l1_waybel_0 @ X8 @ X9 )
      | ( r2_waybel_0 @ X9 @ X8 @ ( k6_subset_1 @ ( u1_struct_0 @ X9 ) @ X10 ) )
      | ( r1_waybel_0 @ X9 @ X8 @ X10 )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t9_waybel_0])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_C_1 @ X0 )
      | ( r2_waybel_0 @ sk_A @ sk_C_1 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['24','25'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_C_1 @ X0 )
      | ( r2_waybel_0 @ sk_A @ sk_C_1 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    m2_yellow_6 @ sk_C_1 @ sk_A @ sk_B ),
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

thf('109',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ~ ( v7_waybel_0 @ X23 )
      | ~ ( l1_waybel_0 @ X23 @ X24 )
      | ~ ( r2_waybel_0 @ X24 @ X25 @ X26 )
      | ( r2_waybel_0 @ X24 @ X23 @ X26 )
      | ~ ( m2_yellow_6 @ X25 @ X24 @ X23 )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t27_yellow_6])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_waybel_0 @ sk_A @ sk_C_1 @ X0 )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['24','25'])).

thf('112',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_waybel_0 @ sk_A @ sk_C_1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['110','111','112','113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ( r1_waybel_0 @ sk_A @ sk_C_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r2_waybel_0 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['107','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( r2_waybel_0 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_C_1 @ X0 )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( l1_waybel_0 @ X8 @ X9 )
      | ~ ( r1_waybel_0 @ X9 @ X8 @ X11 )
      | ~ ( r2_waybel_0 @ X9 @ X8 @ ( k6_subset_1 @ ( u1_struct_0 @ X9 ) @ X11 ) )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t9_waybel_0])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ( r1_waybel_0 @ sk_A @ sk_C_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['24','25'])).

thf('121',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ( r1_waybel_0 @ sk_A @ sk_C_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_C_1 @ X0 )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C_1 )
      | ( r1_waybel_0 @ sk_A @ sk_C_1 @ ( sk_E_1 @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['102','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_0 @ sk_A @ sk_C_1 @ ( sk_E_1 @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('127',plain,(
    ! [X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v7_waybel_0 @ X12 )
      | ~ ( l1_waybel_0 @ X12 @ X13 )
      | ( X14
       != ( k10_yellow_6 @ X13 @ X12 ) )
      | ( r2_hidden @ X16 @ X14 )
      | ~ ( r1_waybel_0 @ X13 @ X12 @ ( sk_E_1 @ X16 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d18_yellow_6])).

thf('128',plain,(
    ! [X12: $i,X13: $i,X16: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ ( k10_yellow_6 @ X13 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r1_waybel_0 @ X13 @ X12 @ ( sk_E_1 @ X16 @ X12 @ X13 ) )
      | ( r2_hidden @ X16 @ ( k10_yellow_6 @ X13 @ X12 ) )
      | ~ ( l1_waybel_0 @ X12 @ X13 )
      | ~ ( v7_waybel_0 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ~ ( v4_orders_2 @ sk_C_1 )
      | ~ ( v7_waybel_0 @ sk_C_1 )
      | ~ ( l1_waybel_0 @ sk_C_1 @ sk_A )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ sk_C_1 ) )
      | ~ ( r1_waybel_0 @ sk_A @ sk_C_1 @ ( sk_E_1 @ X0 @ sk_C_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['126','128'])).

thf('130',plain,(
    v4_orders_2 @ sk_C_1 ),
    inference(clc,[status(thm)],['55','56'])).

thf('131',plain,(
    v7_waybel_0 @ sk_C_1 ),
    inference(clc,[status(thm)],['43','44'])).

thf('132',plain,(
    l1_waybel_0 @ sk_C_1 @ sk_A ),
    inference(clc,[status(thm)],['29','30'])).

thf('133',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ sk_C_1 ) )
      | ~ ( r1_waybel_0 @ sk_A @ sk_C_1 @ ( sk_E_1 @ X0 @ sk_C_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['129','130','131','132','133','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['125','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_yellow_6 @ sk_A @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_C_1 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('141',plain,
    ( ( r1_tarski @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,(
    ~ ( r1_tarski @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('146',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['144','145'])).

thf('147',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['146','147'])).

thf('149',plain,(
    $false ),
    inference(demod,[status(thm)],['0','148'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KO44BvuQIL
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:26:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 79 iterations in 0.041s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.50  thf(r2_waybel_0_type, type, r2_waybel_0: $i > $i > $i > $o).
% 0.21/0.50  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.50  thf(k10_yellow_6_type, type, k10_yellow_6: $i > $i > $i).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.50  thf(m2_yellow_6_type, type, m2_yellow_6: $i > $i > $i > $o).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.21/0.50  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.50  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.21/0.50  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.21/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.21/0.50  thf(t41_yellow_6, conjecture,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.50             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( m2_yellow_6 @ C @ A @ B ) =>
% 0.21/0.50               ( r1_tarski @
% 0.21/0.50                 ( k10_yellow_6 @ A @ B ) @ ( k10_yellow_6 @ A @ C ) ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]:
% 0.21/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.50            ( l1_pre_topc @ A ) ) =>
% 0.21/0.50          ( ![B:$i]:
% 0.21/0.50            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.50                ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.50              ( ![C:$i]:
% 0.21/0.50                ( ( m2_yellow_6 @ C @ A @ B ) =>
% 0.21/0.50                  ( r1_tarski @
% 0.21/0.50                    ( k10_yellow_6 @ A @ B ) @ ( k10_yellow_6 @ A @ C ) ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t41_yellow_6])).
% 0.21/0.50  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(d3_tarski, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (![X1 : $i, X3 : $i]:
% 0.21/0.50         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.50  thf('2', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(dt_k10_yellow_6, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.50         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 0.21/0.50         ( v4_orders_2 @ B ) & ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.50       ( m1_subset_1 @
% 0.21/0.50         ( k10_yellow_6 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X18 : $i, X19 : $i]:
% 0.21/0.50         (~ (l1_pre_topc @ X18)
% 0.21/0.50          | ~ (v2_pre_topc @ X18)
% 0.21/0.50          | (v2_struct_0 @ X18)
% 0.21/0.50          | (v2_struct_0 @ X19)
% 0.21/0.50          | ~ (v4_orders_2 @ X19)
% 0.21/0.50          | ~ (v7_waybel_0 @ X19)
% 0.21/0.50          | ~ (l1_waybel_0 @ X19 @ X18)
% 0.21/0.50          | (m1_subset_1 @ (k10_yellow_6 @ X18 @ X19) @ 
% 0.21/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X18))))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k10_yellow_6])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (((m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_B) @ 
% 0.21/0.50         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50        | ~ (v7_waybel_0 @ sk_B)
% 0.21/0.50        | ~ (v4_orders_2 @ sk_B)
% 0.21/0.50        | (v2_struct_0 @ sk_B)
% 0.21/0.50        | (v2_struct_0 @ sk_A)
% 0.21/0.50        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.50        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf('5', plain, ((v7_waybel_0 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('6', plain, ((v4_orders_2 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('7', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (((m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_B) @ 
% 0.21/0.50         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50        | (v2_struct_0 @ sk_B)
% 0.21/0.50        | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['4', '5', '6', '7', '8'])).
% 0.21/0.50  thf('10', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_A)
% 0.21/0.50        | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_B) @ 
% 0.21/0.50           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.50      inference('clc', [status(thm)], ['9', '10'])).
% 0.21/0.50  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      ((m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_B) @ 
% 0.21/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('clc', [status(thm)], ['11', '12'])).
% 0.21/0.50  thf(t4_subset, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.21/0.50       ( m1_subset_1 @ A @ C ) ))).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X4 @ X5)
% 0.21/0.50          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.21/0.50          | (m1_subset_1 @ X4 @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [t4_subset])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50          | ~ (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r1_tarski @ (k10_yellow_6 @ sk_A @ sk_B) @ X0)
% 0.21/0.50          | (m1_subset_1 @ (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ sk_B)) @ 
% 0.21/0.50             (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '15'])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r1_tarski @ (k10_yellow_6 @ sk_A @ sk_B) @ X0)
% 0.21/0.50          | (m1_subset_1 @ (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ sk_B)) @ 
% 0.21/0.50             (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '15'])).
% 0.21/0.50  thf('18', plain, ((m2_yellow_6 @ sk_C_1 @ sk_A @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(dt_m2_yellow_6, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.21/0.50         ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.50         ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.50       ( ![C:$i]:
% 0.21/0.50         ( ( m2_yellow_6 @ C @ A @ B ) =>
% 0.21/0.50           ( ( ~( v2_struct_0 @ C ) ) & ( v4_orders_2 @ C ) & 
% 0.21/0.50             ( v7_waybel_0 @ C ) & ( l1_waybel_0 @ C @ A ) ) ) ) ))).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.50         (~ (l1_struct_0 @ X20)
% 0.21/0.50          | (v2_struct_0 @ X20)
% 0.21/0.50          | (v2_struct_0 @ X21)
% 0.21/0.50          | ~ (v4_orders_2 @ X21)
% 0.21/0.50          | ~ (v7_waybel_0 @ X21)
% 0.21/0.50          | ~ (l1_waybel_0 @ X21 @ X20)
% 0.21/0.50          | (l1_waybel_0 @ X22 @ X20)
% 0.21/0.50          | ~ (m2_yellow_6 @ X22 @ X20 @ X21))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (((l1_waybel_0 @ sk_C_1 @ sk_A)
% 0.21/0.50        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.21/0.50        | ~ (v7_waybel_0 @ sk_B)
% 0.21/0.50        | ~ (v4_orders_2 @ sk_B)
% 0.21/0.50        | (v2_struct_0 @ sk_B)
% 0.21/0.50        | (v2_struct_0 @ sk_A)
% 0.21/0.50        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.50  thf('21', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('22', plain, ((v7_waybel_0 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('23', plain, ((v4_orders_2 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(dt_l1_pre_topc, axiom,
% 0.21/0.50    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.50  thf('25', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.50  thf('26', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      (((l1_waybel_0 @ sk_C_1 @ sk_A)
% 0.21/0.50        | (v2_struct_0 @ sk_B)
% 0.21/0.50        | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['20', '21', '22', '23', '26'])).
% 0.21/0.50  thf('28', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('29', plain, (((v2_struct_0 @ sk_A) | (l1_waybel_0 @ sk_C_1 @ sk_A))),
% 0.21/0.50      inference('clc', [status(thm)], ['27', '28'])).
% 0.21/0.50  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('31', plain, ((l1_waybel_0 @ sk_C_1 @ sk_A)),
% 0.21/0.50      inference('clc', [status(thm)], ['29', '30'])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      (![X18 : $i, X19 : $i]:
% 0.21/0.50         (~ (l1_pre_topc @ X18)
% 0.21/0.50          | ~ (v2_pre_topc @ X18)
% 0.21/0.50          | (v2_struct_0 @ X18)
% 0.21/0.50          | (v2_struct_0 @ X19)
% 0.21/0.50          | ~ (v4_orders_2 @ X19)
% 0.21/0.50          | ~ (v7_waybel_0 @ X19)
% 0.21/0.50          | ~ (l1_waybel_0 @ X19 @ X18)
% 0.21/0.50          | (m1_subset_1 @ (k10_yellow_6 @ X18 @ X19) @ 
% 0.21/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X18))))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k10_yellow_6])).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      (((m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_C_1) @ 
% 0.21/0.50         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50        | ~ (v7_waybel_0 @ sk_C_1)
% 0.21/0.50        | ~ (v4_orders_2 @ sk_C_1)
% 0.21/0.50        | (v2_struct_0 @ sk_C_1)
% 0.21/0.50        | (v2_struct_0 @ sk_A)
% 0.21/0.50        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.50        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.50  thf('34', plain, ((m2_yellow_6 @ sk_C_1 @ sk_A @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.50         (~ (l1_struct_0 @ X20)
% 0.21/0.50          | (v2_struct_0 @ X20)
% 0.21/0.50          | (v2_struct_0 @ X21)
% 0.21/0.50          | ~ (v4_orders_2 @ X21)
% 0.21/0.50          | ~ (v7_waybel_0 @ X21)
% 0.21/0.50          | ~ (l1_waybel_0 @ X21 @ X20)
% 0.21/0.50          | (v7_waybel_0 @ X22)
% 0.21/0.50          | ~ (m2_yellow_6 @ X22 @ X20 @ X21))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      (((v7_waybel_0 @ sk_C_1)
% 0.21/0.50        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.21/0.50        | ~ (v7_waybel_0 @ sk_B)
% 0.21/0.50        | ~ (v4_orders_2 @ sk_B)
% 0.21/0.50        | (v2_struct_0 @ sk_B)
% 0.21/0.50        | (v2_struct_0 @ sk_A)
% 0.21/0.50        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.50  thf('37', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('38', plain, ((v7_waybel_0 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('39', plain, ((v4_orders_2 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('40', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.50  thf('41', plain,
% 0.21/0.50      (((v7_waybel_0 @ sk_C_1) | (v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['36', '37', '38', '39', '40'])).
% 0.21/0.50  thf('42', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('43', plain, (((v2_struct_0 @ sk_A) | (v7_waybel_0 @ sk_C_1))),
% 0.21/0.50      inference('clc', [status(thm)], ['41', '42'])).
% 0.21/0.50  thf('44', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('45', plain, ((v7_waybel_0 @ sk_C_1)),
% 0.21/0.50      inference('clc', [status(thm)], ['43', '44'])).
% 0.21/0.50  thf('46', plain, ((m2_yellow_6 @ sk_C_1 @ sk_A @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('47', plain,
% 0.21/0.50      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.50         (~ (l1_struct_0 @ X20)
% 0.21/0.50          | (v2_struct_0 @ X20)
% 0.21/0.50          | (v2_struct_0 @ X21)
% 0.21/0.50          | ~ (v4_orders_2 @ X21)
% 0.21/0.50          | ~ (v7_waybel_0 @ X21)
% 0.21/0.50          | ~ (l1_waybel_0 @ X21 @ X20)
% 0.21/0.50          | (v4_orders_2 @ X22)
% 0.21/0.50          | ~ (m2_yellow_6 @ X22 @ X20 @ X21))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 0.21/0.50  thf('48', plain,
% 0.21/0.50      (((v4_orders_2 @ sk_C_1)
% 0.21/0.50        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.21/0.50        | ~ (v7_waybel_0 @ sk_B)
% 0.21/0.50        | ~ (v4_orders_2 @ sk_B)
% 0.21/0.50        | (v2_struct_0 @ sk_B)
% 0.21/0.50        | (v2_struct_0 @ sk_A)
% 0.21/0.50        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.50  thf('49', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('50', plain, ((v7_waybel_0 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('51', plain, ((v4_orders_2 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('52', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.50  thf('53', plain,
% 0.21/0.50      (((v4_orders_2 @ sk_C_1) | (v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['48', '49', '50', '51', '52'])).
% 0.21/0.50  thf('54', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('55', plain, (((v2_struct_0 @ sk_A) | (v4_orders_2 @ sk_C_1))),
% 0.21/0.50      inference('clc', [status(thm)], ['53', '54'])).
% 0.21/0.50  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('57', plain, ((v4_orders_2 @ sk_C_1)),
% 0.21/0.50      inference('clc', [status(thm)], ['55', '56'])).
% 0.21/0.50  thf('58', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('60', plain,
% 0.21/0.50      (((m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_C_1) @ 
% 0.21/0.50         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50        | (v2_struct_0 @ sk_C_1)
% 0.21/0.50        | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['33', '45', '57', '58', '59'])).
% 0.21/0.50  thf('61', plain, ((m2_yellow_6 @ sk_C_1 @ sk_A @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('62', plain,
% 0.21/0.50      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.50         (~ (l1_struct_0 @ X20)
% 0.21/0.50          | (v2_struct_0 @ X20)
% 0.21/0.50          | (v2_struct_0 @ X21)
% 0.21/0.50          | ~ (v4_orders_2 @ X21)
% 0.21/0.50          | ~ (v7_waybel_0 @ X21)
% 0.21/0.50          | ~ (l1_waybel_0 @ X21 @ X20)
% 0.21/0.50          | ~ (v2_struct_0 @ X22)
% 0.21/0.50          | ~ (m2_yellow_6 @ X22 @ X20 @ X21))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 0.21/0.50  thf('63', plain,
% 0.21/0.50      ((~ (v2_struct_0 @ sk_C_1)
% 0.21/0.50        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.21/0.50        | ~ (v7_waybel_0 @ sk_B)
% 0.21/0.50        | ~ (v4_orders_2 @ sk_B)
% 0.21/0.50        | (v2_struct_0 @ sk_B)
% 0.21/0.50        | (v2_struct_0 @ sk_A)
% 0.21/0.50        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['61', '62'])).
% 0.21/0.50  thf('64', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('65', plain, ((v7_waybel_0 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('66', plain, ((v4_orders_2 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('67', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.50  thf('68', plain,
% 0.21/0.50      ((~ (v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['63', '64', '65', '66', '67'])).
% 0.21/0.50  thf('69', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('70', plain, (((v2_struct_0 @ sk_A) | ~ (v2_struct_0 @ sk_C_1))),
% 0.21/0.50      inference('clc', [status(thm)], ['68', '69'])).
% 0.21/0.50  thf('71', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('72', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.21/0.50      inference('clc', [status(thm)], ['70', '71'])).
% 0.21/0.50  thf('73', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_A)
% 0.21/0.50        | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_C_1) @ 
% 0.21/0.50           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.50      inference('clc', [status(thm)], ['60', '72'])).
% 0.21/0.50  thf('74', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('75', plain,
% 0.21/0.50      ((m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_C_1) @ 
% 0.21/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('clc', [status(thm)], ['73', '74'])).
% 0.21/0.50  thf(d18_yellow_6, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.50             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50               ( ( ( C ) = ( k10_yellow_6 @ A @ B ) ) <=>
% 0.21/0.50                 ( ![D:$i]:
% 0.21/0.50                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.50                     ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.50                       ( ![E:$i]:
% 0.21/0.50                         ( ( m1_connsp_2 @ E @ A @ D ) =>
% 0.21/0.50                           ( r1_waybel_0 @ A @ B @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('76', plain,
% 0.21/0.50      (![X12 : $i, X13 : $i, X14 : $i, X16 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X12)
% 0.21/0.50          | ~ (v4_orders_2 @ X12)
% 0.21/0.50          | ~ (v7_waybel_0 @ X12)
% 0.21/0.50          | ~ (l1_waybel_0 @ X12 @ X13)
% 0.21/0.50          | ((X14) != (k10_yellow_6 @ X13 @ X12))
% 0.21/0.50          | (r2_hidden @ X16 @ X14)
% 0.21/0.50          | (m1_connsp_2 @ (sk_E_1 @ X16 @ X12 @ X13) @ X13 @ X16)
% 0.21/0.50          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X13))
% 0.21/0.50          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.50          | ~ (l1_pre_topc @ X13)
% 0.21/0.50          | ~ (v2_pre_topc @ X13)
% 0.21/0.50          | (v2_struct_0 @ X13))),
% 0.21/0.50      inference('cnf', [status(esa)], [d18_yellow_6])).
% 0.21/0.50  thf('77', plain,
% 0.21/0.50      (![X12 : $i, X13 : $i, X16 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X13)
% 0.21/0.50          | ~ (v2_pre_topc @ X13)
% 0.21/0.50          | ~ (l1_pre_topc @ X13)
% 0.21/0.50          | ~ (m1_subset_1 @ (k10_yellow_6 @ X13 @ X12) @ 
% 0.21/0.50               (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.50          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X13))
% 0.21/0.50          | (m1_connsp_2 @ (sk_E_1 @ X16 @ X12 @ X13) @ X13 @ X16)
% 0.21/0.50          | (r2_hidden @ X16 @ (k10_yellow_6 @ X13 @ X12))
% 0.21/0.50          | ~ (l1_waybel_0 @ X12 @ X13)
% 0.21/0.50          | ~ (v7_waybel_0 @ X12)
% 0.21/0.50          | ~ (v4_orders_2 @ X12)
% 0.21/0.50          | (v2_struct_0 @ X12))),
% 0.21/0.50      inference('simplify', [status(thm)], ['76'])).
% 0.21/0.50  thf('78', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_C_1)
% 0.21/0.50          | ~ (v4_orders_2 @ sk_C_1)
% 0.21/0.50          | ~ (v7_waybel_0 @ sk_C_1)
% 0.21/0.50          | ~ (l1_waybel_0 @ sk_C_1 @ sk_A)
% 0.21/0.50          | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ sk_C_1))
% 0.21/0.50          | (m1_connsp_2 @ (sk_E_1 @ X0 @ sk_C_1 @ sk_A) @ sk_A @ X0)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.50          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.50          | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['75', '77'])).
% 0.21/0.50  thf('79', plain, ((v4_orders_2 @ sk_C_1)),
% 0.21/0.50      inference('clc', [status(thm)], ['55', '56'])).
% 0.21/0.50  thf('80', plain, ((v7_waybel_0 @ sk_C_1)),
% 0.21/0.50      inference('clc', [status(thm)], ['43', '44'])).
% 0.21/0.50  thf('81', plain, ((l1_waybel_0 @ sk_C_1 @ sk_A)),
% 0.21/0.50      inference('clc', [status(thm)], ['29', '30'])).
% 0.21/0.50  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('83', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('84', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_C_1)
% 0.21/0.50          | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ sk_C_1))
% 0.21/0.50          | (m1_connsp_2 @ (sk_E_1 @ X0 @ sk_C_1 @ sk_A) @ sk_A @ X0)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50          | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['78', '79', '80', '81', '82', '83'])).
% 0.21/0.50  thf('85', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r1_tarski @ (k10_yellow_6 @ sk_A @ sk_B) @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | (m1_connsp_2 @ 
% 0.21/0.50             (sk_E_1 @ (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ sk_B)) @ sk_C_1 @ 
% 0.21/0.50              sk_A) @ 
% 0.21/0.50             sk_A @ (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ sk_B)))
% 0.21/0.50          | (r2_hidden @ (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ sk_B)) @ 
% 0.21/0.50             (k10_yellow_6 @ sk_A @ sk_C_1))
% 0.21/0.50          | (v2_struct_0 @ sk_C_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['17', '84'])).
% 0.21/0.50  thf('86', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r1_tarski @ (k10_yellow_6 @ sk_A @ sk_B) @ X0)
% 0.21/0.50          | (m1_subset_1 @ (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ sk_B)) @ 
% 0.21/0.50             (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '15'])).
% 0.21/0.50  thf('87', plain,
% 0.21/0.50      (![X1 : $i, X3 : $i]:
% 0.21/0.50         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.50  thf('88', plain,
% 0.21/0.50      ((m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_B) @ 
% 0.21/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('clc', [status(thm)], ['11', '12'])).
% 0.21/0.50  thf('89', plain,
% 0.21/0.50      (![X12 : $i, X13 : $i, X14 : $i, X16 : $i, X17 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X12)
% 0.21/0.50          | ~ (v4_orders_2 @ X12)
% 0.21/0.50          | ~ (v7_waybel_0 @ X12)
% 0.21/0.50          | ~ (l1_waybel_0 @ X12 @ X13)
% 0.21/0.50          | ((X14) != (k10_yellow_6 @ X13 @ X12))
% 0.21/0.50          | ~ (m1_connsp_2 @ X17 @ X13 @ X16)
% 0.21/0.50          | (r1_waybel_0 @ X13 @ X12 @ X17)
% 0.21/0.50          | ~ (r2_hidden @ X16 @ X14)
% 0.21/0.50          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X13))
% 0.21/0.50          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.50          | ~ (l1_pre_topc @ X13)
% 0.21/0.50          | ~ (v2_pre_topc @ X13)
% 0.21/0.50          | (v2_struct_0 @ X13))),
% 0.21/0.50      inference('cnf', [status(esa)], [d18_yellow_6])).
% 0.21/0.50  thf('90', plain,
% 0.21/0.50      (![X12 : $i, X13 : $i, X16 : $i, X17 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X13)
% 0.21/0.50          | ~ (v2_pre_topc @ X13)
% 0.21/0.50          | ~ (l1_pre_topc @ X13)
% 0.21/0.50          | ~ (m1_subset_1 @ (k10_yellow_6 @ X13 @ X12) @ 
% 0.21/0.50               (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.50          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X13))
% 0.21/0.50          | ~ (r2_hidden @ X16 @ (k10_yellow_6 @ X13 @ X12))
% 0.21/0.50          | (r1_waybel_0 @ X13 @ X12 @ X17)
% 0.21/0.50          | ~ (m1_connsp_2 @ X17 @ X13 @ X16)
% 0.21/0.50          | ~ (l1_waybel_0 @ X12 @ X13)
% 0.21/0.50          | ~ (v7_waybel_0 @ X12)
% 0.21/0.50          | ~ (v4_orders_2 @ X12)
% 0.21/0.50          | (v2_struct_0 @ X12))),
% 0.21/0.50      inference('simplify', [status(thm)], ['89'])).
% 0.21/0.50  thf('91', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_B)
% 0.21/0.50          | ~ (v4_orders_2 @ sk_B)
% 0.21/0.50          | ~ (v7_waybel_0 @ sk_B)
% 0.21/0.50          | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.21/0.50          | ~ (m1_connsp_2 @ X1 @ sk_A @ X0)
% 0.21/0.50          | (r1_waybel_0 @ sk_A @ sk_B @ X1)
% 0.21/0.50          | ~ (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.50          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.50          | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['88', '90'])).
% 0.21/0.50  thf('92', plain, ((v4_orders_2 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('93', plain, ((v7_waybel_0 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('94', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('96', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('97', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_B)
% 0.21/0.50          | ~ (m1_connsp_2 @ X1 @ sk_A @ X0)
% 0.21/0.50          | (r1_waybel_0 @ sk_A @ sk_B @ X1)
% 0.21/0.50          | ~ (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50          | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['91', '92', '93', '94', '95', '96'])).
% 0.21/0.50  thf('98', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((r1_tarski @ (k10_yellow_6 @ sk_A @ sk_B) @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | ~ (m1_subset_1 @ (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ sk_B)) @ 
% 0.21/0.50               (u1_struct_0 @ sk_A))
% 0.21/0.50          | (r1_waybel_0 @ sk_A @ sk_B @ X1)
% 0.21/0.50          | ~ (m1_connsp_2 @ X1 @ sk_A @ 
% 0.21/0.50               (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ sk_B)))
% 0.21/0.50          | (v2_struct_0 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['87', '97'])).
% 0.21/0.50  thf('99', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((r1_tarski @ (k10_yellow_6 @ sk_A @ sk_B) @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_B)
% 0.21/0.50          | ~ (m1_connsp_2 @ X1 @ sk_A @ 
% 0.21/0.50               (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ sk_B)))
% 0.21/0.50          | (r1_waybel_0 @ sk_A @ sk_B @ X1)
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | (r1_tarski @ (k10_yellow_6 @ sk_A @ sk_B) @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['86', '98'])).
% 0.21/0.50  thf('100', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_A)
% 0.21/0.50          | (r1_waybel_0 @ sk_A @ sk_B @ X1)
% 0.21/0.50          | ~ (m1_connsp_2 @ X1 @ sk_A @ 
% 0.21/0.50               (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ sk_B)))
% 0.21/0.50          | (v2_struct_0 @ sk_B)
% 0.21/0.50          | (r1_tarski @ (k10_yellow_6 @ sk_A @ sk_B) @ X0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['99'])).
% 0.21/0.50  thf('101', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_C_1)
% 0.21/0.50          | (r2_hidden @ (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ sk_B)) @ 
% 0.21/0.50             (k10_yellow_6 @ sk_A @ sk_C_1))
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | (r1_tarski @ (k10_yellow_6 @ sk_A @ sk_B) @ X0)
% 0.21/0.50          | (r1_tarski @ (k10_yellow_6 @ sk_A @ sk_B) @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_B)
% 0.21/0.50          | (r1_waybel_0 @ sk_A @ sk_B @ 
% 0.21/0.50             (sk_E_1 @ (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ sk_B)) @ sk_C_1 @ 
% 0.21/0.50              sk_A))
% 0.21/0.50          | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['85', '100'])).
% 0.21/0.50  thf('102', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r1_waybel_0 @ sk_A @ sk_B @ 
% 0.21/0.50           (sk_E_1 @ (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ sk_B)) @ sk_C_1 @ sk_A))
% 0.21/0.50          | (v2_struct_0 @ sk_B)
% 0.21/0.50          | (r1_tarski @ (k10_yellow_6 @ sk_A @ sk_B) @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | (r2_hidden @ (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ sk_B)) @ 
% 0.21/0.50             (k10_yellow_6 @ sk_A @ sk_C_1))
% 0.21/0.50          | (v2_struct_0 @ sk_C_1))),
% 0.21/0.50      inference('simplify', [status(thm)], ['101'])).
% 0.21/0.50  thf('103', plain, ((l1_waybel_0 @ sk_C_1 @ sk_A)),
% 0.21/0.50      inference('clc', [status(thm)], ['29', '30'])).
% 0.21/0.50  thf(t9_waybel_0, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( r1_waybel_0 @ A @ B @ C ) <=>
% 0.21/0.50               ( ~( r2_waybel_0 @
% 0.21/0.50                    A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('104', plain,
% 0.21/0.50      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X8)
% 0.21/0.50          | ~ (l1_waybel_0 @ X8 @ X9)
% 0.21/0.50          | (r2_waybel_0 @ X9 @ X8 @ (k6_subset_1 @ (u1_struct_0 @ X9) @ X10))
% 0.21/0.50          | (r1_waybel_0 @ X9 @ X8 @ X10)
% 0.21/0.50          | ~ (l1_struct_0 @ X9)
% 0.21/0.50          | (v2_struct_0 @ X9))),
% 0.21/0.50      inference('cnf', [status(esa)], [t9_waybel_0])).
% 0.21/0.50  thf('105', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_A)
% 0.21/0.50          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.50          | (r1_waybel_0 @ sk_A @ sk_C_1 @ X0)
% 0.21/0.50          | (r2_waybel_0 @ sk_A @ sk_C_1 @ 
% 0.21/0.50             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.21/0.50          | (v2_struct_0 @ sk_C_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['103', '104'])).
% 0.21/0.50  thf('106', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.50  thf('107', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_A)
% 0.21/0.50          | (r1_waybel_0 @ sk_A @ sk_C_1 @ X0)
% 0.21/0.50          | (r2_waybel_0 @ sk_A @ sk_C_1 @ 
% 0.21/0.50             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.21/0.50          | (v2_struct_0 @ sk_C_1))),
% 0.21/0.50      inference('demod', [status(thm)], ['105', '106'])).
% 0.21/0.50  thf('108', plain, ((m2_yellow_6 @ sk_C_1 @ sk_A @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t27_yellow_6, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.50             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( m2_yellow_6 @ C @ A @ B ) =>
% 0.21/0.50               ( ![D:$i]:
% 0.21/0.50                 ( ( r2_waybel_0 @ A @ C @ D ) => ( r2_waybel_0 @ A @ B @ D ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('109', plain,
% 0.21/0.50      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X23)
% 0.21/0.50          | ~ (v4_orders_2 @ X23)
% 0.21/0.50          | ~ (v7_waybel_0 @ X23)
% 0.21/0.50          | ~ (l1_waybel_0 @ X23 @ X24)
% 0.21/0.50          | ~ (r2_waybel_0 @ X24 @ X25 @ X26)
% 0.21/0.50          | (r2_waybel_0 @ X24 @ X23 @ X26)
% 0.21/0.50          | ~ (m2_yellow_6 @ X25 @ X24 @ X23)
% 0.21/0.50          | ~ (l1_struct_0 @ X24)
% 0.21/0.50          | (v2_struct_0 @ X24))),
% 0.21/0.50      inference('cnf', [status(esa)], [t27_yellow_6])).
% 0.21/0.50  thf('110', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_A)
% 0.21/0.50          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.50          | (r2_waybel_0 @ sk_A @ sk_B @ X0)
% 0.21/0.50          | ~ (r2_waybel_0 @ sk_A @ sk_C_1 @ X0)
% 0.21/0.50          | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.21/0.50          | ~ (v7_waybel_0 @ sk_B)
% 0.21/0.50          | ~ (v4_orders_2 @ sk_B)
% 0.21/0.50          | (v2_struct_0 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['108', '109'])).
% 0.21/0.50  thf('111', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.50  thf('112', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('113', plain, ((v7_waybel_0 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('114', plain, ((v4_orders_2 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('115', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_A)
% 0.21/0.50          | (r2_waybel_0 @ sk_A @ sk_B @ X0)
% 0.21/0.50          | ~ (r2_waybel_0 @ sk_A @ sk_C_1 @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['110', '111', '112', '113', '114'])).
% 0.21/0.50  thf('116', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_C_1)
% 0.21/0.50          | (r1_waybel_0 @ sk_A @ sk_C_1 @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | (v2_struct_0 @ sk_B)
% 0.21/0.50          | (r2_waybel_0 @ sk_A @ sk_B @ 
% 0.21/0.50             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.21/0.50          | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['107', '115'])).
% 0.21/0.50  thf('117', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_waybel_0 @ sk_A @ sk_B @ 
% 0.21/0.50           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.21/0.50          | (v2_struct_0 @ sk_B)
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | (r1_waybel_0 @ sk_A @ sk_C_1 @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_C_1))),
% 0.21/0.50      inference('simplify', [status(thm)], ['116'])).
% 0.21/0.50  thf('118', plain,
% 0.21/0.50      (![X8 : $i, X9 : $i, X11 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X8)
% 0.21/0.50          | ~ (l1_waybel_0 @ X8 @ X9)
% 0.21/0.50          | ~ (r1_waybel_0 @ X9 @ X8 @ X11)
% 0.21/0.50          | ~ (r2_waybel_0 @ X9 @ X8 @ (k6_subset_1 @ (u1_struct_0 @ X9) @ X11))
% 0.21/0.50          | ~ (l1_struct_0 @ X9)
% 0.21/0.50          | (v2_struct_0 @ X9))),
% 0.21/0.50      inference('cnf', [status(esa)], [t9_waybel_0])).
% 0.21/0.50  thf('119', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_C_1)
% 0.21/0.50          | (r1_waybel_0 @ sk_A @ sk_C_1 @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | (v2_struct_0 @ sk_B)
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.50          | ~ (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.21/0.50          | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.21/0.50          | (v2_struct_0 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['117', '118'])).
% 0.21/0.50  thf('120', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.50  thf('121', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('122', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_C_1)
% 0.21/0.50          | (r1_waybel_0 @ sk_A @ sk_C_1 @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | (v2_struct_0 @ sk_B)
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | ~ (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['119', '120', '121'])).
% 0.21/0.50  thf('123', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_B)
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | (r1_waybel_0 @ sk_A @ sk_C_1 @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_C_1))),
% 0.21/0.50      inference('simplify', [status(thm)], ['122'])).
% 0.21/0.50  thf('124', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_C_1)
% 0.21/0.50          | (r2_hidden @ (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ sk_B)) @ 
% 0.21/0.50             (k10_yellow_6 @ sk_A @ sk_C_1))
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | (r1_tarski @ (k10_yellow_6 @ sk_A @ sk_B) @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_B)
% 0.21/0.50          | (v2_struct_0 @ sk_C_1)
% 0.21/0.50          | (r1_waybel_0 @ sk_A @ sk_C_1 @ 
% 0.21/0.50             (sk_E_1 @ (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ sk_B)) @ sk_C_1 @ 
% 0.21/0.50              sk_A))
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | (v2_struct_0 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['102', '123'])).
% 0.21/0.50  thf('125', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r1_waybel_0 @ sk_A @ sk_C_1 @ 
% 0.21/0.50           (sk_E_1 @ (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ sk_B)) @ sk_C_1 @ sk_A))
% 0.21/0.50          | (v2_struct_0 @ sk_B)
% 0.21/0.50          | (r1_tarski @ (k10_yellow_6 @ sk_A @ sk_B) @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | (r2_hidden @ (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ sk_B)) @ 
% 0.21/0.50             (k10_yellow_6 @ sk_A @ sk_C_1))
% 0.21/0.50          | (v2_struct_0 @ sk_C_1))),
% 0.21/0.50      inference('simplify', [status(thm)], ['124'])).
% 0.21/0.50  thf('126', plain,
% 0.21/0.50      ((m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_C_1) @ 
% 0.21/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('clc', [status(thm)], ['73', '74'])).
% 0.21/0.50  thf('127', plain,
% 0.21/0.50      (![X12 : $i, X13 : $i, X14 : $i, X16 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X12)
% 0.21/0.50          | ~ (v4_orders_2 @ X12)
% 0.21/0.50          | ~ (v7_waybel_0 @ X12)
% 0.21/0.50          | ~ (l1_waybel_0 @ X12 @ X13)
% 0.21/0.50          | ((X14) != (k10_yellow_6 @ X13 @ X12))
% 0.21/0.50          | (r2_hidden @ X16 @ X14)
% 0.21/0.50          | ~ (r1_waybel_0 @ X13 @ X12 @ (sk_E_1 @ X16 @ X12 @ X13))
% 0.21/0.50          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X13))
% 0.21/0.50          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.50          | ~ (l1_pre_topc @ X13)
% 0.21/0.50          | ~ (v2_pre_topc @ X13)
% 0.21/0.50          | (v2_struct_0 @ X13))),
% 0.21/0.50      inference('cnf', [status(esa)], [d18_yellow_6])).
% 0.21/0.50  thf('128', plain,
% 0.21/0.50      (![X12 : $i, X13 : $i, X16 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X13)
% 0.21/0.50          | ~ (v2_pre_topc @ X13)
% 0.21/0.50          | ~ (l1_pre_topc @ X13)
% 0.21/0.50          | ~ (m1_subset_1 @ (k10_yellow_6 @ X13 @ X12) @ 
% 0.21/0.50               (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.50          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X13))
% 0.21/0.50          | ~ (r1_waybel_0 @ X13 @ X12 @ (sk_E_1 @ X16 @ X12 @ X13))
% 0.21/0.50          | (r2_hidden @ X16 @ (k10_yellow_6 @ X13 @ X12))
% 0.21/0.50          | ~ (l1_waybel_0 @ X12 @ X13)
% 0.21/0.50          | ~ (v7_waybel_0 @ X12)
% 0.21/0.50          | ~ (v4_orders_2 @ X12)
% 0.21/0.50          | (v2_struct_0 @ X12))),
% 0.21/0.50      inference('simplify', [status(thm)], ['127'])).
% 0.21/0.50  thf('129', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_C_1)
% 0.21/0.50          | ~ (v4_orders_2 @ sk_C_1)
% 0.21/0.50          | ~ (v7_waybel_0 @ sk_C_1)
% 0.21/0.50          | ~ (l1_waybel_0 @ sk_C_1 @ sk_A)
% 0.21/0.50          | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ sk_C_1))
% 0.21/0.50          | ~ (r1_waybel_0 @ sk_A @ sk_C_1 @ (sk_E_1 @ X0 @ sk_C_1 @ sk_A))
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.50          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.50          | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['126', '128'])).
% 0.21/0.50  thf('130', plain, ((v4_orders_2 @ sk_C_1)),
% 0.21/0.50      inference('clc', [status(thm)], ['55', '56'])).
% 0.21/0.50  thf('131', plain, ((v7_waybel_0 @ sk_C_1)),
% 0.21/0.50      inference('clc', [status(thm)], ['43', '44'])).
% 0.21/0.50  thf('132', plain, ((l1_waybel_0 @ sk_C_1 @ sk_A)),
% 0.21/0.50      inference('clc', [status(thm)], ['29', '30'])).
% 0.21/0.50  thf('133', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('134', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('135', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_C_1)
% 0.21/0.50          | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ sk_C_1))
% 0.21/0.50          | ~ (r1_waybel_0 @ sk_A @ sk_C_1 @ (sk_E_1 @ X0 @ sk_C_1 @ sk_A))
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50          | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)],
% 0.21/0.50                ['129', '130', '131', '132', '133', '134'])).
% 0.21/0.50  thf('136', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_C_1)
% 0.21/0.50          | (r2_hidden @ (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ sk_B)) @ 
% 0.21/0.50             (k10_yellow_6 @ sk_A @ sk_C_1))
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | (r1_tarski @ (k10_yellow_6 @ sk_A @ sk_B) @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_B)
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | ~ (m1_subset_1 @ (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ sk_B)) @ 
% 0.21/0.50               (u1_struct_0 @ sk_A))
% 0.21/0.50          | (r2_hidden @ (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ sk_B)) @ 
% 0.21/0.50             (k10_yellow_6 @ sk_A @ sk_C_1))
% 0.21/0.50          | (v2_struct_0 @ sk_C_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['125', '135'])).
% 0.21/0.50  thf('137', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ sk_B)) @ 
% 0.21/0.50             (u1_struct_0 @ sk_A))
% 0.21/0.50          | (v2_struct_0 @ sk_B)
% 0.21/0.50          | (r1_tarski @ (k10_yellow_6 @ sk_A @ sk_B) @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | (r2_hidden @ (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ sk_B)) @ 
% 0.21/0.50             (k10_yellow_6 @ sk_A @ sk_C_1))
% 0.21/0.50          | (v2_struct_0 @ sk_C_1))),
% 0.21/0.50      inference('simplify', [status(thm)], ['136'])).
% 0.21/0.50  thf('138', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r1_tarski @ (k10_yellow_6 @ sk_A @ sk_B) @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_C_1)
% 0.21/0.50          | (r2_hidden @ (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ sk_B)) @ 
% 0.21/0.50             (k10_yellow_6 @ sk_A @ sk_C_1))
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | (r1_tarski @ (k10_yellow_6 @ sk_A @ sk_B) @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['16', '137'])).
% 0.21/0.50  thf('139', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_B)
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | (r2_hidden @ (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ sk_B)) @ 
% 0.21/0.50             (k10_yellow_6 @ sk_A @ sk_C_1))
% 0.21/0.50          | (v2_struct_0 @ sk_C_1)
% 0.21/0.50          | (r1_tarski @ (k10_yellow_6 @ sk_A @ sk_B) @ X0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['138'])).
% 0.21/0.50  thf('140', plain,
% 0.21/0.50      (![X1 : $i, X3 : $i]:
% 0.21/0.50         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.50  thf('141', plain,
% 0.21/0.50      (((r1_tarski @ (k10_yellow_6 @ sk_A @ sk_B) @ 
% 0.21/0.50         (k10_yellow_6 @ sk_A @ sk_C_1))
% 0.21/0.50        | (v2_struct_0 @ sk_C_1)
% 0.21/0.50        | (v2_struct_0 @ sk_A)
% 0.21/0.50        | (v2_struct_0 @ sk_B)
% 0.21/0.50        | (r1_tarski @ (k10_yellow_6 @ sk_A @ sk_B) @ 
% 0.21/0.50           (k10_yellow_6 @ sk_A @ sk_C_1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['139', '140'])).
% 0.21/0.50  thf('142', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_B)
% 0.21/0.50        | (v2_struct_0 @ sk_A)
% 0.21/0.50        | (v2_struct_0 @ sk_C_1)
% 0.21/0.50        | (r1_tarski @ (k10_yellow_6 @ sk_A @ sk_B) @ 
% 0.21/0.50           (k10_yellow_6 @ sk_A @ sk_C_1)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['141'])).
% 0.21/0.50  thf('143', plain,
% 0.21/0.50      (~ (r1_tarski @ (k10_yellow_6 @ sk_A @ sk_B) @ 
% 0.21/0.50          (k10_yellow_6 @ sk_A @ sk_C_1))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('144', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['142', '143'])).
% 0.21/0.50  thf('145', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.21/0.50      inference('clc', [status(thm)], ['70', '71'])).
% 0.21/0.50  thf('146', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('clc', [status(thm)], ['144', '145'])).
% 0.21/0.50  thf('147', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('148', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('clc', [status(thm)], ['146', '147'])).
% 0.21/0.50  thf('149', plain, ($false), inference('demod', [status(thm)], ['0', '148'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
