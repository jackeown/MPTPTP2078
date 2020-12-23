%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OACCBg1C6d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 355 expanded)
%              Number of leaves         :   33 ( 117 expanded)
%              Depth                    :   24
%              Number of atoms          : 1569 (5655 expanded)
%              Number of equality atoms :   11 (  14 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(v1_yellow_6_type,type,(
    v1_yellow_6: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i > $i > $i > $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k4_yellow_6_type,type,(
    k4_yellow_6: $i > $i > $i )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(t42_yellow_6,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v4_orders_2 @ B )
              & ( v7_waybel_0 @ B )
              & ( v1_yellow_6 @ B @ A )
              & ( l1_waybel_0 @ B @ A ) )
           => ( r2_hidden @ ( k4_yellow_6 @ A @ B ) @ ( k10_yellow_6 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t42_yellow_6])).

thf('0',plain,(
    ~ ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_yellow_6,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ( l1_waybel_0 @ B @ A ) )
     => ( m1_subset_1 @ ( k4_yellow_6 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_struct_0 @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( l1_waybel_0 @ X23 @ X22 )
      | ( m1_subset_1 @ ( k4_yellow_6 @ X22 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_yellow_6])).

thf('3',plain,
    ( ( m1_subset_1 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('5',plain,(
    ! [X1: $i] :
      ( ( l1_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('6',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
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

thf('11',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v7_waybel_0 @ X21 )
      | ~ ( l1_waybel_0 @ X21 @ X20 )
      | ( m1_subset_1 @ ( k10_yellow_6 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_yellow_6])).

thf('12',plain,
    ( ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v7_waybel_0 @ sk_B_1 )
    | ~ ( v4_orders_2 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v7_waybel_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v4_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','13','14','15','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['19','20'])).

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

thf('22',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v7_waybel_0 @ X14 )
      | ~ ( l1_waybel_0 @ X14 @ X15 )
      | ( X16
       != ( k10_yellow_6 @ X15 @ X14 ) )
      | ( r2_hidden @ X18 @ X16 )
      | ( m1_connsp_2 @ ( sk_E_2 @ X18 @ X14 @ X15 ) @ X15 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d18_yellow_6])).

thf('23',plain,(
    ! [X14: $i,X15: $i,X18: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ ( k10_yellow_6 @ X15 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X15 ) )
      | ( m1_connsp_2 @ ( sk_E_2 @ X18 @ X14 @ X15 ) @ X15 @ X18 )
      | ( r2_hidden @ X18 @ ( k10_yellow_6 @ X15 @ X14 ) )
      | ~ ( l1_waybel_0 @ X14 @ X15 )
      | ~ ( v7_waybel_0 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ~ ( v7_waybel_0 @ sk_B_1 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
      | ( m1_connsp_2 @ ( sk_E_2 @ X0 @ sk_B_1 @ sk_A ) @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    v4_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v7_waybel_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
      | ( m1_connsp_2 @ ( sk_E_2 @ X0 @ sk_B_1 @ sk_A ) @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','26','27','28','29'])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_connsp_2 @ ( sk_E_2 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_A ) @ sk_A @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['9','30'])).

thf('32',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_connsp_2 @ ( sk_E_2 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_A ) @ sk_A @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['9','30'])).

thf('33',plain,(
    m1_subset_1 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf(dt_m1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_connsp_2 @ C @ A @ B )
         => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('34',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_connsp_2 @ X4 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_connsp_2])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_A @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_A @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E_2 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['32','40'])).

thf(t6_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( m1_connsp_2 @ B @ A @ C )
               => ( r2_hidden @ C @ B ) ) ) ) ) )).

thf('42',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( m1_connsp_2 @ X5 @ X6 @ X7 )
      | ( r2_hidden @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t6_connsp_2])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_E_2 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_A ) )
      | ~ ( m1_connsp_2 @ ( sk_E_2 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_A ) @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_E_2 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_A ) )
      | ~ ( m1_connsp_2 @ ( sk_E_2 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_A ) @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ ( sk_E_2 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_A ) @ sk_A @ X0 )
      | ( r2_hidden @ X0 @ ( sk_E_2 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( m1_subset_1 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( sk_E_2 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','47'])).

thf('49',plain,(
    m1_subset_1 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( sk_E_2 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( sk_E_2 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    v1_yellow_6 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('54',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

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

thf('55',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( l1_waybel_0 @ X8 @ X9 )
      | ( m1_subset_1 @ ( sk_E @ X10 @ X11 @ X8 @ X9 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X8 ) )
      | ( r1_waybel_0 @ X9 @ X8 @ X11 )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d11_waybel_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r1_waybel_0 @ X1 @ X0 @ X2 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X2 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf(t25_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( v1_yellow_6 @ B @ A )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ( ( k2_waybel_0 @ A @ B @ C )
                = ( k4_yellow_6 @ A @ B ) ) ) ) ) )).

thf('60',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ~ ( v7_waybel_0 @ X24 )
      | ~ ( v1_yellow_6 @ X24 @ X25 )
      | ~ ( l1_waybel_0 @ X24 @ X25 )
      | ( ( k2_waybel_0 @ X25 @ X24 @ X26 )
        = ( k4_yellow_6 @ X25 @ X24 ) )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t25_yellow_6])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( ( k2_waybel_0 @ X1 @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) )
        = ( k4_yellow_6 @ X1 @ sk_B_1 ) )
      | ~ ( l1_waybel_0 @ sk_B_1 @ X1 )
      | ~ ( v1_yellow_6 @ sk_B_1 @ X1 )
      | ~ ( v7_waybel_0 @ sk_B_1 )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v7_waybel_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v4_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( ( k2_waybel_0 @ X1 @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) )
        = ( k4_yellow_6 @ X1 @ sk_B_1 ) )
      | ~ ( l1_waybel_0 @ sk_B_1 @ X1 )
      | ~ ( v1_yellow_6 @ sk_B_1 @ X1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_yellow_6 @ sk_B_1 @ X1 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ X1 )
      | ( ( k2_waybel_0 @ X1 @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) )
        = ( k4_yellow_6 @ X1 @ sk_B_1 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) )
        = ( k4_yellow_6 @ sk_A @ sk_B_1 ) )
      | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','65'])).

thf('67',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('68',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) )
        = ( k4_yellow_6 @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) )
        = ( k4_yellow_6 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( l1_waybel_0 @ X8 @ X9 )
      | ~ ( r2_hidden @ ( k2_waybel_0 @ X9 @ X8 @ ( sk_E @ X10 @ X11 @ X8 @ X9 ) ) @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X8 ) )
      | ( r1_waybel_0 @ X9 @ X8 @ X11 )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d11_waybel_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ~ ( m1_subset_1 @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('74',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf('75',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['72','73','74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E_2 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['51','77'])).

thf('79',plain,
    ( ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E_2 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('81',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v7_waybel_0 @ X14 )
      | ~ ( l1_waybel_0 @ X14 @ X15 )
      | ( X16
       != ( k10_yellow_6 @ X15 @ X14 ) )
      | ( r2_hidden @ X18 @ X16 )
      | ~ ( r1_waybel_0 @ X15 @ X14 @ ( sk_E_2 @ X18 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d18_yellow_6])).

thf('82',plain,(
    ! [X14: $i,X15: $i,X18: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ ( k10_yellow_6 @ X15 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X15 ) )
      | ~ ( r1_waybel_0 @ X15 @ X14 @ ( sk_E_2 @ X18 @ X14 @ X15 ) )
      | ( r2_hidden @ X18 @ ( k10_yellow_6 @ X15 @ X14 ) )
      | ~ ( l1_waybel_0 @ X14 @ X15 )
      | ~ ( v7_waybel_0 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ~ ( v7_waybel_0 @ sk_B_1 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
      | ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E_2 @ X0 @ sk_B_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','82'])).

thf('84',plain,(
    v4_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v7_waybel_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
      | ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E_2 @ X0 @ sk_B_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['83','84','85','86','87','88'])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['79','89'])).

thf('91',plain,(
    m1_subset_1 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    $false ),
    inference(demod,[status(thm)],['0','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OACCBg1C6d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:24:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 73 iterations in 0.071s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.51  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.51  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.22/0.51  thf(v1_yellow_6_type, type, v1_yellow_6: $i > $i > $o).
% 0.22/0.51  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.22/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.51  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.22/0.51  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.22/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.51  thf(sk_E_2_type, type, sk_E_2: $i > $i > $i > $i).
% 0.22/0.51  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.22/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.51  thf(k10_yellow_6_type, type, k10_yellow_6: $i > $i > $i).
% 0.22/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.51  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.22/0.51  thf(k4_yellow_6_type, type, k4_yellow_6: $i > $i > $i).
% 0.22/0.51  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 0.22/0.51  thf(t42_yellow_6, conjecture,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.22/0.51             ( v7_waybel_0 @ B ) & ( v1_yellow_6 @ B @ A ) & 
% 0.22/0.51             ( l1_waybel_0 @ B @ A ) ) =>
% 0.22/0.51           ( r2_hidden @ ( k4_yellow_6 @ A @ B ) @ ( k10_yellow_6 @ A @ B ) ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i]:
% 0.22/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.51            ( l1_pre_topc @ A ) ) =>
% 0.22/0.51          ( ![B:$i]:
% 0.22/0.51            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.22/0.51                ( v7_waybel_0 @ B ) & ( v1_yellow_6 @ B @ A ) & 
% 0.22/0.51                ( l1_waybel_0 @ B @ A ) ) =>
% 0.22/0.51              ( r2_hidden @ ( k4_yellow_6 @ A @ B ) @ ( k10_yellow_6 @ A @ B ) ) ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t42_yellow_6])).
% 0.22/0.51  thf('0', plain,
% 0.22/0.51      (~ (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.22/0.51          (k10_yellow_6 @ sk_A @ sk_B_1))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('1', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(dt_k4_yellow_6, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.22/0.51         ( l1_waybel_0 @ B @ A ) ) =>
% 0.22/0.51       ( m1_subset_1 @ ( k4_yellow_6 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.22/0.51  thf('2', plain,
% 0.22/0.51      (![X22 : $i, X23 : $i]:
% 0.22/0.51         (~ (l1_struct_0 @ X22)
% 0.22/0.51          | (v2_struct_0 @ X22)
% 0.22/0.51          | ~ (l1_waybel_0 @ X23 @ X22)
% 0.22/0.51          | (m1_subset_1 @ (k4_yellow_6 @ X22 @ X23) @ (u1_struct_0 @ X22)))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_k4_yellow_6])).
% 0.22/0.51  thf('3', plain,
% 0.22/0.51      (((m1_subset_1 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.22/0.51        | (v2_struct_0 @ sk_A)
% 0.22/0.51        | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.51  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(dt_l1_pre_topc, axiom,
% 0.22/0.51    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.22/0.51  thf('5', plain, (![X1 : $i]: ((l1_struct_0 @ X1) | ~ (l1_pre_topc @ X1))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.51  thf('6', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.51  thf('7', plain,
% 0.22/0.51      (((m1_subset_1 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.22/0.51        | (v2_struct_0 @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['3', '6'])).
% 0.22/0.51  thf('8', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('9', plain,
% 0.22/0.51      ((m1_subset_1 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.22/0.51      inference('clc', [status(thm)], ['7', '8'])).
% 0.22/0.51  thf('10', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(dt_k10_yellow_6, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.51         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 0.22/0.51         ( v4_orders_2 @ B ) & ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.22/0.51       ( m1_subset_1 @
% 0.22/0.51         ( k10_yellow_6 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.51  thf('11', plain,
% 0.22/0.51      (![X20 : $i, X21 : $i]:
% 0.22/0.51         (~ (l1_pre_topc @ X20)
% 0.22/0.51          | ~ (v2_pre_topc @ X20)
% 0.22/0.51          | (v2_struct_0 @ X20)
% 0.22/0.51          | (v2_struct_0 @ X21)
% 0.22/0.51          | ~ (v4_orders_2 @ X21)
% 0.22/0.51          | ~ (v7_waybel_0 @ X21)
% 0.22/0.51          | ~ (l1_waybel_0 @ X21 @ X20)
% 0.22/0.51          | (m1_subset_1 @ (k10_yellow_6 @ X20 @ X21) @ 
% 0.22/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X20))))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_k10_yellow_6])).
% 0.22/0.51  thf('12', plain,
% 0.22/0.51      (((m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.22/0.51         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.51        | ~ (v7_waybel_0 @ sk_B_1)
% 0.22/0.51        | ~ (v4_orders_2 @ sk_B_1)
% 0.22/0.51        | (v2_struct_0 @ sk_B_1)
% 0.22/0.51        | (v2_struct_0 @ sk_A)
% 0.22/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.51  thf('13', plain, ((v7_waybel_0 @ sk_B_1)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('14', plain, ((v4_orders_2 @ sk_B_1)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('15', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('17', plain,
% 0.22/0.51      (((m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.22/0.51         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.51        | (v2_struct_0 @ sk_B_1)
% 0.22/0.51        | (v2_struct_0 @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['12', '13', '14', '15', '16'])).
% 0.22/0.51  thf('18', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('19', plain,
% 0.22/0.51      (((v2_struct_0 @ sk_A)
% 0.22/0.51        | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.22/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.51      inference('clc', [status(thm)], ['17', '18'])).
% 0.22/0.51  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('21', plain,
% 0.22/0.51      ((m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.22/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('clc', [status(thm)], ['19', '20'])).
% 0.22/0.51  thf(d18_yellow_6, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.22/0.51             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.22/0.51           ( ![C:$i]:
% 0.22/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51               ( ( ( C ) = ( k10_yellow_6 @ A @ B ) ) <=>
% 0.22/0.51                 ( ![D:$i]:
% 0.22/0.51                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.51                     ( ( r2_hidden @ D @ C ) <=>
% 0.22/0.51                       ( ![E:$i]:
% 0.22/0.51                         ( ( m1_connsp_2 @ E @ A @ D ) =>
% 0.22/0.51                           ( r1_waybel_0 @ A @ B @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.51  thf('22', plain,
% 0.22/0.51      (![X14 : $i, X15 : $i, X16 : $i, X18 : $i]:
% 0.22/0.51         ((v2_struct_0 @ X14)
% 0.22/0.51          | ~ (v4_orders_2 @ X14)
% 0.22/0.51          | ~ (v7_waybel_0 @ X14)
% 0.22/0.51          | ~ (l1_waybel_0 @ X14 @ X15)
% 0.22/0.51          | ((X16) != (k10_yellow_6 @ X15 @ X14))
% 0.22/0.51          | (r2_hidden @ X18 @ X16)
% 0.22/0.51          | (m1_connsp_2 @ (sk_E_2 @ X18 @ X14 @ X15) @ X15 @ X18)
% 0.22/0.51          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X15))
% 0.22/0.51          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.22/0.51          | ~ (l1_pre_topc @ X15)
% 0.22/0.51          | ~ (v2_pre_topc @ X15)
% 0.22/0.51          | (v2_struct_0 @ X15))),
% 0.22/0.51      inference('cnf', [status(esa)], [d18_yellow_6])).
% 0.22/0.51  thf('23', plain,
% 0.22/0.51      (![X14 : $i, X15 : $i, X18 : $i]:
% 0.22/0.51         ((v2_struct_0 @ X15)
% 0.22/0.51          | ~ (v2_pre_topc @ X15)
% 0.22/0.51          | ~ (l1_pre_topc @ X15)
% 0.22/0.51          | ~ (m1_subset_1 @ (k10_yellow_6 @ X15 @ X14) @ 
% 0.22/0.51               (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.22/0.51          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X15))
% 0.22/0.51          | (m1_connsp_2 @ (sk_E_2 @ X18 @ X14 @ X15) @ X15 @ X18)
% 0.22/0.51          | (r2_hidden @ X18 @ (k10_yellow_6 @ X15 @ X14))
% 0.22/0.51          | ~ (l1_waybel_0 @ X14 @ X15)
% 0.22/0.51          | ~ (v7_waybel_0 @ X14)
% 0.22/0.51          | ~ (v4_orders_2 @ X14)
% 0.22/0.51          | (v2_struct_0 @ X14))),
% 0.22/0.51      inference('simplify', [status(thm)], ['22'])).
% 0.22/0.51  thf('24', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((v2_struct_0 @ sk_B_1)
% 0.22/0.51          | ~ (v4_orders_2 @ sk_B_1)
% 0.22/0.51          | ~ (v7_waybel_0 @ sk_B_1)
% 0.22/0.51          | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.22/0.51          | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.22/0.51          | (m1_connsp_2 @ (sk_E_2 @ X0 @ sk_B_1 @ sk_A) @ sk_A @ X0)
% 0.22/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.51          | (v2_struct_0 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['21', '23'])).
% 0.22/0.51  thf('25', plain, ((v4_orders_2 @ sk_B_1)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('26', plain, ((v7_waybel_0 @ sk_B_1)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('27', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('30', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((v2_struct_0 @ sk_B_1)
% 0.22/0.51          | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.22/0.51          | (m1_connsp_2 @ (sk_E_2 @ X0 @ sk_B_1 @ sk_A) @ sk_A @ X0)
% 0.22/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.51          | (v2_struct_0 @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['24', '25', '26', '27', '28', '29'])).
% 0.22/0.51  thf('31', plain,
% 0.22/0.51      (((v2_struct_0 @ sk_A)
% 0.22/0.51        | (m1_connsp_2 @ 
% 0.22/0.51           (sk_E_2 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_A) @ sk_A @ 
% 0.22/0.51           (k4_yellow_6 @ sk_A @ sk_B_1))
% 0.22/0.51        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.22/0.51           (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.22/0.51        | (v2_struct_0 @ sk_B_1))),
% 0.22/0.51      inference('sup-', [status(thm)], ['9', '30'])).
% 0.22/0.51  thf('32', plain,
% 0.22/0.51      (((v2_struct_0 @ sk_A)
% 0.22/0.51        | (m1_connsp_2 @ 
% 0.22/0.51           (sk_E_2 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_A) @ sk_A @ 
% 0.22/0.51           (k4_yellow_6 @ sk_A @ sk_B_1))
% 0.22/0.51        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.22/0.51           (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.22/0.51        | (v2_struct_0 @ sk_B_1))),
% 0.22/0.51      inference('sup-', [status(thm)], ['9', '30'])).
% 0.22/0.51  thf('33', plain,
% 0.22/0.51      ((m1_subset_1 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.22/0.51      inference('clc', [status(thm)], ['7', '8'])).
% 0.22/0.51  thf(dt_m1_connsp_2, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.51         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51       ( ![C:$i]:
% 0.22/0.51         ( ( m1_connsp_2 @ C @ A @ B ) =>
% 0.22/0.51           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.22/0.51  thf('34', plain,
% 0.22/0.51      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.51         (~ (l1_pre_topc @ X2)
% 0.22/0.51          | ~ (v2_pre_topc @ X2)
% 0.22/0.51          | (v2_struct_0 @ X2)
% 0.22/0.51          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.22/0.51          | (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.22/0.51          | ~ (m1_connsp_2 @ X4 @ X2 @ X3))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 0.22/0.51  thf('35', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (m1_connsp_2 @ X0 @ sk_A @ (k4_yellow_6 @ sk_A @ sk_B_1))
% 0.22/0.51          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.51          | (v2_struct_0 @ sk_A)
% 0.22/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.51          | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['33', '34'])).
% 0.22/0.51  thf('36', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('38', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (m1_connsp_2 @ X0 @ sk_A @ (k4_yellow_6 @ sk_A @ sk_B_1))
% 0.22/0.51          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.51          | (v2_struct_0 @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.22/0.51  thf('39', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('40', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.51          | ~ (m1_connsp_2 @ X0 @ sk_A @ (k4_yellow_6 @ sk_A @ sk_B_1)))),
% 0.22/0.51      inference('clc', [status(thm)], ['38', '39'])).
% 0.22/0.51  thf('41', plain,
% 0.22/0.51      (((v2_struct_0 @ sk_B_1)
% 0.22/0.51        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.22/0.51           (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.22/0.51        | (v2_struct_0 @ sk_A)
% 0.22/0.51        | (m1_subset_1 @ 
% 0.22/0.51           (sk_E_2 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_A) @ 
% 0.22/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['32', '40'])).
% 0.22/0.51  thf(t6_connsp_2, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51           ( ![C:$i]:
% 0.22/0.51             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.51               ( ( m1_connsp_2 @ B @ A @ C ) => ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.22/0.51  thf('42', plain,
% 0.22/0.51      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.22/0.51          | ~ (m1_connsp_2 @ X5 @ X6 @ X7)
% 0.22/0.51          | (r2_hidden @ X7 @ X5)
% 0.22/0.51          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 0.22/0.51          | ~ (l1_pre_topc @ X6)
% 0.22/0.51          | ~ (v2_pre_topc @ X6)
% 0.22/0.51          | (v2_struct_0 @ X6))),
% 0.22/0.51      inference('cnf', [status(esa)], [t6_connsp_2])).
% 0.22/0.51  thf('43', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((v2_struct_0 @ sk_A)
% 0.22/0.51          | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.22/0.51             (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.22/0.51          | (v2_struct_0 @ sk_B_1)
% 0.22/0.51          | (v2_struct_0 @ sk_A)
% 0.22/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.51          | (r2_hidden @ X0 @ 
% 0.22/0.51             (sk_E_2 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_A))
% 0.22/0.51          | ~ (m1_connsp_2 @ 
% 0.22/0.51               (sk_E_2 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_A) @ 
% 0.22/0.51               sk_A @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['41', '42'])).
% 0.22/0.51  thf('44', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('46', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((v2_struct_0 @ sk_A)
% 0.22/0.51          | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.22/0.51             (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.22/0.51          | (v2_struct_0 @ sk_B_1)
% 0.22/0.51          | (v2_struct_0 @ sk_A)
% 0.22/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.51          | (r2_hidden @ X0 @ 
% 0.22/0.51             (sk_E_2 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_A))
% 0.22/0.51          | ~ (m1_connsp_2 @ 
% 0.22/0.51               (sk_E_2 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_A) @ 
% 0.22/0.51               sk_A @ X0))),
% 0.22/0.51      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.22/0.51  thf('47', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (m1_connsp_2 @ 
% 0.22/0.51             (sk_E_2 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_A) @ sk_A @ 
% 0.22/0.51             X0)
% 0.22/0.51          | (r2_hidden @ X0 @ 
% 0.22/0.51             (sk_E_2 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_A))
% 0.22/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.51          | (v2_struct_0 @ sk_B_1)
% 0.22/0.51          | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.22/0.51             (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.22/0.51          | (v2_struct_0 @ sk_A))),
% 0.22/0.51      inference('simplify', [status(thm)], ['46'])).
% 0.22/0.51  thf('48', plain,
% 0.22/0.51      (((v2_struct_0 @ sk_B_1)
% 0.22/0.51        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.22/0.51           (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.22/0.51        | (v2_struct_0 @ sk_A)
% 0.22/0.51        | (v2_struct_0 @ sk_A)
% 0.22/0.51        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.22/0.51           (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.22/0.51        | (v2_struct_0 @ sk_B_1)
% 0.22/0.51        | ~ (m1_subset_1 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.22/0.51        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.22/0.51           (sk_E_2 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['31', '47'])).
% 0.22/0.51  thf('49', plain,
% 0.22/0.51      ((m1_subset_1 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.22/0.51      inference('clc', [status(thm)], ['7', '8'])).
% 0.22/0.51  thf('50', plain,
% 0.22/0.51      (((v2_struct_0 @ sk_B_1)
% 0.22/0.51        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.22/0.51           (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.22/0.51        | (v2_struct_0 @ sk_A)
% 0.22/0.51        | (v2_struct_0 @ sk_A)
% 0.22/0.51        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.22/0.51           (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.22/0.51        | (v2_struct_0 @ sk_B_1)
% 0.22/0.51        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.22/0.51           (sk_E_2 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_A)))),
% 0.22/0.51      inference('demod', [status(thm)], ['48', '49'])).
% 0.22/0.51  thf('51', plain,
% 0.22/0.51      (((r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.22/0.51         (sk_E_2 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_A))
% 0.22/0.51        | (v2_struct_0 @ sk_A)
% 0.22/0.51        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.22/0.51           (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.22/0.51        | (v2_struct_0 @ sk_B_1))),
% 0.22/0.51      inference('simplify', [status(thm)], ['50'])).
% 0.22/0.51  thf('52', plain, ((v1_yellow_6 @ sk_B_1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('53', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(existence_m1_subset_1, axiom,
% 0.22/0.51    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.22/0.51  thf('54', plain, (![X0 : $i]: (m1_subset_1 @ (sk_B @ X0) @ X0)),
% 0.22/0.51      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.22/0.51  thf(d11_waybel_0, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.22/0.51           ( ![C:$i]:
% 0.22/0.51             ( ( r1_waybel_0 @ A @ B @ C ) <=>
% 0.22/0.51               ( ?[D:$i]:
% 0.22/0.51                 ( ( ![E:$i]:
% 0.22/0.51                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.22/0.51                       ( ( r1_orders_2 @ B @ D @ E ) =>
% 0.22/0.51                         ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) ) ) ) & 
% 0.22/0.51                   ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ))).
% 0.22/0.51  thf('55', plain,
% 0.22/0.51      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.51         ((v2_struct_0 @ X8)
% 0.22/0.51          | ~ (l1_waybel_0 @ X8 @ X9)
% 0.22/0.51          | (m1_subset_1 @ (sk_E @ X10 @ X11 @ X8 @ X9) @ (u1_struct_0 @ X8))
% 0.22/0.51          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X8))
% 0.22/0.51          | (r1_waybel_0 @ X9 @ X8 @ X11)
% 0.22/0.51          | ~ (l1_struct_0 @ X9)
% 0.22/0.51          | (v2_struct_0 @ X9))),
% 0.22/0.51      inference('cnf', [status(esa)], [d11_waybel_0])).
% 0.22/0.51  thf('56', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         ((v2_struct_0 @ X1)
% 0.22/0.51          | ~ (l1_struct_0 @ X1)
% 0.22/0.51          | (r1_waybel_0 @ X1 @ X0 @ X2)
% 0.22/0.51          | (m1_subset_1 @ 
% 0.22/0.51             (sk_E @ (sk_B @ (u1_struct_0 @ X0)) @ X2 @ X0 @ X1) @ 
% 0.22/0.51             (u1_struct_0 @ X0))
% 0.22/0.51          | ~ (l1_waybel_0 @ X0 @ X1)
% 0.22/0.51          | (v2_struct_0 @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['54', '55'])).
% 0.22/0.51  thf('57', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((v2_struct_0 @ sk_B_1)
% 0.22/0.51          | (m1_subset_1 @ 
% 0.22/0.51             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.22/0.51             (u1_struct_0 @ sk_B_1))
% 0.22/0.51          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.22/0.51          | ~ (l1_struct_0 @ sk_A)
% 0.22/0.51          | (v2_struct_0 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['53', '56'])).
% 0.22/0.51  thf('58', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.51  thf('59', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((v2_struct_0 @ sk_B_1)
% 0.22/0.51          | (m1_subset_1 @ 
% 0.22/0.51             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.22/0.51             (u1_struct_0 @ sk_B_1))
% 0.22/0.51          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.22/0.51          | (v2_struct_0 @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['57', '58'])).
% 0.22/0.51  thf(t25_yellow_6, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.22/0.51             ( v7_waybel_0 @ B ) & ( v1_yellow_6 @ B @ A ) & 
% 0.22/0.51             ( l1_waybel_0 @ B @ A ) ) =>
% 0.22/0.51           ( ![C:$i]:
% 0.22/0.51             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.22/0.51               ( ( k2_waybel_0 @ A @ B @ C ) = ( k4_yellow_6 @ A @ B ) ) ) ) ) ) ))).
% 0.22/0.51  thf('60', plain,
% 0.22/0.51      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.22/0.51         ((v2_struct_0 @ X24)
% 0.22/0.51          | ~ (v4_orders_2 @ X24)
% 0.22/0.51          | ~ (v7_waybel_0 @ X24)
% 0.22/0.51          | ~ (v1_yellow_6 @ X24 @ X25)
% 0.22/0.51          | ~ (l1_waybel_0 @ X24 @ X25)
% 0.22/0.51          | ((k2_waybel_0 @ X25 @ X24 @ X26) = (k4_yellow_6 @ X25 @ X24))
% 0.22/0.51          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X24))
% 0.22/0.51          | ~ (l1_struct_0 @ X25)
% 0.22/0.51          | (v2_struct_0 @ X25))),
% 0.22/0.51      inference('cnf', [status(esa)], [t25_yellow_6])).
% 0.22/0.51  thf('61', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         ((v2_struct_0 @ sk_A)
% 0.22/0.51          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.22/0.51          | (v2_struct_0 @ sk_B_1)
% 0.22/0.51          | (v2_struct_0 @ X1)
% 0.22/0.51          | ~ (l1_struct_0 @ X1)
% 0.22/0.51          | ((k2_waybel_0 @ X1 @ sk_B_1 @ 
% 0.22/0.51              (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A))
% 0.22/0.51              = (k4_yellow_6 @ X1 @ sk_B_1))
% 0.22/0.51          | ~ (l1_waybel_0 @ sk_B_1 @ X1)
% 0.22/0.51          | ~ (v1_yellow_6 @ sk_B_1 @ X1)
% 0.22/0.51          | ~ (v7_waybel_0 @ sk_B_1)
% 0.22/0.51          | ~ (v4_orders_2 @ sk_B_1)
% 0.22/0.51          | (v2_struct_0 @ sk_B_1))),
% 0.22/0.51      inference('sup-', [status(thm)], ['59', '60'])).
% 0.22/0.51  thf('62', plain, ((v7_waybel_0 @ sk_B_1)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('63', plain, ((v4_orders_2 @ sk_B_1)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('64', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         ((v2_struct_0 @ sk_A)
% 0.22/0.51          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.22/0.51          | (v2_struct_0 @ sk_B_1)
% 0.22/0.51          | (v2_struct_0 @ X1)
% 0.22/0.51          | ~ (l1_struct_0 @ X1)
% 0.22/0.51          | ((k2_waybel_0 @ X1 @ sk_B_1 @ 
% 0.22/0.51              (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A))
% 0.22/0.51              = (k4_yellow_6 @ X1 @ sk_B_1))
% 0.22/0.51          | ~ (l1_waybel_0 @ sk_B_1 @ X1)
% 0.22/0.51          | ~ (v1_yellow_6 @ sk_B_1 @ X1)
% 0.22/0.51          | (v2_struct_0 @ sk_B_1))),
% 0.22/0.51      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.22/0.51  thf('65', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         (~ (v1_yellow_6 @ sk_B_1 @ X1)
% 0.22/0.51          | ~ (l1_waybel_0 @ sk_B_1 @ X1)
% 0.22/0.51          | ((k2_waybel_0 @ X1 @ sk_B_1 @ 
% 0.22/0.51              (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A))
% 0.22/0.51              = (k4_yellow_6 @ X1 @ sk_B_1))
% 0.22/0.51          | ~ (l1_struct_0 @ X1)
% 0.22/0.51          | (v2_struct_0 @ X1)
% 0.22/0.51          | (v2_struct_0 @ sk_B_1)
% 0.22/0.51          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.22/0.51          | (v2_struct_0 @ sk_A))),
% 0.22/0.51      inference('simplify', [status(thm)], ['64'])).
% 0.22/0.51  thf('66', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((v2_struct_0 @ sk_A)
% 0.22/0.51          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.22/0.51          | (v2_struct_0 @ sk_B_1)
% 0.22/0.51          | (v2_struct_0 @ sk_A)
% 0.22/0.51          | ~ (l1_struct_0 @ sk_A)
% 0.22/0.51          | ((k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.22/0.51              (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A))
% 0.22/0.51              = (k4_yellow_6 @ sk_A @ sk_B_1))
% 0.22/0.51          | ~ (l1_waybel_0 @ sk_B_1 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['52', '65'])).
% 0.22/0.51  thf('67', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.51  thf('68', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('69', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((v2_struct_0 @ sk_A)
% 0.22/0.51          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.22/0.51          | (v2_struct_0 @ sk_B_1)
% 0.22/0.51          | (v2_struct_0 @ sk_A)
% 0.22/0.51          | ((k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.22/0.51              (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A))
% 0.22/0.51              = (k4_yellow_6 @ sk_A @ sk_B_1)))),
% 0.22/0.51      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.22/0.51  thf('70', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (((k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.22/0.51            (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A))
% 0.22/0.51            = (k4_yellow_6 @ sk_A @ sk_B_1))
% 0.22/0.51          | (v2_struct_0 @ sk_B_1)
% 0.22/0.51          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.22/0.51          | (v2_struct_0 @ sk_A))),
% 0.22/0.51      inference('simplify', [status(thm)], ['69'])).
% 0.22/0.51  thf('71', plain,
% 0.22/0.51      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.51         ((v2_struct_0 @ X8)
% 0.22/0.51          | ~ (l1_waybel_0 @ X8 @ X9)
% 0.22/0.51          | ~ (r2_hidden @ 
% 0.22/0.51               (k2_waybel_0 @ X9 @ X8 @ (sk_E @ X10 @ X11 @ X8 @ X9)) @ X11)
% 0.22/0.51          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X8))
% 0.22/0.51          | (r1_waybel_0 @ X9 @ X8 @ X11)
% 0.22/0.51          | ~ (l1_struct_0 @ X9)
% 0.22/0.51          | (v2_struct_0 @ X9))),
% 0.22/0.51      inference('cnf', [status(esa)], [d11_waybel_0])).
% 0.22/0.51  thf('72', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ X0)
% 0.22/0.51          | (v2_struct_0 @ sk_A)
% 0.22/0.51          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.22/0.51          | (v2_struct_0 @ sk_B_1)
% 0.22/0.51          | (v2_struct_0 @ sk_A)
% 0.22/0.51          | ~ (l1_struct_0 @ sk_A)
% 0.22/0.51          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.22/0.51          | ~ (m1_subset_1 @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ 
% 0.22/0.51               (u1_struct_0 @ sk_B_1))
% 0.22/0.51          | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.22/0.51          | (v2_struct_0 @ sk_B_1))),
% 0.22/0.51      inference('sup-', [status(thm)], ['70', '71'])).
% 0.22/0.51  thf('73', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.51  thf('74', plain, (![X0 : $i]: (m1_subset_1 @ (sk_B @ X0) @ X0)),
% 0.22/0.51      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.22/0.51  thf('75', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('76', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ X0)
% 0.22/0.51          | (v2_struct_0 @ sk_A)
% 0.22/0.51          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.22/0.51          | (v2_struct_0 @ sk_B_1)
% 0.22/0.51          | (v2_struct_0 @ sk_A)
% 0.22/0.51          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.22/0.51          | (v2_struct_0 @ sk_B_1))),
% 0.22/0.51      inference('demod', [status(thm)], ['72', '73', '74', '75'])).
% 0.22/0.51  thf('77', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((v2_struct_0 @ sk_B_1)
% 0.22/0.51          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.22/0.51          | (v2_struct_0 @ sk_A)
% 0.22/0.51          | ~ (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ X0))),
% 0.22/0.51      inference('simplify', [status(thm)], ['76'])).
% 0.22/0.51  thf('78', plain,
% 0.22/0.51      (((v2_struct_0 @ sk_B_1)
% 0.22/0.51        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.22/0.51           (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.22/0.51        | (v2_struct_0 @ sk_A)
% 0.22/0.51        | (v2_struct_0 @ sk_A)
% 0.22/0.51        | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.22/0.51           (sk_E_2 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_A))
% 0.22/0.51        | (v2_struct_0 @ sk_B_1))),
% 0.22/0.51      inference('sup-', [status(thm)], ['51', '77'])).
% 0.22/0.51  thf('79', plain,
% 0.22/0.51      (((r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.22/0.51         (sk_E_2 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_A))
% 0.22/0.51        | (v2_struct_0 @ sk_A)
% 0.22/0.51        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.22/0.51           (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.22/0.51        | (v2_struct_0 @ sk_B_1))),
% 0.22/0.51      inference('simplify', [status(thm)], ['78'])).
% 0.22/0.51  thf('80', plain,
% 0.22/0.51      ((m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.22/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('clc', [status(thm)], ['19', '20'])).
% 0.22/0.51  thf('81', plain,
% 0.22/0.51      (![X14 : $i, X15 : $i, X16 : $i, X18 : $i]:
% 0.22/0.51         ((v2_struct_0 @ X14)
% 0.22/0.51          | ~ (v4_orders_2 @ X14)
% 0.22/0.51          | ~ (v7_waybel_0 @ X14)
% 0.22/0.51          | ~ (l1_waybel_0 @ X14 @ X15)
% 0.22/0.51          | ((X16) != (k10_yellow_6 @ X15 @ X14))
% 0.22/0.51          | (r2_hidden @ X18 @ X16)
% 0.22/0.51          | ~ (r1_waybel_0 @ X15 @ X14 @ (sk_E_2 @ X18 @ X14 @ X15))
% 0.22/0.51          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X15))
% 0.22/0.51          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.22/0.51          | ~ (l1_pre_topc @ X15)
% 0.22/0.51          | ~ (v2_pre_topc @ X15)
% 0.22/0.51          | (v2_struct_0 @ X15))),
% 0.22/0.51      inference('cnf', [status(esa)], [d18_yellow_6])).
% 0.22/0.51  thf('82', plain,
% 0.22/0.51      (![X14 : $i, X15 : $i, X18 : $i]:
% 0.22/0.51         ((v2_struct_0 @ X15)
% 0.22/0.51          | ~ (v2_pre_topc @ X15)
% 0.22/0.51          | ~ (l1_pre_topc @ X15)
% 0.22/0.51          | ~ (m1_subset_1 @ (k10_yellow_6 @ X15 @ X14) @ 
% 0.22/0.51               (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.22/0.51          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X15))
% 0.22/0.51          | ~ (r1_waybel_0 @ X15 @ X14 @ (sk_E_2 @ X18 @ X14 @ X15))
% 0.22/0.51          | (r2_hidden @ X18 @ (k10_yellow_6 @ X15 @ X14))
% 0.22/0.51          | ~ (l1_waybel_0 @ X14 @ X15)
% 0.22/0.51          | ~ (v7_waybel_0 @ X14)
% 0.22/0.51          | ~ (v4_orders_2 @ X14)
% 0.22/0.51          | (v2_struct_0 @ X14))),
% 0.22/0.51      inference('simplify', [status(thm)], ['81'])).
% 0.22/0.51  thf('83', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((v2_struct_0 @ sk_B_1)
% 0.22/0.51          | ~ (v4_orders_2 @ sk_B_1)
% 0.22/0.51          | ~ (v7_waybel_0 @ sk_B_1)
% 0.22/0.51          | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.22/0.51          | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.22/0.51          | ~ (r1_waybel_0 @ sk_A @ sk_B_1 @ (sk_E_2 @ X0 @ sk_B_1 @ sk_A))
% 0.22/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.51          | (v2_struct_0 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['80', '82'])).
% 0.22/0.51  thf('84', plain, ((v4_orders_2 @ sk_B_1)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('85', plain, ((v7_waybel_0 @ sk_B_1)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('86', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('88', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('89', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((v2_struct_0 @ sk_B_1)
% 0.22/0.51          | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.22/0.51          | ~ (r1_waybel_0 @ sk_A @ sk_B_1 @ (sk_E_2 @ X0 @ sk_B_1 @ sk_A))
% 0.22/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.51          | (v2_struct_0 @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['83', '84', '85', '86', '87', '88'])).
% 0.22/0.51  thf('90', plain,
% 0.22/0.51      (((v2_struct_0 @ sk_B_1)
% 0.22/0.51        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.22/0.51           (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.22/0.51        | (v2_struct_0 @ sk_A)
% 0.22/0.51        | (v2_struct_0 @ sk_A)
% 0.22/0.51        | ~ (m1_subset_1 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.22/0.51        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.22/0.51           (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.22/0.51        | (v2_struct_0 @ sk_B_1))),
% 0.22/0.51      inference('sup-', [status(thm)], ['79', '89'])).
% 0.22/0.51  thf('91', plain,
% 0.22/0.51      ((m1_subset_1 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.22/0.51      inference('clc', [status(thm)], ['7', '8'])).
% 0.22/0.51  thf('92', plain,
% 0.22/0.51      (((v2_struct_0 @ sk_B_1)
% 0.22/0.51        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.22/0.51           (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.22/0.51        | (v2_struct_0 @ sk_A)
% 0.22/0.51        | (v2_struct_0 @ sk_A)
% 0.22/0.51        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.22/0.51           (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.22/0.51        | (v2_struct_0 @ sk_B_1))),
% 0.22/0.51      inference('demod', [status(thm)], ['90', '91'])).
% 0.22/0.51  thf('93', plain,
% 0.22/0.51      (((v2_struct_0 @ sk_A)
% 0.22/0.51        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.22/0.51           (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.22/0.51        | (v2_struct_0 @ sk_B_1))),
% 0.22/0.51      inference('simplify', [status(thm)], ['92'])).
% 0.22/0.51  thf('94', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('95', plain,
% 0.22/0.51      (((v2_struct_0 @ sk_B_1)
% 0.22/0.51        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.22/0.51           (k10_yellow_6 @ sk_A @ sk_B_1)))),
% 0.22/0.51      inference('clc', [status(thm)], ['93', '94'])).
% 0.22/0.51  thf('96', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('97', plain,
% 0.22/0.51      ((r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.22/0.51        (k10_yellow_6 @ sk_A @ sk_B_1))),
% 0.22/0.51      inference('clc', [status(thm)], ['95', '96'])).
% 0.22/0.51  thf('98', plain, ($false), inference('demod', [status(thm)], ['0', '97'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
