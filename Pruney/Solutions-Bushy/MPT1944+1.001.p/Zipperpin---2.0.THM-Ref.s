%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1944+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9PDak5NRyz

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:35 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 355 expanded)
%              Number of leaves         :   33 ( 117 expanded)
%              Depth                    :   24
%              Number of atoms          : 1569 (5655 expanded)
%              Number of equality atoms :   11 (  14 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_2_type,type,(
    sk_E_2: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_yellow_6_type,type,(
    v1_yellow_6: $i > $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(k4_yellow_6_type,type,(
    k4_yellow_6: $i > $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

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
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( l1_waybel_0 @ X15 @ X14 )
      | ( m1_subset_1 @ ( k4_yellow_6 @ X14 @ X15 ) @ ( u1_struct_0 @ X14 ) ) ) ),
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
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 )
      | ( v2_struct_0 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v7_waybel_0 @ X13 )
      | ~ ( l1_waybel_0 @ X13 @ X12 )
      | ( m1_subset_1 @ ( k10_yellow_6 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i,X10: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( v4_orders_2 @ X6 )
      | ~ ( v7_waybel_0 @ X6 )
      | ~ ( l1_waybel_0 @ X6 @ X7 )
      | ( X8
       != ( k10_yellow_6 @ X7 @ X6 ) )
      | ( r2_hidden @ X10 @ X8 )
      | ( m1_connsp_2 @ ( sk_E_2 @ X10 @ X6 @ X7 ) @ X7 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d18_yellow_6])).

thf('23',plain,(
    ! [X6: $i,X7: $i,X10: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_subset_1 @ ( k10_yellow_6 @ X7 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X7 ) )
      | ( m1_connsp_2 @ ( sk_E_2 @ X10 @ X6 @ X7 ) @ X7 @ X10 )
      | ( r2_hidden @ X10 @ ( k10_yellow_6 @ X7 @ X6 ) )
      | ~ ( l1_waybel_0 @ X6 @ X7 )
      | ~ ( v7_waybel_0 @ X6 )
      | ~ ( v4_orders_2 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m1_connsp_2 @ X19 @ X17 @ X18 ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( m1_connsp_2 @ X24 @ X25 @ X26 )
      | ( r2_hidden @ X26 @ X24 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
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
    ! [X20: $i] :
      ( m1_subset_1 @ ( sk_B @ X20 ) @ X20 ) ),
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
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( m1_subset_1 @ ( sk_E @ X2 @ X3 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_waybel_0 @ X1 @ X0 @ X3 )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v7_waybel_0 @ X21 )
      | ~ ( v1_yellow_6 @ X21 @ X22 )
      | ~ ( l1_waybel_0 @ X21 @ X22 )
      | ( ( k2_waybel_0 @ X22 @ X21 @ X23 )
        = ( k4_yellow_6 @ X22 @ X21 ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
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
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( k2_waybel_0 @ X1 @ X0 @ ( sk_E @ X2 @ X3 @ X0 @ X1 ) ) @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_waybel_0 @ X1 @ X0 @ X3 )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
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
    ! [X20: $i] :
      ( m1_subset_1 @ ( sk_B @ X20 ) @ X20 ) ),
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
    ! [X6: $i,X7: $i,X8: $i,X10: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( v4_orders_2 @ X6 )
      | ~ ( v7_waybel_0 @ X6 )
      | ~ ( l1_waybel_0 @ X6 @ X7 )
      | ( X8
       != ( k10_yellow_6 @ X7 @ X6 ) )
      | ( r2_hidden @ X10 @ X8 )
      | ~ ( r1_waybel_0 @ X7 @ X6 @ ( sk_E_2 @ X10 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d18_yellow_6])).

thf('82',plain,(
    ! [X6: $i,X7: $i,X10: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_subset_1 @ ( k10_yellow_6 @ X7 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X7 ) )
      | ~ ( r1_waybel_0 @ X7 @ X6 @ ( sk_E_2 @ X10 @ X6 @ X7 ) )
      | ( r2_hidden @ X10 @ ( k10_yellow_6 @ X7 @ X6 ) )
      | ~ ( l1_waybel_0 @ X6 @ X7 )
      | ~ ( v7_waybel_0 @ X6 )
      | ~ ( v4_orders_2 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
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
