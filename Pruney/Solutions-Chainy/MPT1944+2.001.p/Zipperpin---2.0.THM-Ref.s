%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jeeiLR4UeH

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 560 expanded)
%              Number of leaves         :   33 ( 177 expanded)
%              Depth                    :   25
%              Number of atoms          : 1803 (8894 expanded)
%              Number of equality atoms :   18 (  49 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i > $i > $i > $i )).

thf(k4_yellow_6_type,type,(
    k4_yellow_6: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_yellow_6_type,type,(
    v1_yellow_6: $i > $i > $o )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

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

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(dt_k2_waybel_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ~ ( v2_struct_0 @ B )
        & ( l1_waybel_0 @ B @ A )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) )
     => ( m1_subset_1 @ ( k2_waybel_0 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( l1_waybel_0 @ X14 @ X15 )
      | ( v2_struct_0 @ X14 )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X14 ) )
      | ( m1_subset_1 @ ( k2_waybel_0 @ X15 @ X14 @ X16 ) @ ( u1_struct_0 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_waybel_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k2_waybel_0 @ X1 @ X0 @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X1 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('7',plain,(
    ! [X1: $i] :
      ( ( l1_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('8',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( m1_subset_1 @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

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

thf('16',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v4_orders_2 @ X25 )
      | ~ ( v7_waybel_0 @ X25 )
      | ~ ( v1_yellow_6 @ X25 @ X26 )
      | ~ ( l1_waybel_0 @ X25 @ X26 )
      | ( ( k2_waybel_0 @ X26 @ X25 @ X27 )
        = ( k4_yellow_6 @ X26 @ X25 ) )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t25_yellow_6])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( ( k2_waybel_0 @ X1 @ X0 @ ( sk_B @ ( u1_struct_0 @ X0 ) ) )
        = ( k4_yellow_6 @ X1 @ X0 ) )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ~ ( v1_yellow_6 @ X0 @ X1 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ~ ( v4_orders_2 @ sk_B_1 )
    | ~ ( v7_waybel_0 @ sk_B_1 )
    | ~ ( v1_yellow_6 @ sk_B_1 @ sk_A )
    | ( ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) )
      = ( k4_yellow_6 @ sk_A @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    v4_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v7_waybel_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_yellow_6 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) )
      = ( k4_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19','20','21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) )
      = ( k4_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) )
    = ( k4_yellow_6 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['13','27'])).

thf('29',plain,(
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

thf('30',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ~ ( v7_waybel_0 @ X24 )
      | ~ ( l1_waybel_0 @ X24 @ X23 )
      | ( m1_subset_1 @ ( k10_yellow_6 @ X23 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_yellow_6])).

thf('31',plain,
    ( ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v7_waybel_0 @ sk_B_1 )
    | ~ ( v4_orders_2 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v7_waybel_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v4_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33','34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['38','39'])).

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

thf('41',plain,(
    ! [X17: $i,X18: $i,X19: $i,X21: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v7_waybel_0 @ X17 )
      | ~ ( l1_waybel_0 @ X17 @ X18 )
      | ( X19
       != ( k10_yellow_6 @ X18 @ X17 ) )
      | ( r2_hidden @ X21 @ X19 )
      | ( m1_connsp_2 @ ( sk_E_2 @ X21 @ X17 @ X18 ) @ X18 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d18_yellow_6])).

thf('42',plain,(
    ! [X17: $i,X18: $i,X21: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ ( k10_yellow_6 @ X18 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X18 ) )
      | ( m1_connsp_2 @ ( sk_E_2 @ X21 @ X17 @ X18 ) @ X18 @ X21 )
      | ( r2_hidden @ X21 @ ( k10_yellow_6 @ X18 @ X17 ) )
      | ~ ( l1_waybel_0 @ X17 @ X18 )
      | ~ ( v7_waybel_0 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
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
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    v4_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v7_waybel_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
      | ( m1_connsp_2 @ ( sk_E_2 @ X0 @ sk_B_1 @ sk_A ) @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44','45','46','47','48'])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_connsp_2 @ ( sk_E_2 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_A ) @ sk_A @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['28','49'])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_connsp_2 @ ( sk_E_2 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_A ) @ sk_A @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['28','49'])).

thf('52',plain,(
    m1_subset_1 @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['11','12'])).

thf(dt_m1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_connsp_2 @ C @ A @ B )
         => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('53',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_connsp_2 @ X4 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_connsp_2])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_A @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_A @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) ) ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) )
    = ( k4_yellow_6 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E_2 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','61'])).

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

thf('63',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( m1_connsp_2 @ X5 @ X6 @ X7 )
      | ( r2_hidden @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t6_connsp_2])).

thf('64',plain,(
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
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_E_2 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_A ) )
      | ~ ( m1_connsp_2 @ ( sk_E_2 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_A ) @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ ( sk_E_2 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_A ) @ sk_A @ X0 )
      | ( r2_hidden @ X0 @ ( sk_E_2 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( m1_subset_1 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( sk_E_2 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','68'])).

thf('70',plain,(
    m1_subset_1 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['13','27'])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( sk_E_2 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( sk_E_2 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    v1_yellow_6 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
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

thf('76',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( l1_waybel_0 @ X8 @ X9 )
      | ( m1_subset_1 @ ( sk_E @ X10 @ X11 @ X8 @ X9 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X8 ) )
      | ( r1_waybel_0 @ X9 @ X8 @ X11 )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d11_waybel_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r1_waybel_0 @ X1 @ X0 @ X2 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X2 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v4_orders_2 @ X25 )
      | ~ ( v7_waybel_0 @ X25 )
      | ~ ( v1_yellow_6 @ X25 @ X26 )
      | ~ ( l1_waybel_0 @ X25 @ X26 )
      | ( ( k2_waybel_0 @ X26 @ X25 @ X27 )
        = ( k4_yellow_6 @ X26 @ X25 ) )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t25_yellow_6])).

thf('82',plain,(
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
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v7_waybel_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v4_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
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
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
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
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) )
        = ( k4_yellow_6 @ sk_A @ sk_B_1 ) )
      | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','86'])).

thf('88',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('89',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) )
        = ( k4_yellow_6 @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) )
        = ( k4_yellow_6 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( l1_waybel_0 @ X8 @ X9 )
      | ~ ( r2_hidden @ ( k2_waybel_0 @ X9 @ X8 @ ( sk_E @ X10 @ X11 @ X8 @ X9 ) ) @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X8 ) )
      | ( r1_waybel_0 @ X9 @ X8 @ X11 )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d11_waybel_0])).

thf('93',plain,(
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
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('95',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf('96',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['93','94','95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E_2 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['72','98'])).

thf('100',plain,
    ( ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E_2 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('102',plain,(
    ! [X17: $i,X18: $i,X19: $i,X21: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v7_waybel_0 @ X17 )
      | ~ ( l1_waybel_0 @ X17 @ X18 )
      | ( X19
       != ( k10_yellow_6 @ X18 @ X17 ) )
      | ( r2_hidden @ X21 @ X19 )
      | ~ ( r1_waybel_0 @ X18 @ X17 @ ( sk_E_2 @ X21 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d18_yellow_6])).

thf('103',plain,(
    ! [X17: $i,X18: $i,X21: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ ( k10_yellow_6 @ X18 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X18 ) )
      | ~ ( r1_waybel_0 @ X18 @ X17 @ ( sk_E_2 @ X21 @ X17 @ X18 ) )
      | ( r2_hidden @ X21 @ ( k10_yellow_6 @ X18 @ X17 ) )
      | ~ ( l1_waybel_0 @ X17 @ X18 )
      | ~ ( v7_waybel_0 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
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
    inference('sup-',[status(thm)],['101','103'])).

thf('105',plain,(
    v4_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v7_waybel_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
      | ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E_2 @ X0 @ sk_B_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['104','105','106','107','108','109'])).

thf('111',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['100','110'])).

thf('112',plain,(
    m1_subset_1 @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['13','27'])).

thf('113',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['114','115'])).

thf('117',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B_1 ) @ ( k10_yellow_6 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('119',plain,(
    $false ),
    inference(demod,[status(thm)],['0','118'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jeeiLR4UeH
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:50:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 99 iterations in 0.086s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.54  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.20/0.54  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.54  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.20/0.54  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.20/0.54  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.20/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.54  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.54  thf(k10_yellow_6_type, type, k10_yellow_6: $i > $i > $i).
% 0.20/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.54  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.20/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.54  thf(sk_E_2_type, type, sk_E_2: $i > $i > $i > $i).
% 0.20/0.54  thf(k4_yellow_6_type, type, k4_yellow_6: $i > $i > $i).
% 0.20/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.54  thf(v1_yellow_6_type, type, v1_yellow_6: $i > $i > $o).
% 0.20/0.54  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.54  thf(t42_yellow_6, conjecture,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.20/0.54             ( v7_waybel_0 @ B ) & ( v1_yellow_6 @ B @ A ) & 
% 0.20/0.54             ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.54           ( r2_hidden @ ( k4_yellow_6 @ A @ B ) @ ( k10_yellow_6 @ A @ B ) ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i]:
% 0.20/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.54            ( l1_pre_topc @ A ) ) =>
% 0.20/0.54          ( ![B:$i]:
% 0.20/0.54            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.20/0.54                ( v7_waybel_0 @ B ) & ( v1_yellow_6 @ B @ A ) & 
% 0.20/0.54                ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.54              ( r2_hidden @ ( k4_yellow_6 @ A @ B ) @ ( k10_yellow_6 @ A @ B ) ) ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t42_yellow_6])).
% 0.20/0.54  thf('0', plain,
% 0.20/0.54      (~ (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.20/0.54          (k10_yellow_6 @ sk_A @ sk_B_1))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('1', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(existence_m1_subset_1, axiom,
% 0.20/0.54    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.20/0.54  thf('2', plain, (![X0 : $i]: (m1_subset_1 @ (sk_B @ X0) @ X0)),
% 0.20/0.54      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.20/0.54  thf(dt_k2_waybel_0, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.20/0.54         ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) & 
% 0.20/0.54         ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.54       ( m1_subset_1 @ ( k2_waybel_0 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ))).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.54         (~ (l1_waybel_0 @ X14 @ X15)
% 0.20/0.54          | (v2_struct_0 @ X14)
% 0.20/0.54          | ~ (l1_struct_0 @ X15)
% 0.20/0.54          | (v2_struct_0 @ X15)
% 0.20/0.54          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X14))
% 0.20/0.54          | (m1_subset_1 @ (k2_waybel_0 @ X15 @ X14 @ X16) @ 
% 0.20/0.54             (u1_struct_0 @ X15)))),
% 0.20/0.54      inference('cnf', [status(esa)], [dt_k2_waybel_0])).
% 0.20/0.54  thf('4', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((m1_subset_1 @ 
% 0.20/0.54           (k2_waybel_0 @ X1 @ X0 @ (sk_B @ (u1_struct_0 @ X0))) @ 
% 0.20/0.54           (u1_struct_0 @ X1))
% 0.20/0.54          | (v2_struct_0 @ X1)
% 0.20/0.54          | ~ (l1_struct_0 @ X1)
% 0.20/0.54          | (v2_struct_0 @ X0)
% 0.20/0.54          | ~ (l1_waybel_0 @ X0 @ X1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_B_1)
% 0.20/0.54        | ~ (l1_struct_0 @ sk_A)
% 0.20/0.54        | (v2_struct_0 @ sk_A)
% 0.20/0.54        | (m1_subset_1 @ 
% 0.20/0.54           (k2_waybel_0 @ sk_A @ sk_B_1 @ (sk_B @ (u1_struct_0 @ sk_B_1))) @ 
% 0.20/0.54           (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['1', '4'])).
% 0.20/0.54  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(dt_l1_pre_topc, axiom,
% 0.20/0.54    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.54  thf('7', plain, (![X1 : $i]: ((l1_struct_0 @ X1) | ~ (l1_pre_topc @ X1))),
% 0.20/0.54      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.54  thf('8', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_B_1)
% 0.20/0.54        | (v2_struct_0 @ sk_A)
% 0.20/0.54        | (m1_subset_1 @ 
% 0.20/0.54           (k2_waybel_0 @ sk_A @ sk_B_1 @ (sk_B @ (u1_struct_0 @ sk_B_1))) @ 
% 0.20/0.54           (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['5', '8'])).
% 0.20/0.54  thf('10', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      (((m1_subset_1 @ 
% 0.20/0.54         (k2_waybel_0 @ sk_A @ sk_B_1 @ (sk_B @ (u1_struct_0 @ sk_B_1))) @ 
% 0.20/0.54         (u1_struct_0 @ sk_A))
% 0.20/0.54        | (v2_struct_0 @ sk_A))),
% 0.20/0.54      inference('clc', [status(thm)], ['9', '10'])).
% 0.20/0.54  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('13', plain,
% 0.20/0.54      ((m1_subset_1 @ 
% 0.20/0.54        (k2_waybel_0 @ sk_A @ sk_B_1 @ (sk_B @ (u1_struct_0 @ sk_B_1))) @ 
% 0.20/0.54        (u1_struct_0 @ sk_A))),
% 0.20/0.54      inference('clc', [status(thm)], ['11', '12'])).
% 0.20/0.54  thf('14', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('15', plain, (![X0 : $i]: (m1_subset_1 @ (sk_B @ X0) @ X0)),
% 0.20/0.54      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.20/0.54  thf(t25_yellow_6, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.20/0.54             ( v7_waybel_0 @ B ) & ( v1_yellow_6 @ B @ A ) & 
% 0.20/0.54             ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.54           ( ![C:$i]:
% 0.20/0.54             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.54               ( ( k2_waybel_0 @ A @ B @ C ) = ( k4_yellow_6 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.54         ((v2_struct_0 @ X25)
% 0.20/0.54          | ~ (v4_orders_2 @ X25)
% 0.20/0.54          | ~ (v7_waybel_0 @ X25)
% 0.20/0.54          | ~ (v1_yellow_6 @ X25 @ X26)
% 0.20/0.54          | ~ (l1_waybel_0 @ X25 @ X26)
% 0.20/0.54          | ((k2_waybel_0 @ X26 @ X25 @ X27) = (k4_yellow_6 @ X26 @ X25))
% 0.20/0.54          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X25))
% 0.20/0.54          | ~ (l1_struct_0 @ X26)
% 0.20/0.54          | (v2_struct_0 @ X26))),
% 0.20/0.54      inference('cnf', [status(esa)], [t25_yellow_6])).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((v2_struct_0 @ X1)
% 0.20/0.54          | ~ (l1_struct_0 @ X1)
% 0.20/0.54          | ((k2_waybel_0 @ X1 @ X0 @ (sk_B @ (u1_struct_0 @ X0)))
% 0.20/0.54              = (k4_yellow_6 @ X1 @ X0))
% 0.20/0.54          | ~ (l1_waybel_0 @ X0 @ X1)
% 0.20/0.54          | ~ (v1_yellow_6 @ X0 @ X1)
% 0.20/0.54          | ~ (v7_waybel_0 @ X0)
% 0.20/0.54          | ~ (v4_orders_2 @ X0)
% 0.20/0.54          | (v2_struct_0 @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.54  thf('18', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_B_1)
% 0.20/0.54        | ~ (v4_orders_2 @ sk_B_1)
% 0.20/0.54        | ~ (v7_waybel_0 @ sk_B_1)
% 0.20/0.54        | ~ (v1_yellow_6 @ sk_B_1 @ sk_A)
% 0.20/0.54        | ((k2_waybel_0 @ sk_A @ sk_B_1 @ (sk_B @ (u1_struct_0 @ sk_B_1)))
% 0.20/0.54            = (k4_yellow_6 @ sk_A @ sk_B_1))
% 0.20/0.54        | ~ (l1_struct_0 @ sk_A)
% 0.20/0.54        | (v2_struct_0 @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['14', '17'])).
% 0.20/0.54  thf('19', plain, ((v4_orders_2 @ sk_B_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('20', plain, ((v7_waybel_0 @ sk_B_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('21', plain, ((v1_yellow_6 @ sk_B_1 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('22', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.54  thf('23', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_B_1)
% 0.20/0.54        | ((k2_waybel_0 @ sk_A @ sk_B_1 @ (sk_B @ (u1_struct_0 @ sk_B_1)))
% 0.20/0.54            = (k4_yellow_6 @ sk_A @ sk_B_1))
% 0.20/0.54        | (v2_struct_0 @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 0.20/0.54  thf('24', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('25', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A)
% 0.20/0.54        | ((k2_waybel_0 @ sk_A @ sk_B_1 @ (sk_B @ (u1_struct_0 @ sk_B_1)))
% 0.20/0.54            = (k4_yellow_6 @ sk_A @ sk_B_1)))),
% 0.20/0.54      inference('clc', [status(thm)], ['23', '24'])).
% 0.20/0.54  thf('26', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('27', plain,
% 0.20/0.54      (((k2_waybel_0 @ sk_A @ sk_B_1 @ (sk_B @ (u1_struct_0 @ sk_B_1)))
% 0.20/0.54         = (k4_yellow_6 @ sk_A @ sk_B_1))),
% 0.20/0.54      inference('clc', [status(thm)], ['25', '26'])).
% 0.20/0.54  thf('28', plain,
% 0.20/0.54      ((m1_subset_1 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['13', '27'])).
% 0.20/0.54  thf('29', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(dt_k10_yellow_6, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.54         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 0.20/0.54         ( v4_orders_2 @ B ) & ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.54       ( m1_subset_1 @
% 0.20/0.54         ( k10_yellow_6 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.54  thf('30', plain,
% 0.20/0.54      (![X23 : $i, X24 : $i]:
% 0.20/0.54         (~ (l1_pre_topc @ X23)
% 0.20/0.54          | ~ (v2_pre_topc @ X23)
% 0.20/0.54          | (v2_struct_0 @ X23)
% 0.20/0.54          | (v2_struct_0 @ X24)
% 0.20/0.54          | ~ (v4_orders_2 @ X24)
% 0.20/0.54          | ~ (v7_waybel_0 @ X24)
% 0.20/0.54          | ~ (l1_waybel_0 @ X24 @ X23)
% 0.20/0.54          | (m1_subset_1 @ (k10_yellow_6 @ X23 @ X24) @ 
% 0.20/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X23))))),
% 0.20/0.54      inference('cnf', [status(esa)], [dt_k10_yellow_6])).
% 0.20/0.54  thf('31', plain,
% 0.20/0.54      (((m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.20/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54        | ~ (v7_waybel_0 @ sk_B_1)
% 0.20/0.54        | ~ (v4_orders_2 @ sk_B_1)
% 0.20/0.54        | (v2_struct_0 @ sk_B_1)
% 0.20/0.54        | (v2_struct_0 @ sk_A)
% 0.20/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.54  thf('32', plain, ((v7_waybel_0 @ sk_B_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('33', plain, ((v4_orders_2 @ sk_B_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('34', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('36', plain,
% 0.20/0.54      (((m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.20/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54        | (v2_struct_0 @ sk_B_1)
% 0.20/0.54        | (v2_struct_0 @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['31', '32', '33', '34', '35'])).
% 0.20/0.54  thf('37', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('38', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A)
% 0.20/0.54        | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.20/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('clc', [status(thm)], ['36', '37'])).
% 0.20/0.54  thf('39', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('40', plain,
% 0.20/0.54      ((m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.20/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('clc', [status(thm)], ['38', '39'])).
% 0.20/0.54  thf(d18_yellow_6, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.20/0.54             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.54           ( ![C:$i]:
% 0.20/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54               ( ( ( C ) = ( k10_yellow_6 @ A @ B ) ) <=>
% 0.20/0.54                 ( ![D:$i]:
% 0.20/0.54                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.54                     ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.54                       ( ![E:$i]:
% 0.20/0.54                         ( ( m1_connsp_2 @ E @ A @ D ) =>
% 0.20/0.54                           ( r1_waybel_0 @ A @ B @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.54  thf('41', plain,
% 0.20/0.54      (![X17 : $i, X18 : $i, X19 : $i, X21 : $i]:
% 0.20/0.54         ((v2_struct_0 @ X17)
% 0.20/0.54          | ~ (v4_orders_2 @ X17)
% 0.20/0.54          | ~ (v7_waybel_0 @ X17)
% 0.20/0.54          | ~ (l1_waybel_0 @ X17 @ X18)
% 0.20/0.54          | ((X19) != (k10_yellow_6 @ X18 @ X17))
% 0.20/0.54          | (r2_hidden @ X21 @ X19)
% 0.20/0.54          | (m1_connsp_2 @ (sk_E_2 @ X21 @ X17 @ X18) @ X18 @ X21)
% 0.20/0.54          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X18))
% 0.20/0.54          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.54          | ~ (l1_pre_topc @ X18)
% 0.20/0.54          | ~ (v2_pre_topc @ X18)
% 0.20/0.54          | (v2_struct_0 @ X18))),
% 0.20/0.54      inference('cnf', [status(esa)], [d18_yellow_6])).
% 0.20/0.54  thf('42', plain,
% 0.20/0.54      (![X17 : $i, X18 : $i, X21 : $i]:
% 0.20/0.54         ((v2_struct_0 @ X18)
% 0.20/0.54          | ~ (v2_pre_topc @ X18)
% 0.20/0.54          | ~ (l1_pre_topc @ X18)
% 0.20/0.54          | ~ (m1_subset_1 @ (k10_yellow_6 @ X18 @ X17) @ 
% 0.20/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.54          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X18))
% 0.20/0.54          | (m1_connsp_2 @ (sk_E_2 @ X21 @ X17 @ X18) @ X18 @ X21)
% 0.20/0.54          | (r2_hidden @ X21 @ (k10_yellow_6 @ X18 @ X17))
% 0.20/0.54          | ~ (l1_waybel_0 @ X17 @ X18)
% 0.20/0.54          | ~ (v7_waybel_0 @ X17)
% 0.20/0.54          | ~ (v4_orders_2 @ X17)
% 0.20/0.54          | (v2_struct_0 @ X17))),
% 0.20/0.54      inference('simplify', [status(thm)], ['41'])).
% 0.20/0.54  thf('43', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((v2_struct_0 @ sk_B_1)
% 0.20/0.54          | ~ (v4_orders_2 @ sk_B_1)
% 0.20/0.54          | ~ (v7_waybel_0 @ sk_B_1)
% 0.20/0.54          | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.20/0.54          | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.20/0.54          | (m1_connsp_2 @ (sk_E_2 @ X0 @ sk_B_1 @ sk_A) @ sk_A @ X0)
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.54          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.54          | (v2_struct_0 @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['40', '42'])).
% 0.20/0.54  thf('44', plain, ((v4_orders_2 @ sk_B_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('45', plain, ((v7_waybel_0 @ sk_B_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('46', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('48', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('49', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((v2_struct_0 @ sk_B_1)
% 0.20/0.54          | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.20/0.54          | (m1_connsp_2 @ (sk_E_2 @ X0 @ sk_B_1 @ sk_A) @ sk_A @ X0)
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.54          | (v2_struct_0 @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['43', '44', '45', '46', '47', '48'])).
% 0.20/0.54  thf('50', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A)
% 0.20/0.54        | (m1_connsp_2 @ 
% 0.20/0.54           (sk_E_2 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_A) @ sk_A @ 
% 0.20/0.54           (k4_yellow_6 @ sk_A @ sk_B_1))
% 0.20/0.54        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.20/0.54           (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.20/0.54        | (v2_struct_0 @ sk_B_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['28', '49'])).
% 0.20/0.54  thf('51', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A)
% 0.20/0.54        | (m1_connsp_2 @ 
% 0.20/0.54           (sk_E_2 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_A) @ sk_A @ 
% 0.20/0.54           (k4_yellow_6 @ sk_A @ sk_B_1))
% 0.20/0.54        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.20/0.54           (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.20/0.54        | (v2_struct_0 @ sk_B_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['28', '49'])).
% 0.20/0.54  thf('52', plain,
% 0.20/0.54      ((m1_subset_1 @ 
% 0.20/0.54        (k2_waybel_0 @ sk_A @ sk_B_1 @ (sk_B @ (u1_struct_0 @ sk_B_1))) @ 
% 0.20/0.54        (u1_struct_0 @ sk_A))),
% 0.20/0.54      inference('clc', [status(thm)], ['11', '12'])).
% 0.20/0.54  thf(dt_m1_connsp_2, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.54         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54       ( ![C:$i]:
% 0.20/0.54         ( ( m1_connsp_2 @ C @ A @ B ) =>
% 0.20/0.54           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.54  thf('53', plain,
% 0.20/0.54      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.54         (~ (l1_pre_topc @ X2)
% 0.20/0.54          | ~ (v2_pre_topc @ X2)
% 0.20/0.54          | (v2_struct_0 @ X2)
% 0.20/0.54          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.20/0.54          | (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.20/0.54          | ~ (m1_connsp_2 @ X4 @ X2 @ X3))),
% 0.20/0.54      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 0.20/0.54  thf('54', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (m1_connsp_2 @ X0 @ sk_A @ 
% 0.20/0.54             (k2_waybel_0 @ sk_A @ sk_B_1 @ (sk_B @ (u1_struct_0 @ sk_B_1))))
% 0.20/0.54          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54          | (v2_struct_0 @ sk_A)
% 0.20/0.54          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.54          | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.54  thf('55', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('57', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (m1_connsp_2 @ X0 @ sk_A @ 
% 0.20/0.54             (k2_waybel_0 @ sk_A @ sk_B_1 @ (sk_B @ (u1_struct_0 @ sk_B_1))))
% 0.20/0.54          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54          | (v2_struct_0 @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.20/0.54  thf('58', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('59', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54          | ~ (m1_connsp_2 @ X0 @ sk_A @ 
% 0.20/0.54               (k2_waybel_0 @ sk_A @ sk_B_1 @ (sk_B @ (u1_struct_0 @ sk_B_1)))))),
% 0.20/0.54      inference('clc', [status(thm)], ['57', '58'])).
% 0.20/0.54  thf('60', plain,
% 0.20/0.54      (((k2_waybel_0 @ sk_A @ sk_B_1 @ (sk_B @ (u1_struct_0 @ sk_B_1)))
% 0.20/0.54         = (k4_yellow_6 @ sk_A @ sk_B_1))),
% 0.20/0.54      inference('clc', [status(thm)], ['25', '26'])).
% 0.20/0.54  thf('61', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54          | ~ (m1_connsp_2 @ X0 @ sk_A @ (k4_yellow_6 @ sk_A @ sk_B_1)))),
% 0.20/0.54      inference('demod', [status(thm)], ['59', '60'])).
% 0.20/0.54  thf('62', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_B_1)
% 0.20/0.54        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.20/0.54           (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.20/0.54        | (v2_struct_0 @ sk_A)
% 0.20/0.54        | (m1_subset_1 @ 
% 0.20/0.54           (sk_E_2 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_A) @ 
% 0.20/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['51', '61'])).
% 0.20/0.54  thf(t6_connsp_2, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54           ( ![C:$i]:
% 0.20/0.54             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.54               ( ( m1_connsp_2 @ B @ A @ C ) => ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.54  thf('63', plain,
% 0.20/0.55      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.20/0.55          | ~ (m1_connsp_2 @ X5 @ X6 @ X7)
% 0.20/0.55          | (r2_hidden @ X7 @ X5)
% 0.20/0.55          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 0.20/0.55          | ~ (l1_pre_topc @ X6)
% 0.20/0.55          | ~ (v2_pre_topc @ X6)
% 0.20/0.55          | (v2_struct_0 @ X6))),
% 0.20/0.55      inference('cnf', [status(esa)], [t6_connsp_2])).
% 0.20/0.55  thf('64', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((v2_struct_0 @ sk_A)
% 0.20/0.55          | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.20/0.55             (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.20/0.55          | (v2_struct_0 @ sk_B_1)
% 0.20/0.55          | (v2_struct_0 @ sk_A)
% 0.20/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.55          | (r2_hidden @ X0 @ 
% 0.20/0.55             (sk_E_2 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_A))
% 0.20/0.55          | ~ (m1_connsp_2 @ 
% 0.20/0.55               (sk_E_2 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_A) @ 
% 0.20/0.55               sk_A @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['62', '63'])).
% 0.20/0.55  thf('65', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('67', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((v2_struct_0 @ sk_A)
% 0.20/0.55          | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.20/0.55             (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.20/0.55          | (v2_struct_0 @ sk_B_1)
% 0.20/0.55          | (v2_struct_0 @ sk_A)
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.55          | (r2_hidden @ X0 @ 
% 0.20/0.55             (sk_E_2 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_A))
% 0.20/0.55          | ~ (m1_connsp_2 @ 
% 0.20/0.55               (sk_E_2 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_A) @ 
% 0.20/0.55               sk_A @ X0))),
% 0.20/0.55      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.20/0.55  thf('68', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (m1_connsp_2 @ 
% 0.20/0.55             (sk_E_2 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_A) @ sk_A @ 
% 0.20/0.55             X0)
% 0.20/0.55          | (r2_hidden @ X0 @ 
% 0.20/0.55             (sk_E_2 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_A))
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.55          | (v2_struct_0 @ sk_B_1)
% 0.20/0.55          | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.20/0.55             (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.20/0.55          | (v2_struct_0 @ sk_A))),
% 0.20/0.55      inference('simplify', [status(thm)], ['67'])).
% 0.20/0.55  thf('69', plain,
% 0.20/0.55      (((v2_struct_0 @ sk_B_1)
% 0.20/0.55        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.20/0.55           (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.20/0.55        | (v2_struct_0 @ sk_A)
% 0.20/0.55        | (v2_struct_0 @ sk_A)
% 0.20/0.55        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.20/0.55           (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.20/0.55        | (v2_struct_0 @ sk_B_1)
% 0.20/0.55        | ~ (m1_subset_1 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.20/0.55        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.20/0.55           (sk_E_2 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_A)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['50', '68'])).
% 0.20/0.55  thf('70', plain,
% 0.20/0.55      ((m1_subset_1 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['13', '27'])).
% 0.20/0.55  thf('71', plain,
% 0.20/0.55      (((v2_struct_0 @ sk_B_1)
% 0.20/0.55        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.20/0.55           (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.20/0.55        | (v2_struct_0 @ sk_A)
% 0.20/0.55        | (v2_struct_0 @ sk_A)
% 0.20/0.55        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.20/0.55           (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.20/0.55        | (v2_struct_0 @ sk_B_1)
% 0.20/0.55        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.20/0.55           (sk_E_2 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_A)))),
% 0.20/0.55      inference('demod', [status(thm)], ['69', '70'])).
% 0.20/0.55  thf('72', plain,
% 0.20/0.55      (((r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.20/0.55         (sk_E_2 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_A))
% 0.20/0.55        | (v2_struct_0 @ sk_A)
% 0.20/0.55        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.20/0.55           (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.20/0.55        | (v2_struct_0 @ sk_B_1))),
% 0.20/0.55      inference('simplify', [status(thm)], ['71'])).
% 0.20/0.55  thf('73', plain, ((v1_yellow_6 @ sk_B_1 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('74', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('75', plain, (![X0 : $i]: (m1_subset_1 @ (sk_B @ X0) @ X0)),
% 0.20/0.55      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.20/0.55  thf(d11_waybel_0, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.55           ( ![C:$i]:
% 0.20/0.55             ( ( r1_waybel_0 @ A @ B @ C ) <=>
% 0.20/0.55               ( ?[D:$i]:
% 0.20/0.55                 ( ( ![E:$i]:
% 0.20/0.55                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.55                       ( ( r1_orders_2 @ B @ D @ E ) =>
% 0.20/0.55                         ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) ) ) ) & 
% 0.20/0.55                   ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf('76', plain,
% 0.20/0.55      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.55         ((v2_struct_0 @ X8)
% 0.20/0.55          | ~ (l1_waybel_0 @ X8 @ X9)
% 0.20/0.55          | (m1_subset_1 @ (sk_E @ X10 @ X11 @ X8 @ X9) @ (u1_struct_0 @ X8))
% 0.20/0.55          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X8))
% 0.20/0.55          | (r1_waybel_0 @ X9 @ X8 @ X11)
% 0.20/0.55          | ~ (l1_struct_0 @ X9)
% 0.20/0.55          | (v2_struct_0 @ X9))),
% 0.20/0.55      inference('cnf', [status(esa)], [d11_waybel_0])).
% 0.20/0.55  thf('77', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         ((v2_struct_0 @ X1)
% 0.20/0.55          | ~ (l1_struct_0 @ X1)
% 0.20/0.55          | (r1_waybel_0 @ X1 @ X0 @ X2)
% 0.20/0.55          | (m1_subset_1 @ 
% 0.20/0.55             (sk_E @ (sk_B @ (u1_struct_0 @ X0)) @ X2 @ X0 @ X1) @ 
% 0.20/0.55             (u1_struct_0 @ X0))
% 0.20/0.55          | ~ (l1_waybel_0 @ X0 @ X1)
% 0.20/0.55          | (v2_struct_0 @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['75', '76'])).
% 0.20/0.55  thf('78', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((v2_struct_0 @ sk_B_1)
% 0.20/0.55          | (m1_subset_1 @ 
% 0.20/0.55             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.20/0.55             (u1_struct_0 @ sk_B_1))
% 0.20/0.55          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.20/0.55          | ~ (l1_struct_0 @ sk_A)
% 0.20/0.55          | (v2_struct_0 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['74', '77'])).
% 0.20/0.55  thf('79', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.55  thf('80', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((v2_struct_0 @ sk_B_1)
% 0.20/0.55          | (m1_subset_1 @ 
% 0.20/0.55             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.20/0.55             (u1_struct_0 @ sk_B_1))
% 0.20/0.55          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.20/0.55          | (v2_struct_0 @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['78', '79'])).
% 0.20/0.55  thf('81', plain,
% 0.20/0.55      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.55         ((v2_struct_0 @ X25)
% 0.20/0.55          | ~ (v4_orders_2 @ X25)
% 0.20/0.55          | ~ (v7_waybel_0 @ X25)
% 0.20/0.55          | ~ (v1_yellow_6 @ X25 @ X26)
% 0.20/0.55          | ~ (l1_waybel_0 @ X25 @ X26)
% 0.20/0.55          | ((k2_waybel_0 @ X26 @ X25 @ X27) = (k4_yellow_6 @ X26 @ X25))
% 0.20/0.55          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X25))
% 0.20/0.55          | ~ (l1_struct_0 @ X26)
% 0.20/0.55          | (v2_struct_0 @ X26))),
% 0.20/0.55      inference('cnf', [status(esa)], [t25_yellow_6])).
% 0.20/0.55  thf('82', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((v2_struct_0 @ sk_A)
% 0.20/0.55          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.20/0.55          | (v2_struct_0 @ sk_B_1)
% 0.20/0.55          | (v2_struct_0 @ X1)
% 0.20/0.55          | ~ (l1_struct_0 @ X1)
% 0.20/0.55          | ((k2_waybel_0 @ X1 @ sk_B_1 @ 
% 0.20/0.55              (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A))
% 0.20/0.55              = (k4_yellow_6 @ X1 @ sk_B_1))
% 0.20/0.55          | ~ (l1_waybel_0 @ sk_B_1 @ X1)
% 0.20/0.55          | ~ (v1_yellow_6 @ sk_B_1 @ X1)
% 0.20/0.55          | ~ (v7_waybel_0 @ sk_B_1)
% 0.20/0.55          | ~ (v4_orders_2 @ sk_B_1)
% 0.20/0.55          | (v2_struct_0 @ sk_B_1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['80', '81'])).
% 0.20/0.55  thf('83', plain, ((v7_waybel_0 @ sk_B_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('84', plain, ((v4_orders_2 @ sk_B_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('85', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((v2_struct_0 @ sk_A)
% 0.20/0.55          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.20/0.55          | (v2_struct_0 @ sk_B_1)
% 0.20/0.55          | (v2_struct_0 @ X1)
% 0.20/0.55          | ~ (l1_struct_0 @ X1)
% 0.20/0.55          | ((k2_waybel_0 @ X1 @ sk_B_1 @ 
% 0.20/0.55              (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A))
% 0.20/0.55              = (k4_yellow_6 @ X1 @ sk_B_1))
% 0.20/0.55          | ~ (l1_waybel_0 @ sk_B_1 @ X1)
% 0.20/0.55          | ~ (v1_yellow_6 @ sk_B_1 @ X1)
% 0.20/0.55          | (v2_struct_0 @ sk_B_1))),
% 0.20/0.55      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.20/0.55  thf('86', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (v1_yellow_6 @ sk_B_1 @ X1)
% 0.20/0.55          | ~ (l1_waybel_0 @ sk_B_1 @ X1)
% 0.20/0.55          | ((k2_waybel_0 @ X1 @ sk_B_1 @ 
% 0.20/0.55              (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A))
% 0.20/0.55              = (k4_yellow_6 @ X1 @ sk_B_1))
% 0.20/0.55          | ~ (l1_struct_0 @ X1)
% 0.20/0.55          | (v2_struct_0 @ X1)
% 0.20/0.55          | (v2_struct_0 @ sk_B_1)
% 0.20/0.55          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.20/0.55          | (v2_struct_0 @ sk_A))),
% 0.20/0.55      inference('simplify', [status(thm)], ['85'])).
% 0.20/0.55  thf('87', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((v2_struct_0 @ sk_A)
% 0.20/0.55          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.20/0.55          | (v2_struct_0 @ sk_B_1)
% 0.20/0.55          | (v2_struct_0 @ sk_A)
% 0.20/0.55          | ~ (l1_struct_0 @ sk_A)
% 0.20/0.55          | ((k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.20/0.55              (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A))
% 0.20/0.55              = (k4_yellow_6 @ sk_A @ sk_B_1))
% 0.20/0.55          | ~ (l1_waybel_0 @ sk_B_1 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['73', '86'])).
% 0.20/0.55  thf('88', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.55  thf('89', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('90', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((v2_struct_0 @ sk_A)
% 0.20/0.55          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.20/0.55          | (v2_struct_0 @ sk_B_1)
% 0.20/0.55          | (v2_struct_0 @ sk_A)
% 0.20/0.55          | ((k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.20/0.55              (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A))
% 0.20/0.55              = (k4_yellow_6 @ sk_A @ sk_B_1)))),
% 0.20/0.55      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.20/0.55  thf('91', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.20/0.55            (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A))
% 0.20/0.55            = (k4_yellow_6 @ sk_A @ sk_B_1))
% 0.20/0.55          | (v2_struct_0 @ sk_B_1)
% 0.20/0.55          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.20/0.55          | (v2_struct_0 @ sk_A))),
% 0.20/0.55      inference('simplify', [status(thm)], ['90'])).
% 0.20/0.55  thf('92', plain,
% 0.20/0.55      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.55         ((v2_struct_0 @ X8)
% 0.20/0.55          | ~ (l1_waybel_0 @ X8 @ X9)
% 0.20/0.55          | ~ (r2_hidden @ 
% 0.20/0.55               (k2_waybel_0 @ X9 @ X8 @ (sk_E @ X10 @ X11 @ X8 @ X9)) @ X11)
% 0.20/0.55          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X8))
% 0.20/0.55          | (r1_waybel_0 @ X9 @ X8 @ X11)
% 0.20/0.55          | ~ (l1_struct_0 @ X9)
% 0.20/0.55          | (v2_struct_0 @ X9))),
% 0.20/0.55      inference('cnf', [status(esa)], [d11_waybel_0])).
% 0.20/0.55  thf('93', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ X0)
% 0.20/0.55          | (v2_struct_0 @ sk_A)
% 0.20/0.55          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.20/0.55          | (v2_struct_0 @ sk_B_1)
% 0.20/0.55          | (v2_struct_0 @ sk_A)
% 0.20/0.55          | ~ (l1_struct_0 @ sk_A)
% 0.20/0.55          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.20/0.55          | ~ (m1_subset_1 @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ 
% 0.20/0.55               (u1_struct_0 @ sk_B_1))
% 0.20/0.55          | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.20/0.55          | (v2_struct_0 @ sk_B_1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['91', '92'])).
% 0.20/0.55  thf('94', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.55  thf('95', plain, (![X0 : $i]: (m1_subset_1 @ (sk_B @ X0) @ X0)),
% 0.20/0.55      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.20/0.55  thf('96', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('97', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ X0)
% 0.20/0.55          | (v2_struct_0 @ sk_A)
% 0.20/0.55          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.20/0.55          | (v2_struct_0 @ sk_B_1)
% 0.20/0.55          | (v2_struct_0 @ sk_A)
% 0.20/0.55          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.20/0.55          | (v2_struct_0 @ sk_B_1))),
% 0.20/0.55      inference('demod', [status(thm)], ['93', '94', '95', '96'])).
% 0.20/0.55  thf('98', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((v2_struct_0 @ sk_B_1)
% 0.20/0.55          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.20/0.55          | (v2_struct_0 @ sk_A)
% 0.20/0.55          | ~ (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ X0))),
% 0.20/0.55      inference('simplify', [status(thm)], ['97'])).
% 0.20/0.55  thf('99', plain,
% 0.20/0.55      (((v2_struct_0 @ sk_B_1)
% 0.20/0.55        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.20/0.55           (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.20/0.55        | (v2_struct_0 @ sk_A)
% 0.20/0.55        | (v2_struct_0 @ sk_A)
% 0.20/0.55        | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.20/0.55           (sk_E_2 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_A))
% 0.20/0.55        | (v2_struct_0 @ sk_B_1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['72', '98'])).
% 0.20/0.55  thf('100', plain,
% 0.20/0.55      (((r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.20/0.55         (sk_E_2 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ sk_B_1 @ sk_A))
% 0.20/0.55        | (v2_struct_0 @ sk_A)
% 0.20/0.55        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.20/0.55           (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.20/0.55        | (v2_struct_0 @ sk_B_1))),
% 0.20/0.55      inference('simplify', [status(thm)], ['99'])).
% 0.20/0.55  thf('101', plain,
% 0.20/0.55      ((m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.20/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('clc', [status(thm)], ['38', '39'])).
% 0.20/0.55  thf('102', plain,
% 0.20/0.55      (![X17 : $i, X18 : $i, X19 : $i, X21 : $i]:
% 0.20/0.55         ((v2_struct_0 @ X17)
% 0.20/0.55          | ~ (v4_orders_2 @ X17)
% 0.20/0.55          | ~ (v7_waybel_0 @ X17)
% 0.20/0.55          | ~ (l1_waybel_0 @ X17 @ X18)
% 0.20/0.55          | ((X19) != (k10_yellow_6 @ X18 @ X17))
% 0.20/0.55          | (r2_hidden @ X21 @ X19)
% 0.20/0.55          | ~ (r1_waybel_0 @ X18 @ X17 @ (sk_E_2 @ X21 @ X17 @ X18))
% 0.20/0.55          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X18))
% 0.20/0.55          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.55          | ~ (l1_pre_topc @ X18)
% 0.20/0.55          | ~ (v2_pre_topc @ X18)
% 0.20/0.55          | (v2_struct_0 @ X18))),
% 0.20/0.55      inference('cnf', [status(esa)], [d18_yellow_6])).
% 0.20/0.55  thf('103', plain,
% 0.20/0.55      (![X17 : $i, X18 : $i, X21 : $i]:
% 0.20/0.55         ((v2_struct_0 @ X18)
% 0.20/0.55          | ~ (v2_pre_topc @ X18)
% 0.20/0.55          | ~ (l1_pre_topc @ X18)
% 0.20/0.55          | ~ (m1_subset_1 @ (k10_yellow_6 @ X18 @ X17) @ 
% 0.20/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.55          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X18))
% 0.20/0.55          | ~ (r1_waybel_0 @ X18 @ X17 @ (sk_E_2 @ X21 @ X17 @ X18))
% 0.20/0.55          | (r2_hidden @ X21 @ (k10_yellow_6 @ X18 @ X17))
% 0.20/0.55          | ~ (l1_waybel_0 @ X17 @ X18)
% 0.20/0.55          | ~ (v7_waybel_0 @ X17)
% 0.20/0.55          | ~ (v4_orders_2 @ X17)
% 0.20/0.55          | (v2_struct_0 @ X17))),
% 0.20/0.55      inference('simplify', [status(thm)], ['102'])).
% 0.20/0.55  thf('104', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((v2_struct_0 @ sk_B_1)
% 0.20/0.55          | ~ (v4_orders_2 @ sk_B_1)
% 0.20/0.55          | ~ (v7_waybel_0 @ sk_B_1)
% 0.20/0.55          | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.20/0.55          | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.20/0.55          | ~ (r1_waybel_0 @ sk_A @ sk_B_1 @ (sk_E_2 @ X0 @ sk_B_1 @ sk_A))
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.55          | (v2_struct_0 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['101', '103'])).
% 0.20/0.55  thf('105', plain, ((v4_orders_2 @ sk_B_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('106', plain, ((v7_waybel_0 @ sk_B_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('107', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('108', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('109', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('110', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((v2_struct_0 @ sk_B_1)
% 0.20/0.55          | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.20/0.55          | ~ (r1_waybel_0 @ sk_A @ sk_B_1 @ (sk_E_2 @ X0 @ sk_B_1 @ sk_A))
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.55          | (v2_struct_0 @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)],
% 0.20/0.55                ['104', '105', '106', '107', '108', '109'])).
% 0.20/0.55  thf('111', plain,
% 0.20/0.55      (((v2_struct_0 @ sk_B_1)
% 0.20/0.55        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.20/0.55           (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.20/0.55        | (v2_struct_0 @ sk_A)
% 0.20/0.55        | (v2_struct_0 @ sk_A)
% 0.20/0.55        | ~ (m1_subset_1 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.20/0.55        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.20/0.55           (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.20/0.55        | (v2_struct_0 @ sk_B_1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['100', '110'])).
% 0.20/0.55  thf('112', plain,
% 0.20/0.55      ((m1_subset_1 @ (k4_yellow_6 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['13', '27'])).
% 0.20/0.55  thf('113', plain,
% 0.20/0.55      (((v2_struct_0 @ sk_B_1)
% 0.20/0.55        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.20/0.55           (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.20/0.55        | (v2_struct_0 @ sk_A)
% 0.20/0.55        | (v2_struct_0 @ sk_A)
% 0.20/0.55        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.20/0.55           (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.20/0.55        | (v2_struct_0 @ sk_B_1))),
% 0.20/0.55      inference('demod', [status(thm)], ['111', '112'])).
% 0.20/0.55  thf('114', plain,
% 0.20/0.55      (((v2_struct_0 @ sk_A)
% 0.20/0.55        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.20/0.55           (k10_yellow_6 @ sk_A @ sk_B_1))
% 0.20/0.55        | (v2_struct_0 @ sk_B_1))),
% 0.20/0.55      inference('simplify', [status(thm)], ['113'])).
% 0.20/0.55  thf('115', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('116', plain,
% 0.20/0.55      (((v2_struct_0 @ sk_B_1)
% 0.20/0.55        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.20/0.55           (k10_yellow_6 @ sk_A @ sk_B_1)))),
% 0.20/0.55      inference('clc', [status(thm)], ['114', '115'])).
% 0.20/0.55  thf('117', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('118', plain,
% 0.20/0.55      ((r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B_1) @ 
% 0.20/0.55        (k10_yellow_6 @ sk_A @ sk_B_1))),
% 0.20/0.55      inference('clc', [status(thm)], ['116', '117'])).
% 0.20/0.55  thf('119', plain, ($false), inference('demod', [status(thm)], ['0', '118'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
