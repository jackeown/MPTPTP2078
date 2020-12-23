%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4J9kjgIJQJ

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:06 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  324 (2530 expanded)
%              Number of leaves         :   37 ( 721 expanded)
%              Depth                    :   68
%              Number of atoms          : 7898 (57679 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :   24 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k5_yellow_6_type,type,(
    k5_yellow_6: $i > $i > $i > $i )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(v2_yellow_6_type,type,(
    v2_yellow_6: $i > $i > $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_E_2_type,type,(
    sk_E_2: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m2_yellow_6_type,type,(
    m2_yellow_6: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_waybel_0_type,type,(
    r2_waybel_0: $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(t46_yellow_6,conjecture,(
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
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ~ ( ~ ( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) )
                  & ! [D: $i] :
                      ( ( m2_yellow_6 @ D @ A @ B )
                     => ? [E: $i] :
                          ( ( r2_hidden @ C @ ( k10_yellow_6 @ A @ E ) )
                          & ( m2_yellow_6 @ E @ A @ D ) ) ) ) ) ) ) )).

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
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ~ ( ~ ( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) )
                    & ! [D: $i] :
                        ( ( m2_yellow_6 @ D @ A @ B )
                       => ? [E: $i] :
                            ( ( r2_hidden @ C @ ( k10_yellow_6 @ A @ E ) )
                            & ( m2_yellow_6 @ E @ A @ D ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t46_yellow_6])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('3',plain,(
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

thf('4',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_waybel_0 @ X1 @ X2 )
      | ( r2_waybel_0 @ X2 @ X1 @ ( k6_subset_1 @ ( u1_struct_0 @ X2 ) @ X3 ) )
      | ( r1_waybel_0 @ X2 @ X1 @ X3 )
      | ~ ( l1_struct_0 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t9_waybel_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( r2_waybel_0 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r2_waybel_0 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r2_waybel_0 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t30_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( r2_waybel_0 @ A @ B @ C )
             => ( ~ ( v2_struct_0 @ ( k5_yellow_6 @ A @ B @ C ) )
                & ( v7_waybel_0 @ ( k5_yellow_6 @ A @ B @ C ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v4_orders_2 @ X26 )
      | ~ ( v7_waybel_0 @ X26 )
      | ~ ( l1_waybel_0 @ X26 @ X27 )
      | ( v7_waybel_0 @ ( k5_yellow_6 @ X27 @ X26 @ X28 ) )
      | ~ ( r2_waybel_0 @ X27 @ X26 @ X28 )
      | ~ ( l1_struct_0 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t30_yellow_6])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v7_waybel_0 @ X12 )
      | ~ ( l1_waybel_0 @ X12 @ X11 )
      | ( m1_subset_1 @ ( k10_yellow_6 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) ) ),
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

thf('32',plain,(
    ! [X5: $i,X6: $i,X7: $i,X9: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( v4_orders_2 @ X5 )
      | ~ ( v7_waybel_0 @ X5 )
      | ~ ( l1_waybel_0 @ X5 @ X6 )
      | ( X7
       != ( k10_yellow_6 @ X6 @ X5 ) )
      | ( r2_hidden @ X9 @ X7 )
      | ( m1_connsp_2 @ ( sk_E_1 @ X9 @ X5 @ X6 ) @ X6 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d18_yellow_6])).

thf('33',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( m1_subset_1 @ ( k10_yellow_6 @ X6 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X6 ) )
      | ( m1_connsp_2 @ ( sk_E_1 @ X9 @ X5 @ X6 ) @ X6 @ X9 )
      | ( r2_hidden @ X9 @ ( k10_yellow_6 @ X6 @ X5 ) )
      | ~ ( l1_waybel_0 @ X5 @ X6 )
      | ~ ( v7_waybel_0 @ X5 )
      | ~ ( v4_orders_2 @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( m1_connsp_2 @ ( sk_E_1 @ X0 @ sk_B @ sk_A ) @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( m1_connsp_2 @ ( sk_E_1 @ X0 @ sk_B @ sk_A ) @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35','36','37','38','39'])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_connsp_2 @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_C )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['19','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r2_waybel_0 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t31_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( r2_waybel_0 @ A @ B @ C )
             => ( m2_yellow_6 @ ( k5_yellow_6 @ A @ B @ C ) @ A @ B ) ) ) ) )).

thf('46',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X29 )
      | ~ ( v4_orders_2 @ X29 )
      | ~ ( v7_waybel_0 @ X29 )
      | ~ ( l1_waybel_0 @ X29 @ X30 )
      | ( m2_yellow_6 @ ( k5_yellow_6 @ X30 @ X29 @ X31 ) @ X30 @ X29 )
      | ~ ( r2_waybel_0 @ X30 @ X29 @ X31 )
      | ~ ( l1_struct_0 @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t31_yellow_6])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( m2_yellow_6 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( m2_yellow_6 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( m2_yellow_6 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A @ sk_B )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( m2_yellow_6 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( m2_yellow_6 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','54'])).

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

thf('56',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( v2_struct_0 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v7_waybel_0 @ X14 )
      | ~ ( l1_waybel_0 @ X14 @ X13 )
      | ( l1_waybel_0 @ X15 @ X13 )
      | ~ ( m2_yellow_6 @ X15 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( m2_yellow_6 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('68',plain,(
    ! [X36: $i] :
      ( ( m2_yellow_6 @ ( sk_E_2 @ X36 ) @ sk_A @ X36 )
      | ~ ( m2_yellow_6 @ X36 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( m2_yellow_6 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( v2_struct_0 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v7_waybel_0 @ X14 )
      | ~ ( l1_waybel_0 @ X14 @ X13 )
      | ( v4_orders_2 @ X15 )
      | ~ ( m2_yellow_6 @ X15 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('73',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc17_yellow_6,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( v4_orders_2 @ B )
        & ( l1_waybel_0 @ B @ A ) )
     => ( ( v4_orders_2 @ ( k5_yellow_6 @ A @ B @ C ) )
        & ( v6_waybel_0 @ ( k5_yellow_6 @ A @ B @ C ) @ A )
        & ( v2_yellow_6 @ ( k5_yellow_6 @ A @ B @ C ) @ A @ B ) ) ) )).

thf('74',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_waybel_0 @ X16 @ X17 )
      | ~ ( v4_orders_2 @ X16 )
      | ~ ( l1_struct_0 @ X17 )
      | ( v4_orders_2 @ ( k5_yellow_6 @ X17 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fc17_yellow_6])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ X0 ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v4_orders_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ X0 ) )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['72','77'])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['71','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A )
      | ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['66','82'])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['42','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( m2_yellow_6 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('94',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( v2_struct_0 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v7_waybel_0 @ X14 )
      | ~ ( l1_waybel_0 @ X14 @ X13 )
      | ( v7_waybel_0 @ X15 )
      | ~ ( m2_yellow_6 @ X15 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A )
      | ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['92','98'])).

thf('100',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['91','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['90','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( m2_yellow_6 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('110',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( v2_struct_0 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v7_waybel_0 @ X14 )
      | ~ ( l1_waybel_0 @ X14 @ X13 )
      | ( l1_waybel_0 @ X15 @ X13 )
      | ~ ( m2_yellow_6 @ X15 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ~ ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ~ ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A )
      | ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ~ ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['108','114'])).

thf('116',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ~ ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['107','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['106','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( m2_yellow_6 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('123',plain,(
    ! [X36: $i] :
      ( ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( sk_E_2 @ X36 ) ) )
      | ~ ( m2_yellow_6 @ X36 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('128',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v7_waybel_0 @ X12 )
      | ~ ( l1_waybel_0 @ X12 @ X11 )
      | ( m1_subset_1 @ ( k10_yellow_6 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_yellow_6])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['126','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['125','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    ! [X5: $i,X6: $i,X7: $i,X9: $i,X10: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( v4_orders_2 @ X5 )
      | ~ ( v7_waybel_0 @ X5 )
      | ~ ( l1_waybel_0 @ X5 @ X6 )
      | ( X7
       != ( k10_yellow_6 @ X6 @ X5 ) )
      | ~ ( m1_connsp_2 @ X10 @ X6 @ X9 )
      | ( r1_waybel_0 @ X6 @ X5 @ X10 )
      | ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d18_yellow_6])).

thf('139',plain,(
    ! [X5: $i,X6: $i,X9: $i,X10: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( m1_subset_1 @ ( k10_yellow_6 @ X6 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X6 ) )
      | ~ ( r2_hidden @ X9 @ ( k10_yellow_6 @ X6 @ X5 ) )
      | ( r1_waybel_0 @ X6 @ X5 @ X10 )
      | ~ ( m1_connsp_2 @ X10 @ X6 @ X9 )
      | ~ ( l1_waybel_0 @ X5 @ X6 )
      | ~ ( v7_waybel_0 @ X5 )
      | ~ ( v4_orders_2 @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ~ ( m1_connsp_2 @ X2 @ sk_A @ X1 )
      | ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X2 )
      | ~ ( r2_hidden @ X1 @ ( k10_yellow_6 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['137','139'])).

thf('141',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ~ ( m1_connsp_2 @ X2 @ sk_A @ X1 )
      | ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X2 )
      | ~ ( r2_hidden @ X1 @ ( k10_yellow_6 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['140','141','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ ( k10_yellow_6 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) )
      | ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X2 )
      | ~ ( m1_connsp_2 @ X2 @ sk_A @ X1 )
      | ~ ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ~ ( m1_connsp_2 @ X1 @ sk_A @ sk_C )
      | ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X1 )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['124','144'])).

thf('146',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ~ ( m1_connsp_2 @ X1 @ sk_A @ sk_C )
      | ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X1 )
      | ~ ( m1_connsp_2 @ X1 @ sk_A @ sk_C )
      | ~ ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( m1_connsp_2 @ X1 @ sk_A @ sk_C )
      | ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['121','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X1 )
      | ~ ( m1_connsp_2 @ X1 @ sk_A @ sk_C )
      | ~ ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( m1_connsp_2 @ X1 @ sk_A @ sk_C )
      | ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['105','150'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X1 )
      | ~ ( m1_connsp_2 @ X1 @ sk_A @ sk_C )
      | ~ ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( m1_connsp_2 @ X1 @ sk_A @ sk_C )
      | ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['89','152'])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X1 )
      | ~ ( m1_connsp_2 @ X1 @ sk_A @ sk_C )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( m2_yellow_6 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf(t32_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i,D: $i] :
              ( ( m2_yellow_6 @ D @ A @ B )
             => ( ( D
                  = ( k5_yellow_6 @ A @ B @ C ) )
               => ( r1_waybel_0 @ A @ D @ C ) ) ) ) ) )).

thf('165',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( v2_struct_0 @ X32 )
      | ~ ( v4_orders_2 @ X32 )
      | ~ ( v7_waybel_0 @ X32 )
      | ~ ( l1_waybel_0 @ X32 @ X33 )
      | ( X35
       != ( k5_yellow_6 @ X33 @ X32 @ X34 ) )
      | ( r1_waybel_0 @ X33 @ X35 @ X34 )
      | ~ ( m2_yellow_6 @ X35 @ X33 @ X32 )
      | ~ ( l1_struct_0 @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t32_yellow_6])).

thf('166',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X33 )
      | ~ ( l1_struct_0 @ X33 )
      | ~ ( m2_yellow_6 @ ( k5_yellow_6 @ X33 @ X32 @ X34 ) @ X33 @ X32 )
      | ( r1_waybel_0 @ X33 @ ( k5_yellow_6 @ X33 @ X32 @ X34 ) @ X34 )
      | ~ ( l1_waybel_0 @ X32 @ X33 )
      | ~ ( v7_waybel_0 @ X32 )
      | ~ ( v4_orders_2 @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(simplify,[status(thm)],['165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ( r1_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['164','166'])).

thf('168',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['167','168','169','170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['163','172'])).

thf('174',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('181',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('182',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_waybel_0 @ X1 @ X2 )
      | ( r2_waybel_0 @ X2 @ X1 @ ( k6_subset_1 @ ( u1_struct_0 @ X2 ) @ X3 ) )
      | ( r1_waybel_0 @ X2 @ X1 @ X3 )
      | ~ ( l1_struct_0 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t9_waybel_0])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X1 )
      | ( r2_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( r2_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 ) )
      | ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X1 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['183'])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X1 )
      | ( r2_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['180','184'])).

thf('186',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X1 )
      | ( r2_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['185','186'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( m2_yellow_6 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

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

thf('190',plain,(
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

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ X1 )
      | ~ ( r2_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X1 )
      | ~ ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    ! [X0: $i] :
      ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('193',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ X1 )
      | ~ ( r2_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X1 )
      | ~ ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['191','192'])).

thf('194',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A )
      | ~ ( r2_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X1 )
      | ( r2_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ X1 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['193'])).

thf('195',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( r2_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ X1 )
      | ~ ( r2_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X1 )
      | ~ ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['188','194'])).

thf('196',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( r2_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ X1 )
      | ~ ( r2_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X1 )
      | ~ ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('198',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 ) ) ) )
      | ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 ) ) ) @ X0 )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 ) ) )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 ) ) )
      | ~ ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 ) ) @ sk_A )
      | ( r2_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 ) ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['187','197'])).

thf('199',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 ) ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ~ ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 ) ) )
      | ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 ) ) ) @ X0 )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['198'])).

thf('200',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X1 )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( r2_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['179','199'])).

thf('201',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 ) )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X1 )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['200'])).

thf('202',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X1 )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( r2_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['178','201'])).

thf('203',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X1 )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['202'])).

thf('204',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_waybel_0 @ X1 @ X2 )
      | ~ ( r1_waybel_0 @ X2 @ X1 @ X4 )
      | ~ ( r2_waybel_0 @ X2 @ X1 @ ( k6_subset_1 @ ( u1_struct_0 @ X2 ) @ X4 ) )
      | ~ ( l1_struct_0 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t9_waybel_0])).

thf('205',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 ) ) ) )
      | ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 ) ) ) @ X0 )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( r1_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 ) ) @ X0 )
      | ~ ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 ) ) @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 ) ) @ sk_A )
      | ~ ( r1_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 ) ) @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 ) ) )
      | ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 ) ) ) @ X0 )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['205'])).

thf('207',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X1 )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( r1_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ X1 )
      | ~ ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['177','206'])).

thf('208',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X1 )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( r1_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ X1 )
      | ~ ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['207','208'])).

thf('210',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( r1_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ X1 )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X1 )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['176','209'])).

thf('211',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X1 )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( r1_waybel_0 @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['210'])).

thf('212',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['175','211'])).

thf('213',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['212'])).

thf(t28_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( r1_waybel_0 @ A @ B @ C )
             => ( r2_waybel_0 @ A @ B @ C ) ) ) ) )).

thf('214',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ~ ( v7_waybel_0 @ X23 )
      | ~ ( l1_waybel_0 @ X23 @ X24 )
      | ( r2_waybel_0 @ X24 @ X23 @ X25 )
      | ~ ( r1_waybel_0 @ X24 @ X23 @ X25 )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t28_yellow_6])).

thf('215',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ~ ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    ! [X0: $i] :
      ( ~ ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ( r2_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['215'])).

thf('217',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( r2_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ~ ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['162','216'])).

thf('218',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( r2_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ~ ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['217','218'])).

thf('220',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( r2_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['161','219'])).

thf('221',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( r2_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ~ ( v7_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['220'])).

thf('222',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( r2_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['160','221'])).

thf('223',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( r2_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ~ ( v4_orders_2 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['222'])).

thf('224',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( r2_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['159','223'])).

thf('225',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( r2_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['224'])).

thf('226',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_waybel_0 @ X1 @ X2 )
      | ~ ( r1_waybel_0 @ X2 @ X1 @ X4 )
      | ~ ( r2_waybel_0 @ X2 @ X1 @ ( k6_subset_1 @ ( u1_struct_0 @ X2 ) @ X4 ) )
      | ~ ( l1_struct_0 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t9_waybel_0])).

thf('227',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X0 )
      | ~ ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['225','226'])).

thf('228',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A )
      | ~ ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['227'])).

thf('229',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X0 )
      | ~ ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['158','228'])).

thf('230',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X0 )
      | ~ ( l1_waybel_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['229','230'])).

thf('232',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X0 )
      | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['157','231'])).

thf('233',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( r1_waybel_0 @ sk_A @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ X0 )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['232'])).

thf('234',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_0 @ sk_A @ sk_B @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['156','233'])).

thf('235',plain,
    ( ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ) ) )
    | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( r1_waybel_0 @ sk_A @ sk_B @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['234'])).

thf('236',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('237',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('238',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( m2_yellow_6 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) @ sk_A @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('239',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( v2_struct_0 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v7_waybel_0 @ X14 )
      | ~ ( l1_waybel_0 @ X14 @ X13 )
      | ~ ( v2_struct_0 @ X15 )
      | ~ ( m2_yellow_6 @ X15 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('240',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['238','239'])).

thf('241',plain,(
    ! [X0: $i] :
      ( v4_orders_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('242',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['240','241'])).

thf('243',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A )
      | ~ ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['242'])).

thf('244',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['237','243'])).

thf('245',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('246',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( l1_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['244','245'])).

thf('247',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['236','246'])).

thf('248',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( sk_E_2 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) )
      | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['247'])).

thf('249',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['235','248'])).

thf('250',plain,
    ( ~ ( v7_waybel_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( r1_waybel_0 @ sk_A @ sk_B @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['249'])).

thf('251',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r1_waybel_0 @ sk_A @ sk_B @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['18','250'])).

thf('252',plain,
    ( ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['251'])).

thf('253',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('254',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( m2_yellow_6 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('255',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( v2_struct_0 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v7_waybel_0 @ X14 )
      | ~ ( l1_waybel_0 @ X14 @ X13 )
      | ~ ( v2_struct_0 @ X15 )
      | ~ ( m2_yellow_6 @ X15 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('256',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['254','255'])).

thf('257',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('258',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('260',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['256','257','258','259'])).

thf('261',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ~ ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['260'])).

thf('262',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['253','261'])).

thf('263',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_struct_0 @ ( k5_yellow_6 @ sk_A @ sk_B @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['262','263'])).

thf('265',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r1_waybel_0 @ sk_A @ sk_B @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['252','264'])).

thf('266',plain,
    ( ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['265'])).

thf('267',plain,(
    m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('268',plain,(
    ! [X5: $i,X6: $i,X7: $i,X9: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( v4_orders_2 @ X5 )
      | ~ ( v7_waybel_0 @ X5 )
      | ~ ( l1_waybel_0 @ X5 @ X6 )
      | ( X7
       != ( k10_yellow_6 @ X6 @ X5 ) )
      | ( r2_hidden @ X9 @ X7 )
      | ~ ( r1_waybel_0 @ X6 @ X5 @ ( sk_E_1 @ X9 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d18_yellow_6])).

thf('269',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( m1_subset_1 @ ( k10_yellow_6 @ X6 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X6 ) )
      | ~ ( r1_waybel_0 @ X6 @ X5 @ ( sk_E_1 @ X9 @ X5 @ X6 ) )
      | ( r2_hidden @ X9 @ ( k10_yellow_6 @ X6 @ X5 ) )
      | ~ ( l1_waybel_0 @ X5 @ X6 )
      | ~ ( v7_waybel_0 @ X5 )
      | ~ ( v4_orders_2 @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(simplify,[status(thm)],['268'])).

thf('270',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ~ ( r1_waybel_0 @ sk_A @ sk_B @ ( sk_E_1 @ X0 @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['267','269'])).

thf('271',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('272',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('273',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('274',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('275',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ~ ( r1_waybel_0 @ sk_A @ sk_B @ ( sk_E_1 @ X0 @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['270','271','272','273','274','275'])).

thf('277',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['266','276'])).

thf('278',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['277','278'])).

thf('280',plain,
    ( ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['279'])).

thf('281',plain,(
    ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('282',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['280','281'])).

thf('283',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('284',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['282','283'])).

thf('285',plain,(
    $false ),
    inference(demod,[status(thm)],['0','284'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4J9kjgIJQJ
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:44:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.76/0.97  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.76/0.97  % Solved by: fo/fo7.sh
% 0.76/0.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.97  % done 518 iterations in 0.448s
% 0.76/0.97  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.76/0.97  % SZS output start Refutation
% 0.76/0.97  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.76/0.97  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.76/0.97  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.97  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.76/0.97  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.76/0.97  thf(k5_yellow_6_type, type, k5_yellow_6: $i > $i > $i > $i).
% 0.76/0.97  thf(k10_yellow_6_type, type, k10_yellow_6: $i > $i > $i).
% 0.76/0.97  thf(v2_yellow_6_type, type, v2_yellow_6: $i > $i > $i > $o).
% 0.76/0.97  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.76/0.97  thf(sk_C_type, type, sk_C: $i).
% 0.76/0.97  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.76/0.97  thf(sk_E_2_type, type, sk_E_2: $i > $i).
% 0.76/0.97  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.97  thf(m2_yellow_6_type, type, m2_yellow_6: $i > $i > $i > $o).
% 0.76/0.97  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.97  thf(r2_waybel_0_type, type, r2_waybel_0: $i > $i > $i > $o).
% 0.76/0.97  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.76/0.97  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.97  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.76/0.97  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.76/0.97  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.76/0.97  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.76/0.97  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.76/0.97  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.76/0.97  thf(v6_waybel_0_type, type, v6_waybel_0: $i > $i > $o).
% 0.76/0.97  thf(t46_yellow_6, conjecture,
% 0.76/0.97    (![A:$i]:
% 0.76/0.97     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.97       ( ![B:$i]:
% 0.76/0.97         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.76/0.97             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.76/0.97           ( ![C:$i]:
% 0.76/0.97             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.76/0.97               ( ~( ( ~( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) ) ) & 
% 0.76/0.97                    ( ![D:$i]:
% 0.76/0.97                      ( ( m2_yellow_6 @ D @ A @ B ) =>
% 0.76/0.97                        ( ?[E:$i]:
% 0.76/0.97                          ( ( r2_hidden @ C @ ( k10_yellow_6 @ A @ E ) ) & 
% 0.76/0.97                            ( m2_yellow_6 @ E @ A @ D ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.76/0.97  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.97    (~( ![A:$i]:
% 0.76/0.97        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.76/0.97            ( l1_pre_topc @ A ) ) =>
% 0.76/0.97          ( ![B:$i]:
% 0.76/0.97            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.76/0.97                ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.76/0.97              ( ![C:$i]:
% 0.76/0.97                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.76/0.97                  ( ~( ( ~( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) ) ) & 
% 0.76/0.97                       ( ![D:$i]:
% 0.76/0.97                         ( ( m2_yellow_6 @ D @ A @ B ) =>
% 0.76/0.97                           ( ?[E:$i]:
% 0.76/0.97                             ( ( r2_hidden @ C @ ( k10_yellow_6 @ A @ E ) ) & 
% 0.76/0.97                               ( m2_yellow_6 @ E @ A @ D ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.76/0.97    inference('cnf.neg', [status(esa)], [t46_yellow_6])).
% 0.76/0.97  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(dt_l1_pre_topc, axiom,
% 0.76/0.97    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.76/0.97  thf('1', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.76/0.97      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.76/0.97  thf('2', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.76/0.97      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.76/0.97  thf('3', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(t9_waybel_0, axiom,
% 0.76/0.97    (![A:$i]:
% 0.76/0.97     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.76/0.97       ( ![B:$i]:
% 0.76/0.97         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.76/0.97           ( ![C:$i]:
% 0.76/0.97             ( ( r1_waybel_0 @ A @ B @ C ) <=>
% 0.76/0.97               ( ~( r2_waybel_0 @
% 0.76/0.97                    A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ))).
% 0.76/0.97  thf('4', plain,
% 0.76/0.97      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.76/0.97         ((v2_struct_0 @ X1)
% 0.76/0.97          | ~ (l1_waybel_0 @ X1 @ X2)
% 0.76/0.97          | (r2_waybel_0 @ X2 @ X1 @ (k6_subset_1 @ (u1_struct_0 @ X2) @ X3))
% 0.76/0.97          | (r1_waybel_0 @ X2 @ X1 @ X3)
% 0.76/0.97          | ~ (l1_struct_0 @ X2)
% 0.76/0.97          | (v2_struct_0 @ X2))),
% 0.76/0.97      inference('cnf', [status(esa)], [t9_waybel_0])).
% 0.76/0.97  thf('5', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_A)
% 0.76/0.97          | ~ (l1_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (r2_waybel_0 @ sk_A @ sk_B @ 
% 0.76/0.97             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.76/0.97          | (v2_struct_0 @ sk_B))),
% 0.76/0.97      inference('sup-', [status(thm)], ['3', '4'])).
% 0.76/0.97  thf('6', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (l1_pre_topc @ sk_A)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (r2_waybel_0 @ sk_A @ sk_B @ 
% 0.76/0.97             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['2', '5'])).
% 0.76/0.97  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('8', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_B)
% 0.76/0.97          | (r2_waybel_0 @ sk_A @ sk_B @ 
% 0.76/0.97             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_A))),
% 0.76/0.97      inference('demod', [status(thm)], ['6', '7'])).
% 0.76/0.97  thf(t30_yellow_6, axiom,
% 0.76/0.97    (![A:$i]:
% 0.76/0.97     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.76/0.97       ( ![B:$i]:
% 0.76/0.97         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.76/0.97             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.76/0.97           ( ![C:$i]:
% 0.76/0.97             ( ( r2_waybel_0 @ A @ B @ C ) =>
% 0.76/0.97               ( ( ~( v2_struct_0 @ ( k5_yellow_6 @ A @ B @ C ) ) ) & 
% 0.76/0.97                 ( v7_waybel_0 @ ( k5_yellow_6 @ A @ B @ C ) ) ) ) ) ) ) ))).
% 0.76/0.97  thf('9', plain,
% 0.76/0.97      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.76/0.97         ((v2_struct_0 @ X26)
% 0.76/0.97          | ~ (v4_orders_2 @ X26)
% 0.76/0.97          | ~ (v7_waybel_0 @ X26)
% 0.76/0.97          | ~ (l1_waybel_0 @ X26 @ X27)
% 0.76/0.97          | (v7_waybel_0 @ (k5_yellow_6 @ X27 @ X26 @ X28))
% 0.76/0.97          | ~ (r2_waybel_0 @ X27 @ X26 @ X28)
% 0.76/0.97          | ~ (l1_struct_0 @ X27)
% 0.76/0.97          | (v2_struct_0 @ X27))),
% 0.76/0.97      inference('cnf', [status(esa)], [t30_yellow_6])).
% 0.76/0.97  thf('10', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | ~ (l1_struct_0 @ sk_A)
% 0.76/0.97          | (v7_waybel_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.76/0.97          | ~ (v7_waybel_0 @ sk_B)
% 0.76/0.97          | ~ (v4_orders_2 @ sk_B)
% 0.76/0.97          | (v2_struct_0 @ sk_B))),
% 0.76/0.97      inference('sup-', [status(thm)], ['8', '9'])).
% 0.76/0.97  thf('11', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('12', plain, ((v7_waybel_0 @ sk_B)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('13', plain, ((v4_orders_2 @ sk_B)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('14', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | ~ (l1_struct_0 @ sk_A)
% 0.76/0.97          | (v7_waybel_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (v2_struct_0 @ sk_B))),
% 0.76/0.97      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.76/0.97  thf('15', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v7_waybel_0 @ 
% 0.76/0.97           (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97            (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | ~ (l1_struct_0 @ sk_A)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_A))),
% 0.76/0.97      inference('simplify', [status(thm)], ['14'])).
% 0.76/0.97  thf('16', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (l1_pre_topc @ sk_A)
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (v7_waybel_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['1', '15'])).
% 0.76/0.97  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('18', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (v7_waybel_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))),
% 0.76/0.97      inference('demod', [status(thm)], ['16', '17'])).
% 0.76/0.97  thf('19', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('20', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(dt_k10_yellow_6, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.76/0.97         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 0.76/0.97         ( v4_orders_2 @ B ) & ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.76/0.97       ( m1_subset_1 @
% 0.76/0.97         ( k10_yellow_6 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.76/0.97  thf('21', plain,
% 0.76/0.97      (![X11 : $i, X12 : $i]:
% 0.76/0.97         (~ (l1_pre_topc @ X11)
% 0.76/0.97          | ~ (v2_pre_topc @ X11)
% 0.76/0.97          | (v2_struct_0 @ X11)
% 0.76/0.97          | (v2_struct_0 @ X12)
% 0.76/0.97          | ~ (v4_orders_2 @ X12)
% 0.76/0.97          | ~ (v7_waybel_0 @ X12)
% 0.76/0.97          | ~ (l1_waybel_0 @ X12 @ X11)
% 0.76/0.97          | (m1_subset_1 @ (k10_yellow_6 @ X11 @ X12) @ 
% 0.76/0.97             (k1_zfmisc_1 @ (u1_struct_0 @ X11))))),
% 0.76/0.97      inference('cnf', [status(esa)], [dt_k10_yellow_6])).
% 0.76/0.97  thf('22', plain,
% 0.76/0.97      (((m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_B) @ 
% 0.76/0.97         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.97        | ~ (v7_waybel_0 @ sk_B)
% 0.76/0.97        | ~ (v4_orders_2 @ sk_B)
% 0.76/0.97        | (v2_struct_0 @ sk_B)
% 0.76/0.97        | (v2_struct_0 @ sk_A)
% 0.76/0.97        | ~ (v2_pre_topc @ sk_A)
% 0.76/0.97        | ~ (l1_pre_topc @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['20', '21'])).
% 0.76/0.97  thf('23', plain, ((v7_waybel_0 @ sk_B)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('24', plain, ((v4_orders_2 @ sk_B)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('27', plain,
% 0.76/0.97      (((m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_B) @ 
% 0.76/0.97         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.97        | (v2_struct_0 @ sk_B)
% 0.76/0.97        | (v2_struct_0 @ sk_A))),
% 0.76/0.97      inference('demod', [status(thm)], ['22', '23', '24', '25', '26'])).
% 0.76/0.97  thf('28', plain, (~ (v2_struct_0 @ sk_B)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('29', plain,
% 0.76/0.97      (((v2_struct_0 @ sk_A)
% 0.76/0.97        | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_B) @ 
% 0.76/0.97           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.76/0.97      inference('clc', [status(thm)], ['27', '28'])).
% 0.76/0.97  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('31', plain,
% 0.76/0.97      ((m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_B) @ 
% 0.76/0.97        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.97      inference('clc', [status(thm)], ['29', '30'])).
% 0.76/0.97  thf(d18_yellow_6, axiom,
% 0.76/0.97    (![A:$i]:
% 0.76/0.97     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.97       ( ![B:$i]:
% 0.76/0.97         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.76/0.97             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.76/0.97           ( ![C:$i]:
% 0.76/0.97             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.97               ( ( ( C ) = ( k10_yellow_6 @ A @ B ) ) <=>
% 0.76/0.97                 ( ![D:$i]:
% 0.76/0.97                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.76/0.97                     ( ( r2_hidden @ D @ C ) <=>
% 0.76/0.97                       ( ![E:$i]:
% 0.76/0.97                         ( ( m1_connsp_2 @ E @ A @ D ) =>
% 0.76/0.97                           ( r1_waybel_0 @ A @ B @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.76/0.97  thf('32', plain,
% 0.76/0.97      (![X5 : $i, X6 : $i, X7 : $i, X9 : $i]:
% 0.76/0.97         ((v2_struct_0 @ X5)
% 0.76/0.97          | ~ (v4_orders_2 @ X5)
% 0.76/0.97          | ~ (v7_waybel_0 @ X5)
% 0.76/0.97          | ~ (l1_waybel_0 @ X5 @ X6)
% 0.76/0.97          | ((X7) != (k10_yellow_6 @ X6 @ X5))
% 0.76/0.97          | (r2_hidden @ X9 @ X7)
% 0.76/0.97          | (m1_connsp_2 @ (sk_E_1 @ X9 @ X5 @ X6) @ X6 @ X9)
% 0.76/0.97          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X6))
% 0.76/0.97          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.76/0.97          | ~ (l1_pre_topc @ X6)
% 0.76/0.97          | ~ (v2_pre_topc @ X6)
% 0.76/0.97          | (v2_struct_0 @ X6))),
% 0.76/0.97      inference('cnf', [status(esa)], [d18_yellow_6])).
% 0.76/0.97  thf('33', plain,
% 0.76/0.97      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.76/0.97         ((v2_struct_0 @ X6)
% 0.76/0.97          | ~ (v2_pre_topc @ X6)
% 0.76/0.97          | ~ (l1_pre_topc @ X6)
% 0.76/0.97          | ~ (m1_subset_1 @ (k10_yellow_6 @ X6 @ X5) @ 
% 0.76/0.97               (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.76/0.97          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X6))
% 0.76/0.97          | (m1_connsp_2 @ (sk_E_1 @ X9 @ X5 @ X6) @ X6 @ X9)
% 0.76/0.97          | (r2_hidden @ X9 @ (k10_yellow_6 @ X6 @ X5))
% 0.76/0.97          | ~ (l1_waybel_0 @ X5 @ X6)
% 0.76/0.97          | ~ (v7_waybel_0 @ X5)
% 0.76/0.97          | ~ (v4_orders_2 @ X5)
% 0.76/0.97          | (v2_struct_0 @ X5))),
% 0.76/0.97      inference('simplify', [status(thm)], ['32'])).
% 0.76/0.97  thf('34', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_B)
% 0.76/0.97          | ~ (v4_orders_2 @ sk_B)
% 0.76/0.97          | ~ (v7_waybel_0 @ sk_B)
% 0.76/0.97          | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.76/0.97          | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.76/0.97          | (m1_connsp_2 @ (sk_E_1 @ X0 @ sk_B @ sk_A) @ sk_A @ X0)
% 0.76/0.97          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.76/0.97          | ~ (l1_pre_topc @ sk_A)
% 0.76/0.97          | ~ (v2_pre_topc @ sk_A)
% 0.76/0.97          | (v2_struct_0 @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['31', '33'])).
% 0.76/0.97  thf('35', plain, ((v4_orders_2 @ sk_B)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('36', plain, ((v7_waybel_0 @ sk_B)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('37', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('40', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_B)
% 0.76/0.97          | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.76/0.97          | (m1_connsp_2 @ (sk_E_1 @ X0 @ sk_B @ sk_A) @ sk_A @ X0)
% 0.76/0.97          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.76/0.97          | (v2_struct_0 @ sk_A))),
% 0.76/0.97      inference('demod', [status(thm)], ['34', '35', '36', '37', '38', '39'])).
% 0.76/0.97  thf('41', plain,
% 0.76/0.97      (((v2_struct_0 @ sk_A)
% 0.76/0.97        | (m1_connsp_2 @ (sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A @ sk_C)
% 0.76/0.97        | (r2_hidden @ sk_C @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.76/0.97        | (v2_struct_0 @ sk_B))),
% 0.76/0.97      inference('sup-', [status(thm)], ['19', '40'])).
% 0.76/0.97  thf('42', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (v7_waybel_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))),
% 0.76/0.97      inference('demod', [status(thm)], ['16', '17'])).
% 0.76/0.97  thf('43', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.76/0.97      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.76/0.97  thf('44', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.76/0.97      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.76/0.97  thf('45', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_B)
% 0.76/0.97          | (r2_waybel_0 @ sk_A @ sk_B @ 
% 0.76/0.97             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_A))),
% 0.76/0.97      inference('demod', [status(thm)], ['6', '7'])).
% 0.76/0.97  thf(t31_yellow_6, axiom,
% 0.76/0.97    (![A:$i]:
% 0.76/0.97     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.76/0.97       ( ![B:$i]:
% 0.76/0.97         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.76/0.97             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.76/0.97           ( ![C:$i]:
% 0.76/0.97             ( ( r2_waybel_0 @ A @ B @ C ) =>
% 0.76/0.97               ( m2_yellow_6 @ ( k5_yellow_6 @ A @ B @ C ) @ A @ B ) ) ) ) ) ))).
% 0.76/0.97  thf('46', plain,
% 0.76/0.97      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.76/0.97         ((v2_struct_0 @ X29)
% 0.76/0.97          | ~ (v4_orders_2 @ X29)
% 0.76/0.97          | ~ (v7_waybel_0 @ X29)
% 0.76/0.97          | ~ (l1_waybel_0 @ X29 @ X30)
% 0.76/0.97          | (m2_yellow_6 @ (k5_yellow_6 @ X30 @ X29 @ X31) @ X30 @ X29)
% 0.76/0.97          | ~ (r2_waybel_0 @ X30 @ X29 @ X31)
% 0.76/0.97          | ~ (l1_struct_0 @ X30)
% 0.76/0.97          | (v2_struct_0 @ X30))),
% 0.76/0.97      inference('cnf', [status(esa)], [t31_yellow_6])).
% 0.76/0.97  thf('47', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | ~ (l1_struct_0 @ sk_A)
% 0.76/0.97          | (m2_yellow_6 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.97             sk_A @ sk_B)
% 0.76/0.97          | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.76/0.97          | ~ (v7_waybel_0 @ sk_B)
% 0.76/0.97          | ~ (v4_orders_2 @ sk_B)
% 0.76/0.97          | (v2_struct_0 @ sk_B))),
% 0.76/0.97      inference('sup-', [status(thm)], ['45', '46'])).
% 0.76/0.97  thf('48', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('49', plain, ((v7_waybel_0 @ sk_B)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('50', plain, ((v4_orders_2 @ sk_B)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('51', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | ~ (l1_struct_0 @ sk_A)
% 0.76/0.97          | (m2_yellow_6 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.97             sk_A @ sk_B)
% 0.76/0.97          | (v2_struct_0 @ sk_B))),
% 0.76/0.97      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 0.76/0.97  thf('52', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((m2_yellow_6 @ 
% 0.76/0.97           (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97            (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.97           sk_A @ sk_B)
% 0.76/0.97          | ~ (l1_struct_0 @ sk_A)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_A))),
% 0.76/0.97      inference('simplify', [status(thm)], ['51'])).
% 0.76/0.97  thf('53', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (l1_pre_topc @ sk_A)
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (m2_yellow_6 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.97             sk_A @ sk_B))),
% 0.76/0.97      inference('sup-', [status(thm)], ['44', '52'])).
% 0.76/0.97  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('55', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (m2_yellow_6 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.97             sk_A @ sk_B))),
% 0.76/0.97      inference('demod', [status(thm)], ['53', '54'])).
% 0.76/0.97  thf(dt_m2_yellow_6, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.76/0.97         ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.76/0.97         ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.76/0.97       ( ![C:$i]:
% 0.76/0.97         ( ( m2_yellow_6 @ C @ A @ B ) =>
% 0.76/0.97           ( ( ~( v2_struct_0 @ C ) ) & ( v4_orders_2 @ C ) & 
% 0.76/0.97             ( v7_waybel_0 @ C ) & ( l1_waybel_0 @ C @ A ) ) ) ) ))).
% 0.76/0.97  thf('56', plain,
% 0.76/0.97      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.76/0.97         (~ (l1_struct_0 @ X13)
% 0.76/0.97          | (v2_struct_0 @ X13)
% 0.76/0.97          | (v2_struct_0 @ X14)
% 0.76/0.97          | ~ (v4_orders_2 @ X14)
% 0.76/0.97          | ~ (v7_waybel_0 @ X14)
% 0.76/0.97          | ~ (l1_waybel_0 @ X14 @ X13)
% 0.76/0.97          | (l1_waybel_0 @ X15 @ X13)
% 0.76/0.97          | ~ (m2_yellow_6 @ X15 @ X13 @ X14))),
% 0.76/0.97      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 0.76/0.97  thf('57', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_B)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | (l1_waybel_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.97             sk_A)
% 0.76/0.97          | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.76/0.97          | ~ (v7_waybel_0 @ sk_B)
% 0.76/0.97          | ~ (v4_orders_2 @ sk_B)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | ~ (l1_struct_0 @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['55', '56'])).
% 0.76/0.97  thf('58', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('59', plain, ((v7_waybel_0 @ sk_B)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('60', plain, ((v4_orders_2 @ sk_B)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('61', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_B)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | (l1_waybel_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.97             sk_A)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | ~ (l1_struct_0 @ sk_A))),
% 0.76/0.97      inference('demod', [status(thm)], ['57', '58', '59', '60'])).
% 0.76/0.97  thf('62', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (l1_struct_0 @ sk_A)
% 0.76/0.97          | (l1_waybel_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.97             sk_A)
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B))),
% 0.76/0.97      inference('simplify', [status(thm)], ['61'])).
% 0.76/0.97  thf('63', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (l1_pre_topc @ sk_A)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | (l1_waybel_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.97             sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['43', '62'])).
% 0.76/0.97  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('65', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_B)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | (l1_waybel_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.97             sk_A))),
% 0.76/0.97      inference('demod', [status(thm)], ['63', '64'])).
% 0.76/0.97  thf('66', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.76/0.97      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.76/0.97  thf('67', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (m2_yellow_6 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.97             sk_A @ sk_B))),
% 0.76/0.97      inference('demod', [status(thm)], ['53', '54'])).
% 0.76/0.97  thf('68', plain,
% 0.76/0.97      (![X36 : $i]:
% 0.76/0.97         ((m2_yellow_6 @ (sk_E_2 @ X36) @ sk_A @ X36)
% 0.76/0.97          | ~ (m2_yellow_6 @ X36 @ sk_A @ sk_B))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('69', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_B)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | (m2_yellow_6 @ 
% 0.76/0.97             (sk_E_2 @ 
% 0.76/0.97              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.97             sk_A @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['67', '68'])).
% 0.76/0.97  thf('70', plain,
% 0.76/0.97      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.76/0.97         (~ (l1_struct_0 @ X13)
% 0.76/0.97          | (v2_struct_0 @ X13)
% 0.76/0.97          | (v2_struct_0 @ X14)
% 0.76/0.97          | ~ (v4_orders_2 @ X14)
% 0.76/0.97          | ~ (v7_waybel_0 @ X14)
% 0.76/0.97          | ~ (l1_waybel_0 @ X14 @ X13)
% 0.76/0.97          | (v4_orders_2 @ X15)
% 0.76/0.97          | ~ (m2_yellow_6 @ X15 @ X13 @ X14))),
% 0.76/0.97      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 0.76/0.97  thf('71', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (v4_orders_2 @ 
% 0.76/0.97             (sk_E_2 @ 
% 0.76/0.97              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.97          | ~ (l1_waybel_0 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.97               sk_A)
% 0.76/0.97          | ~ (v7_waybel_0 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | ~ (v4_orders_2 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | ~ (l1_struct_0 @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['69', '70'])).
% 0.76/0.97  thf('72', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.76/0.97      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.76/0.97  thf('73', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(fc17_yellow_6, axiom,
% 0.76/0.97    (![A:$i,B:$i,C:$i]:
% 0.76/0.97     ( ( ( l1_struct_0 @ A ) & ( v4_orders_2 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.76/0.97       ( ( v4_orders_2 @ ( k5_yellow_6 @ A @ B @ C ) ) & 
% 0.76/0.97         ( v6_waybel_0 @ ( k5_yellow_6 @ A @ B @ C ) @ A ) & 
% 0.76/0.97         ( v2_yellow_6 @ ( k5_yellow_6 @ A @ B @ C ) @ A @ B ) ) ))).
% 0.76/0.97  thf('74', plain,
% 0.76/0.97      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.76/0.97         (~ (l1_waybel_0 @ X16 @ X17)
% 0.76/0.97          | ~ (v4_orders_2 @ X16)
% 0.76/0.97          | ~ (l1_struct_0 @ X17)
% 0.76/0.97          | (v4_orders_2 @ (k5_yellow_6 @ X17 @ X16 @ X18)))),
% 0.76/0.97      inference('cnf', [status(esa)], [fc17_yellow_6])).
% 0.76/0.97  thf('75', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v4_orders_2 @ (k5_yellow_6 @ sk_A @ sk_B @ X0))
% 0.76/0.97          | ~ (l1_struct_0 @ sk_A)
% 0.76/0.97          | ~ (v4_orders_2 @ sk_B))),
% 0.76/0.97      inference('sup-', [status(thm)], ['73', '74'])).
% 0.76/0.97  thf('76', plain, ((v4_orders_2 @ sk_B)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('77', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v4_orders_2 @ (k5_yellow_6 @ sk_A @ sk_B @ X0))
% 0.76/0.97          | ~ (l1_struct_0 @ sk_A))),
% 0.76/0.97      inference('demod', [status(thm)], ['75', '76'])).
% 0.76/0.97  thf('78', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (l1_pre_topc @ sk_A)
% 0.76/0.97          | (v4_orders_2 @ (k5_yellow_6 @ sk_A @ sk_B @ X0)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['72', '77'])).
% 0.76/0.97  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('80', plain,
% 0.76/0.97      (![X0 : $i]: (v4_orders_2 @ (k5_yellow_6 @ sk_A @ sk_B @ X0))),
% 0.76/0.97      inference('demod', [status(thm)], ['78', '79'])).
% 0.76/0.97  thf('81', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (v4_orders_2 @ 
% 0.76/0.97             (sk_E_2 @ 
% 0.76/0.97              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.97          | ~ (l1_waybel_0 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.97               sk_A)
% 0.76/0.97          | ~ (v7_waybel_0 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | ~ (l1_struct_0 @ sk_A))),
% 0.76/0.97      inference('demod', [status(thm)], ['71', '80'])).
% 0.76/0.97  thf('82', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (l1_struct_0 @ sk_A)
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | ~ (v7_waybel_0 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | ~ (l1_waybel_0 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.97               sk_A)
% 0.76/0.97          | (v4_orders_2 @ 
% 0.76/0.97             (sk_E_2 @ 
% 0.76/0.97              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_A))),
% 0.76/0.97      inference('simplify', [status(thm)], ['81'])).
% 0.76/0.97  thf('83', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (l1_pre_topc @ sk_A)
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (v4_orders_2 @ 
% 0.76/0.97             (sk_E_2 @ 
% 0.76/0.97              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.97          | ~ (l1_waybel_0 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.97               sk_A)
% 0.76/0.97          | ~ (v7_waybel_0 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['66', '82'])).
% 0.76/0.97  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('85', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (v4_orders_2 @ 
% 0.76/0.97             (sk_E_2 @ 
% 0.76/0.97              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.97          | ~ (l1_waybel_0 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.97               sk_A)
% 0.76/0.97          | ~ (v7_waybel_0 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))),
% 0.76/0.97      inference('demod', [status(thm)], ['83', '84'])).
% 0.76/0.97  thf('86', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | ~ (v7_waybel_0 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (v4_orders_2 @ 
% 0.76/0.97             (sk_E_2 @ 
% 0.76/0.97              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['65', '85'])).
% 0.76/0.97  thf('87', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v4_orders_2 @ 
% 0.76/0.97           (sk_E_2 @ 
% 0.76/0.97            (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.97          | ~ (v7_waybel_0 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_A))),
% 0.76/0.97      inference('simplify', [status(thm)], ['86'])).
% 0.76/0.97  thf('88', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_B)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (v4_orders_2 @ 
% 0.76/0.97             (sk_E_2 @ 
% 0.76/0.97              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['42', '87'])).
% 0.76/0.97  thf('89', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v4_orders_2 @ 
% 0.76/0.97           (sk_E_2 @ 
% 0.76/0.97            (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B))),
% 0.76/0.97      inference('simplify', [status(thm)], ['88'])).
% 0.76/0.97  thf('90', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (v7_waybel_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))),
% 0.76/0.97      inference('demod', [status(thm)], ['16', '17'])).
% 0.76/0.97  thf('91', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_B)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | (l1_waybel_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.97             sk_A))),
% 0.76/0.97      inference('demod', [status(thm)], ['63', '64'])).
% 0.76/0.97  thf('92', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.76/0.97      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.76/0.97  thf('93', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_B)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | (m2_yellow_6 @ 
% 0.76/0.97             (sk_E_2 @ 
% 0.76/0.97              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.97             sk_A @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['67', '68'])).
% 0.76/0.97  thf('94', plain,
% 0.76/0.97      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.76/0.97         (~ (l1_struct_0 @ X13)
% 0.76/0.97          | (v2_struct_0 @ X13)
% 0.76/0.97          | (v2_struct_0 @ X14)
% 0.76/0.97          | ~ (v4_orders_2 @ X14)
% 0.76/0.97          | ~ (v7_waybel_0 @ X14)
% 0.76/0.97          | ~ (l1_waybel_0 @ X14 @ X13)
% 0.76/0.97          | (v7_waybel_0 @ X15)
% 0.76/0.97          | ~ (m2_yellow_6 @ X15 @ X13 @ X14))),
% 0.76/0.97      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 0.76/0.97  thf('95', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (v7_waybel_0 @ 
% 0.76/0.97             (sk_E_2 @ 
% 0.76/0.97              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.97          | ~ (l1_waybel_0 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.97               sk_A)
% 0.76/0.97          | ~ (v7_waybel_0 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | ~ (v4_orders_2 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | ~ (l1_struct_0 @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['93', '94'])).
% 0.76/0.97  thf('96', plain,
% 0.76/0.97      (![X0 : $i]: (v4_orders_2 @ (k5_yellow_6 @ sk_A @ sk_B @ X0))),
% 0.76/0.97      inference('demod', [status(thm)], ['78', '79'])).
% 0.76/0.97  thf('97', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (v7_waybel_0 @ 
% 0.76/0.97             (sk_E_2 @ 
% 0.76/0.97              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.97          | ~ (l1_waybel_0 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.97               sk_A)
% 0.76/0.97          | ~ (v7_waybel_0 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | ~ (l1_struct_0 @ sk_A))),
% 0.76/0.97      inference('demod', [status(thm)], ['95', '96'])).
% 0.76/0.97  thf('98', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (l1_struct_0 @ sk_A)
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | ~ (v7_waybel_0 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | ~ (l1_waybel_0 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.97               sk_A)
% 0.76/0.97          | (v7_waybel_0 @ 
% 0.76/0.97             (sk_E_2 @ 
% 0.76/0.97              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_A))),
% 0.76/0.97      inference('simplify', [status(thm)], ['97'])).
% 0.76/0.97  thf('99', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (l1_pre_topc @ sk_A)
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (v7_waybel_0 @ 
% 0.76/0.97             (sk_E_2 @ 
% 0.76/0.97              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.97          | ~ (l1_waybel_0 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.97               sk_A)
% 0.76/0.97          | ~ (v7_waybel_0 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['92', '98'])).
% 0.76/0.97  thf('100', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('101', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (v7_waybel_0 @ 
% 0.76/0.97             (sk_E_2 @ 
% 0.76/0.97              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.97          | ~ (l1_waybel_0 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.97               sk_A)
% 0.76/0.97          | ~ (v7_waybel_0 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))),
% 0.76/0.97      inference('demod', [status(thm)], ['99', '100'])).
% 0.76/0.97  thf('102', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | ~ (v7_waybel_0 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (v7_waybel_0 @ 
% 0.76/0.97             (sk_E_2 @ 
% 0.76/0.97              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['91', '101'])).
% 0.76/0.97  thf('103', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v7_waybel_0 @ 
% 0.76/0.97           (sk_E_2 @ 
% 0.76/0.97            (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.97          | ~ (v7_waybel_0 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_A))),
% 0.76/0.97      inference('simplify', [status(thm)], ['102'])).
% 0.76/0.97  thf('104', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_B)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (v7_waybel_0 @ 
% 0.76/0.97             (sk_E_2 @ 
% 0.76/0.97              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['90', '103'])).
% 0.76/0.97  thf('105', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v7_waybel_0 @ 
% 0.76/0.97           (sk_E_2 @ 
% 0.76/0.97            (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B))),
% 0.76/0.97      inference('simplify', [status(thm)], ['104'])).
% 0.76/0.97  thf('106', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (v7_waybel_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))),
% 0.76/0.97      inference('demod', [status(thm)], ['16', '17'])).
% 0.76/0.97  thf('107', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_B)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | (l1_waybel_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.97             sk_A))),
% 0.76/0.97      inference('demod', [status(thm)], ['63', '64'])).
% 0.76/0.97  thf('108', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.76/0.97      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.76/0.97  thf('109', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_B)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | (m2_yellow_6 @ 
% 0.76/0.97             (sk_E_2 @ 
% 0.76/0.97              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.97             sk_A @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['67', '68'])).
% 0.76/0.97  thf('110', plain,
% 0.76/0.97      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.76/0.97         (~ (l1_struct_0 @ X13)
% 0.76/0.97          | (v2_struct_0 @ X13)
% 0.76/0.97          | (v2_struct_0 @ X14)
% 0.76/0.97          | ~ (v4_orders_2 @ X14)
% 0.76/0.97          | ~ (v7_waybel_0 @ X14)
% 0.76/0.97          | ~ (l1_waybel_0 @ X14 @ X13)
% 0.76/0.97          | (l1_waybel_0 @ X15 @ X13)
% 0.76/0.97          | ~ (m2_yellow_6 @ X15 @ X13 @ X14))),
% 0.76/0.97      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 0.76/0.97  thf('111', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (l1_waybel_0 @ 
% 0.76/0.97             (sk_E_2 @ 
% 0.76/0.97              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.97             sk_A)
% 0.76/0.97          | ~ (l1_waybel_0 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.97               sk_A)
% 0.76/0.97          | ~ (v7_waybel_0 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | ~ (v4_orders_2 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | ~ (l1_struct_0 @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['109', '110'])).
% 0.76/0.97  thf('112', plain,
% 0.76/0.97      (![X0 : $i]: (v4_orders_2 @ (k5_yellow_6 @ sk_A @ sk_B @ X0))),
% 0.76/0.97      inference('demod', [status(thm)], ['78', '79'])).
% 0.76/0.97  thf('113', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (l1_waybel_0 @ 
% 0.76/0.97             (sk_E_2 @ 
% 0.76/0.97              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.97             sk_A)
% 0.76/0.97          | ~ (l1_waybel_0 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.97               sk_A)
% 0.76/0.97          | ~ (v7_waybel_0 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | ~ (l1_struct_0 @ sk_A))),
% 0.76/0.97      inference('demod', [status(thm)], ['111', '112'])).
% 0.76/0.97  thf('114', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (l1_struct_0 @ sk_A)
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | ~ (v7_waybel_0 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | ~ (l1_waybel_0 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.97               sk_A)
% 0.76/0.97          | (l1_waybel_0 @ 
% 0.76/0.97             (sk_E_2 @ 
% 0.76/0.97              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.97             sk_A)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_A))),
% 0.76/0.97      inference('simplify', [status(thm)], ['113'])).
% 0.76/0.97  thf('115', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (l1_pre_topc @ sk_A)
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (l1_waybel_0 @ 
% 0.76/0.97             (sk_E_2 @ 
% 0.76/0.97              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.97             sk_A)
% 0.76/0.97          | ~ (l1_waybel_0 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.97               sk_A)
% 0.76/0.97          | ~ (v7_waybel_0 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['108', '114'])).
% 0.76/0.97  thf('116', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('117', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (l1_waybel_0 @ 
% 0.76/0.97             (sk_E_2 @ 
% 0.76/0.97              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.97             sk_A)
% 0.76/0.97          | ~ (l1_waybel_0 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.97               sk_A)
% 0.76/0.97          | ~ (v7_waybel_0 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))),
% 0.76/0.97      inference('demod', [status(thm)], ['115', '116'])).
% 0.76/0.97  thf('118', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | ~ (v7_waybel_0 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (l1_waybel_0 @ 
% 0.76/0.97             (sk_E_2 @ 
% 0.76/0.97              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.97             sk_A)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['107', '117'])).
% 0.76/0.97  thf('119', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((l1_waybel_0 @ 
% 0.76/0.97           (sk_E_2 @ 
% 0.76/0.97            (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.97           sk_A)
% 0.76/0.97          | ~ (v7_waybel_0 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_A))),
% 0.76/0.97      inference('simplify', [status(thm)], ['118'])).
% 0.76/0.97  thf('120', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_B)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (l1_waybel_0 @ 
% 0.76/0.97             (sk_E_2 @ 
% 0.76/0.97              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.97             sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['106', '119'])).
% 0.76/0.97  thf('121', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((l1_waybel_0 @ 
% 0.76/0.97           (sk_E_2 @ 
% 0.76/0.97            (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.97           sk_A)
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B))),
% 0.76/0.97      inference('simplify', [status(thm)], ['120'])).
% 0.76/0.97  thf('122', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (m2_yellow_6 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.97             sk_A @ sk_B))),
% 0.76/0.97      inference('demod', [status(thm)], ['53', '54'])).
% 0.76/0.97  thf('123', plain,
% 0.76/0.97      (![X36 : $i]:
% 0.76/0.97         ((r2_hidden @ sk_C @ (k10_yellow_6 @ sk_A @ (sk_E_2 @ X36)))
% 0.76/0.97          | ~ (m2_yellow_6 @ X36 @ sk_A @ sk_B))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('124', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_B)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | (r2_hidden @ sk_C @ 
% 0.76/0.97             (k10_yellow_6 @ sk_A @ 
% 0.76/0.97              (sk_E_2 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['122', '123'])).
% 0.76/0.97  thf('125', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v7_waybel_0 @ 
% 0.76/0.97           (sk_E_2 @ 
% 0.76/0.97            (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B))),
% 0.76/0.97      inference('simplify', [status(thm)], ['104'])).
% 0.76/0.97  thf('126', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v4_orders_2 @ 
% 0.76/0.97           (sk_E_2 @ 
% 0.76/0.97            (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B))),
% 0.76/0.97      inference('simplify', [status(thm)], ['88'])).
% 0.76/0.97  thf('127', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((l1_waybel_0 @ 
% 0.76/0.97           (sk_E_2 @ 
% 0.76/0.97            (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.97           sk_A)
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B))),
% 0.76/0.97      inference('simplify', [status(thm)], ['120'])).
% 0.76/0.97  thf('128', plain,
% 0.76/0.97      (![X11 : $i, X12 : $i]:
% 0.76/0.97         (~ (l1_pre_topc @ X11)
% 0.76/0.97          | ~ (v2_pre_topc @ X11)
% 0.76/0.97          | (v2_struct_0 @ X11)
% 0.76/0.97          | (v2_struct_0 @ X12)
% 0.76/0.97          | ~ (v4_orders_2 @ X12)
% 0.76/0.97          | ~ (v7_waybel_0 @ X12)
% 0.76/0.97          | ~ (l1_waybel_0 @ X12 @ X11)
% 0.76/0.97          | (m1_subset_1 @ (k10_yellow_6 @ X11 @ X12) @ 
% 0.76/0.97             (k1_zfmisc_1 @ (u1_struct_0 @ X11))))),
% 0.76/0.97      inference('cnf', [status(esa)], [dt_k10_yellow_6])).
% 0.76/0.97  thf('129', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_B)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (m1_subset_1 @ 
% 0.76/0.97             (k10_yellow_6 @ sk_A @ 
% 0.76/0.97              (sk_E_2 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))) @ 
% 0.76/0.97             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.97          | ~ (v7_waybel_0 @ 
% 0.76/0.97               (sk_E_2 @ 
% 0.76/0.97                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.97          | ~ (v4_orders_2 @ 
% 0.76/0.97               (sk_E_2 @ 
% 0.76/0.97                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (sk_E_2 @ 
% 0.76/0.97              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | ~ (v2_pre_topc @ sk_A)
% 0.76/0.97          | ~ (l1_pre_topc @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['127', '128'])).
% 0.76/0.97  thf('130', plain, ((v2_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('131', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('132', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_B)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (m1_subset_1 @ 
% 0.76/0.97             (k10_yellow_6 @ sk_A @ 
% 0.76/0.97              (sk_E_2 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))) @ 
% 0.76/0.97             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.97          | ~ (v7_waybel_0 @ 
% 0.76/0.97               (sk_E_2 @ 
% 0.76/0.97                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.97          | ~ (v4_orders_2 @ 
% 0.76/0.97               (sk_E_2 @ 
% 0.76/0.97                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (sk_E_2 @ 
% 0.76/0.97              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.97          | (v2_struct_0 @ sk_A))),
% 0.76/0.97      inference('demod', [status(thm)], ['129', '130', '131'])).
% 0.76/0.97  thf('133', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ 
% 0.76/0.97           (sk_E_2 @ 
% 0.76/0.97            (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.97          | ~ (v4_orders_2 @ 
% 0.76/0.97               (sk_E_2 @ 
% 0.76/0.97                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.97          | ~ (v7_waybel_0 @ 
% 0.76/0.97               (sk_E_2 @ 
% 0.76/0.97                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.97          | (m1_subset_1 @ 
% 0.76/0.97             (k10_yellow_6 @ sk_A @ 
% 0.76/0.97              (sk_E_2 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))) @ 
% 0.76/0.97             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B))),
% 0.76/0.97      inference('simplify', [status(thm)], ['132'])).
% 0.76/0.97  thf('134', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_B)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (m1_subset_1 @ 
% 0.76/0.97             (k10_yellow_6 @ sk_A @ 
% 0.76/0.97              (sk_E_2 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))) @ 
% 0.76/0.97             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.97          | ~ (v7_waybel_0 @ 
% 0.76/0.97               (sk_E_2 @ 
% 0.76/0.97                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (sk_E_2 @ 
% 0.76/0.97              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['126', '133'])).
% 0.76/0.97  thf('135', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ 
% 0.76/0.97           (sk_E_2 @ 
% 0.76/0.97            (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.97          | ~ (v7_waybel_0 @ 
% 0.76/0.97               (sk_E_2 @ 
% 0.76/0.97                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.97          | (m1_subset_1 @ 
% 0.76/0.97             (k10_yellow_6 @ sk_A @ 
% 0.76/0.97              (sk_E_2 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))) @ 
% 0.76/0.97             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B))),
% 0.76/0.97      inference('simplify', [status(thm)], ['134'])).
% 0.76/0.97  thf('136', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_B)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (m1_subset_1 @ 
% 0.76/0.97             (k10_yellow_6 @ sk_A @ 
% 0.76/0.97              (sk_E_2 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))) @ 
% 0.76/0.97             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (sk_E_2 @ 
% 0.76/0.97              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['125', '135'])).
% 0.76/0.97  thf('137', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ 
% 0.76/0.97           (sk_E_2 @ 
% 0.76/0.97            (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.97          | (m1_subset_1 @ 
% 0.76/0.97             (k10_yellow_6 @ sk_A @ 
% 0.76/0.97              (sk_E_2 @ 
% 0.76/0.97               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))) @ 
% 0.76/0.97             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_B))),
% 0.76/0.97      inference('simplify', [status(thm)], ['136'])).
% 0.76/0.97  thf('138', plain,
% 0.76/0.97      (![X5 : $i, X6 : $i, X7 : $i, X9 : $i, X10 : $i]:
% 0.76/0.97         ((v2_struct_0 @ X5)
% 0.76/0.97          | ~ (v4_orders_2 @ X5)
% 0.76/0.97          | ~ (v7_waybel_0 @ X5)
% 0.76/0.97          | ~ (l1_waybel_0 @ X5 @ X6)
% 0.76/0.97          | ((X7) != (k10_yellow_6 @ X6 @ X5))
% 0.76/0.97          | ~ (m1_connsp_2 @ X10 @ X6 @ X9)
% 0.76/0.97          | (r1_waybel_0 @ X6 @ X5 @ X10)
% 0.76/0.97          | ~ (r2_hidden @ X9 @ X7)
% 0.76/0.97          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X6))
% 0.76/0.97          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.76/0.97          | ~ (l1_pre_topc @ X6)
% 0.76/0.97          | ~ (v2_pre_topc @ X6)
% 0.76/0.97          | (v2_struct_0 @ X6))),
% 0.76/0.97      inference('cnf', [status(esa)], [d18_yellow_6])).
% 0.76/0.97  thf('139', plain,
% 0.76/0.97      (![X5 : $i, X6 : $i, X9 : $i, X10 : $i]:
% 0.76/0.97         ((v2_struct_0 @ X6)
% 0.76/0.97          | ~ (v2_pre_topc @ X6)
% 0.76/0.97          | ~ (l1_pre_topc @ X6)
% 0.76/0.97          | ~ (m1_subset_1 @ (k10_yellow_6 @ X6 @ X5) @ 
% 0.76/0.97               (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.76/0.97          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X6))
% 0.76/0.97          | ~ (r2_hidden @ X9 @ (k10_yellow_6 @ X6 @ X5))
% 0.76/0.97          | (r1_waybel_0 @ X6 @ X5 @ X10)
% 0.76/0.97          | ~ (m1_connsp_2 @ X10 @ X6 @ X9)
% 0.76/0.97          | ~ (l1_waybel_0 @ X5 @ X6)
% 0.76/0.97          | ~ (v7_waybel_0 @ X5)
% 0.76/0.97          | ~ (v4_orders_2 @ X5)
% 0.76/0.97          | (v2_struct_0 @ X5))),
% 0.76/0.97      inference('simplify', [status(thm)], ['138'])).
% 0.76/0.97  thf('140', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_B)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (sk_E_2 @ 
% 0.76/0.97              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (sk_E_2 @ 
% 0.76/0.97              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.97          | ~ (v4_orders_2 @ 
% 0.76/0.97               (sk_E_2 @ 
% 0.76/0.97                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.97          | ~ (v7_waybel_0 @ 
% 0.76/0.97               (sk_E_2 @ 
% 0.76/0.97                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.97          | ~ (l1_waybel_0 @ 
% 0.76/0.97               (sk_E_2 @ 
% 0.76/0.97                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.97               sk_A)
% 0.76/0.97          | ~ (m1_connsp_2 @ X2 @ sk_A @ X1)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ 
% 0.76/0.97             (sk_E_2 @ 
% 0.76/0.97              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.97             X2)
% 0.76/0.97          | ~ (r2_hidden @ X1 @ 
% 0.76/0.97               (k10_yellow_6 @ sk_A @ 
% 0.76/0.97                (sk_E_2 @ 
% 0.76/0.97                 (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97                  (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))))
% 0.76/0.97          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.76/0.97          | ~ (l1_pre_topc @ sk_A)
% 0.76/0.97          | ~ (v2_pre_topc @ sk_A)
% 0.76/0.97          | (v2_struct_0 @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['137', '139'])).
% 0.76/0.97  thf('141', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('142', plain, ((v2_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('143', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_B)
% 0.76/0.97          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (sk_E_2 @ 
% 0.76/0.97              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.97          | (v2_struct_0 @ 
% 0.76/0.97             (sk_E_2 @ 
% 0.76/0.97              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.97               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | ~ (v4_orders_2 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | ~ (v7_waybel_0 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | ~ (l1_waybel_0 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98               sk_A)
% 0.76/0.98          | ~ (m1_connsp_2 @ X2 @ sk_A @ X1)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98             X2)
% 0.76/0.98          | ~ (r2_hidden @ X1 @ 
% 0.76/0.98               (k10_yellow_6 @ sk_A @ 
% 0.76/0.98                (sk_E_2 @ 
% 0.76/0.98                 (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                  (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))))
% 0.76/0.98          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.76/0.98          | (v2_struct_0 @ sk_A))),
% 0.76/0.98      inference('demod', [status(thm)], ['140', '141', '142'])).
% 0.76/0.98  thf('144', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.98         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.76/0.98          | ~ (r2_hidden @ X1 @ 
% 0.76/0.98               (k10_yellow_6 @ sk_A @ 
% 0.76/0.98                (sk_E_2 @ 
% 0.76/0.98                 (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                  (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))))
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98             X2)
% 0.76/0.98          | ~ (m1_connsp_2 @ X2 @ sk_A @ X1)
% 0.76/0.98          | ~ (l1_waybel_0 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98               sk_A)
% 0.76/0.98          | ~ (v7_waybel_0 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | ~ (v4_orders_2 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B))),
% 0.76/0.98      inference('simplify', [status(thm)], ['143'])).
% 0.76/0.98  thf('145', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | ~ (v4_orders_2 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | ~ (v7_waybel_0 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | ~ (l1_waybel_0 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98               sk_A)
% 0.76/0.98          | ~ (m1_connsp_2 @ X1 @ sk_A @ sk_C)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98             X1)
% 0.76/0.98          | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['124', '144'])).
% 0.76/0.98  thf('146', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('147', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | ~ (v4_orders_2 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | ~ (v7_waybel_0 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | ~ (l1_waybel_0 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98               sk_A)
% 0.76/0.98          | ~ (m1_connsp_2 @ X1 @ sk_A @ sk_C)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98             X1))),
% 0.76/0.98      inference('demod', [status(thm)], ['145', '146'])).
% 0.76/0.98  thf('148', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((r1_waybel_0 @ sk_A @ 
% 0.76/0.98           (sk_E_2 @ 
% 0.76/0.98            (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98           X1)
% 0.76/0.98          | ~ (m1_connsp_2 @ X1 @ sk_A @ sk_C)
% 0.76/0.98          | ~ (l1_waybel_0 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98               sk_A)
% 0.76/0.98          | ~ (v7_waybel_0 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | ~ (v4_orders_2 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A))),
% 0.76/0.98      inference('simplify', [status(thm)], ['147'])).
% 0.76/0.98  thf('149', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | ~ (v4_orders_2 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | ~ (v7_waybel_0 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | ~ (m1_connsp_2 @ X1 @ sk_A @ sk_C)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98             X1))),
% 0.76/0.98      inference('sup-', [status(thm)], ['121', '148'])).
% 0.76/0.98  thf('150', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((r1_waybel_0 @ sk_A @ 
% 0.76/0.98           (sk_E_2 @ 
% 0.76/0.98            (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98           X1)
% 0.76/0.98          | ~ (m1_connsp_2 @ X1 @ sk_A @ sk_C)
% 0.76/0.98          | ~ (v7_waybel_0 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | ~ (v4_orders_2 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B))),
% 0.76/0.98      inference('simplify', [status(thm)], ['149'])).
% 0.76/0.98  thf('151', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | ~ (v4_orders_2 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | ~ (m1_connsp_2 @ X1 @ sk_A @ sk_C)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98             X1))),
% 0.76/0.98      inference('sup-', [status(thm)], ['105', '150'])).
% 0.76/0.98  thf('152', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((r1_waybel_0 @ sk_A @ 
% 0.76/0.98           (sk_E_2 @ 
% 0.76/0.98            (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98           X1)
% 0.76/0.98          | ~ (m1_connsp_2 @ X1 @ sk_A @ sk_C)
% 0.76/0.98          | ~ (v4_orders_2 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B))),
% 0.76/0.98      inference('simplify', [status(thm)], ['151'])).
% 0.76/0.98  thf('153', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | ~ (m1_connsp_2 @ X1 @ sk_A @ sk_C)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98             X1))),
% 0.76/0.98      inference('sup-', [status(thm)], ['89', '152'])).
% 0.76/0.98  thf('154', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((r1_waybel_0 @ sk_A @ 
% 0.76/0.98           (sk_E_2 @ 
% 0.76/0.98            (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98           X1)
% 0.76/0.98          | ~ (m1_connsp_2 @ X1 @ sk_A @ sk_C)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B))),
% 0.76/0.98      inference('simplify', [status(thm)], ['153'])).
% 0.76/0.98  thf('155', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_B)
% 0.76/0.98          | (r2_hidden @ sk_C @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98             (sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['41', '154'])).
% 0.76/0.98  thf('156', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((r1_waybel_0 @ sk_A @ 
% 0.76/0.98           (sk_E_2 @ 
% 0.76/0.98            (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98           (sk_E_1 @ sk_C @ sk_B @ sk_A))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (r2_hidden @ sk_C @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.76/0.98          | (v2_struct_0 @ sk_B))),
% 0.76/0.98      inference('simplify', [status(thm)], ['155'])).
% 0.76/0.98  thf('157', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((l1_waybel_0 @ 
% 0.76/0.98           (sk_E_2 @ 
% 0.76/0.98            (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98           sk_A)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B))),
% 0.76/0.98      inference('simplify', [status(thm)], ['120'])).
% 0.76/0.98  thf('158', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.76/0.98      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.76/0.98  thf('159', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((v4_orders_2 @ 
% 0.76/0.98           (sk_E_2 @ 
% 0.76/0.98            (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B))),
% 0.76/0.98      inference('simplify', [status(thm)], ['88'])).
% 0.76/0.98  thf('160', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((v7_waybel_0 @ 
% 0.76/0.98           (sk_E_2 @ 
% 0.76/0.98            (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B))),
% 0.76/0.98      inference('simplify', [status(thm)], ['104'])).
% 0.76/0.98  thf('161', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((l1_waybel_0 @ 
% 0.76/0.98           (sk_E_2 @ 
% 0.76/0.98            (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98           sk_A)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B))),
% 0.76/0.98      inference('simplify', [status(thm)], ['120'])).
% 0.76/0.98  thf('162', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.76/0.98      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.76/0.98  thf('163', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.76/0.98      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.76/0.98  thf('164', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (m2_yellow_6 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.98             sk_A @ sk_B))),
% 0.76/0.98      inference('demod', [status(thm)], ['53', '54'])).
% 0.76/0.98  thf(t32_yellow_6, axiom,
% 0.76/0.98    (![A:$i]:
% 0.76/0.98     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.76/0.98       ( ![B:$i]:
% 0.76/0.98         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.76/0.98             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.76/0.98           ( ![C:$i,D:$i]:
% 0.76/0.98             ( ( m2_yellow_6 @ D @ A @ B ) =>
% 0.76/0.98               ( ( ( D ) = ( k5_yellow_6 @ A @ B @ C ) ) =>
% 0.76/0.98                 ( r1_waybel_0 @ A @ D @ C ) ) ) ) ) ) ))).
% 0.76/0.98  thf('165', plain,
% 0.76/0.98      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.76/0.98         ((v2_struct_0 @ X32)
% 0.76/0.98          | ~ (v4_orders_2 @ X32)
% 0.76/0.98          | ~ (v7_waybel_0 @ X32)
% 0.76/0.98          | ~ (l1_waybel_0 @ X32 @ X33)
% 0.76/0.98          | ((X35) != (k5_yellow_6 @ X33 @ X32 @ X34))
% 0.76/0.98          | (r1_waybel_0 @ X33 @ X35 @ X34)
% 0.76/0.98          | ~ (m2_yellow_6 @ X35 @ X33 @ X32)
% 0.76/0.98          | ~ (l1_struct_0 @ X33)
% 0.76/0.98          | (v2_struct_0 @ X33))),
% 0.76/0.98      inference('cnf', [status(esa)], [t32_yellow_6])).
% 0.76/0.98  thf('166', plain,
% 0.76/0.98      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.76/0.98         ((v2_struct_0 @ X33)
% 0.76/0.98          | ~ (l1_struct_0 @ X33)
% 0.76/0.98          | ~ (m2_yellow_6 @ (k5_yellow_6 @ X33 @ X32 @ X34) @ X33 @ X32)
% 0.76/0.98          | (r1_waybel_0 @ X33 @ (k5_yellow_6 @ X33 @ X32 @ X34) @ X34)
% 0.76/0.98          | ~ (l1_waybel_0 @ X32 @ X33)
% 0.76/0.98          | ~ (v7_waybel_0 @ X32)
% 0.76/0.98          | ~ (v4_orders_2 @ X32)
% 0.76/0.98          | (v2_struct_0 @ X32))),
% 0.76/0.98      inference('simplify', [status(thm)], ['165'])).
% 0.76/0.98  thf('167', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | ~ (v4_orders_2 @ sk_B)
% 0.76/0.98          | ~ (v7_waybel_0 @ sk_B)
% 0.76/0.98          | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.76/0.98          | ~ (l1_struct_0 @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ sk_A))),
% 0.76/0.98      inference('sup-', [status(thm)], ['164', '166'])).
% 0.76/0.98  thf('168', plain, ((v4_orders_2 @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('169', plain, ((v7_waybel_0 @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('170', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('171', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.76/0.98          | ~ (l1_struct_0 @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ sk_A))),
% 0.76/0.98      inference('demod', [status(thm)], ['167', '168', '169', '170'])).
% 0.76/0.98  thf('172', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (~ (l1_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B))),
% 0.76/0.98      inference('simplify', [status(thm)], ['171'])).
% 0.76/0.98  thf('173', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (~ (l1_pre_topc @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['163', '172'])).
% 0.76/0.98  thf('174', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('175', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))),
% 0.76/0.98      inference('demod', [status(thm)], ['173', '174'])).
% 0.76/0.98  thf('176', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (l1_waybel_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.98             sk_A))),
% 0.76/0.98      inference('demod', [status(thm)], ['63', '64'])).
% 0.76/0.98  thf('177', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.76/0.98      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.76/0.98  thf('178', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (v7_waybel_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))),
% 0.76/0.98      inference('demod', [status(thm)], ['16', '17'])).
% 0.76/0.98  thf('179', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (l1_waybel_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.98             sk_A))),
% 0.76/0.98      inference('demod', [status(thm)], ['63', '64'])).
% 0.76/0.98  thf('180', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.76/0.98      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.76/0.98  thf('181', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((l1_waybel_0 @ 
% 0.76/0.98           (sk_E_2 @ 
% 0.76/0.98            (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98           sk_A)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B))),
% 0.76/0.98      inference('simplify', [status(thm)], ['120'])).
% 0.76/0.98  thf('182', plain,
% 0.76/0.98      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.76/0.98         ((v2_struct_0 @ X1)
% 0.76/0.98          | ~ (l1_waybel_0 @ X1 @ X2)
% 0.76/0.98          | (r2_waybel_0 @ X2 @ X1 @ (k6_subset_1 @ (u1_struct_0 @ X2) @ X3))
% 0.76/0.98          | (r1_waybel_0 @ X2 @ X1 @ X3)
% 0.76/0.98          | ~ (l1_struct_0 @ X2)
% 0.76/0.98          | (v2_struct_0 @ X2))),
% 0.76/0.98      inference('cnf', [status(esa)], [t9_waybel_0])).
% 0.76/0.98  thf('183', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | ~ (l1_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98             X1)
% 0.76/0.98          | (r2_waybel_0 @ sk_A @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X1))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['181', '182'])).
% 0.76/0.98  thf('184', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((v2_struct_0 @ 
% 0.76/0.98           (sk_E_2 @ 
% 0.76/0.98            (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | (r2_waybel_0 @ sk_A @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X1))
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98             X1)
% 0.76/0.98          | ~ (l1_struct_0 @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B))),
% 0.76/0.98      inference('simplify', [status(thm)], ['183'])).
% 0.76/0.98  thf('185', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         (~ (l1_pre_topc @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98             X1)
% 0.76/0.98          | (r2_waybel_0 @ sk_A @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X1))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['180', '184'])).
% 0.76/0.98  thf('186', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('187', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98             X1)
% 0.76/0.98          | (r2_waybel_0 @ sk_A @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X1))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))))),
% 0.76/0.98      inference('demod', [status(thm)], ['185', '186'])).
% 0.76/0.98  thf('188', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.76/0.98      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.76/0.98  thf('189', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (m2_yellow_6 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98             sk_A @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['67', '68'])).
% 0.76/0.98  thf(t27_yellow_6, axiom,
% 0.76/0.98    (![A:$i]:
% 0.76/0.98     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.76/0.98       ( ![B:$i]:
% 0.76/0.98         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.76/0.98             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.76/0.98           ( ![C:$i]:
% 0.76/0.98             ( ( m2_yellow_6 @ C @ A @ B ) =>
% 0.76/0.98               ( ![D:$i]:
% 0.76/0.98                 ( ( r2_waybel_0 @ A @ C @ D ) => ( r2_waybel_0 @ A @ B @ D ) ) ) ) ) ) ) ))).
% 0.76/0.98  thf('190', plain,
% 0.76/0.98      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.76/0.98         ((v2_struct_0 @ X19)
% 0.76/0.98          | ~ (v4_orders_2 @ X19)
% 0.76/0.98          | ~ (v7_waybel_0 @ X19)
% 0.76/0.98          | ~ (l1_waybel_0 @ X19 @ X20)
% 0.76/0.98          | ~ (r2_waybel_0 @ X20 @ X21 @ X22)
% 0.76/0.98          | (r2_waybel_0 @ X20 @ X19 @ X22)
% 0.76/0.98          | ~ (m2_yellow_6 @ X21 @ X20 @ X19)
% 0.76/0.98          | ~ (l1_struct_0 @ X20)
% 0.76/0.98          | (v2_struct_0 @ X20))),
% 0.76/0.98      inference('cnf', [status(esa)], [t27_yellow_6])).
% 0.76/0.98  thf('191', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | ~ (l1_struct_0 @ sk_A)
% 0.76/0.98          | (r2_waybel_0 @ sk_A @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.98             X1)
% 0.76/0.98          | ~ (r2_waybel_0 @ sk_A @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98               X1)
% 0.76/0.98          | ~ (l1_waybel_0 @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.98               sk_A)
% 0.76/0.98          | ~ (v7_waybel_0 @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | ~ (v4_orders_2 @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['189', '190'])).
% 0.76/0.98  thf('192', plain,
% 0.76/0.98      (![X0 : $i]: (v4_orders_2 @ (k5_yellow_6 @ sk_A @ sk_B @ X0))),
% 0.76/0.98      inference('demod', [status(thm)], ['78', '79'])).
% 0.76/0.98  thf('193', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | ~ (l1_struct_0 @ sk_A)
% 0.76/0.98          | (r2_waybel_0 @ sk_A @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.98             X1)
% 0.76/0.98          | ~ (r2_waybel_0 @ sk_A @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98               X1)
% 0.76/0.98          | ~ (l1_waybel_0 @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.98               sk_A)
% 0.76/0.98          | ~ (v7_waybel_0 @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))),
% 0.76/0.98      inference('demod', [status(thm)], ['191', '192'])).
% 0.76/0.98  thf('194', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((v2_struct_0 @ 
% 0.76/0.98           (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98            (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | ~ (v7_waybel_0 @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | ~ (l1_waybel_0 @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.98               sk_A)
% 0.76/0.98          | ~ (r2_waybel_0 @ sk_A @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98               X1)
% 0.76/0.98          | (r2_waybel_0 @ sk_A @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.98             X1)
% 0.76/0.98          | ~ (l1_struct_0 @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A))),
% 0.76/0.98      inference('simplify', [status(thm)], ['193'])).
% 0.76/0.98  thf('195', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         (~ (l1_pre_topc @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (r2_waybel_0 @ sk_A @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.98             X1)
% 0.76/0.98          | ~ (r2_waybel_0 @ sk_A @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98               X1)
% 0.76/0.98          | ~ (l1_waybel_0 @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.98               sk_A)
% 0.76/0.98          | ~ (v7_waybel_0 @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['188', '194'])).
% 0.76/0.98  thf('196', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('197', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (r2_waybel_0 @ sk_A @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.98             X1)
% 0.76/0.98          | ~ (r2_waybel_0 @ sk_A @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98               X1)
% 0.76/0.98          | ~ (l1_waybel_0 @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.98               sk_A)
% 0.76/0.98          | ~ (v7_waybel_0 @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))),
% 0.76/0.98      inference('demod', [status(thm)], ['195', '196'])).
% 0.76/0.98  thf('198', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((v2_struct_0 @ 
% 0.76/0.98           (sk_E_2 @ 
% 0.76/0.98            (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X1))))
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X1))) @ 
% 0.76/0.98             X0)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X1)))
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X1)
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X1)))
% 0.76/0.98          | ~ (v7_waybel_0 @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X1)))
% 0.76/0.98          | ~ (l1_waybel_0 @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X1)) @ 
% 0.76/0.98               sk_A)
% 0.76/0.98          | (r2_waybel_0 @ sk_A @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X1)) @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X1)
% 0.76/0.98          | (v2_struct_0 @ sk_A))),
% 0.76/0.98      inference('sup-', [status(thm)], ['187', '197'])).
% 0.76/0.98  thf('199', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((r2_waybel_0 @ sk_A @ 
% 0.76/0.98           (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98            (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X1)) @ 
% 0.76/0.98           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.76/0.98          | ~ (l1_waybel_0 @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X1)) @ 
% 0.76/0.98               sk_A)
% 0.76/0.98          | ~ (v7_waybel_0 @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X1)))
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X1)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X1)))
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X1))) @ 
% 0.76/0.98             X0)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X1)))))),
% 0.76/0.98      inference('simplify', [status(thm)], ['198'])).
% 0.76/0.98  thf('200', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98             X1)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | ~ (v7_waybel_0 @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (r2_waybel_0 @ sk_A @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X1)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['179', '199'])).
% 0.76/0.98  thf('201', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((r2_waybel_0 @ sk_A @ 
% 0.76/0.98           (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98            (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.98           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X1))
% 0.76/0.98          | ~ (v7_waybel_0 @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98             X1)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A))),
% 0.76/0.98      inference('simplify', [status(thm)], ['200'])).
% 0.76/0.98  thf('202', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98             X1)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (r2_waybel_0 @ sk_A @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X1)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['178', '201'])).
% 0.76/0.98  thf('203', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((r2_waybel_0 @ sk_A @ 
% 0.76/0.98           (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98            (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.98           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X1))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98             X1)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B))),
% 0.76/0.98      inference('simplify', [status(thm)], ['202'])).
% 0.76/0.98  thf('204', plain,
% 0.76/0.98      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.76/0.98         ((v2_struct_0 @ X1)
% 0.76/0.98          | ~ (l1_waybel_0 @ X1 @ X2)
% 0.76/0.98          | ~ (r1_waybel_0 @ X2 @ X1 @ X4)
% 0.76/0.98          | ~ (r2_waybel_0 @ X2 @ X1 @ (k6_subset_1 @ (u1_struct_0 @ X2) @ X4))
% 0.76/0.98          | ~ (l1_struct_0 @ X2)
% 0.76/0.98          | (v2_struct_0 @ X2))),
% 0.76/0.98      inference('cnf', [status(esa)], [t9_waybel_0])).
% 0.76/0.98  thf('205', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X1)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X1))))
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X1))) @ 
% 0.76/0.98             X0)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X1)))
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | ~ (l1_struct_0 @ sk_A)
% 0.76/0.98          | ~ (r1_waybel_0 @ sk_A @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X1)) @ 
% 0.76/0.98               X0)
% 0.76/0.98          | ~ (l1_waybel_0 @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X1)) @ 
% 0.76/0.98               sk_A)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X1))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['203', '204'])).
% 0.76/0.98  thf('206', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         (~ (l1_waybel_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X1)) @ 
% 0.76/0.98             sk_A)
% 0.76/0.98          | ~ (r1_waybel_0 @ sk_A @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X1)) @ 
% 0.76/0.98               X0)
% 0.76/0.98          | ~ (l1_struct_0 @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X1)))
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X1))) @ 
% 0.76/0.98             X0)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X1))))
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X1)
% 0.76/0.98          | (v2_struct_0 @ sk_B))),
% 0.76/0.98      inference('simplify', [status(thm)], ['205'])).
% 0.76/0.98  thf('207', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         (~ (l1_pre_topc @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98             X1)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | ~ (r1_waybel_0 @ sk_A @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.98               X1)
% 0.76/0.98          | ~ (l1_waybel_0 @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.98               sk_A))),
% 0.76/0.98      inference('sup-', [status(thm)], ['177', '206'])).
% 0.76/0.98  thf('208', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('209', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98             X1)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | ~ (r1_waybel_0 @ sk_A @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.98               X1)
% 0.76/0.98          | ~ (l1_waybel_0 @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.98               sk_A))),
% 0.76/0.98      inference('demod', [status(thm)], ['207', '208'])).
% 0.76/0.98  thf('210', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | ~ (r1_waybel_0 @ sk_A @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.98               X1)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98             X1)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B))),
% 0.76/0.98      inference('sup-', [status(thm)], ['176', '209'])).
% 0.76/0.98  thf('211', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((v2_struct_0 @ 
% 0.76/0.98           (sk_E_2 @ 
% 0.76/0.98            (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98             X1)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | ~ (r1_waybel_0 @ sk_A @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.98               X1)
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A))),
% 0.76/0.98      inference('simplify', [status(thm)], ['210'])).
% 0.76/0.98  thf('212', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['175', '211'])).
% 0.76/0.98  thf('213', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((v2_struct_0 @ 
% 0.76/0.98           (sk_E_2 @ 
% 0.76/0.98            (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A))),
% 0.76/0.98      inference('simplify', [status(thm)], ['212'])).
% 0.76/0.98  thf(t28_yellow_6, axiom,
% 0.76/0.98    (![A:$i]:
% 0.76/0.98     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.76/0.98       ( ![B:$i]:
% 0.76/0.98         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.76/0.98             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.76/0.98           ( ![C:$i]:
% 0.76/0.98             ( ( r1_waybel_0 @ A @ B @ C ) => ( r2_waybel_0 @ A @ B @ C ) ) ) ) ) ))).
% 0.76/0.98  thf('214', plain,
% 0.76/0.98      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.76/0.98         ((v2_struct_0 @ X23)
% 0.76/0.98          | ~ (v4_orders_2 @ X23)
% 0.76/0.98          | ~ (v7_waybel_0 @ X23)
% 0.76/0.98          | ~ (l1_waybel_0 @ X23 @ X24)
% 0.76/0.98          | (r2_waybel_0 @ X24 @ X23 @ X25)
% 0.76/0.98          | ~ (r1_waybel_0 @ X24 @ X23 @ X25)
% 0.76/0.98          | ~ (l1_struct_0 @ X24)
% 0.76/0.98          | (v2_struct_0 @ X24))),
% 0.76/0.98      inference('cnf', [status(esa)], [t28_yellow_6])).
% 0.76/0.98  thf('215', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | ~ (l1_struct_0 @ sk_A)
% 0.76/0.98          | (r2_waybel_0 @ sk_A @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.76/0.98          | ~ (l1_waybel_0 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98               sk_A)
% 0.76/0.98          | ~ (v7_waybel_0 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | ~ (v4_orders_2 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['213', '214'])).
% 0.76/0.98  thf('216', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (~ (v4_orders_2 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | ~ (v7_waybel_0 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | ~ (l1_waybel_0 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98               sk_A)
% 0.76/0.98          | (r2_waybel_0 @ sk_A @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.76/0.98          | ~ (l1_struct_0 @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A))),
% 0.76/0.98      inference('simplify', [status(thm)], ['215'])).
% 0.76/0.98  thf('217', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (~ (l1_pre_topc @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | (r2_waybel_0 @ sk_A @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.76/0.98          | ~ (l1_waybel_0 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98               sk_A)
% 0.76/0.98          | ~ (v7_waybel_0 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | ~ (v4_orders_2 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['162', '216'])).
% 0.76/0.98  thf('218', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('219', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | (r2_waybel_0 @ sk_A @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.76/0.98          | ~ (l1_waybel_0 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98               sk_A)
% 0.76/0.98          | ~ (v7_waybel_0 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | ~ (v4_orders_2 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))))),
% 0.76/0.98      inference('demod', [status(thm)], ['217', '218'])).
% 0.76/0.98  thf('220', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | ~ (v4_orders_2 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | ~ (v7_waybel_0 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | (r2_waybel_0 @ sk_A @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A))),
% 0.76/0.98      inference('sup-', [status(thm)], ['161', '219'])).
% 0.76/0.98  thf('221', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((v2_struct_0 @ 
% 0.76/0.98           (sk_E_2 @ 
% 0.76/0.98            (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | (r2_waybel_0 @ sk_A @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.76/0.98          | ~ (v7_waybel_0 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | ~ (v4_orders_2 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B))),
% 0.76/0.98      inference('simplify', [status(thm)], ['220'])).
% 0.76/0.98  thf('222', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | ~ (v4_orders_2 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | (r2_waybel_0 @ sk_A @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['160', '221'])).
% 0.76/0.98  thf('223', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((v2_struct_0 @ 
% 0.76/0.98           (sk_E_2 @ 
% 0.76/0.98            (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | (r2_waybel_0 @ sk_A @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.76/0.98          | ~ (v4_orders_2 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B))),
% 0.76/0.98      inference('simplify', [status(thm)], ['222'])).
% 0.76/0.98  thf('224', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (r2_waybel_0 @ sk_A @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['159', '223'])).
% 0.76/0.98  thf('225', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((v2_struct_0 @ 
% 0.76/0.98           (sk_E_2 @ 
% 0.76/0.98            (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | (r2_waybel_0 @ sk_A @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B))),
% 0.76/0.98      inference('simplify', [status(thm)], ['224'])).
% 0.76/0.98  thf('226', plain,
% 0.76/0.98      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.76/0.98         ((v2_struct_0 @ X1)
% 0.76/0.98          | ~ (l1_waybel_0 @ X1 @ X2)
% 0.76/0.98          | ~ (r1_waybel_0 @ X2 @ X1 @ X4)
% 0.76/0.98          | ~ (r2_waybel_0 @ X2 @ X1 @ (k6_subset_1 @ (u1_struct_0 @ X2) @ X4))
% 0.76/0.98          | ~ (l1_struct_0 @ X2)
% 0.76/0.98          | (v2_struct_0 @ X2))),
% 0.76/0.98      inference('cnf', [status(esa)], [t9_waybel_0])).
% 0.76/0.98  thf('227', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | ~ (l1_struct_0 @ sk_A)
% 0.76/0.98          | ~ (r1_waybel_0 @ sk_A @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98               X0)
% 0.76/0.98          | ~ (l1_waybel_0 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98               sk_A)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['225', '226'])).
% 0.76/0.98  thf('228', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (~ (l1_waybel_0 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98             sk_A)
% 0.76/0.98          | ~ (r1_waybel_0 @ sk_A @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98               X0)
% 0.76/0.98          | ~ (l1_struct_0 @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B))),
% 0.76/0.98      inference('simplify', [status(thm)], ['227'])).
% 0.76/0.98  thf('229', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (~ (l1_pre_topc @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | ~ (r1_waybel_0 @ sk_A @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98               X0)
% 0.76/0.98          | ~ (l1_waybel_0 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98               sk_A))),
% 0.76/0.98      inference('sup-', [status(thm)], ['158', '228'])).
% 0.76/0.98  thf('230', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('231', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | ~ (r1_waybel_0 @ sk_A @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98               X0)
% 0.76/0.98          | ~ (l1_waybel_0 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98               sk_A))),
% 0.76/0.98      inference('demod', [status(thm)], ['229', '230'])).
% 0.76/0.98  thf('232', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | ~ (r1_waybel_0 @ sk_A @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98               X0)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B))),
% 0.76/0.98      inference('sup-', [status(thm)], ['157', '231'])).
% 0.76/0.98  thf('233', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((v2_struct_0 @ 
% 0.76/0.98           (sk_E_2 @ 
% 0.76/0.98            (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | ~ (r1_waybel_0 @ sk_A @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98               X0)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B))),
% 0.76/0.98      inference('simplify', [status(thm)], ['232'])).
% 0.76/0.98  thf('234', plain,
% 0.76/0.98      (((v2_struct_0 @ sk_B)
% 0.76/0.98        | (r2_hidden @ sk_C @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.76/0.98        | (v2_struct_0 @ sk_A)
% 0.76/0.98        | (r1_waybel_0 @ sk_A @ sk_B @ (sk_E_1 @ sk_C @ sk_B @ sk_A))
% 0.76/0.98        | (v2_struct_0 @ 
% 0.76/0.98           (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98            (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_E_1 @ sk_C @ sk_B @ sk_A))))
% 0.76/0.98        | (v2_struct_0 @ 
% 0.76/0.98           (sk_E_2 @ 
% 0.76/0.98            (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.98              (sk_E_1 @ sk_C @ sk_B @ sk_A)))))
% 0.76/0.98        | (v2_struct_0 @ sk_B)
% 0.76/0.98        | (r1_waybel_0 @ sk_A @ sk_B @ (sk_E_1 @ sk_C @ sk_B @ sk_A))
% 0.76/0.98        | (v2_struct_0 @ sk_A)
% 0.76/0.98        | (v2_struct_0 @ 
% 0.76/0.98           (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98            (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_E_1 @ sk_C @ sk_B @ sk_A))))
% 0.76/0.98        | (v2_struct_0 @ 
% 0.76/0.98           (sk_E_2 @ 
% 0.76/0.98            (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.98              (sk_E_1 @ sk_C @ sk_B @ sk_A))))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['156', '233'])).
% 0.76/0.98  thf('235', plain,
% 0.76/0.98      (((v2_struct_0 @ 
% 0.76/0.98         (sk_E_2 @ 
% 0.76/0.98          (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_E_1 @ sk_C @ sk_B @ sk_A)))))
% 0.76/0.98        | (v2_struct_0 @ 
% 0.76/0.98           (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98            (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_E_1 @ sk_C @ sk_B @ sk_A))))
% 0.76/0.98        | (r1_waybel_0 @ sk_A @ sk_B @ (sk_E_1 @ sk_C @ sk_B @ sk_A))
% 0.76/0.98        | (v2_struct_0 @ sk_A)
% 0.76/0.98        | (r2_hidden @ sk_C @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.76/0.98        | (v2_struct_0 @ sk_B))),
% 0.76/0.98      inference('simplify', [status(thm)], ['234'])).
% 0.76/0.98  thf('236', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (l1_waybel_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.98             sk_A))),
% 0.76/0.98      inference('demod', [status(thm)], ['63', '64'])).
% 0.76/0.98  thf('237', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.76/0.98      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.76/0.98  thf('238', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (m2_yellow_6 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))) @ 
% 0.76/0.98             sk_A @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['67', '68'])).
% 0.76/0.98  thf('239', plain,
% 0.76/0.98      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.76/0.98         (~ (l1_struct_0 @ X13)
% 0.76/0.98          | (v2_struct_0 @ X13)
% 0.76/0.98          | (v2_struct_0 @ X14)
% 0.76/0.98          | ~ (v4_orders_2 @ X14)
% 0.76/0.98          | ~ (v7_waybel_0 @ X14)
% 0.76/0.98          | ~ (l1_waybel_0 @ X14 @ X13)
% 0.76/0.98          | ~ (v2_struct_0 @ X15)
% 0.76/0.98          | ~ (m2_yellow_6 @ X15 @ X13 @ X14))),
% 0.76/0.98      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 0.76/0.98  thf('240', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | ~ (v2_struct_0 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | ~ (l1_waybel_0 @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.98               sk_A)
% 0.76/0.98          | ~ (v7_waybel_0 @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | ~ (v4_orders_2 @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | ~ (l1_struct_0 @ sk_A))),
% 0.76/0.98      inference('sup-', [status(thm)], ['238', '239'])).
% 0.76/0.98  thf('241', plain,
% 0.76/0.98      (![X0 : $i]: (v4_orders_2 @ (k5_yellow_6 @ sk_A @ sk_B @ X0))),
% 0.76/0.98      inference('demod', [status(thm)], ['78', '79'])).
% 0.76/0.98  thf('242', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | ~ (v2_struct_0 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | ~ (l1_waybel_0 @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.98               sk_A)
% 0.76/0.98          | ~ (v7_waybel_0 @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | ~ (l1_struct_0 @ sk_A))),
% 0.76/0.98      inference('demod', [status(thm)], ['240', '241'])).
% 0.76/0.98  thf('243', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (~ (l1_struct_0 @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | ~ (v7_waybel_0 @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | ~ (l1_waybel_0 @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.98               sk_A)
% 0.76/0.98          | ~ (v2_struct_0 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A))),
% 0.76/0.98      inference('simplify', [status(thm)], ['242'])).
% 0.76/0.98  thf('244', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (~ (l1_pre_topc @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | ~ (v2_struct_0 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | ~ (l1_waybel_0 @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.98               sk_A)
% 0.76/0.98          | ~ (v7_waybel_0 @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['237', '243'])).
% 0.76/0.98  thf('245', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('246', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | ~ (v2_struct_0 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | ~ (l1_waybel_0 @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.98               sk_A)
% 0.76/0.98          | ~ (v7_waybel_0 @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))),
% 0.76/0.98      inference('demod', [status(thm)], ['244', '245'])).
% 0.76/0.98  thf('247', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | ~ (v7_waybel_0 @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | ~ (v2_struct_0 @ 
% 0.76/0.98               (sk_E_2 @ 
% 0.76/0.98                (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                 (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A))),
% 0.76/0.98      inference('sup-', [status(thm)], ['236', '246'])).
% 0.76/0.98  thf('248', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (~ (v2_struct_0 @ 
% 0.76/0.98             (sk_E_2 @ 
% 0.76/0.98              (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))
% 0.76/0.98          | ~ (v7_waybel_0 @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A))),
% 0.76/0.98      inference('simplify', [status(thm)], ['247'])).
% 0.76/0.98  thf('249', plain,
% 0.76/0.98      (((v2_struct_0 @ sk_B)
% 0.76/0.98        | (r2_hidden @ sk_C @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.76/0.98        | (v2_struct_0 @ sk_A)
% 0.76/0.98        | (r1_waybel_0 @ sk_A @ sk_B @ (sk_E_1 @ sk_C @ sk_B @ sk_A))
% 0.76/0.98        | (v2_struct_0 @ 
% 0.76/0.98           (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98            (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_E_1 @ sk_C @ sk_B @ sk_A))))
% 0.76/0.98        | (v2_struct_0 @ sk_A)
% 0.76/0.98        | (r1_waybel_0 @ sk_A @ sk_B @ (sk_E_1 @ sk_C @ sk_B @ sk_A))
% 0.76/0.98        | (v2_struct_0 @ sk_B)
% 0.76/0.98        | (v2_struct_0 @ 
% 0.76/0.98           (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98            (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_E_1 @ sk_C @ sk_B @ sk_A))))
% 0.76/0.98        | ~ (v7_waybel_0 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.98               (sk_E_1 @ sk_C @ sk_B @ sk_A)))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['235', '248'])).
% 0.76/0.98  thf('250', plain,
% 0.76/0.98      ((~ (v7_waybel_0 @ 
% 0.76/0.98           (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98            (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_E_1 @ sk_C @ sk_B @ sk_A))))
% 0.76/0.98        | (v2_struct_0 @ 
% 0.76/0.98           (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98            (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_E_1 @ sk_C @ sk_B @ sk_A))))
% 0.76/0.98        | (r1_waybel_0 @ sk_A @ sk_B @ (sk_E_1 @ sk_C @ sk_B @ sk_A))
% 0.76/0.98        | (v2_struct_0 @ sk_A)
% 0.76/0.98        | (r2_hidden @ sk_C @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.76/0.98        | (v2_struct_0 @ sk_B))),
% 0.76/0.98      inference('simplify', [status(thm)], ['249'])).
% 0.76/0.98  thf('251', plain,
% 0.76/0.98      (((v2_struct_0 @ sk_B)
% 0.76/0.98        | (r1_waybel_0 @ sk_A @ sk_B @ (sk_E_1 @ sk_C @ sk_B @ sk_A))
% 0.76/0.98        | (v2_struct_0 @ sk_A)
% 0.76/0.98        | (v2_struct_0 @ sk_B)
% 0.76/0.98        | (r2_hidden @ sk_C @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.76/0.98        | (v2_struct_0 @ sk_A)
% 0.76/0.98        | (r1_waybel_0 @ sk_A @ sk_B @ (sk_E_1 @ sk_C @ sk_B @ sk_A))
% 0.76/0.98        | (v2_struct_0 @ 
% 0.76/0.98           (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98            (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_E_1 @ sk_C @ sk_B @ sk_A)))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['18', '250'])).
% 0.76/0.98  thf('252', plain,
% 0.76/0.98      (((v2_struct_0 @ 
% 0.76/0.98         (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98          (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_E_1 @ sk_C @ sk_B @ sk_A))))
% 0.76/0.98        | (r2_hidden @ sk_C @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.76/0.98        | (v2_struct_0 @ sk_A)
% 0.76/0.98        | (r1_waybel_0 @ sk_A @ sk_B @ (sk_E_1 @ sk_C @ sk_B @ sk_A))
% 0.76/0.98        | (v2_struct_0 @ sk_B))),
% 0.76/0.98      inference('simplify', [status(thm)], ['251'])).
% 0.76/0.98  thf('253', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.76/0.98      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.76/0.98  thf('254', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (m2_yellow_6 @ 
% 0.76/0.98             (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)) @ 
% 0.76/0.98             sk_A @ sk_B))),
% 0.76/0.98      inference('demod', [status(thm)], ['53', '54'])).
% 0.76/0.98  thf('255', plain,
% 0.76/0.98      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.76/0.98         (~ (l1_struct_0 @ X13)
% 0.76/0.98          | (v2_struct_0 @ X13)
% 0.76/0.98          | (v2_struct_0 @ X14)
% 0.76/0.98          | ~ (v4_orders_2 @ X14)
% 0.76/0.98          | ~ (v7_waybel_0 @ X14)
% 0.76/0.98          | ~ (l1_waybel_0 @ X14 @ X13)
% 0.76/0.98          | ~ (v2_struct_0 @ X15)
% 0.76/0.98          | ~ (m2_yellow_6 @ X15 @ X13 @ X14))),
% 0.76/0.98      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 0.76/0.98  thf('256', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | ~ (v2_struct_0 @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.76/0.98          | ~ (v7_waybel_0 @ sk_B)
% 0.76/0.98          | ~ (v4_orders_2 @ sk_B)
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | ~ (l1_struct_0 @ sk_A))),
% 0.76/0.98      inference('sup-', [status(thm)], ['254', '255'])).
% 0.76/0.98  thf('257', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('258', plain, ((v7_waybel_0 @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('259', plain, ((v4_orders_2 @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('260', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | ~ (v2_struct_0 @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | ~ (l1_struct_0 @ sk_A))),
% 0.76/0.98      inference('demod', [status(thm)], ['256', '257', '258', '259'])).
% 0.76/0.98  thf('261', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (~ (l1_struct_0 @ sk_A)
% 0.76/0.98          | ~ (v2_struct_0 @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_B))),
% 0.76/0.98      inference('simplify', [status(thm)], ['260'])).
% 0.76/0.98  thf('262', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (~ (l1_pre_topc @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | ~ (v2_struct_0 @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['253', '261'])).
% 0.76/0.98  thf('263', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('264', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_B)
% 0.76/0.98          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.76/0.98          | (v2_struct_0 @ sk_A)
% 0.76/0.98          | ~ (v2_struct_0 @ 
% 0.76/0.98               (k5_yellow_6 @ sk_A @ sk_B @ 
% 0.76/0.98                (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))))),
% 0.76/0.98      inference('demod', [status(thm)], ['262', '263'])).
% 0.76/0.98  thf('265', plain,
% 0.76/0.98      (((v2_struct_0 @ sk_B)
% 0.76/0.98        | (r1_waybel_0 @ sk_A @ sk_B @ (sk_E_1 @ sk_C @ sk_B @ sk_A))
% 0.76/0.98        | (v2_struct_0 @ sk_A)
% 0.76/0.98        | (r2_hidden @ sk_C @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.76/0.98        | (v2_struct_0 @ sk_A)
% 0.76/0.98        | (r1_waybel_0 @ sk_A @ sk_B @ (sk_E_1 @ sk_C @ sk_B @ sk_A))
% 0.76/0.98        | (v2_struct_0 @ sk_B))),
% 0.76/0.98      inference('sup-', [status(thm)], ['252', '264'])).
% 0.76/0.98  thf('266', plain,
% 0.76/0.98      (((r2_hidden @ sk_C @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.76/0.98        | (v2_struct_0 @ sk_A)
% 0.76/0.98        | (r1_waybel_0 @ sk_A @ sk_B @ (sk_E_1 @ sk_C @ sk_B @ sk_A))
% 0.76/0.98        | (v2_struct_0 @ sk_B))),
% 0.76/0.98      inference('simplify', [status(thm)], ['265'])).
% 0.76/0.98  thf('267', plain,
% 0.76/0.98      ((m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_B) @ 
% 0.76/0.98        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.98      inference('clc', [status(thm)], ['29', '30'])).
% 0.76/0.98  thf('268', plain,
% 0.76/0.98      (![X5 : $i, X6 : $i, X7 : $i, X9 : $i]:
% 0.76/0.98         ((v2_struct_0 @ X5)
% 0.76/0.98          | ~ (v4_orders_2 @ X5)
% 0.76/0.98          | ~ (v7_waybel_0 @ X5)
% 0.76/0.98          | ~ (l1_waybel_0 @ X5 @ X6)
% 0.76/0.98          | ((X7) != (k10_yellow_6 @ X6 @ X5))
% 0.76/0.98          | (r2_hidden @ X9 @ X7)
% 0.76/0.98          | ~ (r1_waybel_0 @ X6 @ X5 @ (sk_E_1 @ X9 @ X5 @ X6))
% 0.76/0.98          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X6))
% 0.76/0.98          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.76/0.98          | ~ (l1_pre_topc @ X6)
% 0.76/0.98          | ~ (v2_pre_topc @ X6)
% 0.76/0.98          | (v2_struct_0 @ X6))),
% 0.76/0.98      inference('cnf', [status(esa)], [d18_yellow_6])).
% 0.76/0.98  thf('269', plain,
% 0.76/0.98      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.76/0.98         ((v2_struct_0 @ X6)
% 0.76/0.98          | ~ (v2_pre_topc @ X6)
% 0.76/0.98          | ~ (l1_pre_topc @ X6)
% 0.76/0.98          | ~ (m1_subset_1 @ (k10_yellow_6 @ X6 @ X5) @ 
% 0.76/0.98               (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.76/0.98          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X6))
% 0.76/0.98          | ~ (r1_waybel_0 @ X6 @ X5 @ (sk_E_1 @ X9 @ X5 @ X6))
% 0.76/0.98          | (r2_hidden @ X9 @ (k10_yellow_6 @ X6 @ X5))
% 0.76/0.98          | ~ (l1_waybel_0 @ X5 @ X6)
% 0.76/0.98          | ~ (v7_waybel_0 @ X5)
% 0.76/0.98          | ~ (v4_orders_2 @ X5)
% 0.76/0.98          | (v2_struct_0 @ X5))),
% 0.76/0.98      inference('simplify', [status(thm)], ['268'])).
% 0.76/0.98  thf('270', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_B)
% 0.76/0.98          | ~ (v4_orders_2 @ sk_B)
% 0.76/0.98          | ~ (v7_waybel_0 @ sk_B)
% 0.76/0.98          | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.76/0.98          | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.76/0.98          | ~ (r1_waybel_0 @ sk_A @ sk_B @ (sk_E_1 @ X0 @ sk_B @ sk_A))
% 0.76/0.98          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.76/0.98          | ~ (l1_pre_topc @ sk_A)
% 0.76/0.98          | ~ (v2_pre_topc @ sk_A)
% 0.76/0.98          | (v2_struct_0 @ sk_A))),
% 0.76/0.98      inference('sup-', [status(thm)], ['267', '269'])).
% 0.76/0.98  thf('271', plain, ((v4_orders_2 @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('272', plain, ((v7_waybel_0 @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('273', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('274', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('275', plain, ((v2_pre_topc @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('276', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((v2_struct_0 @ sk_B)
% 0.76/0.98          | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.76/0.98          | ~ (r1_waybel_0 @ sk_A @ sk_B @ (sk_E_1 @ X0 @ sk_B @ sk_A))
% 0.76/0.98          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.76/0.98          | (v2_struct_0 @ sk_A))),
% 0.76/0.98      inference('demod', [status(thm)],
% 0.76/0.98                ['270', '271', '272', '273', '274', '275'])).
% 0.76/0.98  thf('277', plain,
% 0.76/0.98      (((v2_struct_0 @ sk_B)
% 0.76/0.98        | (v2_struct_0 @ sk_A)
% 0.76/0.98        | (r2_hidden @ sk_C @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.76/0.98        | (v2_struct_0 @ sk_A)
% 0.76/0.98        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.76/0.98        | (r2_hidden @ sk_C @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.76/0.98        | (v2_struct_0 @ sk_B))),
% 0.76/0.98      inference('sup-', [status(thm)], ['266', '276'])).
% 0.76/0.98  thf('278', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('279', plain,
% 0.76/0.98      (((v2_struct_0 @ sk_B)
% 0.76/0.98        | (v2_struct_0 @ sk_A)
% 0.76/0.98        | (r2_hidden @ sk_C @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.76/0.98        | (v2_struct_0 @ sk_A)
% 0.76/0.98        | (r2_hidden @ sk_C @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.76/0.98        | (v2_struct_0 @ sk_B))),
% 0.76/0.98      inference('demod', [status(thm)], ['277', '278'])).
% 0.76/0.98  thf('280', plain,
% 0.76/0.98      (((r2_hidden @ sk_C @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.76/0.98        | (v2_struct_0 @ sk_A)
% 0.76/0.98        | (v2_struct_0 @ sk_B))),
% 0.76/0.98      inference('simplify', [status(thm)], ['279'])).
% 0.76/0.98  thf('281', plain, (~ (r2_hidden @ sk_C @ (k10_yellow_6 @ sk_A @ sk_B))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('282', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A))),
% 0.76/0.98      inference('clc', [status(thm)], ['280', '281'])).
% 0.76/0.98  thf('283', plain, (~ (v2_struct_0 @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('284', plain, ((v2_struct_0 @ sk_A)),
% 0.76/0.98      inference('clc', [status(thm)], ['282', '283'])).
% 0.76/0.98  thf('285', plain, ($false), inference('demod', [status(thm)], ['0', '284'])).
% 0.76/0.98  
% 0.76/0.98  % SZS output end Refutation
% 0.76/0.98  
% 0.76/0.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
