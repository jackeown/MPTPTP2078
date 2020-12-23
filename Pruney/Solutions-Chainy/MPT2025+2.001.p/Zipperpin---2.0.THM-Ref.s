%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ehgt8LSCVJ

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 190 expanded)
%              Number of leaves         :   30 (  70 expanded)
%              Depth                    :   19
%              Number of atoms          :  916 (4297 expanded)
%              Number of equality atoms :    5 (  81 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_waybel_0_type,type,(
    u1_waybel_0: $i > $i > $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t24_waybel_9,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( v4_orders_2 @ C )
                & ( v7_waybel_0 @ C )
                & ( l1_waybel_0 @ C @ A ) )
             => ( ( r2_hidden @ B @ ( k10_yellow_6 @ A @ C ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ( ( D
                        = ( k2_relset_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ ( u1_waybel_0 @ A @ C ) ) )
                     => ( r2_hidden @ B @ ( k2_pre_topc @ A @ D ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( v4_orders_2 @ C )
                  & ( v7_waybel_0 @ C )
                  & ( l1_waybel_0 @ C @ A ) )
               => ( ( r2_hidden @ B @ ( k10_yellow_6 @ A @ C ) )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                     => ( ( D
                          = ( k2_relset_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ ( u1_waybel_0 @ A @ C ) ) )
                       => ( r2_hidden @ B @ ( k2_pre_topc @ A @ D ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_waybel_9])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t34_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( m1_connsp_2 @ D @ A @ C )
                   => ~ ( r1_xboole_0 @ D @ B ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( r1_xboole_0 @ ( sk_D @ X3 @ X1 @ X2 ) @ X1 )
      | ( r2_hidden @ X3 @ ( k2_pre_topc @ X2 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t34_connsp_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_D_2 ) )
      | ( r1_xboole_0 @ ( sk_D @ X0 @ sk_D_2 @ sk_A ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_D_2 ) )
      | ( r1_xboole_0 @ ( sk_D @ X0 @ sk_D_2 @ sk_A ) @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ( r1_xboole_0 @ ( sk_D @ sk_B @ sk_D_2 @ sk_A ) @ sk_D_2 )
    | ( r2_hidden @ sk_B @ ( k2_pre_topc @ sk_A @ sk_D_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    ~ ( r2_hidden @ sk_B @ ( k2_pre_topc @ sk_A @ sk_D_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_xboole_0 @ ( sk_D @ sk_B @ sk_D_2 @ sk_A ) @ sk_D_2 ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r1_xboole_0 @ ( sk_D @ sk_B @ sk_D_2 @ sk_A ) @ sk_D_2 ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( m1_connsp_2 @ ( sk_D @ X3 @ X1 @ X2 ) @ X2 @ X3 )
      | ( r2_hidden @ X3 @ ( k2_pre_topc @ X2 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t34_connsp_2])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_D_2 ) )
      | ( m1_connsp_2 @ ( sk_D @ X0 @ sk_D_2 @ sk_A ) @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_D_2 ) )
      | ( m1_connsp_2 @ ( sk_D @ X0 @ sk_D_2 @ sk_A ) @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,
    ( ( m1_connsp_2 @ ( sk_D @ sk_B @ sk_D_2 @ sk_A ) @ sk_A @ sk_B )
    | ( r2_hidden @ sk_B @ ( k2_pre_topc @ sk_A @ sk_D_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,(
    ~ ( r2_hidden @ sk_B @ ( k2_pre_topc @ sk_A @ sk_D_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_connsp_2 @ ( sk_D @ sk_B @ sk_D_2 @ sk_A ) @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_connsp_2 @ ( sk_D @ sk_B @ sk_D_2 @ sk_A ) @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    r2_hidden @ sk_B @ ( k10_yellow_6 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
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

thf('27',plain,(
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
    v7_waybel_0 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v4_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29','30','31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

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

thf('38',plain,(
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

thf('39',plain,(
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
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( v4_orders_2 @ sk_C )
      | ~ ( v7_waybel_0 @ sk_C )
      | ~ ( l1_waybel_0 @ sk_C @ sk_A )
      | ~ ( m1_connsp_2 @ X1 @ sk_A @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_C @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    v4_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v7_waybel_0 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( m1_connsp_2 @ X1 @ sk_A @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_C @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41','42','43','44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_0 @ sk_A @ sk_C @ X0 )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['25','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_C @ X0 )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_waybel_0 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_D_2 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_D_2 @ sk_A ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    r1_waybel_0 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_D_2 @ sk_A ) ),
    inference(clc,[status(thm)],['52','53'])).

thf(t26_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i,D: $i] :
              ~ ( ( r1_waybel_0 @ A @ B @ C )
                & ( r1_waybel_0 @ A @ B @ D )
                & ( r1_xboole_0 @ C @ D ) ) ) ) )).

thf('55',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v7_waybel_0 @ X13 )
      | ~ ( l1_waybel_0 @ X13 @ X14 )
      | ~ ( r1_waybel_0 @ X14 @ X13 @ X15 )
      | ~ ( r1_xboole_0 @ X15 @ X16 )
      | ~ ( r1_waybel_0 @ X14 @ X13 @ X16 )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t26_yellow_6])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( r1_waybel_0 @ sk_A @ sk_C @ X0 )
      | ~ ( r1_xboole_0 @ ( sk_D @ sk_B @ sk_D_2 @ sk_A ) @ X0 )
      | ~ ( l1_waybel_0 @ sk_C @ sk_A )
      | ~ ( v7_waybel_0 @ sk_C )
      | ~ ( v4_orders_2 @ sk_C )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('58',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('59',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v7_waybel_0 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v4_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r1_waybel_0 @ sk_A @ sk_C @ X0 )
      | ~ ( r1_xboole_0 @ ( sk_D @ sk_B @ sk_D_2 @ sk_A ) @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['56','59','60','61','62'])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_C )
    | ~ ( r1_waybel_0 @ sk_A @ sk_C @ sk_D_2 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','63'])).

thf('65',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_waybel_9,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ( r1_waybel_0 @ A @ B @ ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_waybel_0 @ A @ B ) ) ) ) ) )).

thf('66',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( l1_waybel_0 @ X17 @ X18 )
      | ( r1_waybel_0 @ X18 @ X17 @ ( k2_relset_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X18 ) @ ( u1_waybel_0 @ X18 @ X17 ) ) )
      | ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t8_waybel_9])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_C @ ( k2_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('69',plain,
    ( sk_D_2
    = ( k2_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_C @ sk_D_2 )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_waybel_0 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    r1_waybel_0 @ sk_A @ sk_C @ sk_D_2 ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    $false ),
    inference(demod,[status(thm)],['0','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ehgt8LSCVJ
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:12:48 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 80 iterations in 0.059s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.51  thf(u1_waybel_0_type, type, u1_waybel_0: $i > $i > $i).
% 0.21/0.51  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.21/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.21/0.51  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.21/0.51  thf(k10_yellow_6_type, type, k10_yellow_6: $i > $i > $i).
% 0.21/0.51  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.51  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.51  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.51  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.21/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.51  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.21/0.51  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(t24_waybel_9, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( ( ~( v2_struct_0 @ C ) ) & ( v4_orders_2 @ C ) & 
% 0.21/0.51                 ( v7_waybel_0 @ C ) & ( l1_waybel_0 @ C @ A ) ) =>
% 0.21/0.51               ( ( r2_hidden @ B @ ( k10_yellow_6 @ A @ C ) ) =>
% 0.21/0.51                 ( ![D:$i]:
% 0.21/0.51                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51                     ( ( ( D ) =
% 0.21/0.51                         ( k2_relset_1 @
% 0.21/0.52                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ 
% 0.21/0.52                           ( u1_waybel_0 @ A @ C ) ) ) =>
% 0.21/0.52                       ( r2_hidden @ B @ ( k2_pre_topc @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i]:
% 0.21/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.52            ( l1_pre_topc @ A ) ) =>
% 0.21/0.52          ( ![B:$i]:
% 0.21/0.52            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.52              ( ![C:$i]:
% 0.21/0.52                ( ( ( ~( v2_struct_0 @ C ) ) & ( v4_orders_2 @ C ) & 
% 0.21/0.52                    ( v7_waybel_0 @ C ) & ( l1_waybel_0 @ C @ A ) ) =>
% 0.21/0.52                  ( ( r2_hidden @ B @ ( k10_yellow_6 @ A @ C ) ) =>
% 0.21/0.52                    ( ![D:$i]:
% 0.21/0.52                      ( ( m1_subset_1 @
% 0.21/0.52                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52                        ( ( ( D ) =
% 0.21/0.52                            ( k2_relset_1 @
% 0.21/0.52                              ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ 
% 0.21/0.52                              ( u1_waybel_0 @ A @ C ) ) ) =>
% 0.21/0.52                          ( r2_hidden @ B @ ( k2_pre_topc @ A @ D ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t24_waybel_9])).
% 0.21/0.52  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t34_connsp_2, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.52               ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) ) <=>
% 0.21/0.52                 ( ![D:$i]:
% 0.21/0.52                   ( ( m1_connsp_2 @ D @ A @ C ) =>
% 0.21/0.52                     ( ~( r1_xboole_0 @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.21/0.52          | (r1_xboole_0 @ (sk_D @ X3 @ X1 @ X2) @ X1)
% 0.21/0.52          | (r2_hidden @ X3 @ (k2_pre_topc @ X2 @ X1))
% 0.21/0.52          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.21/0.52          | ~ (l1_pre_topc @ X2)
% 0.21/0.52          | ~ (v2_pre_topc @ X2)
% 0.21/0.52          | (v2_struct_0 @ X2))),
% 0.21/0.52      inference('cnf', [status(esa)], [t34_connsp_2])).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.52          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_D_2))
% 0.21/0.52          | (r1_xboole_0 @ (sk_D @ X0 @ sk_D_2 @ sk_A) @ sk_D_2))),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.52  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.52          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_D_2))
% 0.21/0.52          | (r1_xboole_0 @ (sk_D @ X0 @ sk_D_2 @ sk_A) @ sk_D_2))),
% 0.21/0.52      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (((r1_xboole_0 @ (sk_D @ sk_B @ sk_D_2 @ sk_A) @ sk_D_2)
% 0.21/0.52        | (r2_hidden @ sk_B @ (k2_pre_topc @ sk_A @ sk_D_2))
% 0.21/0.52        | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['1', '7'])).
% 0.21/0.52  thf('9', plain, (~ (r2_hidden @ sk_B @ (k2_pre_topc @ sk_A @ sk_D_2))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A)
% 0.21/0.52        | (r1_xboole_0 @ (sk_D @ sk_B @ sk_D_2 @ sk_A) @ sk_D_2))),
% 0.21/0.52      inference('clc', [status(thm)], ['8', '9'])).
% 0.21/0.52  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('12', plain, ((r1_xboole_0 @ (sk_D @ sk_B @ sk_D_2 @ sk_A) @ sk_D_2)),
% 0.21/0.52      inference('clc', [status(thm)], ['10', '11'])).
% 0.21/0.52  thf('13', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.21/0.52          | (m1_connsp_2 @ (sk_D @ X3 @ X1 @ X2) @ X2 @ X3)
% 0.21/0.52          | (r2_hidden @ X3 @ (k2_pre_topc @ X2 @ X1))
% 0.21/0.52          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.21/0.52          | ~ (l1_pre_topc @ X2)
% 0.21/0.52          | ~ (v2_pre_topc @ X2)
% 0.21/0.52          | (v2_struct_0 @ X2))),
% 0.21/0.52      inference('cnf', [status(esa)], [t34_connsp_2])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.52          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_D_2))
% 0.21/0.52          | (m1_connsp_2 @ (sk_D @ X0 @ sk_D_2 @ sk_A) @ sk_A @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.52  thf('17', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.52          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_D_2))
% 0.21/0.52          | (m1_connsp_2 @ (sk_D @ X0 @ sk_D_2 @ sk_A) @ sk_A @ X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (((m1_connsp_2 @ (sk_D @ sk_B @ sk_D_2 @ sk_A) @ sk_A @ sk_B)
% 0.21/0.52        | (r2_hidden @ sk_B @ (k2_pre_topc @ sk_A @ sk_D_2))
% 0.21/0.52        | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['13', '19'])).
% 0.21/0.52  thf('21', plain, (~ (r2_hidden @ sk_B @ (k2_pre_topc @ sk_A @ sk_D_2))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A)
% 0.21/0.52        | (m1_connsp_2 @ (sk_D @ sk_B @ sk_D_2 @ sk_A) @ sk_A @ sk_B))),
% 0.21/0.52      inference('clc', [status(thm)], ['20', '21'])).
% 0.21/0.52  thf('23', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      ((m1_connsp_2 @ (sk_D @ sk_B @ sk_D_2 @ sk_A) @ sk_A @ sk_B)),
% 0.21/0.52      inference('clc', [status(thm)], ['22', '23'])).
% 0.21/0.52  thf('25', plain, ((r2_hidden @ sk_B @ (k10_yellow_6 @ sk_A @ sk_C))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('26', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(dt_k10_yellow_6, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.52         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 0.21/0.52         ( v4_orders_2 @ B ) & ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.52       ( m1_subset_1 @
% 0.21/0.52         ( k10_yellow_6 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      (![X11 : $i, X12 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ X11)
% 0.21/0.52          | ~ (v2_pre_topc @ X11)
% 0.21/0.52          | (v2_struct_0 @ X11)
% 0.21/0.52          | (v2_struct_0 @ X12)
% 0.21/0.52          | ~ (v4_orders_2 @ X12)
% 0.21/0.52          | ~ (v7_waybel_0 @ X12)
% 0.21/0.52          | ~ (l1_waybel_0 @ X12 @ X11)
% 0.21/0.52          | (m1_subset_1 @ (k10_yellow_6 @ X11 @ X12) @ 
% 0.21/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X11))))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k10_yellow_6])).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      (((m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_C) @ 
% 0.21/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52        | ~ (v7_waybel_0 @ sk_C)
% 0.21/0.52        | ~ (v4_orders_2 @ sk_C)
% 0.21/0.52        | (v2_struct_0 @ sk_C)
% 0.21/0.52        | (v2_struct_0 @ sk_A)
% 0.21/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.52  thf('29', plain, ((v7_waybel_0 @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('30', plain, ((v4_orders_2 @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('33', plain,
% 0.21/0.52      (((m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_C) @ 
% 0.21/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52        | (v2_struct_0 @ sk_C)
% 0.21/0.52        | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['28', '29', '30', '31', '32'])).
% 0.21/0.52  thf('34', plain, (~ (v2_struct_0 @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('35', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A)
% 0.21/0.52        | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_C) @ 
% 0.21/0.52           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('clc', [status(thm)], ['33', '34'])).
% 0.21/0.52  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('37', plain,
% 0.21/0.52      ((m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_C) @ 
% 0.21/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('clc', [status(thm)], ['35', '36'])).
% 0.21/0.52  thf(d18_yellow_6, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.52             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52               ( ( ( C ) = ( k10_yellow_6 @ A @ B ) ) <=>
% 0.21/0.52                 ( ![D:$i]:
% 0.21/0.52                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.52                     ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.52                       ( ![E:$i]:
% 0.21/0.52                         ( ( m1_connsp_2 @ E @ A @ D ) =>
% 0.21/0.52                           ( r1_waybel_0 @ A @ B @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('38', plain,
% 0.21/0.52      (![X5 : $i, X6 : $i, X7 : $i, X9 : $i, X10 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X5)
% 0.21/0.52          | ~ (v4_orders_2 @ X5)
% 0.21/0.52          | ~ (v7_waybel_0 @ X5)
% 0.21/0.52          | ~ (l1_waybel_0 @ X5 @ X6)
% 0.21/0.52          | ((X7) != (k10_yellow_6 @ X6 @ X5))
% 0.21/0.52          | ~ (m1_connsp_2 @ X10 @ X6 @ X9)
% 0.21/0.52          | (r1_waybel_0 @ X6 @ X5 @ X10)
% 0.21/0.52          | ~ (r2_hidden @ X9 @ X7)
% 0.21/0.52          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X6))
% 0.21/0.52          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.21/0.52          | ~ (l1_pre_topc @ X6)
% 0.21/0.52          | ~ (v2_pre_topc @ X6)
% 0.21/0.52          | (v2_struct_0 @ X6))),
% 0.21/0.52      inference('cnf', [status(esa)], [d18_yellow_6])).
% 0.21/0.52  thf('39', plain,
% 0.21/0.52      (![X5 : $i, X6 : $i, X9 : $i, X10 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X6)
% 0.21/0.52          | ~ (v2_pre_topc @ X6)
% 0.21/0.52          | ~ (l1_pre_topc @ X6)
% 0.21/0.52          | ~ (m1_subset_1 @ (k10_yellow_6 @ X6 @ X5) @ 
% 0.21/0.52               (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.21/0.52          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X6))
% 0.21/0.52          | ~ (r2_hidden @ X9 @ (k10_yellow_6 @ X6 @ X5))
% 0.21/0.52          | (r1_waybel_0 @ X6 @ X5 @ X10)
% 0.21/0.52          | ~ (m1_connsp_2 @ X10 @ X6 @ X9)
% 0.21/0.52          | ~ (l1_waybel_0 @ X5 @ X6)
% 0.21/0.52          | ~ (v7_waybel_0 @ X5)
% 0.21/0.52          | ~ (v4_orders_2 @ X5)
% 0.21/0.52          | (v2_struct_0 @ X5))),
% 0.21/0.52      inference('simplify', [status(thm)], ['38'])).
% 0.21/0.52  thf('40', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_C)
% 0.21/0.52          | ~ (v4_orders_2 @ sk_C)
% 0.21/0.52          | ~ (v7_waybel_0 @ sk_C)
% 0.21/0.52          | ~ (l1_waybel_0 @ sk_C @ sk_A)
% 0.21/0.52          | ~ (m1_connsp_2 @ X1 @ sk_A @ X0)
% 0.21/0.52          | (r1_waybel_0 @ sk_A @ sk_C @ X1)
% 0.21/0.52          | ~ (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ sk_C))
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.52          | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['37', '39'])).
% 0.21/0.52  thf('41', plain, ((v4_orders_2 @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('42', plain, ((v7_waybel_0 @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('43', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('46', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_C)
% 0.21/0.52          | ~ (m1_connsp_2 @ X1 @ sk_A @ X0)
% 0.21/0.52          | (r1_waybel_0 @ sk_A @ sk_C @ X1)
% 0.21/0.52          | ~ (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ sk_C))
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.52          | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['40', '41', '42', '43', '44', '45'])).
% 0.21/0.52  thf('47', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.52          | (r1_waybel_0 @ sk_A @ sk_C @ X0)
% 0.21/0.52          | ~ (m1_connsp_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.52          | (v2_struct_0 @ sk_C))),
% 0.21/0.52      inference('sup-', [status(thm)], ['25', '46'])).
% 0.21/0.52  thf('48', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('49', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_A)
% 0.21/0.52          | (r1_waybel_0 @ sk_A @ sk_C @ X0)
% 0.21/0.52          | ~ (m1_connsp_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.52          | (v2_struct_0 @ sk_C))),
% 0.21/0.52      inference('demod', [status(thm)], ['47', '48'])).
% 0.21/0.52  thf('50', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_C)
% 0.21/0.52        | (r1_waybel_0 @ sk_A @ sk_C @ (sk_D @ sk_B @ sk_D_2 @ sk_A))
% 0.21/0.52        | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['24', '49'])).
% 0.21/0.52  thf('51', plain, (~ (v2_struct_0 @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('52', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A)
% 0.21/0.52        | (r1_waybel_0 @ sk_A @ sk_C @ (sk_D @ sk_B @ sk_D_2 @ sk_A)))),
% 0.21/0.52      inference('clc', [status(thm)], ['50', '51'])).
% 0.21/0.52  thf('53', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('54', plain,
% 0.21/0.52      ((r1_waybel_0 @ sk_A @ sk_C @ (sk_D @ sk_B @ sk_D_2 @ sk_A))),
% 0.21/0.52      inference('clc', [status(thm)], ['52', '53'])).
% 0.21/0.52  thf(t26_yellow_6, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.52             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.52           ( ![C:$i,D:$i]:
% 0.21/0.52             ( ~( ( r1_waybel_0 @ A @ B @ C ) & ( r1_waybel_0 @ A @ B @ D ) & 
% 0.21/0.52                  ( r1_xboole_0 @ C @ D ) ) ) ) ) ) ))).
% 0.21/0.52  thf('55', plain,
% 0.21/0.52      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X13)
% 0.21/0.52          | ~ (v4_orders_2 @ X13)
% 0.21/0.52          | ~ (v7_waybel_0 @ X13)
% 0.21/0.52          | ~ (l1_waybel_0 @ X13 @ X14)
% 0.21/0.52          | ~ (r1_waybel_0 @ X14 @ X13 @ X15)
% 0.21/0.52          | ~ (r1_xboole_0 @ X15 @ X16)
% 0.21/0.52          | ~ (r1_waybel_0 @ X14 @ X13 @ X16)
% 0.21/0.52          | ~ (l1_struct_0 @ X14)
% 0.21/0.52          | (v2_struct_0 @ X14))),
% 0.21/0.52      inference('cnf', [status(esa)], [t26_yellow_6])).
% 0.21/0.52  thf('56', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.52          | ~ (r1_waybel_0 @ sk_A @ sk_C @ X0)
% 0.21/0.52          | ~ (r1_xboole_0 @ (sk_D @ sk_B @ sk_D_2 @ sk_A) @ X0)
% 0.21/0.52          | ~ (l1_waybel_0 @ sk_C @ sk_A)
% 0.21/0.52          | ~ (v7_waybel_0 @ sk_C)
% 0.21/0.52          | ~ (v4_orders_2 @ sk_C)
% 0.21/0.52          | (v2_struct_0 @ sk_C))),
% 0.21/0.52      inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.52  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(dt_l1_pre_topc, axiom,
% 0.21/0.52    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.52  thf('58', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.52  thf('59', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.52      inference('sup-', [status(thm)], ['57', '58'])).
% 0.21/0.52  thf('60', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('61', plain, ((v7_waybel_0 @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('62', plain, ((v4_orders_2 @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('63', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (r1_waybel_0 @ sk_A @ sk_C @ X0)
% 0.21/0.52          | ~ (r1_xboole_0 @ (sk_D @ sk_B @ sk_D_2 @ sk_A) @ X0)
% 0.21/0.52          | (v2_struct_0 @ sk_C))),
% 0.21/0.52      inference('demod', [status(thm)], ['56', '59', '60', '61', '62'])).
% 0.21/0.52  thf('64', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_C)
% 0.21/0.52        | ~ (r1_waybel_0 @ sk_A @ sk_C @ sk_D_2)
% 0.21/0.52        | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['12', '63'])).
% 0.21/0.52  thf('65', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t8_waybel_9, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.52           ( r1_waybel_0 @
% 0.21/0.52             A @ B @ 
% 0.21/0.52             ( k2_relset_1 @
% 0.21/0.52               ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.21/0.52               ( u1_waybel_0 @ A @ B ) ) ) ) ) ))).
% 0.21/0.52  thf('66', plain,
% 0.21/0.52      (![X17 : $i, X18 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X17)
% 0.21/0.52          | ~ (l1_waybel_0 @ X17 @ X18)
% 0.21/0.52          | (r1_waybel_0 @ X18 @ X17 @ 
% 0.21/0.52             (k2_relset_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X18) @ 
% 0.21/0.52              (u1_waybel_0 @ X18 @ X17)))
% 0.21/0.52          | ~ (l1_struct_0 @ X18)
% 0.21/0.52          | (v2_struct_0 @ X18))),
% 0.21/0.52      inference('cnf', [status(esa)], [t8_waybel_9])).
% 0.21/0.52  thf('67', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A)
% 0.21/0.52        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.52        | (r1_waybel_0 @ sk_A @ sk_C @ 
% 0.21/0.52           (k2_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.52            (u1_waybel_0 @ sk_A @ sk_C)))
% 0.21/0.52        | (v2_struct_0 @ sk_C))),
% 0.21/0.52      inference('sup-', [status(thm)], ['65', '66'])).
% 0.21/0.52  thf('68', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.52      inference('sup-', [status(thm)], ['57', '58'])).
% 0.21/0.52  thf('69', plain,
% 0.21/0.52      (((sk_D_2)
% 0.21/0.52         = (k2_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.52            (u1_waybel_0 @ sk_A @ sk_C)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('70', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A)
% 0.21/0.52        | (r1_waybel_0 @ sk_A @ sk_C @ sk_D_2)
% 0.21/0.52        | (v2_struct_0 @ sk_C))),
% 0.21/0.52      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.21/0.52  thf('71', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('72', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_C) | (r1_waybel_0 @ sk_A @ sk_C @ sk_D_2))),
% 0.21/0.52      inference('clc', [status(thm)], ['70', '71'])).
% 0.21/0.52  thf('73', plain, (~ (v2_struct_0 @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('74', plain, ((r1_waybel_0 @ sk_A @ sk_C @ sk_D_2)),
% 0.21/0.52      inference('clc', [status(thm)], ['72', '73'])).
% 0.21/0.52  thf('75', plain, (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['64', '74'])).
% 0.21/0.52  thf('76', plain, (~ (v2_struct_0 @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('77', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('clc', [status(thm)], ['75', '76'])).
% 0.21/0.52  thf('78', plain, ($false), inference('demod', [status(thm)], ['0', '77'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
