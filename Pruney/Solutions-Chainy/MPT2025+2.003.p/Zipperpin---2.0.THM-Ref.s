%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.R3kMuNu7xB

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:30 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 249 expanded)
%              Number of leaves         :   32 (  86 expanded)
%              Depth                    :   20
%              Number of atoms          : 1295 (5801 expanded)
%              Number of equality atoms :    5 ( 105 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(u1_waybel_0_type,type,(
    u1_waybel_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf(t54_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) )
              <=> ( ~ ( v2_struct_0 @ A )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                     => ~ ( ( v3_pre_topc @ D @ A )
                          & ( r2_hidden @ C @ D )
                          & ( r1_xboole_0 @ B @ D ) ) ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( v2_struct_0 @ X5 )
      | ( r2_hidden @ X6 @ ( sk_D @ X6 @ X4 @ X5 ) )
      | ( r2_hidden @ X6 @ ( k2_pre_topc @ X5 @ X4 ) )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[t54_pre_topc])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_D_2 ) )
      | ( r2_hidden @ X0 @ ( sk_D @ X0 @ sk_D_2 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_D_2 ) )
      | ( r2_hidden @ X0 @ ( sk_D @ X0 @ sk_D_2 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ ( sk_D @ sk_B @ sk_D_2 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k2_pre_topc @ sk_A @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r2_hidden @ sk_B @ ( k2_pre_topc @ sk_A @ sk_D_2 ) )
    | ( r2_hidden @ sk_B @ ( sk_D @ sk_B @ sk_D_2 @ sk_A ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( r2_hidden @ sk_B @ ( k2_pre_topc @ sk_A @ sk_D_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r2_hidden @ sk_B @ ( sk_D @ sk_B @ sk_D_2 @ sk_A ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( v2_struct_0 @ X5 )
      | ( m1_subset_1 @ ( sk_D @ X6 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( r2_hidden @ X6 @ ( k2_pre_topc @ X5 @ X4 ) )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[t54_pre_topc])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_D_2 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_D_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_D_2 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_D_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ sk_B @ sk_D_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k2_pre_topc @ sk_A @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( r2_hidden @ sk_B @ ( k2_pre_topc @ sk_A @ sk_D_2 ) )
    | ( m1_subset_1 @ ( sk_D @ sk_B @ sk_D_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    ~ ( r2_hidden @ sk_B @ ( k2_pre_topc @ sk_A @ sk_D_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ ( sk_D @ sk_B @ sk_D_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf(t5_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r2_hidden @ C @ B ) )
               => ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) )).

thf('23',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v3_pre_topc @ X8 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( m1_connsp_2 @ X8 @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t5_connsp_2])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ ( sk_D @ sk_B @ sk_D_2 @ sk_A ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( sk_D @ sk_B @ sk_D_2 @ sk_A ) )
      | ~ ( v3_pre_topc @ ( sk_D @ sk_B @ sk_D_2 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ ( sk_D @ sk_B @ sk_D_2 @ sk_A ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( sk_D @ sk_B @ sk_D_2 @ sk_A ) )
      | ~ ( v3_pre_topc @ ( sk_D @ sk_B @ sk_D_2 @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( v2_struct_0 @ X5 )
      | ( v3_pre_topc @ ( sk_D @ X6 @ X4 @ X5 ) @ X5 )
      | ( r2_hidden @ X6 @ ( k2_pre_topc @ X5 @ X4 ) )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[t54_pre_topc])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_D_2 ) )
      | ( v3_pre_topc @ ( sk_D @ X0 @ sk_D_2 @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_D_2 ) )
      | ( v3_pre_topc @ ( sk_D @ X0 @ sk_D_2 @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ ( sk_D @ sk_B @ sk_D_2 @ sk_A ) @ sk_A )
    | ( r2_hidden @ sk_B @ ( k2_pre_topc @ sk_A @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( r2_hidden @ sk_B @ ( k2_pre_topc @ sk_A @ sk_D_2 ) )
    | ( v3_pre_topc @ ( sk_D @ sk_B @ sk_D_2 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( r2_hidden @ sk_B @ ( k2_pre_topc @ sk_A @ sk_D_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v3_pre_topc @ ( sk_D @ sk_B @ sk_D_2 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ ( sk_D @ sk_B @ sk_D_2 @ sk_A ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( sk_D @ sk_B @ sk_D_2 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['27','38'])).

thf('40',plain,
    ( ( m1_connsp_2 @ ( sk_D @ sk_B @ sk_D_2 @ sk_A ) @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( m1_connsp_2 @ ( sk_D @ sk_B @ sk_D_2 @ sk_A ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_connsp_2 @ ( sk_D @ sk_B @ sk_D_2 @ sk_A ) @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    r2_hidden @ sk_B @ ( k10_yellow_6 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
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

thf('47',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 )
      | ( v2_struct_0 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v7_waybel_0 @ X18 )
      | ~ ( l1_waybel_0 @ X18 @ X17 )
      | ( m1_subset_1 @ ( k10_yellow_6 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_yellow_6])).

thf('48',plain,
    ( ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v7_waybel_0 @ sk_C )
    | ~ ( v4_orders_2 @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v7_waybel_0 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v4_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','49','50','51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_subset_1 @ ( k10_yellow_6 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['55','56'])).

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

thf('58',plain,(
    ! [X11: $i,X12: $i,X13: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v7_waybel_0 @ X11 )
      | ~ ( l1_waybel_0 @ X11 @ X12 )
      | ( X13
       != ( k10_yellow_6 @ X12 @ X11 ) )
      | ~ ( m1_connsp_2 @ X16 @ X12 @ X15 )
      | ( r1_waybel_0 @ X12 @ X11 @ X16 )
      | ~ ( r2_hidden @ X15 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d18_yellow_6])).

thf('59',plain,(
    ! [X11: $i,X12: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ ( k10_yellow_6 @ X12 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X12 ) )
      | ~ ( r2_hidden @ X15 @ ( k10_yellow_6 @ X12 @ X11 ) )
      | ( r1_waybel_0 @ X12 @ X11 @ X16 )
      | ~ ( m1_connsp_2 @ X16 @ X12 @ X15 )
      | ~ ( l1_waybel_0 @ X11 @ X12 )
      | ~ ( v7_waybel_0 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
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
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,(
    v4_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v7_waybel_0 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( m1_connsp_2 @ X1 @ sk_A @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_C @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','61','62','63','64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_0 @ sk_A @ sk_C @ X0 )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['45','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_C @ X0 )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_waybel_0 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_D_2 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_D_2 @ sk_A ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    r1_waybel_0 @ sk_A @ sk_C @ ( sk_D @ sk_B @ sk_D_2 @ sk_A ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
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

thf('76',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( l1_waybel_0 @ X23 @ X24 )
      | ( r1_waybel_0 @ X24 @ X23 @ ( k2_relset_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X24 ) @ ( u1_waybel_0 @ X24 @ X23 ) ) )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t8_waybel_9])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_C @ ( k2_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('79',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('80',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( sk_D_2
    = ( k2_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_C @ sk_D_2 )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['77','80','81'])).

thf('83',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_waybel_0 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    r1_waybel_0 @ sk_A @ sk_C @ sk_D_2 ),
    inference(clc,[status(thm)],['84','85'])).

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

thf('87',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v7_waybel_0 @ X19 )
      | ~ ( l1_waybel_0 @ X19 @ X20 )
      | ~ ( r1_waybel_0 @ X20 @ X19 @ X21 )
      | ~ ( r1_xboole_0 @ X21 @ X22 )
      | ~ ( r1_waybel_0 @ X20 @ X19 @ X22 )
      | ~ ( l1_struct_0 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t26_yellow_6])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( r1_waybel_0 @ sk_A @ sk_C @ X0 )
      | ~ ( r1_xboole_0 @ sk_D_2 @ X0 )
      | ~ ( l1_waybel_0 @ sk_C @ sk_A )
      | ~ ( v7_waybel_0 @ sk_C )
      | ~ ( v4_orders_2 @ sk_C )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['78','79'])).

thf('90',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v7_waybel_0 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v4_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r1_waybel_0 @ sk_A @ sk_C @ X0 )
      | ~ ( r1_xboole_0 @ sk_D_2 @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['88','89','90','91','92'])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_C )
    | ~ ( r1_xboole_0 @ sk_D_2 @ ( sk_D @ sk_B @ sk_D_2 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['74','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( v2_struct_0 @ X5 )
      | ( r1_xboole_0 @ X4 @ ( sk_D @ X6 @ X4 @ X5 ) )
      | ( r2_hidden @ X6 @ ( k2_pre_topc @ X5 @ X4 ) )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[t54_pre_topc])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_D_2 ) )
      | ( r1_xboole_0 @ sk_D_2 @ ( sk_D @ X0 @ sk_D_2 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_D_2 ) )
      | ( r1_xboole_0 @ sk_D_2 @ ( sk_D @ X0 @ sk_D_2 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_xboole_0 @ sk_D_2 @ ( sk_D @ sk_B @ sk_D_2 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k2_pre_topc @ sk_A @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['95','100'])).

thf('102',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( r2_hidden @ sk_B @ ( k2_pre_topc @ sk_A @ sk_D_2 ) )
    | ( r1_xboole_0 @ sk_D_2 @ ( sk_D @ sk_B @ sk_D_2 @ sk_A ) ) ),
    inference(clc,[status(thm)],['101','102'])).

thf('104',plain,(
    ~ ( r2_hidden @ sk_B @ ( k2_pre_topc @ sk_A @ sk_D_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    r1_xboole_0 @ sk_D_2 @ ( sk_D @ sk_B @ sk_D_2 @ sk_A ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['94','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    $false ),
    inference(demod,[status(thm)],['0','108'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.R3kMuNu7xB
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:51:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.47/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.66  % Solved by: fo/fo7.sh
% 0.47/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.66  % done 186 iterations in 0.199s
% 0.47/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.66  % SZS output start Refutation
% 0.47/0.66  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.47/0.66  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.47/0.66  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.47/0.66  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.47/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.66  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.66  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.47/0.66  thf(u1_waybel_0_type, type, u1_waybel_0: $i > $i > $i).
% 0.47/0.66  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.47/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.66  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.47/0.66  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.47/0.66  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.47/0.66  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.47/0.66  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.47/0.66  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.47/0.66  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.47/0.66  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.47/0.66  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.47/0.66  thf(k10_yellow_6_type, type, k10_yellow_6: $i > $i > $i).
% 0.47/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.66  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.47/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.66  thf(t24_waybel_9, conjecture,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.66       ( ![B:$i]:
% 0.47/0.66         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.66           ( ![C:$i]:
% 0.47/0.66             ( ( ( ~( v2_struct_0 @ C ) ) & ( v4_orders_2 @ C ) & 
% 0.47/0.66                 ( v7_waybel_0 @ C ) & ( l1_waybel_0 @ C @ A ) ) =>
% 0.47/0.66               ( ( r2_hidden @ B @ ( k10_yellow_6 @ A @ C ) ) =>
% 0.47/0.66                 ( ![D:$i]:
% 0.47/0.66                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.66                     ( ( ( D ) =
% 0.47/0.66                         ( k2_relset_1 @
% 0.47/0.66                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ 
% 0.47/0.66                           ( u1_waybel_0 @ A @ C ) ) ) =>
% 0.47/0.66                       ( r2_hidden @ B @ ( k2_pre_topc @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.47/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.66    (~( ![A:$i]:
% 0.47/0.66        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.47/0.66            ( l1_pre_topc @ A ) ) =>
% 0.47/0.66          ( ![B:$i]:
% 0.47/0.66            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.66              ( ![C:$i]:
% 0.47/0.66                ( ( ( ~( v2_struct_0 @ C ) ) & ( v4_orders_2 @ C ) & 
% 0.47/0.66                    ( v7_waybel_0 @ C ) & ( l1_waybel_0 @ C @ A ) ) =>
% 0.47/0.66                  ( ( r2_hidden @ B @ ( k10_yellow_6 @ A @ C ) ) =>
% 0.47/0.66                    ( ![D:$i]:
% 0.47/0.66                      ( ( m1_subset_1 @
% 0.47/0.66                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.66                        ( ( ( D ) =
% 0.47/0.66                            ( k2_relset_1 @
% 0.47/0.66                              ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ 
% 0.47/0.66                              ( u1_waybel_0 @ A @ C ) ) ) =>
% 0.47/0.66                          ( r2_hidden @ B @ ( k2_pre_topc @ A @ D ) ) ) ) ) ) ) ) ) ) ) )),
% 0.47/0.66    inference('cnf.neg', [status(esa)], [t24_waybel_9])).
% 0.47/0.66  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('2', plain,
% 0.47/0.66      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(t54_pre_topc, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( l1_pre_topc @ A ) =>
% 0.47/0.66       ( ![B:$i]:
% 0.47/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.66           ( ![C:$i]:
% 0.47/0.66             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.66               ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) ) <=>
% 0.47/0.66                 ( ( ~( v2_struct_0 @ A ) ) & 
% 0.47/0.66                   ( ![D:$i]:
% 0.47/0.66                     ( ( m1_subset_1 @
% 0.47/0.66                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.66                       ( ~( ( v3_pre_topc @ D @ A ) & ( r2_hidden @ C @ D ) & 
% 0.47/0.66                            ( r1_xboole_0 @ B @ D ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.47/0.66  thf('3', plain,
% 0.47/0.66      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.47/0.66          | (v2_struct_0 @ X5)
% 0.47/0.66          | (r2_hidden @ X6 @ (sk_D @ X6 @ X4 @ X5))
% 0.47/0.66          | (r2_hidden @ X6 @ (k2_pre_topc @ X5 @ X4))
% 0.47/0.66          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.47/0.66          | ~ (l1_pre_topc @ X5))),
% 0.47/0.66      inference('cnf', [status(esa)], [t54_pre_topc])).
% 0.47/0.66  thf('4', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (l1_pre_topc @ sk_A)
% 0.47/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_D_2))
% 0.47/0.66          | (r2_hidden @ X0 @ (sk_D @ X0 @ sk_D_2 @ sk_A))
% 0.47/0.66          | (v2_struct_0 @ sk_A))),
% 0.47/0.66      inference('sup-', [status(thm)], ['2', '3'])).
% 0.47/0.66  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('6', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_D_2))
% 0.47/0.66          | (r2_hidden @ X0 @ (sk_D @ X0 @ sk_D_2 @ sk_A))
% 0.47/0.66          | (v2_struct_0 @ sk_A))),
% 0.47/0.66      inference('demod', [status(thm)], ['4', '5'])).
% 0.47/0.66  thf('7', plain,
% 0.47/0.66      (((v2_struct_0 @ sk_A)
% 0.47/0.66        | (r2_hidden @ sk_B @ (sk_D @ sk_B @ sk_D_2 @ sk_A))
% 0.47/0.66        | (r2_hidden @ sk_B @ (k2_pre_topc @ sk_A @ sk_D_2)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['1', '6'])).
% 0.47/0.66  thf('8', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('9', plain,
% 0.47/0.66      (((r2_hidden @ sk_B @ (k2_pre_topc @ sk_A @ sk_D_2))
% 0.47/0.66        | (r2_hidden @ sk_B @ (sk_D @ sk_B @ sk_D_2 @ sk_A)))),
% 0.47/0.66      inference('clc', [status(thm)], ['7', '8'])).
% 0.47/0.66  thf('10', plain, (~ (r2_hidden @ sk_B @ (k2_pre_topc @ sk_A @ sk_D_2))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('11', plain, ((r2_hidden @ sk_B @ (sk_D @ sk_B @ sk_D_2 @ sk_A))),
% 0.47/0.66      inference('clc', [status(thm)], ['9', '10'])).
% 0.47/0.66  thf('12', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('13', plain,
% 0.47/0.66      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('14', plain,
% 0.47/0.66      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.47/0.66          | (v2_struct_0 @ X5)
% 0.47/0.66          | (m1_subset_1 @ (sk_D @ X6 @ X4 @ X5) @ 
% 0.47/0.66             (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.47/0.66          | (r2_hidden @ X6 @ (k2_pre_topc @ X5 @ X4))
% 0.47/0.66          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.47/0.66          | ~ (l1_pre_topc @ X5))),
% 0.47/0.66      inference('cnf', [status(esa)], [t54_pre_topc])).
% 0.47/0.66  thf('15', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (l1_pre_topc @ sk_A)
% 0.47/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_D_2))
% 0.47/0.66          | (m1_subset_1 @ (sk_D @ X0 @ sk_D_2 @ sk_A) @ 
% 0.47/0.66             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.47/0.66          | (v2_struct_0 @ sk_A))),
% 0.47/0.66      inference('sup-', [status(thm)], ['13', '14'])).
% 0.47/0.66  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('17', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_D_2))
% 0.47/0.66          | (m1_subset_1 @ (sk_D @ X0 @ sk_D_2 @ sk_A) @ 
% 0.47/0.66             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.47/0.66          | (v2_struct_0 @ sk_A))),
% 0.47/0.66      inference('demod', [status(thm)], ['15', '16'])).
% 0.47/0.66  thf('18', plain,
% 0.47/0.66      (((v2_struct_0 @ sk_A)
% 0.47/0.66        | (m1_subset_1 @ (sk_D @ sk_B @ sk_D_2 @ sk_A) @ 
% 0.47/0.66           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.47/0.66        | (r2_hidden @ sk_B @ (k2_pre_topc @ sk_A @ sk_D_2)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['12', '17'])).
% 0.47/0.66  thf('19', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('20', plain,
% 0.47/0.66      (((r2_hidden @ sk_B @ (k2_pre_topc @ sk_A @ sk_D_2))
% 0.47/0.66        | (m1_subset_1 @ (sk_D @ sk_B @ sk_D_2 @ sk_A) @ 
% 0.47/0.66           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.66      inference('clc', [status(thm)], ['18', '19'])).
% 0.47/0.66  thf('21', plain, (~ (r2_hidden @ sk_B @ (k2_pre_topc @ sk_A @ sk_D_2))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('22', plain,
% 0.47/0.66      ((m1_subset_1 @ (sk_D @ sk_B @ sk_D_2 @ sk_A) @ 
% 0.47/0.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('clc', [status(thm)], ['20', '21'])).
% 0.47/0.66  thf(t5_connsp_2, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.66       ( ![B:$i]:
% 0.47/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.66           ( ![C:$i]:
% 0.47/0.66             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.66               ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 0.47/0.66                 ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ))).
% 0.47/0.66  thf('23', plain,
% 0.47/0.66      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.47/0.66          | ~ (v3_pre_topc @ X8 @ X9)
% 0.47/0.66          | ~ (r2_hidden @ X10 @ X8)
% 0.47/0.66          | (m1_connsp_2 @ X8 @ X9 @ X10)
% 0.47/0.66          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.47/0.66          | ~ (l1_pre_topc @ X9)
% 0.47/0.66          | ~ (v2_pre_topc @ X9)
% 0.47/0.66          | (v2_struct_0 @ X9))),
% 0.47/0.66      inference('cnf', [status(esa)], [t5_connsp_2])).
% 0.47/0.66  thf('24', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((v2_struct_0 @ sk_A)
% 0.47/0.66          | ~ (v2_pre_topc @ sk_A)
% 0.47/0.66          | ~ (l1_pre_topc @ sk_A)
% 0.47/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | (m1_connsp_2 @ (sk_D @ sk_B @ sk_D_2 @ sk_A) @ sk_A @ X0)
% 0.47/0.66          | ~ (r2_hidden @ X0 @ (sk_D @ sk_B @ sk_D_2 @ sk_A))
% 0.47/0.66          | ~ (v3_pre_topc @ (sk_D @ sk_B @ sk_D_2 @ sk_A) @ sk_A))),
% 0.47/0.66      inference('sup-', [status(thm)], ['22', '23'])).
% 0.47/0.66  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('27', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((v2_struct_0 @ sk_A)
% 0.47/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | (m1_connsp_2 @ (sk_D @ sk_B @ sk_D_2 @ sk_A) @ sk_A @ X0)
% 0.47/0.66          | ~ (r2_hidden @ X0 @ (sk_D @ sk_B @ sk_D_2 @ sk_A))
% 0.47/0.66          | ~ (v3_pre_topc @ (sk_D @ sk_B @ sk_D_2 @ sk_A) @ sk_A))),
% 0.47/0.66      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.47/0.66  thf('28', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('29', plain,
% 0.47/0.66      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('30', plain,
% 0.47/0.66      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.47/0.66          | (v2_struct_0 @ X5)
% 0.47/0.66          | (v3_pre_topc @ (sk_D @ X6 @ X4 @ X5) @ X5)
% 0.47/0.66          | (r2_hidden @ X6 @ (k2_pre_topc @ X5 @ X4))
% 0.47/0.66          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.47/0.66          | ~ (l1_pre_topc @ X5))),
% 0.47/0.66      inference('cnf', [status(esa)], [t54_pre_topc])).
% 0.47/0.66  thf('31', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (l1_pre_topc @ sk_A)
% 0.47/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_D_2))
% 0.47/0.66          | (v3_pre_topc @ (sk_D @ X0 @ sk_D_2 @ sk_A) @ sk_A)
% 0.47/0.66          | (v2_struct_0 @ sk_A))),
% 0.47/0.66      inference('sup-', [status(thm)], ['29', '30'])).
% 0.47/0.66  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('33', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_D_2))
% 0.47/0.66          | (v3_pre_topc @ (sk_D @ X0 @ sk_D_2 @ sk_A) @ sk_A)
% 0.47/0.66          | (v2_struct_0 @ sk_A))),
% 0.47/0.66      inference('demod', [status(thm)], ['31', '32'])).
% 0.47/0.66  thf('34', plain,
% 0.47/0.66      (((v2_struct_0 @ sk_A)
% 0.47/0.66        | (v3_pre_topc @ (sk_D @ sk_B @ sk_D_2 @ sk_A) @ sk_A)
% 0.47/0.66        | (r2_hidden @ sk_B @ (k2_pre_topc @ sk_A @ sk_D_2)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['28', '33'])).
% 0.47/0.66  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('36', plain,
% 0.47/0.66      (((r2_hidden @ sk_B @ (k2_pre_topc @ sk_A @ sk_D_2))
% 0.47/0.66        | (v3_pre_topc @ (sk_D @ sk_B @ sk_D_2 @ sk_A) @ sk_A))),
% 0.47/0.66      inference('clc', [status(thm)], ['34', '35'])).
% 0.47/0.66  thf('37', plain, (~ (r2_hidden @ sk_B @ (k2_pre_topc @ sk_A @ sk_D_2))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('38', plain, ((v3_pre_topc @ (sk_D @ sk_B @ sk_D_2 @ sk_A) @ sk_A)),
% 0.47/0.66      inference('clc', [status(thm)], ['36', '37'])).
% 0.47/0.66  thf('39', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((v2_struct_0 @ sk_A)
% 0.47/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | (m1_connsp_2 @ (sk_D @ sk_B @ sk_D_2 @ sk_A) @ sk_A @ X0)
% 0.47/0.66          | ~ (r2_hidden @ X0 @ (sk_D @ sk_B @ sk_D_2 @ sk_A)))),
% 0.47/0.66      inference('demod', [status(thm)], ['27', '38'])).
% 0.47/0.66  thf('40', plain,
% 0.47/0.66      (((m1_connsp_2 @ (sk_D @ sk_B @ sk_D_2 @ sk_A) @ sk_A @ sk_B)
% 0.47/0.66        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.47/0.66        | (v2_struct_0 @ sk_A))),
% 0.47/0.66      inference('sup-', [status(thm)], ['11', '39'])).
% 0.47/0.66  thf('41', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('42', plain,
% 0.47/0.66      (((m1_connsp_2 @ (sk_D @ sk_B @ sk_D_2 @ sk_A) @ sk_A @ sk_B)
% 0.47/0.66        | (v2_struct_0 @ sk_A))),
% 0.47/0.66      inference('demod', [status(thm)], ['40', '41'])).
% 0.47/0.66  thf('43', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('44', plain,
% 0.47/0.66      ((m1_connsp_2 @ (sk_D @ sk_B @ sk_D_2 @ sk_A) @ sk_A @ sk_B)),
% 0.47/0.66      inference('clc', [status(thm)], ['42', '43'])).
% 0.47/0.66  thf('45', plain, ((r2_hidden @ sk_B @ (k10_yellow_6 @ sk_A @ sk_C))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('46', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(dt_k10_yellow_6, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.47/0.66         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 0.47/0.66         ( v4_orders_2 @ B ) & ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.47/0.66       ( m1_subset_1 @
% 0.47/0.66         ( k10_yellow_6 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.47/0.66  thf('47', plain,
% 0.47/0.66      (![X17 : $i, X18 : $i]:
% 0.47/0.66         (~ (l1_pre_topc @ X17)
% 0.47/0.66          | ~ (v2_pre_topc @ X17)
% 0.47/0.66          | (v2_struct_0 @ X17)
% 0.47/0.66          | (v2_struct_0 @ X18)
% 0.47/0.66          | ~ (v4_orders_2 @ X18)
% 0.47/0.66          | ~ (v7_waybel_0 @ X18)
% 0.47/0.66          | ~ (l1_waybel_0 @ X18 @ X17)
% 0.47/0.66          | (m1_subset_1 @ (k10_yellow_6 @ X17 @ X18) @ 
% 0.47/0.66             (k1_zfmisc_1 @ (u1_struct_0 @ X17))))),
% 0.47/0.66      inference('cnf', [status(esa)], [dt_k10_yellow_6])).
% 0.47/0.66  thf('48', plain,
% 0.47/0.66      (((m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_C) @ 
% 0.47/0.66         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.47/0.66        | ~ (v7_waybel_0 @ sk_C)
% 0.47/0.66        | ~ (v4_orders_2 @ sk_C)
% 0.47/0.66        | (v2_struct_0 @ sk_C)
% 0.47/0.66        | (v2_struct_0 @ sk_A)
% 0.47/0.66        | ~ (v2_pre_topc @ sk_A)
% 0.47/0.66        | ~ (l1_pre_topc @ sk_A))),
% 0.47/0.66      inference('sup-', [status(thm)], ['46', '47'])).
% 0.47/0.66  thf('49', plain, ((v7_waybel_0 @ sk_C)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('50', plain, ((v4_orders_2 @ sk_C)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('51', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('53', plain,
% 0.47/0.66      (((m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_C) @ 
% 0.47/0.66         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.47/0.66        | (v2_struct_0 @ sk_C)
% 0.47/0.66        | (v2_struct_0 @ sk_A))),
% 0.47/0.66      inference('demod', [status(thm)], ['48', '49', '50', '51', '52'])).
% 0.47/0.66  thf('54', plain, (~ (v2_struct_0 @ sk_C)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('55', plain,
% 0.47/0.66      (((v2_struct_0 @ sk_A)
% 0.47/0.66        | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_C) @ 
% 0.47/0.66           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.66      inference('clc', [status(thm)], ['53', '54'])).
% 0.47/0.66  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('57', plain,
% 0.47/0.66      ((m1_subset_1 @ (k10_yellow_6 @ sk_A @ sk_C) @ 
% 0.47/0.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('clc', [status(thm)], ['55', '56'])).
% 0.47/0.66  thf(d18_yellow_6, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.66       ( ![B:$i]:
% 0.47/0.66         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.47/0.66             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.47/0.66           ( ![C:$i]:
% 0.47/0.66             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.66               ( ( ( C ) = ( k10_yellow_6 @ A @ B ) ) <=>
% 0.47/0.66                 ( ![D:$i]:
% 0.47/0.66                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.66                     ( ( r2_hidden @ D @ C ) <=>
% 0.47/0.66                       ( ![E:$i]:
% 0.47/0.66                         ( ( m1_connsp_2 @ E @ A @ D ) =>
% 0.47/0.66                           ( r1_waybel_0 @ A @ B @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.47/0.66  thf('58', plain,
% 0.47/0.66      (![X11 : $i, X12 : $i, X13 : $i, X15 : $i, X16 : $i]:
% 0.47/0.66         ((v2_struct_0 @ X11)
% 0.47/0.66          | ~ (v4_orders_2 @ X11)
% 0.47/0.66          | ~ (v7_waybel_0 @ X11)
% 0.47/0.66          | ~ (l1_waybel_0 @ X11 @ X12)
% 0.47/0.66          | ((X13) != (k10_yellow_6 @ X12 @ X11))
% 0.47/0.66          | ~ (m1_connsp_2 @ X16 @ X12 @ X15)
% 0.47/0.66          | (r1_waybel_0 @ X12 @ X11 @ X16)
% 0.47/0.66          | ~ (r2_hidden @ X15 @ X13)
% 0.47/0.66          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X12))
% 0.47/0.66          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.47/0.66          | ~ (l1_pre_topc @ X12)
% 0.47/0.66          | ~ (v2_pre_topc @ X12)
% 0.47/0.66          | (v2_struct_0 @ X12))),
% 0.47/0.66      inference('cnf', [status(esa)], [d18_yellow_6])).
% 0.47/0.66  thf('59', plain,
% 0.47/0.66      (![X11 : $i, X12 : $i, X15 : $i, X16 : $i]:
% 0.47/0.66         ((v2_struct_0 @ X12)
% 0.47/0.66          | ~ (v2_pre_topc @ X12)
% 0.47/0.66          | ~ (l1_pre_topc @ X12)
% 0.47/0.66          | ~ (m1_subset_1 @ (k10_yellow_6 @ X12 @ X11) @ 
% 0.47/0.66               (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.47/0.66          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X12))
% 0.47/0.66          | ~ (r2_hidden @ X15 @ (k10_yellow_6 @ X12 @ X11))
% 0.47/0.66          | (r1_waybel_0 @ X12 @ X11 @ X16)
% 0.47/0.66          | ~ (m1_connsp_2 @ X16 @ X12 @ X15)
% 0.47/0.66          | ~ (l1_waybel_0 @ X11 @ X12)
% 0.47/0.66          | ~ (v7_waybel_0 @ X11)
% 0.47/0.66          | ~ (v4_orders_2 @ X11)
% 0.47/0.66          | (v2_struct_0 @ X11))),
% 0.47/0.66      inference('simplify', [status(thm)], ['58'])).
% 0.47/0.66  thf('60', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((v2_struct_0 @ sk_C)
% 0.47/0.66          | ~ (v4_orders_2 @ sk_C)
% 0.47/0.66          | ~ (v7_waybel_0 @ sk_C)
% 0.47/0.66          | ~ (l1_waybel_0 @ sk_C @ sk_A)
% 0.47/0.66          | ~ (m1_connsp_2 @ X1 @ sk_A @ X0)
% 0.47/0.66          | (r1_waybel_0 @ sk_A @ sk_C @ X1)
% 0.47/0.66          | ~ (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ sk_C))
% 0.47/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | ~ (l1_pre_topc @ sk_A)
% 0.47/0.66          | ~ (v2_pre_topc @ sk_A)
% 0.47/0.66          | (v2_struct_0 @ sk_A))),
% 0.47/0.66      inference('sup-', [status(thm)], ['57', '59'])).
% 0.47/0.66  thf('61', plain, ((v4_orders_2 @ sk_C)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('62', plain, ((v7_waybel_0 @ sk_C)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('63', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('65', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('66', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((v2_struct_0 @ sk_C)
% 0.47/0.66          | ~ (m1_connsp_2 @ X1 @ sk_A @ X0)
% 0.47/0.66          | (r1_waybel_0 @ sk_A @ sk_C @ X1)
% 0.47/0.66          | ~ (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ sk_C))
% 0.47/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | (v2_struct_0 @ sk_A))),
% 0.47/0.66      inference('demod', [status(thm)], ['60', '61', '62', '63', '64', '65'])).
% 0.47/0.66  thf('67', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((v2_struct_0 @ sk_A)
% 0.47/0.66          | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | (r1_waybel_0 @ sk_A @ sk_C @ X0)
% 0.47/0.66          | ~ (m1_connsp_2 @ X0 @ sk_A @ sk_B)
% 0.47/0.66          | (v2_struct_0 @ sk_C))),
% 0.47/0.66      inference('sup-', [status(thm)], ['45', '66'])).
% 0.47/0.66  thf('68', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('69', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((v2_struct_0 @ sk_A)
% 0.47/0.66          | (r1_waybel_0 @ sk_A @ sk_C @ X0)
% 0.47/0.66          | ~ (m1_connsp_2 @ X0 @ sk_A @ sk_B)
% 0.47/0.66          | (v2_struct_0 @ sk_C))),
% 0.47/0.66      inference('demod', [status(thm)], ['67', '68'])).
% 0.47/0.66  thf('70', plain,
% 0.47/0.66      (((v2_struct_0 @ sk_C)
% 0.47/0.66        | (r1_waybel_0 @ sk_A @ sk_C @ (sk_D @ sk_B @ sk_D_2 @ sk_A))
% 0.47/0.66        | (v2_struct_0 @ sk_A))),
% 0.47/0.66      inference('sup-', [status(thm)], ['44', '69'])).
% 0.47/0.66  thf('71', plain, (~ (v2_struct_0 @ sk_C)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('72', plain,
% 0.47/0.66      (((v2_struct_0 @ sk_A)
% 0.47/0.66        | (r1_waybel_0 @ sk_A @ sk_C @ (sk_D @ sk_B @ sk_D_2 @ sk_A)))),
% 0.47/0.66      inference('clc', [status(thm)], ['70', '71'])).
% 0.47/0.66  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('74', plain,
% 0.47/0.66      ((r1_waybel_0 @ sk_A @ sk_C @ (sk_D @ sk_B @ sk_D_2 @ sk_A))),
% 0.47/0.66      inference('clc', [status(thm)], ['72', '73'])).
% 0.47/0.66  thf('75', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(t8_waybel_9, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.47/0.66       ( ![B:$i]:
% 0.47/0.66         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.47/0.66           ( r1_waybel_0 @
% 0.47/0.66             A @ B @ 
% 0.47/0.66             ( k2_relset_1 @
% 0.47/0.66               ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.47/0.66               ( u1_waybel_0 @ A @ B ) ) ) ) ) ))).
% 0.47/0.66  thf('76', plain,
% 0.47/0.66      (![X23 : $i, X24 : $i]:
% 0.47/0.66         ((v2_struct_0 @ X23)
% 0.47/0.66          | ~ (l1_waybel_0 @ X23 @ X24)
% 0.47/0.66          | (r1_waybel_0 @ X24 @ X23 @ 
% 0.47/0.66             (k2_relset_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X24) @ 
% 0.47/0.66              (u1_waybel_0 @ X24 @ X23)))
% 0.47/0.66          | ~ (l1_struct_0 @ X24)
% 0.47/0.66          | (v2_struct_0 @ X24))),
% 0.47/0.66      inference('cnf', [status(esa)], [t8_waybel_9])).
% 0.47/0.66  thf('77', plain,
% 0.47/0.66      (((v2_struct_0 @ sk_A)
% 0.47/0.66        | ~ (l1_struct_0 @ sk_A)
% 0.47/0.66        | (r1_waybel_0 @ sk_A @ sk_C @ 
% 0.47/0.66           (k2_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.66            (u1_waybel_0 @ sk_A @ sk_C)))
% 0.47/0.66        | (v2_struct_0 @ sk_C))),
% 0.47/0.66      inference('sup-', [status(thm)], ['75', '76'])).
% 0.47/0.66  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(dt_l1_pre_topc, axiom,
% 0.47/0.66    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.47/0.66  thf('79', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.47/0.66      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.66  thf('80', plain, ((l1_struct_0 @ sk_A)),
% 0.47/0.66      inference('sup-', [status(thm)], ['78', '79'])).
% 0.47/0.66  thf('81', plain,
% 0.47/0.66      (((sk_D_2)
% 0.47/0.66         = (k2_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.66            (u1_waybel_0 @ sk_A @ sk_C)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('82', plain,
% 0.47/0.66      (((v2_struct_0 @ sk_A)
% 0.47/0.66        | (r1_waybel_0 @ sk_A @ sk_C @ sk_D_2)
% 0.47/0.66        | (v2_struct_0 @ sk_C))),
% 0.47/0.66      inference('demod', [status(thm)], ['77', '80', '81'])).
% 0.47/0.66  thf('83', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('84', plain,
% 0.47/0.66      (((v2_struct_0 @ sk_C) | (r1_waybel_0 @ sk_A @ sk_C @ sk_D_2))),
% 0.47/0.66      inference('clc', [status(thm)], ['82', '83'])).
% 0.47/0.66  thf('85', plain, (~ (v2_struct_0 @ sk_C)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('86', plain, ((r1_waybel_0 @ sk_A @ sk_C @ sk_D_2)),
% 0.47/0.66      inference('clc', [status(thm)], ['84', '85'])).
% 0.47/0.66  thf(t26_yellow_6, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.47/0.66       ( ![B:$i]:
% 0.47/0.66         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.47/0.66             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.47/0.66           ( ![C:$i,D:$i]:
% 0.47/0.66             ( ~( ( r1_waybel_0 @ A @ B @ C ) & ( r1_waybel_0 @ A @ B @ D ) & 
% 0.47/0.66                  ( r1_xboole_0 @ C @ D ) ) ) ) ) ) ))).
% 0.47/0.66  thf('87', plain,
% 0.47/0.66      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.47/0.66         ((v2_struct_0 @ X19)
% 0.47/0.66          | ~ (v4_orders_2 @ X19)
% 0.47/0.66          | ~ (v7_waybel_0 @ X19)
% 0.47/0.66          | ~ (l1_waybel_0 @ X19 @ X20)
% 0.47/0.66          | ~ (r1_waybel_0 @ X20 @ X19 @ X21)
% 0.47/0.66          | ~ (r1_xboole_0 @ X21 @ X22)
% 0.47/0.66          | ~ (r1_waybel_0 @ X20 @ X19 @ X22)
% 0.47/0.66          | ~ (l1_struct_0 @ X20)
% 0.47/0.66          | (v2_struct_0 @ X20))),
% 0.47/0.66      inference('cnf', [status(esa)], [t26_yellow_6])).
% 0.47/0.66  thf('88', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((v2_struct_0 @ sk_A)
% 0.47/0.66          | ~ (l1_struct_0 @ sk_A)
% 0.47/0.66          | ~ (r1_waybel_0 @ sk_A @ sk_C @ X0)
% 0.47/0.66          | ~ (r1_xboole_0 @ sk_D_2 @ X0)
% 0.47/0.66          | ~ (l1_waybel_0 @ sk_C @ sk_A)
% 0.47/0.66          | ~ (v7_waybel_0 @ sk_C)
% 0.47/0.66          | ~ (v4_orders_2 @ sk_C)
% 0.47/0.66          | (v2_struct_0 @ sk_C))),
% 0.47/0.66      inference('sup-', [status(thm)], ['86', '87'])).
% 0.47/0.66  thf('89', plain, ((l1_struct_0 @ sk_A)),
% 0.47/0.66      inference('sup-', [status(thm)], ['78', '79'])).
% 0.47/0.66  thf('90', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('91', plain, ((v7_waybel_0 @ sk_C)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('92', plain, ((v4_orders_2 @ sk_C)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('93', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((v2_struct_0 @ sk_A)
% 0.47/0.66          | ~ (r1_waybel_0 @ sk_A @ sk_C @ X0)
% 0.47/0.66          | ~ (r1_xboole_0 @ sk_D_2 @ X0)
% 0.47/0.66          | (v2_struct_0 @ sk_C))),
% 0.47/0.66      inference('demod', [status(thm)], ['88', '89', '90', '91', '92'])).
% 0.47/0.66  thf('94', plain,
% 0.47/0.66      (((v2_struct_0 @ sk_C)
% 0.47/0.66        | ~ (r1_xboole_0 @ sk_D_2 @ (sk_D @ sk_B @ sk_D_2 @ sk_A))
% 0.47/0.66        | (v2_struct_0 @ sk_A))),
% 0.47/0.66      inference('sup-', [status(thm)], ['74', '93'])).
% 0.47/0.66  thf('95', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('96', plain,
% 0.47/0.66      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('97', plain,
% 0.47/0.66      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.47/0.66          | (v2_struct_0 @ X5)
% 0.47/0.66          | (r1_xboole_0 @ X4 @ (sk_D @ X6 @ X4 @ X5))
% 0.47/0.66          | (r2_hidden @ X6 @ (k2_pre_topc @ X5 @ X4))
% 0.47/0.66          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.47/0.66          | ~ (l1_pre_topc @ X5))),
% 0.47/0.66      inference('cnf', [status(esa)], [t54_pre_topc])).
% 0.47/0.66  thf('98', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (l1_pre_topc @ sk_A)
% 0.47/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_D_2))
% 0.47/0.66          | (r1_xboole_0 @ sk_D_2 @ (sk_D @ X0 @ sk_D_2 @ sk_A))
% 0.47/0.66          | (v2_struct_0 @ sk_A))),
% 0.47/0.66      inference('sup-', [status(thm)], ['96', '97'])).
% 0.47/0.66  thf('99', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('100', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.66          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_D_2))
% 0.47/0.66          | (r1_xboole_0 @ sk_D_2 @ (sk_D @ X0 @ sk_D_2 @ sk_A))
% 0.47/0.66          | (v2_struct_0 @ sk_A))),
% 0.47/0.66      inference('demod', [status(thm)], ['98', '99'])).
% 0.47/0.66  thf('101', plain,
% 0.47/0.66      (((v2_struct_0 @ sk_A)
% 0.47/0.66        | (r1_xboole_0 @ sk_D_2 @ (sk_D @ sk_B @ sk_D_2 @ sk_A))
% 0.47/0.66        | (r2_hidden @ sk_B @ (k2_pre_topc @ sk_A @ sk_D_2)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['95', '100'])).
% 0.47/0.66  thf('102', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('103', plain,
% 0.47/0.66      (((r2_hidden @ sk_B @ (k2_pre_topc @ sk_A @ sk_D_2))
% 0.47/0.66        | (r1_xboole_0 @ sk_D_2 @ (sk_D @ sk_B @ sk_D_2 @ sk_A)))),
% 0.47/0.66      inference('clc', [status(thm)], ['101', '102'])).
% 0.47/0.66  thf('104', plain, (~ (r2_hidden @ sk_B @ (k2_pre_topc @ sk_A @ sk_D_2))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('105', plain, ((r1_xboole_0 @ sk_D_2 @ (sk_D @ sk_B @ sk_D_2 @ sk_A))),
% 0.47/0.66      inference('clc', [status(thm)], ['103', '104'])).
% 0.47/0.66  thf('106', plain, (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 0.47/0.66      inference('demod', [status(thm)], ['94', '105'])).
% 0.47/0.66  thf('107', plain, (~ (v2_struct_0 @ sk_C)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('108', plain, ((v2_struct_0 @ sk_A)),
% 0.47/0.66      inference('clc', [status(thm)], ['106', '107'])).
% 0.47/0.66  thf('109', plain, ($false), inference('demod', [status(thm)], ['0', '108'])).
% 0.47/0.66  
% 0.47/0.66  % SZS output end Refutation
% 0.47/0.66  
% 0.47/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
