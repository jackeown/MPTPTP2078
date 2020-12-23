%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT2064+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pOVyIIx4sw

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  277 (2924 expanded)
%              Number of leaves         :   37 ( 797 expanded)
%              Depth                    :   23
%              Number of atoms          : 3653 (74070 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(m2_yellow_6_type,type,(
    m2_yellow_6: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(v3_yellow_6_type,type,(
    v3_yellow_6: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r3_waybel_9_type,type,(
    r3_waybel_9: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(t24_yellow19,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) )
              <=> ? [D: $i] :
                    ( ( r2_hidden @ C @ ( k10_yellow_6 @ A @ D ) )
                    & ( r1_waybel_0 @ A @ D @ B )
                    & ( l1_waybel_0 @ D @ A )
                    & ( v3_yellow_6 @ D @ A )
                    & ( v7_waybel_0 @ D )
                    & ( v4_orders_2 @ D )
                    & ~ ( v2_struct_0 @ D ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) )
                <=> ? [D: $i] :
                      ( ( r2_hidden @ C @ ( k10_yellow_6 @ A @ D ) )
                      & ( r1_waybel_0 @ A @ D @ B )
                      & ( l1_waybel_0 @ D @ A )
                      & ( v3_yellow_6 @ D @ A )
                      & ( v7_waybel_0 @ D )
                      & ( v4_orders_2 @ D )
                      & ~ ( v2_struct_0 @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_yellow19])).

thf('0',plain,
    ( ~ ( v2_struct_0 @ sk_D_2 )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v2_struct_0 @ sk_D_2 )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_waybel_0 @ sk_A @ sk_D_2 @ sk_B )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_waybel_0 @ sk_A @ sk_D_2 @ sk_B )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( l1_waybel_0 @ sk_D_2 @ sk_A )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( l1_waybel_0 @ sk_D_2 @ sk_A )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( v7_waybel_0 @ sk_D_2 )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v7_waybel_0 @ sk_D_2 )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( v4_orders_2 @ sk_D_2 )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v4_orders_2 @ sk_D_2 )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,(
    ! [X26: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v4_orders_2 @ X26 )
      | ~ ( v7_waybel_0 @ X26 )
      | ~ ( v3_yellow_6 @ X26 @ sk_A )
      | ~ ( l1_waybel_0 @ X26 @ sk_A )
      | ~ ( r1_waybel_0 @ sk_A @ X26 @ sk_B )
      | ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ X26 ) )
      | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ! [X26: $i] :
        ( ( v2_struct_0 @ X26 )
        | ~ ( v4_orders_2 @ X26 )
        | ~ ( v7_waybel_0 @ X26 )
        | ~ ( v3_yellow_6 @ X26 @ sk_A )
        | ~ ( l1_waybel_0 @ X26 @ sk_A )
        | ~ ( r1_waybel_0 @ sk_A @ X26 @ sk_B )
        | ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ X26 ) ) )
    | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_D_2 ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t23_yellow19,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) )
              <=> ? [D: $i] :
                    ( ( r3_waybel_9 @ A @ D @ C )
                    & ( r1_waybel_0 @ A @ D @ B )
                    & ( l1_waybel_0 @ D @ A )
                    & ( v7_waybel_0 @ D )
                    & ( v4_orders_2 @ D )
                    & ~ ( v2_struct_0 @ D ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( r2_hidden @ X14 @ ( k2_pre_topc @ X13 @ X12 ) )
      | ( r3_waybel_9 @ X13 @ ( sk_D @ X14 @ X12 @ X13 ) @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t23_yellow19])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
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
      | ( r3_waybel_9 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,
    ( ( ( r3_waybel_9 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( r3_waybel_9 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( r3_waybel_9 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t32_waybel_9,axiom,(
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
             => ~ ( ( r3_waybel_9 @ A @ B @ C )
                  & ! [D: $i] :
                      ( ( m2_yellow_6 @ D @ A @ B )
                     => ~ ( r2_hidden @ C @ ( k10_yellow_6 @ A @ D ) ) ) ) ) ) ) )).

thf('26',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v7_waybel_0 @ X21 )
      | ~ ( l1_waybel_0 @ X21 @ X22 )
      | ( m2_yellow_6 @ ( sk_D_1 @ X23 @ X21 @ X22 ) @ X22 @ X21 )
      | ~ ( r3_waybel_9 @ X22 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t32_waybel_9])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ sk_C )
      | ( m2_yellow_6 @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ sk_A @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ sk_C )
      | ( m2_yellow_6 @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) @ sk_A @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( m2_yellow_6 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['12'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( r2_hidden @ X14 @ ( k2_pre_topc @ X13 @ X12 ) )
      | ( v4_orders_2 @ ( sk_D @ X14 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t23_yellow19])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v4_orders_2 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v4_orders_2 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ( ( v4_orders_2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( v4_orders_2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v4_orders_2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['12'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( r2_hidden @ X14 @ ( k2_pre_topc @ X13 @ X12 ) )
      | ( v7_waybel_0 @ ( sk_D @ X14 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t23_yellow19])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( ( v7_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( v7_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v7_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['12'])).

thf('57',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( r2_hidden @ X14 @ ( k2_pre_topc @ X13 @ X12 ) )
      | ( l1_waybel_0 @ ( sk_D @ X14 @ X12 @ X13 ) @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t23_yellow19])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( ( l1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( ( l1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( l1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( m2_yellow_6 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','43','55','67'])).

thf('69',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['12'])).

thf('70',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( r2_hidden @ X14 @ ( k2_pre_topc @ X13 @ X12 ) )
      | ~ ( v2_struct_0 @ ( sk_D @ X14 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t23_yellow19])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,
    ( ( ~ ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['69','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( ~ ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ~ ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m2_yellow_6 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['68','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( m2_yellow_6 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['81','82'])).

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

thf('84',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( l1_struct_0 @ X3 )
      | ( v2_struct_0 @ X3 )
      | ( v2_struct_0 @ X4 )
      | ~ ( v4_orders_2 @ X4 )
      | ~ ( v7_waybel_0 @ X4 )
      | ~ ( l1_waybel_0 @ X4 @ X3 )
      | ( l1_waybel_0 @ X5 @ X3 )
      | ~ ( m2_yellow_6 @ X5 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('85',plain,
    ( ( ( l1_waybel_0 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ~ ( l1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( l1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('87',plain,
    ( ( v7_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('88',plain,
    ( ( v4_orders_2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('90',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('91',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( ( l1_waybel_0 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['85','86','87','88','91'])).

thf('93',plain,
    ( ~ ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('94',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( l1_waybel_0 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( l1_waybel_0 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf(d19_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ( ( v3_yellow_6 @ B @ A )
          <=> ( ( k10_yellow_6 @ A @ B )
             != k1_xboole_0 ) ) ) ) )).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( ( k10_yellow_6 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( v3_yellow_6 @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d19_yellow_6])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('98',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( ( k10_yellow_6 @ X1 @ X0 )
        = o_0_0_xboole_0 )
      | ( v3_yellow_6 @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v3_yellow_6 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ( ( k10_yellow_6 @ sk_A @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
        = o_0_0_xboole_0 )
      | ~ ( v7_waybel_0 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['96','99'])).

thf('101',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( m2_yellow_6 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('104',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( l1_struct_0 @ X3 )
      | ( v2_struct_0 @ X3 )
      | ( v2_struct_0 @ X4 )
      | ~ ( v4_orders_2 @ X4 )
      | ~ ( v7_waybel_0 @ X4 )
      | ~ ( l1_waybel_0 @ X4 @ X3 )
      | ( v7_waybel_0 @ X5 )
      | ~ ( m2_yellow_6 @ X5 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('105',plain,
    ( ( ( v7_waybel_0 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( l1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('107',plain,
    ( ( v7_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('108',plain,
    ( ( v4_orders_2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('109',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['89','90'])).

thf('110',plain,
    ( ( ( v7_waybel_0 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['105','106','107','108','109'])).

thf('111',plain,
    ( ~ ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('112',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v7_waybel_0 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( v7_waybel_0 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( m2_yellow_6 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('116',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( l1_struct_0 @ X3 )
      | ( v2_struct_0 @ X3 )
      | ( v2_struct_0 @ X4 )
      | ~ ( v4_orders_2 @ X4 )
      | ~ ( v7_waybel_0 @ X4 )
      | ~ ( l1_waybel_0 @ X4 @ X3 )
      | ( v4_orders_2 @ X5 )
      | ~ ( m2_yellow_6 @ X5 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('117',plain,
    ( ( ( v4_orders_2 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( l1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('119',plain,
    ( ( v7_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('120',plain,
    ( ( v4_orders_2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('121',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['89','90'])).

thf('122',plain,
    ( ( ( v4_orders_2 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['117','118','119','120','121'])).

thf('123',plain,
    ( ~ ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('124',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v4_orders_2 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( v4_orders_2 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v3_yellow_6 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ( ( k10_yellow_6 @ sk_A @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['100','101','102','114','126'])).

thf('128',plain,
    ( ( r3_waybel_9 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('129',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v7_waybel_0 @ X21 )
      | ~ ( l1_waybel_0 @ X21 @ X22 )
      | ( r2_hidden @ X23 @ ( k10_yellow_6 @ X22 @ ( sk_D_1 @ X23 @ X21 @ X22 ) ) )
      | ~ ( r3_waybel_9 @ X22 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t32_waybel_9])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ sk_C )
      | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ sk_C )
      | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( sk_D_1 @ sk_C @ X0 @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['131','132','133'])).

thf('135',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['128','134'])).

thf('136',plain,
    ( ( v4_orders_2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('137',plain,
    ( ( v7_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('138',plain,
    ( ( l1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('139',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['135','136','137','138'])).

thf('140',plain,
    ( ~ ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('141',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['139','140'])).

thf('142',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['141','142'])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('144',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ~ ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('145',plain,
    ( ~ ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,
    ( ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
      | ( v2_struct_0 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ( v3_yellow_6 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['127','145'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('147',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('148',plain,
    ( ( ( v2_struct_0 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ( v3_yellow_6 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,
    ( ( m2_yellow_6 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('150',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( l1_struct_0 @ X3 )
      | ( v2_struct_0 @ X3 )
      | ( v2_struct_0 @ X4 )
      | ~ ( v4_orders_2 @ X4 )
      | ~ ( v7_waybel_0 @ X4 )
      | ~ ( l1_waybel_0 @ X4 @ X3 )
      | ~ ( v2_struct_0 @ X5 )
      | ~ ( m2_yellow_6 @ X5 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('151',plain,
    ( ( ~ ( v2_struct_0 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,
    ( ( l1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('153',plain,
    ( ( v7_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('154',plain,
    ( ( v4_orders_2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('155',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['89','90'])).

thf('156',plain,
    ( ( ~ ( v2_struct_0 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['151','152','153','154','155'])).

thf('157',plain,
    ( ~ ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('158',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_struct_0 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('159',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ~ ( v2_struct_0 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['158','159'])).

thf('161',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v3_yellow_6 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['148','160'])).

thf('162',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( v3_yellow_6 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['161','162'])).

thf('164',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['12'])).

thf('165',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( r2_hidden @ X14 @ ( k2_pre_topc @ X13 @ X12 ) )
      | ( r1_waybel_0 @ X13 @ ( sk_D @ X14 @ X12 @ X13 ) @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t23_yellow19])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_0 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_0 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['167','168','169'])).

thf('171',plain,
    ( ( ( r1_waybel_0 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['164','170'])).

thf('172',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,
    ( ( ( r1_waybel_0 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['171','172'])).

thf('174',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,
    ( ( r1_waybel_0 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['173','174'])).

thf('176',plain,
    ( ( m2_yellow_6 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['81','82'])).

thf(t21_yellow19,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( v2_struct_0 @ C )
            & ( v4_orders_2 @ C )
            & ( v7_waybel_0 @ C )
            & ( l1_waybel_0 @ C @ A ) )
         => ( ( r1_waybel_0 @ A @ C @ B )
           => ! [D: $i] :
                ( ( m2_yellow_6 @ D @ A @ C )
               => ( r1_waybel_0 @ A @ D @ B ) ) ) ) ) )).

thf('177',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v4_orders_2 @ X8 )
      | ~ ( v7_waybel_0 @ X8 )
      | ~ ( l1_waybel_0 @ X8 @ X9 )
      | ( r1_waybel_0 @ X9 @ X10 @ X11 )
      | ~ ( m2_yellow_6 @ X10 @ X9 @ X8 )
      | ~ ( r1_waybel_0 @ X9 @ X8 @ X11 )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t21_yellow19])).

thf('178',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( l1_struct_0 @ sk_A )
        | ~ ( r1_waybel_0 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ X0 )
        | ( r1_waybel_0 @ sk_A @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ X0 )
        | ~ ( l1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
        | ~ ( v7_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v4_orders_2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['89','90'])).

thf('180',plain,
    ( ( l1_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('181',plain,
    ( ( v7_waybel_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('182',plain,
    ( ( v4_orders_2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('183',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( r1_waybel_0 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ X0 )
        | ( r1_waybel_0 @ sk_A @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ X0 )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['178','179','180','181','182'])).

thf('184',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r1_waybel_0 @ sk_A @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['175','183'])).

thf('185',plain,
    ( ~ ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('186',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_B ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['184','185'])).

thf('187',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,
    ( ( r1_waybel_0 @ sk_A @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_B )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['186','187'])).

thf('189',plain,
    ( ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['141','142'])).

thf('190',plain,
    ( ! [X26: $i] :
        ( ( v2_struct_0 @ X26 )
        | ~ ( v4_orders_2 @ X26 )
        | ~ ( v7_waybel_0 @ X26 )
        | ~ ( v3_yellow_6 @ X26 @ sk_A )
        | ~ ( l1_waybel_0 @ X26 @ sk_A )
        | ~ ( r1_waybel_0 @ sk_A @ X26 @ sk_B )
        | ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ X26 ) ) )
   <= ! [X26: $i] :
        ( ( v2_struct_0 @ X26 )
        | ~ ( v4_orders_2 @ X26 )
        | ~ ( v7_waybel_0 @ X26 )
        | ~ ( v3_yellow_6 @ X26 @ sk_A )
        | ~ ( l1_waybel_0 @ X26 @ sk_A )
        | ~ ( r1_waybel_0 @ sk_A @ X26 @ sk_B )
        | ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ X26 ) ) ) ),
    inference(split,[status(esa)],['10'])).

thf('191',plain,
    ( ( ~ ( r1_waybel_0 @ sk_A @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_B )
      | ~ ( l1_waybel_0 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ~ ( v3_yellow_6 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) )
   <= ( ! [X26: $i] :
          ( ( v2_struct_0 @ X26 )
          | ~ ( v4_orders_2 @ X26 )
          | ~ ( v7_waybel_0 @ X26 )
          | ~ ( v3_yellow_6 @ X26 @ sk_A )
          | ~ ( l1_waybel_0 @ X26 @ sk_A )
          | ~ ( r1_waybel_0 @ sk_A @ X26 @ sk_B )
          | ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ X26 ) ) )
      & ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,
    ( ( ( v2_struct_0 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( v3_yellow_6 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ~ ( l1_waybel_0 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A ) )
   <= ( ! [X26: $i] :
          ( ( v2_struct_0 @ X26 )
          | ~ ( v4_orders_2 @ X26 )
          | ~ ( v7_waybel_0 @ X26 )
          | ~ ( v3_yellow_6 @ X26 @ sk_A )
          | ~ ( l1_waybel_0 @ X26 @ sk_A )
          | ~ ( r1_waybel_0 @ sk_A @ X26 @ sk_B )
          | ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ X26 ) ) )
      & ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['188','191'])).

thf('193',plain,
    ( ( v4_orders_2 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('194',plain,
    ( ( v7_waybel_0 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('195',plain,
    ( ( l1_waybel_0 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('196',plain,
    ( ( ( v2_struct_0 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( v3_yellow_6 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A ) )
   <= ( ! [X26: $i] :
          ( ( v2_struct_0 @ X26 )
          | ~ ( v4_orders_2 @ X26 )
          | ~ ( v7_waybel_0 @ X26 )
          | ~ ( v3_yellow_6 @ X26 @ sk_A )
          | ~ ( l1_waybel_0 @ X26 @ sk_A )
          | ~ ( r1_waybel_0 @ sk_A @ X26 @ sk_B )
          | ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ X26 ) ) )
      & ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['192','193','194','195'])).

thf('197',plain,
    ( ~ ( v2_struct_0 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['158','159'])).

thf('198',plain,
    ( ~ ( v3_yellow_6 @ ( sk_D_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
   <= ( ! [X26: $i] :
          ( ( v2_struct_0 @ X26 )
          | ~ ( v4_orders_2 @ X26 )
          | ~ ( v7_waybel_0 @ X26 )
          | ~ ( v3_yellow_6 @ X26 @ sk_A )
          | ~ ( l1_waybel_0 @ X26 @ sk_A )
          | ~ ( r1_waybel_0 @ sk_A @ X26 @ sk_B )
          | ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ X26 ) ) )
      & ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['196','197'])).

thf('199',plain,
    ( ~ ! [X26: $i] :
          ( ( v2_struct_0 @ X26 )
          | ~ ( v4_orders_2 @ X26 )
          | ~ ( v7_waybel_0 @ X26 )
          | ~ ( v3_yellow_6 @ X26 @ sk_A )
          | ~ ( l1_waybel_0 @ X26 @ sk_A )
          | ~ ( r1_waybel_0 @ sk_A @ X26 @ sk_B )
          | ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ X26 ) ) )
    | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['163','198'])).

thf('200',plain,
    ( ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_D_2 ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['12'])).

thf('201',plain,
    ( ( r1_waybel_0 @ sk_A @ sk_D_2 @ sk_B )
   <= ( r1_waybel_0 @ sk_A @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('202',plain,
    ( ( v7_waybel_0 @ sk_D_2 )
   <= ( v7_waybel_0 @ sk_D_2 ) ),
    inference(split,[status(esa)],['6'])).

thf('203',plain,
    ( ( v4_orders_2 @ sk_D_2 )
   <= ( v4_orders_2 @ sk_D_2 ) ),
    inference(split,[status(esa)],['8'])).

thf('204',plain,
    ( ( l1_waybel_0 @ sk_D_2 @ sk_A )
   <= ( l1_waybel_0 @ sk_D_2 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('205',plain,
    ( ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_D_2 ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_D_2 ) ) ),
    inference(split,[status(esa)],['12'])).

thf(t29_waybel_9,axiom,(
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
             => ( ( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) )
               => ( r3_waybel_9 @ A @ B @ C ) ) ) ) ) )).

thf('206',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ~ ( v7_waybel_0 @ X16 )
      | ~ ( l1_waybel_0 @ X16 @ X17 )
      | ~ ( r2_hidden @ X18 @ ( k10_yellow_6 @ X17 @ X16 ) )
      | ( r3_waybel_9 @ X17 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t29_waybel_9])).

thf('207',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ sk_D_2 @ sk_C )
      | ~ ( l1_waybel_0 @ sk_D_2 @ sk_A )
      | ~ ( v7_waybel_0 @ sk_D_2 )
      | ~ ( v4_orders_2 @ sk_D_2 )
      | ( v2_struct_0 @ sk_D_2 ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r3_waybel_9 @ sk_A @ sk_D_2 @ sk_C )
      | ~ ( l1_waybel_0 @ sk_D_2 @ sk_A )
      | ~ ( v7_waybel_0 @ sk_D_2 )
      | ~ ( v4_orders_2 @ sk_D_2 )
      | ( v2_struct_0 @ sk_D_2 ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['207','208','209','210'])).

thf('212',plain,
    ( ( ( v2_struct_0 @ sk_D_2 )
      | ~ ( v4_orders_2 @ sk_D_2 )
      | ~ ( v7_waybel_0 @ sk_D_2 )
      | ( r3_waybel_9 @ sk_A @ sk_D_2 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_D_2 ) )
      & ( l1_waybel_0 @ sk_D_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['204','211'])).

thf('213',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r3_waybel_9 @ sk_A @ sk_D_2 @ sk_C )
      | ~ ( v7_waybel_0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_D_2 ) )
   <= ( ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_D_2 ) )
      & ( l1_waybel_0 @ sk_D_2 @ sk_A )
      & ( v4_orders_2 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['203','212'])).

thf('214',plain,
    ( ( ( v2_struct_0 @ sk_D_2 )
      | ( r3_waybel_9 @ sk_A @ sk_D_2 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_D_2 ) )
      & ( l1_waybel_0 @ sk_D_2 @ sk_A )
      & ( v7_waybel_0 @ sk_D_2 )
      & ( v4_orders_2 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['202','213'])).

thf('215',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,
    ( ( ( r3_waybel_9 @ sk_A @ sk_D_2 @ sk_C )
      | ( v2_struct_0 @ sk_D_2 ) )
   <= ( ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_D_2 ) )
      & ( l1_waybel_0 @ sk_D_2 @ sk_A )
      & ( v7_waybel_0 @ sk_D_2 )
      & ( v4_orders_2 @ sk_D_2 ) ) ),
    inference(clc,[status(thm)],['214','215'])).

thf('217',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( r3_waybel_9 @ X13 @ X15 @ X14 )
      | ~ ( r1_waybel_0 @ X13 @ X15 @ X12 )
      | ~ ( l1_waybel_0 @ X15 @ X13 )
      | ~ ( v7_waybel_0 @ X15 )
      | ~ ( v4_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ( r2_hidden @ X14 @ ( k2_pre_topc @ X13 @ X12 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t23_yellow19])).

thf('220',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v7_waybel_0 @ X1 )
      | ~ ( l1_waybel_0 @ X1 @ sk_A )
      | ~ ( r1_waybel_0 @ sk_A @ X1 @ sk_B )
      | ~ ( r3_waybel_9 @ sk_A @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['218','219'])).

thf('221',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v7_waybel_0 @ X1 )
      | ~ ( l1_waybel_0 @ X1 @ sk_A )
      | ~ ( r1_waybel_0 @ sk_A @ X1 @ sk_B )
      | ~ ( r3_waybel_9 @ sk_A @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['220','221','222'])).

thf('224',plain,(
    ! [X0: $i] :
      ( ~ ( r3_waybel_9 @ sk_A @ X0 @ sk_C )
      | ~ ( r1_waybel_0 @ sk_A @ X0 @ sk_B )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['217','223'])).

thf('225',plain,
    ( ( ( v2_struct_0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_D_2 )
      | ~ ( v4_orders_2 @ sk_D_2 )
      | ~ ( v7_waybel_0 @ sk_D_2 )
      | ~ ( l1_waybel_0 @ sk_D_2 @ sk_A )
      | ~ ( r1_waybel_0 @ sk_A @ sk_D_2 @ sk_B ) )
   <= ( ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_D_2 ) )
      & ( l1_waybel_0 @ sk_D_2 @ sk_A )
      & ( v7_waybel_0 @ sk_D_2 )
      & ( v4_orders_2 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['216','224'])).

thf('226',plain,
    ( ( v4_orders_2 @ sk_D_2 )
   <= ( v4_orders_2 @ sk_D_2 ) ),
    inference(split,[status(esa)],['8'])).

thf('227',plain,
    ( ( v7_waybel_0 @ sk_D_2 )
   <= ( v7_waybel_0 @ sk_D_2 ) ),
    inference(split,[status(esa)],['6'])).

thf('228',plain,
    ( ( l1_waybel_0 @ sk_D_2 @ sk_A )
   <= ( l1_waybel_0 @ sk_D_2 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('229',plain,
    ( ( ( v2_struct_0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_D_2 )
      | ~ ( r1_waybel_0 @ sk_A @ sk_D_2 @ sk_B ) )
   <= ( ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_D_2 ) )
      & ( l1_waybel_0 @ sk_D_2 @ sk_A )
      & ( v7_waybel_0 @ sk_D_2 )
      & ( v4_orders_2 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['225','226','227','228'])).

thf('230',plain,
    ( ( ~ ( r1_waybel_0 @ sk_A @ sk_D_2 @ sk_B )
      | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_2 ) )
   <= ( ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_D_2 ) )
      & ( l1_waybel_0 @ sk_D_2 @ sk_A )
      & ( v7_waybel_0 @ sk_D_2 )
      & ( v4_orders_2 @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['229'])).

thf('231',plain,
    ( ( ( v2_struct_0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
   <= ( ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_D_2 ) )
      & ( r1_waybel_0 @ sk_A @ sk_D_2 @ sk_B )
      & ( l1_waybel_0 @ sk_D_2 @ sk_A )
      & ( v7_waybel_0 @ sk_D_2 )
      & ( v4_orders_2 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['201','230'])).

thf('232',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,
    ( ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_D_2 ) )
   <= ( ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_D_2 ) )
      & ( r1_waybel_0 @ sk_A @ sk_D_2 @ sk_B )
      & ( l1_waybel_0 @ sk_D_2 @ sk_A )
      & ( v7_waybel_0 @ sk_D_2 )
      & ( v4_orders_2 @ sk_D_2 ) ) ),
    inference(clc,[status(thm)],['231','232'])).

thf('234',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf('235',plain,
    ( ( v2_struct_0 @ sk_D_2 )
   <= ( ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_D_2 ) )
      & ( r1_waybel_0 @ sk_A @ sk_D_2 @ sk_B )
      & ( l1_waybel_0 @ sk_D_2 @ sk_A )
      & ( v7_waybel_0 @ sk_D_2 )
      & ( v4_orders_2 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['233','234'])).

thf('236',plain,
    ( ~ ( v2_struct_0 @ sk_D_2 )
   <= ~ ( v2_struct_0 @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('237',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ sk_D_2 ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v4_orders_2 @ sk_D_2 )
    | ~ ( v7_waybel_0 @ sk_D_2 )
    | ~ ( l1_waybel_0 @ sk_D_2 @ sk_A )
    | ~ ( r1_waybel_0 @ sk_A @ sk_D_2 @ sk_B )
    | ( v2_struct_0 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['235','236'])).

thf('238',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','9','11','199','200','237'])).


%------------------------------------------------------------------------------
