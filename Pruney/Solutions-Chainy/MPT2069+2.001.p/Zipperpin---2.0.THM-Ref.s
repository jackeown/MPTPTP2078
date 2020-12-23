%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VKGcGDXodM

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:55 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :  363 (1770 expanded)
%              Number of leaves         :   33 ( 475 expanded)
%              Depth                    :   45
%              Number of atoms          : 7497 (57616 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   21 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(r1_waybel_7_type,type,(
    r1_waybel_7: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r3_waybel_9_type,type,(
    r3_waybel_9: $i > $i > $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t29_yellow19,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ! [C: $i] :
                ( ( ~ ( v1_xboole_0 @ C )
                  & ( v1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) )
                  & ( v2_waybel_0 @ C @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
                  & ( v13_waybel_0 @ C @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )
               => ( ( r2_hidden @ B @ C )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r1_waybel_7 @ A @ C @ D )
                       => ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
            <=> ! [C: $i] :
                  ( ( ~ ( v1_xboole_0 @ C )
                    & ( v1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) )
                    & ( v2_waybel_0 @ C @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
                    & ( v13_waybel_0 @ C @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
                    & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )
                 => ( ( r2_hidden @ B @ C )
                   => ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                       => ( ( r1_waybel_7 @ A @ C @ D )
                         => ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_yellow19])).

thf('0',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v1_xboole_0 @ X12 )
      | ~ ( v1_subset_1 @ X12 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ~ ( r1_waybel_7 @ sk_A @ X12 @ X13 )
      | ( r2_hidden @ X13 @ sk_B )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ sk_B @ X12 )
      | ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v1_subset_1 @ X12 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r1_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_yellow19,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( v4_orders_2 @ C )
                  & ( v7_waybel_0 @ C )
                  & ( l1_waybel_0 @ C @ A ) )
               => ( ( r1_waybel_0 @ A @ C @ B )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r3_waybel_9 @ A @ C @ D )
                       => ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X4 @ X5 ) @ ( u1_struct_0 @ X5 ) )
      | ( v4_pre_topc @ X4 @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t25_yellow19])).

thf('4',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( v4_orders_2 @ ( sk_C @ X4 @ X5 ) )
      | ( v4_pre_topc @ X4 @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t25_yellow19])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( v4_orders_2 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( v4_orders_2 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( v4_orders_2 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( v7_waybel_0 @ ( sk_C @ X4 @ X5 ) )
      | ( v4_pre_topc @ X4 @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t25_yellow19])).

thf('20',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( v7_waybel_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( v7_waybel_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( v7_waybel_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( l1_waybel_0 @ ( sk_C @ X4 @ X5 ) @ X5 )
      | ( v4_pre_topc @ X4 @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t25_yellow19])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( l1_waybel_0 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( l1_waybel_0 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( l1_waybel_0 @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( r1_waybel_0 @ X5 @ ( sk_C @ X4 @ X5 ) @ X4 )
      | ( v4_pre_topc @ X4 @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t25_yellow19])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_waybel_0 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_waybel_0 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( r1_waybel_0 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( r3_waybel_9 @ X5 @ ( sk_C @ X4 @ X5 ) @ ( sk_D_1 @ X4 @ X5 ) )
      | ( v4_pre_topc @ X4 @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t25_yellow19])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( r3_waybel_9 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ ( sk_D_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( r3_waybel_9 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ ( sk_D_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( r3_waybel_9 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ ( sk_D_1 @ sk_B @ sk_A ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('51',plain,(
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

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r3_waybel_9 @ X1 @ X3 @ X2 )
      | ~ ( r1_waybel_0 @ X1 @ X3 @ X0 )
      | ~ ( l1_waybel_0 @ X3 @ X1 )
      | ~ ( v7_waybel_0 @ X3 )
      | ~ ( v4_orders_2 @ X3 )
      | ( v2_struct_0 @ X3 )
      | ( r2_hidden @ X2 @ ( k2_pre_topc @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t23_yellow19])).

thf('53',plain,(
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
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
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
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ sk_B @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_D_1 @ sk_B @ sk_A ) )
      | ~ ( r1_waybel_0 @ sk_A @ X0 @ sk_B )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','56'])).

thf('58',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v7_waybel_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( l1_waybel_0 @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r1_waybel_0 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['49','57'])).

thf('59',plain,
    ( ~ ( r1_waybel_0 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
    | ~ ( l1_waybel_0 @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( v7_waybel_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v7_waybel_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( l1_waybel_0 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['41','59'])).

thf('61',plain,
    ( ~ ( l1_waybel_0 @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( v7_waybel_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v7_waybel_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','61'])).

thf('63',plain,
    ( ~ ( v7_waybel_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','63'])).

thf('65',plain,
    ( ~ ( v4_orders_2 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','65'])).

thf('67',plain,
    ( ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('69',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('70',plain,
    ( ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['66'])).

thf('71',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t27_yellow19,axiom,(
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
                    ( ( r1_waybel_7 @ A @ D @ C )
                    & ( r2_hidden @ B @ D )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) )
                    & ( v13_waybel_0 @ D @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
                    & ( v2_waybel_0 @ D @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
                    & ( v1_subset_1 @ D @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) )
                    & ~ ( v1_xboole_0 @ D ) ) ) ) ) ) )).

thf('72',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( r2_hidden @ X10 @ ( k2_pre_topc @ X9 @ X8 ) )
      | ( r1_waybel_7 @ X9 @ ( sk_D_2 @ X10 @ X8 @ X9 ) @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t27_yellow19])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r1_waybel_7 @ sk_A @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( sk_D_1 @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['70','76'])).

thf('78',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_waybel_7 @ sk_A @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( sk_D_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r1_waybel_7 @ sk_A @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( sk_D_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','78'])).

thf('80',plain,
    ( ( r1_waybel_7 @ sk_A @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( sk_D_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('82',plain,
    ( ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['66'])).

thf('83',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( r2_hidden @ X10 @ ( k2_pre_topc @ X9 @ X8 ) )
      | ( r2_hidden @ X8 @ ( sk_D_2 @ X10 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t27_yellow19])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['82','88'])).

thf('90',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['81','90'])).

thf('92',plain,
    ( ( r2_hidden @ sk_B @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('94',plain,
    ( ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['66'])).

thf('95',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( r2_hidden @ X10 @ ( k2_pre_topc @ X9 @ X8 ) )
      | ( v2_waybel_0 @ ( sk_D_2 @ X10 @ X8 @ X9 ) @ ( k3_yellow_1 @ ( k2_struct_0 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t27_yellow19])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_waybel_0 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_waybel_0 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_waybel_0 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['94','100'])).

thf('102',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_waybel_0 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_waybel_0 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['93','102'])).

thf('104',plain,
    ( ( v2_waybel_0 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('106',plain,
    ( ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['66'])).

thf('107',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( r2_hidden @ X10 @ ( k2_pre_topc @ X9 @ X8 ) )
      | ( v13_waybel_0 @ ( sk_D_2 @ X10 @ X8 @ X9 ) @ ( k3_yellow_1 @ ( k2_struct_0 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t27_yellow19])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v13_waybel_0 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v13_waybel_0 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v13_waybel_0 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['106','112'])).

thf('114',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v13_waybel_0 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v13_waybel_0 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['105','114'])).

thf('116',plain,
    ( ( v13_waybel_0 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('118',plain,
    ( ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['66'])).

thf('119',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( r2_hidden @ X10 @ ( k2_pre_topc @ X9 @ X8 ) )
      | ( v1_subset_1 @ ( sk_D_2 @ X10 @ X8 @ X9 ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X9 ) ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t27_yellow19])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_subset_1 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_subset_1 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['121','122','123'])).

thf('125',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v1_subset_1 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['118','124'])).

thf('126',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_subset_1 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v1_subset_1 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['117','126'])).

thf('128',plain,
    ( ( v1_subset_1 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('130',plain,
    ( ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['66'])).

thf('131',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( r2_hidden @ X10 @ ( k2_pre_topc @ X9 @ X8 ) )
      | ( m1_subset_1 @ ( sk_D_2 @ X10 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X9 ) ) ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t27_yellow19])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['133','134','135'])).

thf('137',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['130','136'])).

thf('138',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['129','138'])).

thf('140',plain,
    ( ( m1_subset_1 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,
    ( ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v1_subset_1 @ X12 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r1_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v1_subset_1 @ X12 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r1_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('142',plain,
    ( ! [X0: $i] :
        ( ( v4_pre_topc @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r1_waybel_7 @ sk_A @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ X0 )
        | ~ ( v13_waybel_0 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v2_waybel_0 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v1_subset_1 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
        | ( v1_xboole_0 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v1_subset_1 @ X12 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r1_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ! [X0: $i] :
        ( ( v4_pre_topc @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
        | ( v1_xboole_0 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
        | ~ ( v2_waybel_0 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( r1_waybel_7 @ sk_A @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ X0 )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v1_subset_1 @ X12 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r1_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference('sup-',[status(thm)],['128','142'])).

thf('144',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_B @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r1_waybel_7 @ sk_A @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ X0 )
        | ~ ( v13_waybel_0 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v2_waybel_0 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ( v1_xboole_0 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v1_subset_1 @ X12 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r1_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,
    ( ! [X0: $i] :
        ( ( v4_pre_topc @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
        | ( v4_pre_topc @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
        | ( v1_xboole_0 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
        | ~ ( v2_waybel_0 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( r1_waybel_7 @ sk_A @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ X0 )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v1_subset_1 @ X12 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r1_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference('sup-',[status(thm)],['116','144'])).

thf('146',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_B @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r1_waybel_7 @ sk_A @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ X0 )
        | ~ ( v2_waybel_0 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ( v1_xboole_0 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v1_subset_1 @ X12 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r1_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,
    ( ! [X0: $i] :
        ( ( v4_pre_topc @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
        | ( v4_pre_topc @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
        | ( v1_xboole_0 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
        | ~ ( r1_waybel_7 @ sk_A @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ X0 )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v1_subset_1 @ X12 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r1_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference('sup-',[status(thm)],['104','146'])).

thf('148',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_B @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r1_waybel_7 @ sk_A @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ X0 )
        | ( v1_xboole_0 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v1_subset_1 @ X12 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r1_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,
    ( ! [X0: $i] :
        ( ( v4_pre_topc @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
        | ( v4_pre_topc @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
        | ( v1_xboole_0 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
        | ~ ( r1_waybel_7 @ sk_A @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ X0 )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v1_subset_1 @ X12 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r1_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference('sup-',[status(thm)],['92','148'])).

thf('150',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r1_waybel_7 @ sk_A @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ X0 )
        | ( v1_xboole_0 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v1_subset_1 @ X12 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r1_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,
    ( ( ( v4_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v4_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v1_subset_1 @ X12 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r1_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference('sup-',[status(thm)],['80','150'])).

thf('152',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v1_subset_1 @ X12 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r1_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,
    ( ( ( v4_pre_topc @ sk_B @ sk_A )
      | ( v4_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v1_subset_1 @ X12 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r1_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference('sup-',[status(thm)],['68','152'])).

thf('154',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v1_subset_1 @ X12 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r1_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( r2_hidden @ X10 @ ( k2_pre_topc @ X9 @ X8 ) )
      | ~ ( v1_xboole_0 @ ( sk_D_2 @ X10 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t27_yellow19])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['157','158','159'])).

thf('161',plain,
    ( ( ( v4_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v1_subset_1 @ X12 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r1_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference('sup-',[status(thm)],['154','160'])).

thf('162',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v1_subset_1 @ X12 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r1_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,
    ( ( ( v4_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v4_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v1_subset_1 @ X12 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r1_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference('sup-',[status(thm)],['67','162'])).

thf('164',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v1_subset_1 @ X12 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r1_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference(simplify,[status(thm)],['163'])).

thf('165',plain,
    ( ( ( v4_pre_topc @ sk_B @ sk_A )
      | ( v4_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v1_subset_1 @ X12 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r1_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference('sup-',[status(thm)],['9','164'])).

thf('166',plain,
    ( ( ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v1_subset_1 @ X12 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r1_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference(simplify,[status(thm)],['165'])).

thf('167',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X4 @ X5 ) @ X4 )
      | ( v4_pre_topc @ X4 @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t25_yellow19])).

thf('169',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['169','170','171'])).

thf('173',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ~ ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['172','173'])).

thf('175',plain,
    ( ( ( v4_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v1_subset_1 @ X12 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r1_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference('sup-',[status(thm)],['166','174'])).

thf('176',plain,
    ( ( ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v1_subset_1 @ X12 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r1_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( v2_struct_0 @ ( sk_C @ X4 @ X5 ) )
      | ( v4_pre_topc @ X4 @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t25_yellow19])).

thf('179',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['179','180','181'])).

thf('183',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ~ ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['182','183'])).

thf('185',plain,
    ( ( ( v4_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v1_subset_1 @ X12 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r1_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference(clc,[status(thm)],['176','184'])).

thf('186',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v1_subset_1 @ X12 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r1_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference(clc,[status(thm)],['185','186'])).

thf('188',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['188'])).

thf('190',plain,
    ( ~ ! [X12: $i,X13: $i] :
          ( ( v1_xboole_0 @ X12 )
          | ~ ( v1_subset_1 @ X12 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
          | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
          | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
          | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
          | ~ ( r1_waybel_7 @ sk_A @ X12 @ X13 )
          | ( r2_hidden @ X13 @ sk_B )
          | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ sk_B @ X12 ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['187','189'])).

thf('191',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['188'])).

thf('192',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['192'])).

thf('194',plain,
    ( ~ ( r2_hidden @ sk_D_3 @ sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ~ ( r2_hidden @ sk_D_3 @ sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['194'])).

thf('196',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['196'])).

thf('198',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['198'])).

thf('200',plain,
    ( ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,
    ( ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['200'])).

thf('202',plain,
    ( ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,
    ( ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['202'])).

thf('204',plain,
    ( ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,
    ( ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['204'])).

thf('206',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['206'])).

thf('208',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['192'])).

thf('209',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
   <= ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 ) ),
    inference(split,[status(esa)],['196'])).

thf('210',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
   <= ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['188'])).

thf('211',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,
    ( ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['202'])).

thf('213',plain,
    ( ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['200'])).

thf('214',plain,
    ( ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
   <= ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['204'])).

thf('215',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['198'])).

thf('216',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( r1_waybel_7 @ X9 @ X11 @ X10 )
      | ~ ( r2_hidden @ X8 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X9 ) ) ) ) )
      | ~ ( v13_waybel_0 @ X11 @ ( k3_yellow_1 @ ( k2_struct_0 @ X9 ) ) )
      | ~ ( v2_waybel_0 @ X11 @ ( k3_yellow_1 @ ( k2_struct_0 @ X9 ) ) )
      | ~ ( v1_subset_1 @ X11 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X9 ) ) ) )
      | ( v1_xboole_0 @ X11 )
      | ( r2_hidden @ X10 @ ( k2_pre_topc @ X9 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t27_yellow19])).

thf('217',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ X1 ) )
        | ( v1_xboole_0 @ sk_C_1 )
        | ~ ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( r2_hidden @ X1 @ sk_C_1 )
        | ~ ( r1_waybel_7 @ sk_A @ sk_C_1 @ X0 )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['215','216'])).

thf('218',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ X1 ) )
        | ( v1_xboole_0 @ sk_C_1 )
        | ~ ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( r2_hidden @ X1 @ sk_C_1 )
        | ~ ( r1_waybel_7 @ sk_A @ sk_C_1 @ X0 )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['217','218','219'])).

thf('221',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( r1_waybel_7 @ sk_A @ sk_C_1 @ X1 )
        | ~ ( r2_hidden @ X0 @ sk_C_1 )
        | ~ ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ( v1_xboole_0 @ sk_C_1 )
        | ( r2_hidden @ X1 @ ( k2_pre_topc @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['214','220'])).

thf('222',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ X1 ) )
        | ( v1_xboole_0 @ sk_C_1 )
        | ~ ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( r2_hidden @ X1 @ sk_C_1 )
        | ~ ( r1_waybel_7 @ sk_A @ sk_C_1 @ X0 )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['213','221'])).

thf('223',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( r1_waybel_7 @ sk_A @ sk_C_1 @ X1 )
        | ~ ( r2_hidden @ X0 @ sk_C_1 )
        | ( v1_xboole_0 @ sk_C_1 )
        | ( r2_hidden @ X1 @ ( k2_pre_topc @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['212','222'])).

thf('224',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
        | ( v1_xboole_0 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ sk_C_1 )
        | ~ ( r1_waybel_7 @ sk_A @ sk_C_1 @ X0 ) )
   <= ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['211','223'])).

thf('225',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_waybel_7 @ sk_A @ sk_C_1 @ X0 )
        | ( v1_xboole_0 @ sk_C_1 )
        | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['210','224'])).

thf('226',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_D_3 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['209','225'])).

thf('227',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( r2_hidden @ sk_D_3 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['208','226'])).

thf('228',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,
    ( ( ( r2_hidden @ sk_D_3 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['227','228'])).

thf('230',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k2_pre_topc @ X1 @ X0 ) )
      | ( r3_waybel_9 @ X1 @ ( sk_D @ X2 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t23_yellow19])).

thf('232',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['230','231'])).

thf('233',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['232','233','234'])).

thf('236',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( r3_waybel_9 @ sk_A @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ sk_D_3 )
      | ~ ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['229','235'])).

thf('237',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['192'])).

thf('238',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( r3_waybel_9 @ sk_A @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ sk_D_3 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['236','237'])).

thf('239',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,
    ( ( ( r3_waybel_9 @ sk_A @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ sk_D_3 )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['238','239'])).

thf('241',plain,
    ( ( ( r2_hidden @ sk_D_3 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['227','228'])).

thf('242',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k2_pre_topc @ X1 @ X0 ) )
      | ( v7_waybel_0 @ ( sk_D @ X2 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t23_yellow19])).

thf('244',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['242','243'])).

thf('245',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('246',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['244','245','246'])).

thf('248',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( v7_waybel_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['241','247'])).

thf('249',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['192'])).

thf('250',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( v7_waybel_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['248','249'])).

thf('251',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,
    ( ( ( v7_waybel_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['250','251'])).

thf('253',plain,
    ( ( ( r2_hidden @ sk_D_3 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['227','228'])).

thf('254',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k2_pre_topc @ X1 @ X0 ) )
      | ( v4_orders_2 @ ( sk_D @ X2 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t23_yellow19])).

thf('256',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v4_orders_2 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['254','255'])).

thf('257',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('258',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v4_orders_2 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['256','257','258'])).

thf('260',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( v4_orders_2 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['253','259'])).

thf('261',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['192'])).

thf('262',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( v4_orders_2 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['260','261'])).

thf('263',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,
    ( ( ( v4_orders_2 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['262','263'])).

thf('265',plain,
    ( ( ( r2_hidden @ sk_D_3 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['227','228'])).

thf('266',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k2_pre_topc @ X1 @ X0 ) )
      | ( l1_waybel_0 @ ( sk_D @ X2 @ X0 @ X1 ) @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t23_yellow19])).

thf('268',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['266','267'])).

thf('269',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('270',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('271',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['268','269','270'])).

thf('272',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( l1_waybel_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['265','271'])).

thf('273',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['192'])).

thf('274',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( l1_waybel_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['272','273'])).

thf('275',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,
    ( ( ( l1_waybel_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['274','275'])).

thf('277',plain,
    ( ( ( r2_hidden @ sk_D_3 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['227','228'])).

thf('278',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k2_pre_topc @ X1 @ X0 ) )
      | ( r1_waybel_0 @ X1 @ ( sk_D @ X2 @ X0 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t23_yellow19])).

thf('280',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_0 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['278','279'])).

thf('281',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('282',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('283',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_0 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['280','281','282'])).

thf('284',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( r1_waybel_0 @ sk_A @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['277','283'])).

thf('285',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['192'])).

thf('286',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( r1_waybel_0 @ sk_A @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['284','285'])).

thf('287',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('288',plain,
    ( ( ( r1_waybel_0 @ sk_A @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['286','287'])).

thf('289',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('290',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('291',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( v4_pre_topc @ X4 @ X5 )
      | ~ ( r1_waybel_0 @ X5 @ X6 @ X4 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X5 ) )
      | ( r2_hidden @ X7 @ X4 )
      | ~ ( r3_waybel_9 @ X5 @ X6 @ X7 )
      | ~ ( l1_waybel_0 @ X6 @ X5 )
      | ~ ( v7_waybel_0 @ X6 )
      | ~ ( v4_orders_2 @ X6 )
      | ( v2_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t25_yellow19])).

thf('292',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_waybel_0 @ sk_A @ X0 @ sk_B )
      | ~ ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['290','291'])).

thf('293',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('294',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('295',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_waybel_0 @ sk_A @ X0 @ sk_B )
      | ~ ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['292','293','294'])).

thf('296',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_waybel_0 @ sk_A @ X0 @ sk_B )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X1 @ sk_B )
        | ~ ( r3_waybel_9 @ sk_A @ X0 @ X1 )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['289','295'])).

thf('297',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ sk_C_1 )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( v4_orders_2 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( v7_waybel_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( l1_waybel_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ sk_A )
        | ~ ( r3_waybel_9 @ sk_A @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ X0 )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( v4_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['288','296'])).

thf('298',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ sk_C_1 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r3_waybel_9 @ sk_A @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ X0 )
        | ~ ( v7_waybel_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( v4_orders_2 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( v4_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['276','297'])).

thf('299',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( v4_orders_2 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( v7_waybel_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( r3_waybel_9 @ sk_A @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ X0 )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( v4_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(simplify,[status(thm)],['298'])).

thf('300',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ sk_C_1 )
        | ( v1_xboole_0 @ sk_C_1 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r3_waybel_9 @ sk_A @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ X0 )
        | ~ ( v7_waybel_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ( v4_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['264','299'])).

thf('301',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( v7_waybel_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( r3_waybel_9 @ sk_A @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ X0 )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( v4_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(simplify,[status(thm)],['300'])).

thf('302',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ sk_C_1 )
        | ( v1_xboole_0 @ sk_C_1 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r3_waybel_9 @ sk_A @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ X0 )
        | ( v2_struct_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ( v4_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['252','301'])).

thf('303',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( r3_waybel_9 @ sk_A @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ X0 )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( v4_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(simplify,[status(thm)],['302'])).

thf('304',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_D_3 @ sk_B )
      | ( v2_struct_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v4_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['240','303'])).

thf('305',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['192'])).

thf('306',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( r2_hidden @ sk_D_3 @ sk_B )
      | ( v2_struct_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v4_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['304','305'])).

thf('307',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
      | ( r2_hidden @ sk_D_3 @ sk_B )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( v4_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(simplify,[status(thm)],['306'])).

thf('308',plain,
    ( ( ( r2_hidden @ sk_D_3 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['227','228'])).

thf('309',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('310',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k2_pre_topc @ X1 @ X0 ) )
      | ~ ( v2_struct_0 @ ( sk_D @ X2 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t23_yellow19])).

thf('311',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['309','310'])).

thf('312',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('313',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('314',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['311','312','313'])).

thf('315',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v2_struct_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['308','314'])).

thf('316',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['192'])).

thf('317',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v2_struct_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['315','316'])).

thf('318',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('319',plain,
    ( ( ~ ( v2_struct_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['317','318'])).

thf('320',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( r2_hidden @ sk_D_3 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( v4_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['307','319'])).

thf('321',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_D_3 @ sk_B )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( v4_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(simplify,[status(thm)],['320'])).

thf('322',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('323',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( r2_hidden @ sk_D_3 @ sk_B ) )
   <= ( ( v4_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['321','322'])).

thf('324',plain,
    ( ~ ( r2_hidden @ sk_D_3 @ sk_B )
   <= ~ ( r2_hidden @ sk_D_3 @ sk_B ) ),
    inference(split,[status(esa)],['194'])).

thf('325',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
   <= ( ~ ( r2_hidden @ sk_D_3 @ sk_B )
      & ( v4_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['323','324'])).

thf('326',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
   <= ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(split,[status(esa)],['206'])).

thf('327',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ~ ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ~ ( r2_hidden @ sk_B @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_D_3 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['325','326'])).

thf('328',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','190','191','193','195','197','199','201','203','205','207','327'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VKGcGDXodM
% 0.16/0.37  % Computer   : n020.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 12:44:07 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.24/0.38  % Python version: Python 3.6.8
% 0.24/0.38  % Running in FO mode
% 0.24/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.66  % Solved by: fo/fo7.sh
% 0.24/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.66  % done 211 iterations in 0.154s
% 0.24/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.66  % SZS output start Refutation
% 0.24/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.66  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.24/0.66  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.24/0.66  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.24/0.66  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.24/0.66  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.24/0.66  thf(r1_waybel_7_type, type, r1_waybel_7: $i > $i > $i > $o).
% 0.24/0.66  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.24/0.66  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.24/0.66  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 0.24/0.66  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.24/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.66  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.24/0.66  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.24/0.66  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.24/0.66  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.24/0.66  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.24/0.66  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.24/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.66  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.24/0.66  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.24/0.66  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.24/0.66  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.24/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.66  thf(r3_waybel_9_type, type, r3_waybel_9: $i > $i > $i > $o).
% 0.24/0.66  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.24/0.66  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.24/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.66  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.24/0.66  thf(t29_yellow19, conjecture,
% 0.24/0.66    (![A:$i]:
% 0.24/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.66       ( ![B:$i]:
% 0.24/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.66           ( ( v4_pre_topc @ B @ A ) <=>
% 0.24/0.66             ( ![C:$i]:
% 0.24/0.66               ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.24/0.66                   ( v1_subset_1 @
% 0.24/0.66                     C @ 
% 0.24/0.66                     ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.24/0.66                   ( v2_waybel_0 @ C @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.24/0.66                   ( v13_waybel_0 @ C @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.24/0.66                   ( m1_subset_1 @
% 0.24/0.66                     C @ 
% 0.24/0.66                     ( k1_zfmisc_1 @
% 0.24/0.66                       ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.24/0.66                 ( ( r2_hidden @ B @ C ) =>
% 0.24/0.66                   ( ![D:$i]:
% 0.24/0.66                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.24/0.66                       ( ( r1_waybel_7 @ A @ C @ D ) => ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.24/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.66    (~( ![A:$i]:
% 0.24/0.66        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.24/0.66            ( l1_pre_topc @ A ) ) =>
% 0.24/0.66          ( ![B:$i]:
% 0.24/0.66            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.66              ( ( v4_pre_topc @ B @ A ) <=>
% 0.24/0.66                ( ![C:$i]:
% 0.24/0.66                  ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.24/0.66                      ( v1_subset_1 @
% 0.24/0.66                        C @ 
% 0.24/0.66                        ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.24/0.66                      ( v2_waybel_0 @ C @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.24/0.66                      ( v13_waybel_0 @
% 0.24/0.66                        C @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.24/0.66                      ( m1_subset_1 @
% 0.24/0.66                        C @ 
% 0.24/0.66                        ( k1_zfmisc_1 @
% 0.24/0.66                          ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.24/0.66                    ( ( r2_hidden @ B @ C ) =>
% 0.24/0.66                      ( ![D:$i]:
% 0.24/0.66                        ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.24/0.66                          ( ( r1_waybel_7 @ A @ C @ D ) =>
% 0.24/0.66                            ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ) ) )),
% 0.24/0.66    inference('cnf.neg', [status(esa)], [t29_yellow19])).
% 0.24/0.66  thf('0', plain,
% 0.24/0.66      (![X12 : $i, X13 : $i]:
% 0.24/0.66         ((v1_xboole_0 @ X12)
% 0.24/0.66          | ~ (v1_subset_1 @ X12 @ 
% 0.24/0.66               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.24/0.66          | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66          | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66          | ~ (m1_subset_1 @ X12 @ 
% 0.24/0.66               (k1_zfmisc_1 @ 
% 0.24/0.66                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.24/0.66          | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.24/0.66          | (r2_hidden @ X13 @ sk_B)
% 0.24/0.66          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.24/0.66          | ~ (r2_hidden @ sk_B @ X12)
% 0.24/0.66          | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('1', plain,
% 0.24/0.66      ((![X12 : $i, X13 : $i]:
% 0.24/0.66          ((v1_xboole_0 @ X12)
% 0.24/0.66           | ~ (v1_subset_1 @ X12 @ 
% 0.24/0.66                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.24/0.66           | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66           | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66           | ~ (m1_subset_1 @ X12 @ 
% 0.24/0.66                (k1_zfmisc_1 @ 
% 0.24/0.66                 (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.24/0.66           | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.24/0.66           | (r2_hidden @ X13 @ sk_B)
% 0.24/0.66           | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.24/0.66           | ~ (r2_hidden @ sk_B @ X12))) | 
% 0.24/0.66       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('split', [status(esa)], ['0'])).
% 0.24/0.66  thf('2', plain,
% 0.24/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf(t25_yellow19, axiom,
% 0.24/0.66    (![A:$i]:
% 0.24/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.66       ( ![B:$i]:
% 0.24/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.66           ( ( v4_pre_topc @ B @ A ) <=>
% 0.24/0.66             ( ![C:$i]:
% 0.24/0.66               ( ( ( ~( v2_struct_0 @ C ) ) & ( v4_orders_2 @ C ) & 
% 0.24/0.66                   ( v7_waybel_0 @ C ) & ( l1_waybel_0 @ C @ A ) ) =>
% 0.24/0.66                 ( ( r1_waybel_0 @ A @ C @ B ) =>
% 0.24/0.66                   ( ![D:$i]:
% 0.24/0.66                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.24/0.66                       ( ( r3_waybel_9 @ A @ C @ D ) => ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.24/0.66  thf('3', plain,
% 0.24/0.66      (![X4 : $i, X5 : $i]:
% 0.24/0.66         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.24/0.66          | (m1_subset_1 @ (sk_D_1 @ X4 @ X5) @ (u1_struct_0 @ X5))
% 0.24/0.66          | (v4_pre_topc @ X4 @ X5)
% 0.24/0.66          | ~ (l1_pre_topc @ X5)
% 0.24/0.66          | ~ (v2_pre_topc @ X5)
% 0.24/0.66          | (v2_struct_0 @ X5))),
% 0.24/0.66      inference('cnf', [status(esa)], [t25_yellow19])).
% 0.24/0.66  thf('4', plain,
% 0.24/0.66      (((v2_struct_0 @ sk_A)
% 0.24/0.66        | ~ (v2_pre_topc @ sk_A)
% 0.24/0.66        | ~ (l1_pre_topc @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.24/0.66      inference('sup-', [status(thm)], ['2', '3'])).
% 0.24/0.66  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('7', plain,
% 0.24/0.66      (((v2_struct_0 @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.24/0.66      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.24/0.66  thf('8', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('9', plain,
% 0.24/0.66      (((m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('clc', [status(thm)], ['7', '8'])).
% 0.24/0.66  thf('10', plain,
% 0.24/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('11', plain,
% 0.24/0.66      (![X4 : $i, X5 : $i]:
% 0.24/0.66         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.24/0.66          | (v4_orders_2 @ (sk_C @ X4 @ X5))
% 0.24/0.66          | (v4_pre_topc @ X4 @ X5)
% 0.24/0.66          | ~ (l1_pre_topc @ X5)
% 0.24/0.66          | ~ (v2_pre_topc @ X5)
% 0.24/0.66          | (v2_struct_0 @ X5))),
% 0.24/0.66      inference('cnf', [status(esa)], [t25_yellow19])).
% 0.24/0.66  thf('12', plain,
% 0.24/0.66      (((v2_struct_0 @ sk_A)
% 0.24/0.66        | ~ (v2_pre_topc @ sk_A)
% 0.24/0.66        | ~ (l1_pre_topc @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | (v4_orders_2 @ (sk_C @ sk_B @ sk_A)))),
% 0.24/0.66      inference('sup-', [status(thm)], ['10', '11'])).
% 0.24/0.66  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('15', plain,
% 0.24/0.66      (((v2_struct_0 @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | (v4_orders_2 @ (sk_C @ sk_B @ sk_A)))),
% 0.24/0.66      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.24/0.66  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('17', plain,
% 0.24/0.66      (((v4_orders_2 @ (sk_C @ sk_B @ sk_A)) | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('clc', [status(thm)], ['15', '16'])).
% 0.24/0.66  thf('18', plain,
% 0.24/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('19', plain,
% 0.24/0.66      (![X4 : $i, X5 : $i]:
% 0.24/0.66         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.24/0.66          | (v7_waybel_0 @ (sk_C @ X4 @ X5))
% 0.24/0.66          | (v4_pre_topc @ X4 @ X5)
% 0.24/0.66          | ~ (l1_pre_topc @ X5)
% 0.24/0.66          | ~ (v2_pre_topc @ X5)
% 0.24/0.66          | (v2_struct_0 @ X5))),
% 0.24/0.66      inference('cnf', [status(esa)], [t25_yellow19])).
% 0.24/0.66  thf('20', plain,
% 0.24/0.66      (((v2_struct_0 @ sk_A)
% 0.24/0.66        | ~ (v2_pre_topc @ sk_A)
% 0.24/0.66        | ~ (l1_pre_topc @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | (v7_waybel_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.24/0.66      inference('sup-', [status(thm)], ['18', '19'])).
% 0.24/0.66  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('23', plain,
% 0.24/0.66      (((v2_struct_0 @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | (v7_waybel_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.24/0.66      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.24/0.66  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('25', plain,
% 0.24/0.66      (((v7_waybel_0 @ (sk_C @ sk_B @ sk_A)) | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('clc', [status(thm)], ['23', '24'])).
% 0.24/0.66  thf('26', plain,
% 0.24/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('27', plain,
% 0.24/0.66      (![X4 : $i, X5 : $i]:
% 0.24/0.66         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.24/0.66          | (l1_waybel_0 @ (sk_C @ X4 @ X5) @ X5)
% 0.24/0.66          | (v4_pre_topc @ X4 @ X5)
% 0.24/0.66          | ~ (l1_pre_topc @ X5)
% 0.24/0.66          | ~ (v2_pre_topc @ X5)
% 0.24/0.66          | (v2_struct_0 @ X5))),
% 0.24/0.66      inference('cnf', [status(esa)], [t25_yellow19])).
% 0.24/0.66  thf('28', plain,
% 0.24/0.66      (((v2_struct_0 @ sk_A)
% 0.24/0.66        | ~ (v2_pre_topc @ sk_A)
% 0.24/0.66        | ~ (l1_pre_topc @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | (l1_waybel_0 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.24/0.66      inference('sup-', [status(thm)], ['26', '27'])).
% 0.24/0.66  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('31', plain,
% 0.24/0.66      (((v2_struct_0 @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | (l1_waybel_0 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.24/0.66      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.24/0.66  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('33', plain,
% 0.24/0.66      (((l1_waybel_0 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('clc', [status(thm)], ['31', '32'])).
% 0.24/0.66  thf('34', plain,
% 0.24/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('35', plain,
% 0.24/0.66      (![X4 : $i, X5 : $i]:
% 0.24/0.66         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.24/0.66          | (r1_waybel_0 @ X5 @ (sk_C @ X4 @ X5) @ X4)
% 0.24/0.66          | (v4_pre_topc @ X4 @ X5)
% 0.24/0.66          | ~ (l1_pre_topc @ X5)
% 0.24/0.66          | ~ (v2_pre_topc @ X5)
% 0.24/0.66          | (v2_struct_0 @ X5))),
% 0.24/0.66      inference('cnf', [status(esa)], [t25_yellow19])).
% 0.24/0.66  thf('36', plain,
% 0.24/0.66      (((v2_struct_0 @ sk_A)
% 0.24/0.66        | ~ (v2_pre_topc @ sk_A)
% 0.24/0.66        | ~ (l1_pre_topc @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | (r1_waybel_0 @ sk_A @ (sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.24/0.66      inference('sup-', [status(thm)], ['34', '35'])).
% 0.24/0.66  thf('37', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('39', plain,
% 0.24/0.66      (((v2_struct_0 @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | (r1_waybel_0 @ sk_A @ (sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.24/0.66      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.24/0.66  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('41', plain,
% 0.24/0.66      (((r1_waybel_0 @ sk_A @ (sk_C @ sk_B @ sk_A) @ sk_B)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('clc', [status(thm)], ['39', '40'])).
% 0.24/0.66  thf('42', plain,
% 0.24/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('43', plain,
% 0.24/0.66      (![X4 : $i, X5 : $i]:
% 0.24/0.66         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.24/0.66          | (r3_waybel_9 @ X5 @ (sk_C @ X4 @ X5) @ (sk_D_1 @ X4 @ X5))
% 0.24/0.66          | (v4_pre_topc @ X4 @ X5)
% 0.24/0.66          | ~ (l1_pre_topc @ X5)
% 0.24/0.66          | ~ (v2_pre_topc @ X5)
% 0.24/0.66          | (v2_struct_0 @ X5))),
% 0.24/0.66      inference('cnf', [status(esa)], [t25_yellow19])).
% 0.24/0.66  thf('44', plain,
% 0.24/0.66      (((v2_struct_0 @ sk_A)
% 0.24/0.66        | ~ (v2_pre_topc @ sk_A)
% 0.24/0.66        | ~ (l1_pre_topc @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | (r3_waybel_9 @ sk_A @ (sk_C @ sk_B @ sk_A) @ (sk_D_1 @ sk_B @ sk_A)))),
% 0.24/0.66      inference('sup-', [status(thm)], ['42', '43'])).
% 0.24/0.66  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('47', plain,
% 0.24/0.66      (((v2_struct_0 @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | (r3_waybel_9 @ sk_A @ (sk_C @ sk_B @ sk_A) @ (sk_D_1 @ sk_B @ sk_A)))),
% 0.24/0.66      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.24/0.66  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('49', plain,
% 0.24/0.66      (((r3_waybel_9 @ sk_A @ (sk_C @ sk_B @ sk_A) @ (sk_D_1 @ sk_B @ sk_A))
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('clc', [status(thm)], ['47', '48'])).
% 0.24/0.66  thf('50', plain,
% 0.24/0.66      (((m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('clc', [status(thm)], ['7', '8'])).
% 0.24/0.66  thf('51', plain,
% 0.24/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf(t23_yellow19, axiom,
% 0.24/0.66    (![A:$i]:
% 0.24/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.66       ( ![B:$i]:
% 0.24/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.66           ( ![C:$i]:
% 0.24/0.66             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.24/0.66               ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) ) <=>
% 0.24/0.66                 ( ?[D:$i]:
% 0.24/0.66                   ( ( r3_waybel_9 @ A @ D @ C ) & 
% 0.24/0.66                     ( r1_waybel_0 @ A @ D @ B ) & ( l1_waybel_0 @ D @ A ) & 
% 0.24/0.66                     ( v7_waybel_0 @ D ) & ( v4_orders_2 @ D ) & 
% 0.24/0.66                     ( ~( v2_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.24/0.66  thf('52', plain,
% 0.24/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.24/0.66         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.24/0.66          | ~ (r3_waybel_9 @ X1 @ X3 @ X2)
% 0.24/0.66          | ~ (r1_waybel_0 @ X1 @ X3 @ X0)
% 0.24/0.66          | ~ (l1_waybel_0 @ X3 @ X1)
% 0.24/0.66          | ~ (v7_waybel_0 @ X3)
% 0.24/0.66          | ~ (v4_orders_2 @ X3)
% 0.24/0.66          | (v2_struct_0 @ X3)
% 0.24/0.66          | (r2_hidden @ X2 @ (k2_pre_topc @ X1 @ X0))
% 0.24/0.66          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.24/0.66          | ~ (l1_pre_topc @ X1)
% 0.24/0.66          | ~ (v2_pre_topc @ X1)
% 0.24/0.66          | (v2_struct_0 @ X1))),
% 0.24/0.66      inference('cnf', [status(esa)], [t23_yellow19])).
% 0.24/0.66  thf('53', plain,
% 0.24/0.66      (![X0 : $i, X1 : $i]:
% 0.24/0.66         ((v2_struct_0 @ sk_A)
% 0.24/0.66          | ~ (v2_pre_topc @ sk_A)
% 0.24/0.66          | ~ (l1_pre_topc @ sk_A)
% 0.24/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.66          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.24/0.66          | (v2_struct_0 @ X1)
% 0.24/0.66          | ~ (v4_orders_2 @ X1)
% 0.24/0.66          | ~ (v7_waybel_0 @ X1)
% 0.24/0.66          | ~ (l1_waybel_0 @ X1 @ sk_A)
% 0.24/0.66          | ~ (r1_waybel_0 @ sk_A @ X1 @ sk_B)
% 0.24/0.66          | ~ (r3_waybel_9 @ sk_A @ X1 @ X0))),
% 0.24/0.66      inference('sup-', [status(thm)], ['51', '52'])).
% 0.24/0.66  thf('54', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('56', plain,
% 0.24/0.66      (![X0 : $i, X1 : $i]:
% 0.24/0.66         ((v2_struct_0 @ sk_A)
% 0.24/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.66          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.24/0.66          | (v2_struct_0 @ X1)
% 0.24/0.66          | ~ (v4_orders_2 @ X1)
% 0.24/0.66          | ~ (v7_waybel_0 @ X1)
% 0.24/0.66          | ~ (l1_waybel_0 @ X1 @ sk_A)
% 0.24/0.66          | ~ (r1_waybel_0 @ sk_A @ X1 @ sk_B)
% 0.24/0.66          | ~ (r3_waybel_9 @ sk_A @ X1 @ X0))),
% 0.24/0.66      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.24/0.66  thf('57', plain,
% 0.24/0.66      (![X0 : $i]:
% 0.24/0.66         ((v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_D_1 @ sk_B @ sk_A))
% 0.24/0.66          | ~ (r1_waybel_0 @ sk_A @ X0 @ sk_B)
% 0.24/0.66          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.24/0.66          | ~ (v7_waybel_0 @ X0)
% 0.24/0.66          | ~ (v4_orders_2 @ X0)
% 0.24/0.66          | (v2_struct_0 @ X0)
% 0.24/0.66          | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.24/0.66          | (v2_struct_0 @ sk_A))),
% 0.24/0.66      inference('sup-', [status(thm)], ['50', '56'])).
% 0.24/0.66  thf('58', plain,
% 0.24/0.66      (((v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | (v2_struct_0 @ sk_A)
% 0.24/0.66        | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.24/0.66        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | ~ (v4_orders_2 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | ~ (v7_waybel_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | ~ (l1_waybel_0 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.24/0.66        | ~ (r1_waybel_0 @ sk_A @ (sk_C @ sk_B @ sk_A) @ sk_B)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('sup-', [status(thm)], ['49', '57'])).
% 0.24/0.66  thf('59', plain,
% 0.24/0.66      ((~ (r1_waybel_0 @ sk_A @ (sk_C @ sk_B @ sk_A) @ sk_B)
% 0.24/0.66        | ~ (l1_waybel_0 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.24/0.66        | ~ (v7_waybel_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | ~ (v4_orders_2 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.24/0.66        | (v2_struct_0 @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('simplify', [status(thm)], ['58'])).
% 0.24/0.66  thf('60', plain,
% 0.24/0.66      (((v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | (v2_struct_0 @ sk_A)
% 0.24/0.66        | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.24/0.66        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | ~ (v4_orders_2 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | ~ (v7_waybel_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | ~ (l1_waybel_0 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.24/0.66      inference('sup-', [status(thm)], ['41', '59'])).
% 0.24/0.66  thf('61', plain,
% 0.24/0.66      ((~ (l1_waybel_0 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.24/0.66        | ~ (v7_waybel_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | ~ (v4_orders_2 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.24/0.66        | (v2_struct_0 @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('simplify', [status(thm)], ['60'])).
% 0.24/0.66  thf('62', plain,
% 0.24/0.66      (((v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | (v2_struct_0 @ sk_A)
% 0.24/0.66        | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.24/0.66        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | ~ (v4_orders_2 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | ~ (v7_waybel_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.24/0.66      inference('sup-', [status(thm)], ['33', '61'])).
% 0.24/0.66  thf('63', plain,
% 0.24/0.66      ((~ (v7_waybel_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | ~ (v4_orders_2 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.24/0.66        | (v2_struct_0 @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('simplify', [status(thm)], ['62'])).
% 0.24/0.66  thf('64', plain,
% 0.24/0.66      (((v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | (v2_struct_0 @ sk_A)
% 0.24/0.66        | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.24/0.66        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | ~ (v4_orders_2 @ (sk_C @ sk_B @ sk_A)))),
% 0.24/0.66      inference('sup-', [status(thm)], ['25', '63'])).
% 0.24/0.66  thf('65', plain,
% 0.24/0.66      ((~ (v4_orders_2 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.24/0.66        | (v2_struct_0 @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('simplify', [status(thm)], ['64'])).
% 0.24/0.66  thf('66', plain,
% 0.24/0.66      (((v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | (v2_struct_0 @ sk_A)
% 0.24/0.66        | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.24/0.66        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.24/0.66      inference('sup-', [status(thm)], ['17', '65'])).
% 0.24/0.66  thf('67', plain,
% 0.24/0.66      (((v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.24/0.66        | (v2_struct_0 @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('simplify', [status(thm)], ['66'])).
% 0.24/0.66  thf('68', plain,
% 0.24/0.66      (((m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('clc', [status(thm)], ['7', '8'])).
% 0.24/0.66  thf('69', plain,
% 0.24/0.66      (((m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('clc', [status(thm)], ['7', '8'])).
% 0.24/0.66  thf('70', plain,
% 0.24/0.66      (((v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.24/0.66        | (v2_struct_0 @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('simplify', [status(thm)], ['66'])).
% 0.24/0.66  thf('71', plain,
% 0.24/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf(t27_yellow19, axiom,
% 0.24/0.66    (![A:$i]:
% 0.24/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.66       ( ![B:$i]:
% 0.24/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.66           ( ![C:$i]:
% 0.24/0.66             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.24/0.66               ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) ) <=>
% 0.24/0.66                 ( ?[D:$i]:
% 0.24/0.66                   ( ( r1_waybel_7 @ A @ D @ C ) & ( r2_hidden @ B @ D ) & 
% 0.24/0.66                     ( m1_subset_1 @
% 0.24/0.66                       D @ 
% 0.24/0.66                       ( k1_zfmisc_1 @
% 0.24/0.66                         ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) & 
% 0.24/0.66                     ( v13_waybel_0 @ D @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.24/0.66                     ( v2_waybel_0 @ D @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.24/0.66                     ( v1_subset_1 @
% 0.24/0.66                       D @ 
% 0.24/0.66                       ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.24/0.66                     ( ~( v1_xboole_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.24/0.66  thf('72', plain,
% 0.24/0.66      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.24/0.66         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.24/0.66          | ~ (r2_hidden @ X10 @ (k2_pre_topc @ X9 @ X8))
% 0.24/0.66          | (r1_waybel_7 @ X9 @ (sk_D_2 @ X10 @ X8 @ X9) @ X10)
% 0.24/0.66          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.24/0.66          | ~ (l1_pre_topc @ X9)
% 0.24/0.66          | ~ (v2_pre_topc @ X9)
% 0.24/0.66          | (v2_struct_0 @ X9))),
% 0.24/0.66      inference('cnf', [status(esa)], [t27_yellow19])).
% 0.24/0.66  thf('73', plain,
% 0.24/0.66      (![X0 : $i]:
% 0.24/0.66         ((v2_struct_0 @ sk_A)
% 0.24/0.66          | ~ (v2_pre_topc @ sk_A)
% 0.24/0.66          | ~ (l1_pre_topc @ sk_A)
% 0.24/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.66          | (r1_waybel_7 @ sk_A @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ X0)
% 0.24/0.66          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.24/0.66      inference('sup-', [status(thm)], ['71', '72'])).
% 0.24/0.66  thf('74', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('76', plain,
% 0.24/0.66      (![X0 : $i]:
% 0.24/0.66         ((v2_struct_0 @ sk_A)
% 0.24/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.66          | (r1_waybel_7 @ sk_A @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ X0)
% 0.24/0.66          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.24/0.66      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.24/0.66  thf('77', plain,
% 0.24/0.66      (((v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | (v2_struct_0 @ sk_A)
% 0.24/0.66        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | (r1_waybel_7 @ sk_A @ 
% 0.24/0.66           (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.24/0.66           (sk_D_1 @ sk_B @ sk_A))
% 0.24/0.66        | ~ (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.24/0.66        | (v2_struct_0 @ sk_A))),
% 0.24/0.66      inference('sup-', [status(thm)], ['70', '76'])).
% 0.24/0.66  thf('78', plain,
% 0.24/0.66      ((~ (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.24/0.66        | (r1_waybel_7 @ sk_A @ 
% 0.24/0.66           (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.24/0.66           (sk_D_1 @ sk_B @ sk_A))
% 0.24/0.66        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | (v2_struct_0 @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('simplify', [status(thm)], ['77'])).
% 0.24/0.66  thf('79', plain,
% 0.24/0.66      (((v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | (v2_struct_0 @ sk_A)
% 0.24/0.66        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | (r1_waybel_7 @ sk_A @ 
% 0.24/0.66           (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.24/0.66           (sk_D_1 @ sk_B @ sk_A)))),
% 0.24/0.66      inference('sup-', [status(thm)], ['69', '78'])).
% 0.24/0.66  thf('80', plain,
% 0.24/0.66      (((r1_waybel_7 @ sk_A @ 
% 0.24/0.66         (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.24/0.66         (sk_D_1 @ sk_B @ sk_A))
% 0.24/0.66        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | (v2_struct_0 @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('simplify', [status(thm)], ['79'])).
% 0.24/0.66  thf('81', plain,
% 0.24/0.66      (((m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('clc', [status(thm)], ['7', '8'])).
% 0.24/0.66  thf('82', plain,
% 0.24/0.66      (((v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.24/0.66        | (v2_struct_0 @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('simplify', [status(thm)], ['66'])).
% 0.24/0.66  thf('83', plain,
% 0.24/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('84', plain,
% 0.24/0.66      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.24/0.66         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.24/0.66          | ~ (r2_hidden @ X10 @ (k2_pre_topc @ X9 @ X8))
% 0.24/0.66          | (r2_hidden @ X8 @ (sk_D_2 @ X10 @ X8 @ X9))
% 0.24/0.66          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.24/0.66          | ~ (l1_pre_topc @ X9)
% 0.24/0.66          | ~ (v2_pre_topc @ X9)
% 0.24/0.66          | (v2_struct_0 @ X9))),
% 0.24/0.66      inference('cnf', [status(esa)], [t27_yellow19])).
% 0.24/0.66  thf('85', plain,
% 0.24/0.66      (![X0 : $i]:
% 0.24/0.66         ((v2_struct_0 @ sk_A)
% 0.24/0.66          | ~ (v2_pre_topc @ sk_A)
% 0.24/0.66          | ~ (l1_pre_topc @ sk_A)
% 0.24/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.66          | (r2_hidden @ sk_B @ (sk_D_2 @ X0 @ sk_B @ sk_A))
% 0.24/0.66          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.24/0.66      inference('sup-', [status(thm)], ['83', '84'])).
% 0.24/0.66  thf('86', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('88', plain,
% 0.24/0.66      (![X0 : $i]:
% 0.24/0.66         ((v2_struct_0 @ sk_A)
% 0.24/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.66          | (r2_hidden @ sk_B @ (sk_D_2 @ X0 @ sk_B @ sk_A))
% 0.24/0.66          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.24/0.66      inference('demod', [status(thm)], ['85', '86', '87'])).
% 0.24/0.66  thf('89', plain,
% 0.24/0.66      (((v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | (v2_struct_0 @ sk_A)
% 0.24/0.66        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | (r2_hidden @ sk_B @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.24/0.66        | ~ (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.24/0.66        | (v2_struct_0 @ sk_A))),
% 0.24/0.66      inference('sup-', [status(thm)], ['82', '88'])).
% 0.24/0.66  thf('90', plain,
% 0.24/0.66      ((~ (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.24/0.66        | (r2_hidden @ sk_B @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.24/0.66        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | (v2_struct_0 @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('simplify', [status(thm)], ['89'])).
% 0.24/0.66  thf('91', plain,
% 0.24/0.66      (((v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | (v2_struct_0 @ sk_A)
% 0.24/0.66        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | (r2_hidden @ sk_B @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A)))),
% 0.24/0.66      inference('sup-', [status(thm)], ['81', '90'])).
% 0.24/0.66  thf('92', plain,
% 0.24/0.66      (((r2_hidden @ sk_B @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.24/0.66        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | (v2_struct_0 @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('simplify', [status(thm)], ['91'])).
% 0.24/0.66  thf('93', plain,
% 0.24/0.66      (((m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('clc', [status(thm)], ['7', '8'])).
% 0.24/0.66  thf('94', plain,
% 0.24/0.66      (((v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.24/0.66        | (v2_struct_0 @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('simplify', [status(thm)], ['66'])).
% 0.24/0.66  thf('95', plain,
% 0.24/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('96', plain,
% 0.24/0.66      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.24/0.66         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.24/0.66          | ~ (r2_hidden @ X10 @ (k2_pre_topc @ X9 @ X8))
% 0.24/0.66          | (v2_waybel_0 @ (sk_D_2 @ X10 @ X8 @ X9) @ 
% 0.24/0.66             (k3_yellow_1 @ (k2_struct_0 @ X9)))
% 0.24/0.66          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.24/0.66          | ~ (l1_pre_topc @ X9)
% 0.24/0.66          | ~ (v2_pre_topc @ X9)
% 0.24/0.66          | (v2_struct_0 @ X9))),
% 0.24/0.66      inference('cnf', [status(esa)], [t27_yellow19])).
% 0.24/0.66  thf('97', plain,
% 0.24/0.66      (![X0 : $i]:
% 0.24/0.66         ((v2_struct_0 @ sk_A)
% 0.24/0.66          | ~ (v2_pre_topc @ sk_A)
% 0.24/0.66          | ~ (l1_pre_topc @ sk_A)
% 0.24/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.66          | (v2_waybel_0 @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ 
% 0.24/0.66             (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.24/0.66      inference('sup-', [status(thm)], ['95', '96'])).
% 0.24/0.66  thf('98', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('99', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('100', plain,
% 0.24/0.66      (![X0 : $i]:
% 0.24/0.66         ((v2_struct_0 @ sk_A)
% 0.24/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.66          | (v2_waybel_0 @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ 
% 0.24/0.66             (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.24/0.66      inference('demod', [status(thm)], ['97', '98', '99'])).
% 0.24/0.66  thf('101', plain,
% 0.24/0.66      (((v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | (v2_struct_0 @ sk_A)
% 0.24/0.66        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | (v2_waybel_0 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.24/0.66           (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66        | ~ (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.24/0.66        | (v2_struct_0 @ sk_A))),
% 0.24/0.66      inference('sup-', [status(thm)], ['94', '100'])).
% 0.24/0.66  thf('102', plain,
% 0.24/0.66      ((~ (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.24/0.66        | (v2_waybel_0 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.24/0.66           (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | (v2_struct_0 @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('simplify', [status(thm)], ['101'])).
% 0.24/0.66  thf('103', plain,
% 0.24/0.66      (((v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | (v2_struct_0 @ sk_A)
% 0.24/0.66        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | (v2_waybel_0 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.24/0.66           (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.24/0.66      inference('sup-', [status(thm)], ['93', '102'])).
% 0.24/0.66  thf('104', plain,
% 0.24/0.66      (((v2_waybel_0 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.24/0.66         (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | (v2_struct_0 @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('simplify', [status(thm)], ['103'])).
% 0.24/0.66  thf('105', plain,
% 0.24/0.66      (((m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('clc', [status(thm)], ['7', '8'])).
% 0.24/0.66  thf('106', plain,
% 0.24/0.66      (((v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.24/0.66        | (v2_struct_0 @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('simplify', [status(thm)], ['66'])).
% 0.24/0.66  thf('107', plain,
% 0.24/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('108', plain,
% 0.24/0.66      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.24/0.66         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.24/0.66          | ~ (r2_hidden @ X10 @ (k2_pre_topc @ X9 @ X8))
% 0.24/0.66          | (v13_waybel_0 @ (sk_D_2 @ X10 @ X8 @ X9) @ 
% 0.24/0.66             (k3_yellow_1 @ (k2_struct_0 @ X9)))
% 0.24/0.66          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.24/0.66          | ~ (l1_pre_topc @ X9)
% 0.24/0.66          | ~ (v2_pre_topc @ X9)
% 0.24/0.66          | (v2_struct_0 @ X9))),
% 0.24/0.66      inference('cnf', [status(esa)], [t27_yellow19])).
% 0.24/0.66  thf('109', plain,
% 0.24/0.66      (![X0 : $i]:
% 0.24/0.66         ((v2_struct_0 @ sk_A)
% 0.24/0.66          | ~ (v2_pre_topc @ sk_A)
% 0.24/0.66          | ~ (l1_pre_topc @ sk_A)
% 0.24/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.66          | (v13_waybel_0 @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ 
% 0.24/0.66             (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.24/0.66      inference('sup-', [status(thm)], ['107', '108'])).
% 0.24/0.66  thf('110', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('111', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('112', plain,
% 0.24/0.66      (![X0 : $i]:
% 0.24/0.66         ((v2_struct_0 @ sk_A)
% 0.24/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.66          | (v13_waybel_0 @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ 
% 0.24/0.66             (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.24/0.66      inference('demod', [status(thm)], ['109', '110', '111'])).
% 0.24/0.66  thf('113', plain,
% 0.24/0.66      (((v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | (v2_struct_0 @ sk_A)
% 0.24/0.66        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | (v13_waybel_0 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.24/0.66           (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66        | ~ (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.24/0.66        | (v2_struct_0 @ sk_A))),
% 0.24/0.66      inference('sup-', [status(thm)], ['106', '112'])).
% 0.24/0.66  thf('114', plain,
% 0.24/0.66      ((~ (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.24/0.66        | (v13_waybel_0 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.24/0.66           (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | (v2_struct_0 @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('simplify', [status(thm)], ['113'])).
% 0.24/0.66  thf('115', plain,
% 0.24/0.66      (((v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | (v2_struct_0 @ sk_A)
% 0.24/0.66        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | (v13_waybel_0 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.24/0.66           (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.24/0.66      inference('sup-', [status(thm)], ['105', '114'])).
% 0.24/0.66  thf('116', plain,
% 0.24/0.66      (((v13_waybel_0 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.24/0.66         (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | (v2_struct_0 @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('simplify', [status(thm)], ['115'])).
% 0.24/0.66  thf('117', plain,
% 0.24/0.66      (((m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('clc', [status(thm)], ['7', '8'])).
% 0.24/0.66  thf('118', plain,
% 0.24/0.66      (((v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.24/0.66        | (v2_struct_0 @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('simplify', [status(thm)], ['66'])).
% 0.24/0.66  thf('119', plain,
% 0.24/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('120', plain,
% 0.24/0.66      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.24/0.66         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.24/0.66          | ~ (r2_hidden @ X10 @ (k2_pre_topc @ X9 @ X8))
% 0.24/0.66          | (v1_subset_1 @ (sk_D_2 @ X10 @ X8 @ X9) @ 
% 0.24/0.66             (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X9))))
% 0.24/0.66          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.24/0.66          | ~ (l1_pre_topc @ X9)
% 0.24/0.66          | ~ (v2_pre_topc @ X9)
% 0.24/0.66          | (v2_struct_0 @ X9))),
% 0.24/0.66      inference('cnf', [status(esa)], [t27_yellow19])).
% 0.24/0.66  thf('121', plain,
% 0.24/0.66      (![X0 : $i]:
% 0.24/0.66         ((v2_struct_0 @ sk_A)
% 0.24/0.66          | ~ (v2_pre_topc @ sk_A)
% 0.24/0.66          | ~ (l1_pre_topc @ sk_A)
% 0.24/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.66          | (v1_subset_1 @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ 
% 0.24/0.66             (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.24/0.66          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.24/0.66      inference('sup-', [status(thm)], ['119', '120'])).
% 0.24/0.66  thf('122', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('123', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('124', plain,
% 0.24/0.66      (![X0 : $i]:
% 0.24/0.66         ((v2_struct_0 @ sk_A)
% 0.24/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.66          | (v1_subset_1 @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ 
% 0.24/0.66             (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.24/0.66          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.24/0.66      inference('demod', [status(thm)], ['121', '122', '123'])).
% 0.24/0.66  thf('125', plain,
% 0.24/0.66      (((v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | (v2_struct_0 @ sk_A)
% 0.24/0.66        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | (v1_subset_1 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.24/0.66           (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.24/0.66        | ~ (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.24/0.66        | (v2_struct_0 @ sk_A))),
% 0.24/0.66      inference('sup-', [status(thm)], ['118', '124'])).
% 0.24/0.66  thf('126', plain,
% 0.24/0.66      ((~ (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.24/0.66        | (v1_subset_1 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.24/0.66           (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.24/0.66        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | (v2_struct_0 @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('simplify', [status(thm)], ['125'])).
% 0.24/0.66  thf('127', plain,
% 0.24/0.66      (((v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | (v2_struct_0 @ sk_A)
% 0.24/0.66        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | (v1_subset_1 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.24/0.66           (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.24/0.66      inference('sup-', [status(thm)], ['117', '126'])).
% 0.24/0.66  thf('128', plain,
% 0.24/0.66      (((v1_subset_1 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.24/0.66         (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.24/0.66        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | (v2_struct_0 @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('simplify', [status(thm)], ['127'])).
% 0.24/0.66  thf('129', plain,
% 0.24/0.66      (((m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('clc', [status(thm)], ['7', '8'])).
% 0.24/0.66  thf('130', plain,
% 0.24/0.66      (((v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.24/0.66        | (v2_struct_0 @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('simplify', [status(thm)], ['66'])).
% 0.24/0.66  thf('131', plain,
% 0.24/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('132', plain,
% 0.24/0.66      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.24/0.66         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.24/0.66          | ~ (r2_hidden @ X10 @ (k2_pre_topc @ X9 @ X8))
% 0.24/0.66          | (m1_subset_1 @ (sk_D_2 @ X10 @ X8 @ X9) @ 
% 0.24/0.66             (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X9)))))
% 0.24/0.66          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.24/0.66          | ~ (l1_pre_topc @ X9)
% 0.24/0.66          | ~ (v2_pre_topc @ X9)
% 0.24/0.66          | (v2_struct_0 @ X9))),
% 0.24/0.66      inference('cnf', [status(esa)], [t27_yellow19])).
% 0.24/0.66  thf('133', plain,
% 0.24/0.66      (![X0 : $i]:
% 0.24/0.66         ((v2_struct_0 @ sk_A)
% 0.24/0.66          | ~ (v2_pre_topc @ sk_A)
% 0.24/0.66          | ~ (l1_pre_topc @ sk_A)
% 0.24/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.66          | (m1_subset_1 @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ 
% 0.24/0.66             (k1_zfmisc_1 @ 
% 0.24/0.66              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.24/0.66          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.24/0.66      inference('sup-', [status(thm)], ['131', '132'])).
% 0.24/0.66  thf('134', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('135', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('136', plain,
% 0.24/0.66      (![X0 : $i]:
% 0.24/0.66         ((v2_struct_0 @ sk_A)
% 0.24/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.66          | (m1_subset_1 @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ 
% 0.24/0.66             (k1_zfmisc_1 @ 
% 0.24/0.66              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.24/0.66          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.24/0.66      inference('demod', [status(thm)], ['133', '134', '135'])).
% 0.24/0.66  thf('137', plain,
% 0.24/0.66      (((v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | (v2_struct_0 @ sk_A)
% 0.24/0.66        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | (m1_subset_1 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.24/0.66           (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.24/0.66        | ~ (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.24/0.66        | (v2_struct_0 @ sk_A))),
% 0.24/0.66      inference('sup-', [status(thm)], ['130', '136'])).
% 0.24/0.66  thf('138', plain,
% 0.24/0.66      ((~ (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.24/0.66        | (m1_subset_1 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.24/0.66           (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.24/0.66        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | (v2_struct_0 @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('simplify', [status(thm)], ['137'])).
% 0.24/0.66  thf('139', plain,
% 0.24/0.66      (((v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | (v2_struct_0 @ sk_A)
% 0.24/0.66        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | (m1_subset_1 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.24/0.66           (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.66      inference('sup-', [status(thm)], ['129', '138'])).
% 0.24/0.66  thf('140', plain,
% 0.24/0.66      (((m1_subset_1 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.24/0.66         (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.24/0.66        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66        | (v2_struct_0 @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('simplify', [status(thm)], ['139'])).
% 0.24/0.66  thf('141', plain,
% 0.24/0.66      ((![X12 : $i, X13 : $i]:
% 0.24/0.66          ((v1_xboole_0 @ X12)
% 0.24/0.66           | ~ (v1_subset_1 @ X12 @ 
% 0.24/0.66                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.24/0.66           | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66           | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66           | ~ (m1_subset_1 @ X12 @ 
% 0.24/0.66                (k1_zfmisc_1 @ 
% 0.24/0.66                 (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.24/0.66           | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.24/0.66           | (r2_hidden @ X13 @ sk_B)
% 0.24/0.66           | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.24/0.66           | ~ (r2_hidden @ sk_B @ X12)))
% 0.24/0.66         <= ((![X12 : $i, X13 : $i]:
% 0.24/0.66                ((v1_xboole_0 @ X12)
% 0.24/0.66                 | ~ (v1_subset_1 @ X12 @ 
% 0.24/0.66                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.24/0.66                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (m1_subset_1 @ X12 @ 
% 0.24/0.66                      (k1_zfmisc_1 @ 
% 0.24/0.66                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.24/0.66                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.24/0.66                 | (r2_hidden @ X13 @ sk_B)
% 0.24/0.66                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.24/0.66                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.24/0.66      inference('split', [status(esa)], ['0'])).
% 0.24/0.66  thf('142', plain,
% 0.24/0.66      ((![X0 : $i]:
% 0.24/0.66          ((v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66           | (v2_struct_0 @ sk_A)
% 0.24/0.66           | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66           | ~ (r2_hidden @ sk_B @ 
% 0.24/0.66                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.24/0.66           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.66           | (r2_hidden @ X0 @ sk_B)
% 0.24/0.66           | ~ (r1_waybel_7 @ sk_A @ 
% 0.24/0.66                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ X0)
% 0.24/0.66           | ~ (v13_waybel_0 @ 
% 0.24/0.66                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.24/0.66                (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66           | ~ (v2_waybel_0 @ 
% 0.24/0.66                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.24/0.66                (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66           | ~ (v1_subset_1 @ 
% 0.24/0.66                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.24/0.66                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.24/0.66           | (v1_xboole_0 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))))
% 0.24/0.66         <= ((![X12 : $i, X13 : $i]:
% 0.24/0.66                ((v1_xboole_0 @ X12)
% 0.24/0.66                 | ~ (v1_subset_1 @ X12 @ 
% 0.24/0.66                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.24/0.66                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (m1_subset_1 @ X12 @ 
% 0.24/0.66                      (k1_zfmisc_1 @ 
% 0.24/0.66                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.24/0.66                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.24/0.66                 | (r2_hidden @ X13 @ sk_B)
% 0.24/0.66                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.24/0.66                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.24/0.66      inference('sup-', [status(thm)], ['140', '141'])).
% 0.24/0.66  thf('143', plain,
% 0.24/0.66      ((![X0 : $i]:
% 0.24/0.66          ((v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66           | (v2_struct_0 @ sk_A)
% 0.24/0.66           | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66           | (v1_xboole_0 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.24/0.66           | ~ (v2_waybel_0 @ 
% 0.24/0.66                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.24/0.66                (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66           | ~ (v13_waybel_0 @ 
% 0.24/0.66                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.24/0.66                (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66           | ~ (r1_waybel_7 @ sk_A @ 
% 0.24/0.66                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ X0)
% 0.24/0.66           | (r2_hidden @ X0 @ sk_B)
% 0.24/0.66           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.66           | ~ (r2_hidden @ sk_B @ 
% 0.24/0.66                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.24/0.66           | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66           | (v2_struct_0 @ sk_A)
% 0.24/0.66           | (v4_pre_topc @ sk_B @ sk_A)))
% 0.24/0.66         <= ((![X12 : $i, X13 : $i]:
% 0.24/0.66                ((v1_xboole_0 @ X12)
% 0.24/0.66                 | ~ (v1_subset_1 @ X12 @ 
% 0.24/0.66                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.24/0.66                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (m1_subset_1 @ X12 @ 
% 0.24/0.66                      (k1_zfmisc_1 @ 
% 0.24/0.66                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.24/0.66                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.24/0.66                 | (r2_hidden @ X13 @ sk_B)
% 0.24/0.66                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.24/0.66                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.24/0.66      inference('sup-', [status(thm)], ['128', '142'])).
% 0.24/0.66  thf('144', plain,
% 0.24/0.66      ((![X0 : $i]:
% 0.24/0.66          (~ (r2_hidden @ sk_B @ 
% 0.24/0.66              (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.24/0.66           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.66           | (r2_hidden @ X0 @ sk_B)
% 0.24/0.66           | ~ (r1_waybel_7 @ sk_A @ 
% 0.24/0.66                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ X0)
% 0.24/0.66           | ~ (v13_waybel_0 @ 
% 0.24/0.66                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.24/0.66                (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66           | ~ (v2_waybel_0 @ 
% 0.24/0.66                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.24/0.66                (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66           | (v1_xboole_0 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.24/0.66           | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66           | (v2_struct_0 @ sk_A)
% 0.24/0.66           | (v4_pre_topc @ sk_B @ sk_A)))
% 0.24/0.66         <= ((![X12 : $i, X13 : $i]:
% 0.24/0.66                ((v1_xboole_0 @ X12)
% 0.24/0.66                 | ~ (v1_subset_1 @ X12 @ 
% 0.24/0.66                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.24/0.66                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (m1_subset_1 @ X12 @ 
% 0.24/0.66                      (k1_zfmisc_1 @ 
% 0.24/0.66                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.24/0.66                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.24/0.66                 | (r2_hidden @ X13 @ sk_B)
% 0.24/0.66                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.24/0.66                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.24/0.66      inference('simplify', [status(thm)], ['143'])).
% 0.24/0.66  thf('145', plain,
% 0.24/0.66      ((![X0 : $i]:
% 0.24/0.66          ((v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66           | (v2_struct_0 @ sk_A)
% 0.24/0.66           | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66           | (v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66           | (v2_struct_0 @ sk_A)
% 0.24/0.66           | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66           | (v1_xboole_0 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.24/0.66           | ~ (v2_waybel_0 @ 
% 0.24/0.66                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.24/0.66                (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66           | ~ (r1_waybel_7 @ sk_A @ 
% 0.24/0.66                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ X0)
% 0.24/0.66           | (r2_hidden @ X0 @ sk_B)
% 0.24/0.66           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.66           | ~ (r2_hidden @ sk_B @ 
% 0.24/0.66                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))))
% 0.24/0.66         <= ((![X12 : $i, X13 : $i]:
% 0.24/0.66                ((v1_xboole_0 @ X12)
% 0.24/0.66                 | ~ (v1_subset_1 @ X12 @ 
% 0.24/0.66                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.24/0.66                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (m1_subset_1 @ X12 @ 
% 0.24/0.66                      (k1_zfmisc_1 @ 
% 0.24/0.66                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.24/0.66                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.24/0.66                 | (r2_hidden @ X13 @ sk_B)
% 0.24/0.66                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.24/0.66                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.24/0.66      inference('sup-', [status(thm)], ['116', '144'])).
% 0.24/0.66  thf('146', plain,
% 0.24/0.66      ((![X0 : $i]:
% 0.24/0.66          (~ (r2_hidden @ sk_B @ 
% 0.24/0.66              (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.24/0.66           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.66           | (r2_hidden @ X0 @ sk_B)
% 0.24/0.66           | ~ (r1_waybel_7 @ sk_A @ 
% 0.24/0.66                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ X0)
% 0.24/0.66           | ~ (v2_waybel_0 @ 
% 0.24/0.66                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.24/0.66                (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66           | (v1_xboole_0 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.24/0.66           | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66           | (v2_struct_0 @ sk_A)
% 0.24/0.66           | (v4_pre_topc @ sk_B @ sk_A)))
% 0.24/0.66         <= ((![X12 : $i, X13 : $i]:
% 0.24/0.66                ((v1_xboole_0 @ X12)
% 0.24/0.66                 | ~ (v1_subset_1 @ X12 @ 
% 0.24/0.66                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.24/0.66                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (m1_subset_1 @ X12 @ 
% 0.24/0.66                      (k1_zfmisc_1 @ 
% 0.24/0.66                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.24/0.66                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.24/0.66                 | (r2_hidden @ X13 @ sk_B)
% 0.24/0.66                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.24/0.66                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.24/0.66      inference('simplify', [status(thm)], ['145'])).
% 0.24/0.66  thf('147', plain,
% 0.24/0.66      ((![X0 : $i]:
% 0.24/0.66          ((v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66           | (v2_struct_0 @ sk_A)
% 0.24/0.66           | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66           | (v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66           | (v2_struct_0 @ sk_A)
% 0.24/0.66           | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66           | (v1_xboole_0 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.24/0.66           | ~ (r1_waybel_7 @ sk_A @ 
% 0.24/0.66                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ X0)
% 0.24/0.66           | (r2_hidden @ X0 @ sk_B)
% 0.24/0.66           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.66           | ~ (r2_hidden @ sk_B @ 
% 0.24/0.66                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))))
% 0.24/0.66         <= ((![X12 : $i, X13 : $i]:
% 0.24/0.66                ((v1_xboole_0 @ X12)
% 0.24/0.66                 | ~ (v1_subset_1 @ X12 @ 
% 0.24/0.66                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.24/0.66                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (m1_subset_1 @ X12 @ 
% 0.24/0.66                      (k1_zfmisc_1 @ 
% 0.24/0.66                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.24/0.66                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.24/0.66                 | (r2_hidden @ X13 @ sk_B)
% 0.24/0.66                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.24/0.66                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.24/0.66      inference('sup-', [status(thm)], ['104', '146'])).
% 0.24/0.66  thf('148', plain,
% 0.24/0.66      ((![X0 : $i]:
% 0.24/0.66          (~ (r2_hidden @ sk_B @ 
% 0.24/0.66              (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.24/0.66           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.66           | (r2_hidden @ X0 @ sk_B)
% 0.24/0.66           | ~ (r1_waybel_7 @ sk_A @ 
% 0.24/0.66                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ X0)
% 0.24/0.66           | (v1_xboole_0 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.24/0.66           | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66           | (v2_struct_0 @ sk_A)
% 0.24/0.66           | (v4_pre_topc @ sk_B @ sk_A)))
% 0.24/0.66         <= ((![X12 : $i, X13 : $i]:
% 0.24/0.66                ((v1_xboole_0 @ X12)
% 0.24/0.66                 | ~ (v1_subset_1 @ X12 @ 
% 0.24/0.66                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.24/0.66                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (m1_subset_1 @ X12 @ 
% 0.24/0.66                      (k1_zfmisc_1 @ 
% 0.24/0.66                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.24/0.66                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.24/0.66                 | (r2_hidden @ X13 @ sk_B)
% 0.24/0.66                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.24/0.66                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.24/0.66      inference('simplify', [status(thm)], ['147'])).
% 0.24/0.66  thf('149', plain,
% 0.24/0.66      ((![X0 : $i]:
% 0.24/0.66          ((v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66           | (v2_struct_0 @ sk_A)
% 0.24/0.66           | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66           | (v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66           | (v2_struct_0 @ sk_A)
% 0.24/0.66           | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66           | (v1_xboole_0 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.24/0.66           | ~ (r1_waybel_7 @ sk_A @ 
% 0.24/0.66                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ X0)
% 0.24/0.66           | (r2_hidden @ X0 @ sk_B)
% 0.24/0.66           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.24/0.66         <= ((![X12 : $i, X13 : $i]:
% 0.24/0.66                ((v1_xboole_0 @ X12)
% 0.24/0.66                 | ~ (v1_subset_1 @ X12 @ 
% 0.24/0.66                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.24/0.66                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (m1_subset_1 @ X12 @ 
% 0.24/0.66                      (k1_zfmisc_1 @ 
% 0.24/0.66                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.24/0.66                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.24/0.66                 | (r2_hidden @ X13 @ sk_B)
% 0.24/0.66                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.24/0.66                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.24/0.66      inference('sup-', [status(thm)], ['92', '148'])).
% 0.24/0.66  thf('150', plain,
% 0.24/0.66      ((![X0 : $i]:
% 0.24/0.66          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.66           | (r2_hidden @ X0 @ sk_B)
% 0.24/0.66           | ~ (r1_waybel_7 @ sk_A @ 
% 0.24/0.66                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ X0)
% 0.24/0.66           | (v1_xboole_0 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.24/0.66           | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66           | (v2_struct_0 @ sk_A)
% 0.24/0.66           | (v4_pre_topc @ sk_B @ sk_A)))
% 0.24/0.66         <= ((![X12 : $i, X13 : $i]:
% 0.24/0.66                ((v1_xboole_0 @ X12)
% 0.24/0.66                 | ~ (v1_subset_1 @ X12 @ 
% 0.24/0.66                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.24/0.66                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (m1_subset_1 @ X12 @ 
% 0.24/0.66                      (k1_zfmisc_1 @ 
% 0.24/0.66                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.24/0.66                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.24/0.66                 | (r2_hidden @ X13 @ sk_B)
% 0.24/0.66                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.24/0.66                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.24/0.66      inference('simplify', [status(thm)], ['149'])).
% 0.24/0.66  thf('151', plain,
% 0.24/0.66      ((((v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66         | (v2_struct_0 @ sk_A)
% 0.24/0.66         | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66         | (v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66         | (v2_struct_0 @ sk_A)
% 0.24/0.66         | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66         | (v1_xboole_0 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.24/0.66         | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ sk_B)
% 0.24/0.66         | ~ (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.24/0.66         <= ((![X12 : $i, X13 : $i]:
% 0.24/0.66                ((v1_xboole_0 @ X12)
% 0.24/0.66                 | ~ (v1_subset_1 @ X12 @ 
% 0.24/0.66                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.24/0.66                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (m1_subset_1 @ X12 @ 
% 0.24/0.66                      (k1_zfmisc_1 @ 
% 0.24/0.66                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.24/0.66                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.24/0.66                 | (r2_hidden @ X13 @ sk_B)
% 0.24/0.66                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.24/0.66                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.24/0.66      inference('sup-', [status(thm)], ['80', '150'])).
% 0.24/0.66  thf('152', plain,
% 0.24/0.66      (((~ (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.24/0.66         | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ sk_B)
% 0.24/0.66         | (v1_xboole_0 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.24/0.66         | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66         | (v2_struct_0 @ sk_A)
% 0.24/0.66         | (v4_pre_topc @ sk_B @ sk_A)))
% 0.24/0.66         <= ((![X12 : $i, X13 : $i]:
% 0.24/0.66                ((v1_xboole_0 @ X12)
% 0.24/0.66                 | ~ (v1_subset_1 @ X12 @ 
% 0.24/0.66                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.24/0.66                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (m1_subset_1 @ X12 @ 
% 0.24/0.66                      (k1_zfmisc_1 @ 
% 0.24/0.66                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.24/0.66                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.24/0.66                 | (r2_hidden @ X13 @ sk_B)
% 0.24/0.66                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.24/0.66                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.24/0.66      inference('simplify', [status(thm)], ['151'])).
% 0.24/0.66  thf('153', plain,
% 0.24/0.66      ((((v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66         | (v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66         | (v2_struct_0 @ sk_A)
% 0.24/0.66         | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66         | (v1_xboole_0 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.24/0.66         | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ sk_B)))
% 0.24/0.66         <= ((![X12 : $i, X13 : $i]:
% 0.24/0.66                ((v1_xboole_0 @ X12)
% 0.24/0.66                 | ~ (v1_subset_1 @ X12 @ 
% 0.24/0.66                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.24/0.66                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (m1_subset_1 @ X12 @ 
% 0.24/0.66                      (k1_zfmisc_1 @ 
% 0.24/0.66                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.24/0.66                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.24/0.66                 | (r2_hidden @ X13 @ sk_B)
% 0.24/0.66                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.24/0.66                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.24/0.66      inference('sup-', [status(thm)], ['68', '152'])).
% 0.24/0.66  thf('154', plain,
% 0.24/0.66      ((((r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ sk_B)
% 0.24/0.66         | (v1_xboole_0 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.24/0.66         | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66         | (v2_struct_0 @ sk_A)
% 0.24/0.66         | (v4_pre_topc @ sk_B @ sk_A)))
% 0.24/0.66         <= ((![X12 : $i, X13 : $i]:
% 0.24/0.66                ((v1_xboole_0 @ X12)
% 0.24/0.66                 | ~ (v1_subset_1 @ X12 @ 
% 0.24/0.66                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.24/0.66                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (m1_subset_1 @ X12 @ 
% 0.24/0.66                      (k1_zfmisc_1 @ 
% 0.24/0.66                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.24/0.66                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.24/0.66                 | (r2_hidden @ X13 @ sk_B)
% 0.24/0.66                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.24/0.66                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.24/0.66      inference('simplify', [status(thm)], ['153'])).
% 0.24/0.66  thf('155', plain,
% 0.24/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('156', plain,
% 0.24/0.66      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.24/0.66         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.24/0.66          | ~ (r2_hidden @ X10 @ (k2_pre_topc @ X9 @ X8))
% 0.24/0.66          | ~ (v1_xboole_0 @ (sk_D_2 @ X10 @ X8 @ X9))
% 0.24/0.66          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.24/0.66          | ~ (l1_pre_topc @ X9)
% 0.24/0.66          | ~ (v2_pre_topc @ X9)
% 0.24/0.66          | (v2_struct_0 @ X9))),
% 0.24/0.66      inference('cnf', [status(esa)], [t27_yellow19])).
% 0.24/0.66  thf('157', plain,
% 0.24/0.66      (![X0 : $i]:
% 0.24/0.66         ((v2_struct_0 @ sk_A)
% 0.24/0.66          | ~ (v2_pre_topc @ sk_A)
% 0.24/0.66          | ~ (l1_pre_topc @ sk_A)
% 0.24/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.66          | ~ (v1_xboole_0 @ (sk_D_2 @ X0 @ sk_B @ sk_A))
% 0.24/0.66          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.24/0.66      inference('sup-', [status(thm)], ['155', '156'])).
% 0.24/0.66  thf('158', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('159', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('160', plain,
% 0.24/0.66      (![X0 : $i]:
% 0.24/0.66         ((v2_struct_0 @ sk_A)
% 0.24/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.66          | ~ (v1_xboole_0 @ (sk_D_2 @ X0 @ sk_B @ sk_A))
% 0.24/0.66          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.24/0.66      inference('demod', [status(thm)], ['157', '158', '159'])).
% 0.24/0.66  thf('161', plain,
% 0.24/0.66      ((((v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66         | (v2_struct_0 @ sk_A)
% 0.24/0.66         | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66         | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ sk_B)
% 0.24/0.66         | ~ (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.24/0.66         | ~ (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.24/0.66         | (v2_struct_0 @ sk_A)))
% 0.24/0.66         <= ((![X12 : $i, X13 : $i]:
% 0.24/0.66                ((v1_xboole_0 @ X12)
% 0.24/0.66                 | ~ (v1_subset_1 @ X12 @ 
% 0.24/0.66                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.24/0.66                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (m1_subset_1 @ X12 @ 
% 0.24/0.66                      (k1_zfmisc_1 @ 
% 0.24/0.66                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.24/0.66                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.24/0.66                 | (r2_hidden @ X13 @ sk_B)
% 0.24/0.66                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.24/0.66                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.24/0.66      inference('sup-', [status(thm)], ['154', '160'])).
% 0.24/0.66  thf('162', plain,
% 0.24/0.66      (((~ (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.24/0.66         | ~ (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.24/0.66         | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ sk_B)
% 0.24/0.66         | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66         | (v2_struct_0 @ sk_A)
% 0.24/0.66         | (v4_pre_topc @ sk_B @ sk_A)))
% 0.24/0.66         <= ((![X12 : $i, X13 : $i]:
% 0.24/0.66                ((v1_xboole_0 @ X12)
% 0.24/0.66                 | ~ (v1_subset_1 @ X12 @ 
% 0.24/0.66                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.24/0.66                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (m1_subset_1 @ X12 @ 
% 0.24/0.66                      (k1_zfmisc_1 @ 
% 0.24/0.66                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.24/0.66                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.24/0.66                 | (r2_hidden @ X13 @ sk_B)
% 0.24/0.66                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.24/0.66                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.24/0.66      inference('simplify', [status(thm)], ['161'])).
% 0.24/0.66  thf('163', plain,
% 0.24/0.66      ((((v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66         | (v2_struct_0 @ sk_A)
% 0.24/0.66         | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66         | (v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66         | (v2_struct_0 @ sk_A)
% 0.24/0.66         | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66         | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ sk_B)
% 0.24/0.66         | ~ (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.24/0.66         <= ((![X12 : $i, X13 : $i]:
% 0.24/0.66                ((v1_xboole_0 @ X12)
% 0.24/0.66                 | ~ (v1_subset_1 @ X12 @ 
% 0.24/0.66                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.24/0.66                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (m1_subset_1 @ X12 @ 
% 0.24/0.66                      (k1_zfmisc_1 @ 
% 0.24/0.66                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.24/0.66                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.24/0.66                 | (r2_hidden @ X13 @ sk_B)
% 0.24/0.66                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.24/0.66                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.24/0.66      inference('sup-', [status(thm)], ['67', '162'])).
% 0.24/0.66  thf('164', plain,
% 0.24/0.66      (((~ (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.24/0.66         | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ sk_B)
% 0.24/0.66         | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66         | (v2_struct_0 @ sk_A)
% 0.24/0.66         | (v4_pre_topc @ sk_B @ sk_A)))
% 0.24/0.66         <= ((![X12 : $i, X13 : $i]:
% 0.24/0.66                ((v1_xboole_0 @ X12)
% 0.24/0.66                 | ~ (v1_subset_1 @ X12 @ 
% 0.24/0.66                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.24/0.66                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (m1_subset_1 @ X12 @ 
% 0.24/0.66                      (k1_zfmisc_1 @ 
% 0.24/0.66                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.24/0.66                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.24/0.66                 | (r2_hidden @ X13 @ sk_B)
% 0.24/0.66                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.24/0.66                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.24/0.66      inference('simplify', [status(thm)], ['163'])).
% 0.24/0.66  thf('165', plain,
% 0.24/0.66      ((((v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66         | (v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66         | (v2_struct_0 @ sk_A)
% 0.24/0.66         | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66         | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ sk_B)))
% 0.24/0.66         <= ((![X12 : $i, X13 : $i]:
% 0.24/0.66                ((v1_xboole_0 @ X12)
% 0.24/0.66                 | ~ (v1_subset_1 @ X12 @ 
% 0.24/0.66                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.24/0.66                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (m1_subset_1 @ X12 @ 
% 0.24/0.66                      (k1_zfmisc_1 @ 
% 0.24/0.66                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.24/0.66                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.24/0.66                 | (r2_hidden @ X13 @ sk_B)
% 0.24/0.66                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.24/0.66                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.24/0.66      inference('sup-', [status(thm)], ['9', '164'])).
% 0.24/0.66  thf('166', plain,
% 0.24/0.66      ((((r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ sk_B)
% 0.24/0.66         | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66         | (v2_struct_0 @ sk_A)
% 0.24/0.66         | (v4_pre_topc @ sk_B @ sk_A)))
% 0.24/0.66         <= ((![X12 : $i, X13 : $i]:
% 0.24/0.66                ((v1_xboole_0 @ X12)
% 0.24/0.66                 | ~ (v1_subset_1 @ X12 @ 
% 0.24/0.66                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.24/0.66                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (m1_subset_1 @ X12 @ 
% 0.24/0.66                      (k1_zfmisc_1 @ 
% 0.24/0.66                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.24/0.66                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.24/0.66                 | (r2_hidden @ X13 @ sk_B)
% 0.24/0.66                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.24/0.66                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.24/0.66      inference('simplify', [status(thm)], ['165'])).
% 0.24/0.66  thf('167', plain,
% 0.24/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('168', plain,
% 0.24/0.66      (![X4 : $i, X5 : $i]:
% 0.24/0.66         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.24/0.66          | ~ (r2_hidden @ (sk_D_1 @ X4 @ X5) @ X4)
% 0.24/0.66          | (v4_pre_topc @ X4 @ X5)
% 0.24/0.66          | ~ (l1_pre_topc @ X5)
% 0.24/0.66          | ~ (v2_pre_topc @ X5)
% 0.24/0.66          | (v2_struct_0 @ X5))),
% 0.24/0.66      inference('cnf', [status(esa)], [t25_yellow19])).
% 0.24/0.66  thf('169', plain,
% 0.24/0.66      (((v2_struct_0 @ sk_A)
% 0.24/0.66        | ~ (v2_pre_topc @ sk_A)
% 0.24/0.66        | ~ (l1_pre_topc @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | ~ (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ sk_B))),
% 0.24/0.66      inference('sup-', [status(thm)], ['167', '168'])).
% 0.24/0.66  thf('170', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('171', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('172', plain,
% 0.24/0.66      (((v2_struct_0 @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | ~ (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ sk_B))),
% 0.24/0.66      inference('demod', [status(thm)], ['169', '170', '171'])).
% 0.24/0.66  thf('173', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('174', plain,
% 0.24/0.66      ((~ (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ sk_B)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('clc', [status(thm)], ['172', '173'])).
% 0.24/0.66  thf('175', plain,
% 0.24/0.66      ((((v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66         | (v2_struct_0 @ sk_A)
% 0.24/0.66         | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66         | (v4_pre_topc @ sk_B @ sk_A)))
% 0.24/0.66         <= ((![X12 : $i, X13 : $i]:
% 0.24/0.66                ((v1_xboole_0 @ X12)
% 0.24/0.66                 | ~ (v1_subset_1 @ X12 @ 
% 0.24/0.66                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.24/0.66                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (m1_subset_1 @ X12 @ 
% 0.24/0.66                      (k1_zfmisc_1 @ 
% 0.24/0.66                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.24/0.66                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.24/0.66                 | (r2_hidden @ X13 @ sk_B)
% 0.24/0.66                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.24/0.66                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.24/0.66      inference('sup-', [status(thm)], ['166', '174'])).
% 0.24/0.66  thf('176', plain,
% 0.24/0.66      ((((v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.24/0.66         | (v2_struct_0 @ sk_A)
% 0.24/0.66         | (v4_pre_topc @ sk_B @ sk_A)))
% 0.24/0.66         <= ((![X12 : $i, X13 : $i]:
% 0.24/0.66                ((v1_xboole_0 @ X12)
% 0.24/0.66                 | ~ (v1_subset_1 @ X12 @ 
% 0.24/0.66                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.24/0.66                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (m1_subset_1 @ X12 @ 
% 0.24/0.66                      (k1_zfmisc_1 @ 
% 0.24/0.66                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.24/0.66                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.24/0.66                 | (r2_hidden @ X13 @ sk_B)
% 0.24/0.66                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.24/0.66                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.24/0.66      inference('simplify', [status(thm)], ['175'])).
% 0.24/0.66  thf('177', plain,
% 0.24/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('178', plain,
% 0.24/0.66      (![X4 : $i, X5 : $i]:
% 0.24/0.66         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.24/0.66          | ~ (v2_struct_0 @ (sk_C @ X4 @ X5))
% 0.24/0.66          | (v4_pre_topc @ X4 @ X5)
% 0.24/0.66          | ~ (l1_pre_topc @ X5)
% 0.24/0.66          | ~ (v2_pre_topc @ X5)
% 0.24/0.66          | (v2_struct_0 @ X5))),
% 0.24/0.66      inference('cnf', [status(esa)], [t25_yellow19])).
% 0.24/0.66  thf('179', plain,
% 0.24/0.66      (((v2_struct_0 @ sk_A)
% 0.24/0.66        | ~ (v2_pre_topc @ sk_A)
% 0.24/0.66        | ~ (l1_pre_topc @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | ~ (v2_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.24/0.66      inference('sup-', [status(thm)], ['177', '178'])).
% 0.24/0.66  thf('180', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('181', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('182', plain,
% 0.24/0.66      (((v2_struct_0 @ sk_A)
% 0.24/0.66        | (v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.66        | ~ (v2_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.24/0.66      inference('demod', [status(thm)], ['179', '180', '181'])).
% 0.24/0.66  thf('183', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('184', plain,
% 0.24/0.66      ((~ (v2_struct_0 @ (sk_C @ sk_B @ sk_A)) | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('clc', [status(thm)], ['182', '183'])).
% 0.24/0.66  thf('185', plain,
% 0.24/0.66      ((((v4_pre_topc @ sk_B @ sk_A) | (v2_struct_0 @ sk_A)))
% 0.24/0.66         <= ((![X12 : $i, X13 : $i]:
% 0.24/0.66                ((v1_xboole_0 @ X12)
% 0.24/0.66                 | ~ (v1_subset_1 @ X12 @ 
% 0.24/0.66                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.24/0.66                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (m1_subset_1 @ X12 @ 
% 0.24/0.66                      (k1_zfmisc_1 @ 
% 0.24/0.66                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.24/0.66                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.24/0.66                 | (r2_hidden @ X13 @ sk_B)
% 0.24/0.66                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.24/0.66                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.24/0.66      inference('clc', [status(thm)], ['176', '184'])).
% 0.24/0.66  thf('186', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('187', plain,
% 0.24/0.66      (((v4_pre_topc @ sk_B @ sk_A))
% 0.24/0.66         <= ((![X12 : $i, X13 : $i]:
% 0.24/0.66                ((v1_xboole_0 @ X12)
% 0.24/0.66                 | ~ (v1_subset_1 @ X12 @ 
% 0.24/0.66                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.24/0.66                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66                 | ~ (m1_subset_1 @ X12 @ 
% 0.24/0.66                      (k1_zfmisc_1 @ 
% 0.24/0.66                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.24/0.66                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.24/0.66                 | (r2_hidden @ X13 @ sk_B)
% 0.24/0.66                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.24/0.66                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.24/0.66      inference('clc', [status(thm)], ['185', '186'])).
% 0.24/0.66  thf('188', plain,
% 0.24/0.66      (((r2_hidden @ sk_B @ sk_C_1) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('189', plain,
% 0.24/0.66      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.24/0.66      inference('split', [status(esa)], ['188'])).
% 0.24/0.66  thf('190', plain,
% 0.24/0.66      (~
% 0.24/0.66       (![X12 : $i, X13 : $i]:
% 0.24/0.66          ((v1_xboole_0 @ X12)
% 0.24/0.66           | ~ (v1_subset_1 @ X12 @ 
% 0.24/0.66                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.24/0.66           | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66           | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66           | ~ (m1_subset_1 @ X12 @ 
% 0.24/0.66                (k1_zfmisc_1 @ 
% 0.24/0.66                 (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.24/0.66           | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.24/0.66           | (r2_hidden @ X13 @ sk_B)
% 0.24/0.66           | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.24/0.66           | ~ (r2_hidden @ sk_B @ X12))) | 
% 0.24/0.66       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('sup-', [status(thm)], ['187', '189'])).
% 0.24/0.66  thf('191', plain,
% 0.24/0.66      (((r2_hidden @ sk_B @ sk_C_1)) | ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('split', [status(esa)], ['188'])).
% 0.24/0.66  thf('192', plain,
% 0.24/0.66      (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))
% 0.24/0.66        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('193', plain,
% 0.24/0.66      (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) | 
% 0.24/0.66       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('split', [status(esa)], ['192'])).
% 0.24/0.66  thf('194', plain,
% 0.24/0.66      ((~ (r2_hidden @ sk_D_3 @ sk_B) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('195', plain,
% 0.24/0.66      (~ ((r2_hidden @ sk_D_3 @ sk_B)) | ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('split', [status(esa)], ['194'])).
% 0.24/0.66  thf('196', plain,
% 0.24/0.66      (((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('197', plain,
% 0.24/0.66      (((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) | 
% 0.24/0.66       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('split', [status(esa)], ['196'])).
% 0.24/0.66  thf('198', plain,
% 0.24/0.66      (((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.66         (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.24/0.66        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('199', plain,
% 0.24/0.66      (((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.66         (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) | 
% 0.24/0.66       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('split', [status(esa)], ['198'])).
% 0.24/0.66  thf('200', plain,
% 0.24/0.66      (((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('201', plain,
% 0.24/0.66      (((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) | 
% 0.24/0.66       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('split', [status(esa)], ['200'])).
% 0.24/0.66  thf('202', plain,
% 0.24/0.66      (((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('203', plain,
% 0.24/0.66      (((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) | 
% 0.24/0.66       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('split', [status(esa)], ['202'])).
% 0.24/0.66  thf('204', plain,
% 0.24/0.66      (((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.66         (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.24/0.66        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('205', plain,
% 0.24/0.66      (((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.66         (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))) | 
% 0.24/0.66       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('split', [status(esa)], ['204'])).
% 0.24/0.66  thf('206', plain,
% 0.24/0.66      ((~ (v1_xboole_0 @ sk_C_1) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('207', plain,
% 0.24/0.66      (~ ((v1_xboole_0 @ sk_C_1)) | ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.66      inference('split', [status(esa)], ['206'])).
% 0.24/0.66  thf('208', plain,
% 0.24/0.66      (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A)))
% 0.24/0.66         <= (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))))),
% 0.24/0.66      inference('split', [status(esa)], ['192'])).
% 0.24/0.66  thf('209', plain,
% 0.24/0.66      (((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3))
% 0.24/0.66         <= (((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)))),
% 0.24/0.66      inference('split', [status(esa)], ['196'])).
% 0.24/0.66  thf('210', plain,
% 0.24/0.66      (((r2_hidden @ sk_B @ sk_C_1)) <= (((r2_hidden @ sk_B @ sk_C_1)))),
% 0.24/0.66      inference('split', [status(esa)], ['188'])).
% 0.24/0.66  thf('211', plain,
% 0.24/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('212', plain,
% 0.24/0.66      (((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.24/0.66         <= (((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.24/0.66      inference('split', [status(esa)], ['202'])).
% 0.24/0.66  thf('213', plain,
% 0.24/0.66      (((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.24/0.66         <= (((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.24/0.66      inference('split', [status(esa)], ['200'])).
% 0.24/0.66  thf('214', plain,
% 0.24/0.66      (((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.66         (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.24/0.66         <= (((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.66               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.66      inference('split', [status(esa)], ['204'])).
% 0.24/0.66  thf('215', plain,
% 0.24/0.66      (((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.66         (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))
% 0.24/0.66         <= (((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.66               (k1_zfmisc_1 @ 
% 0.24/0.66                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))))),
% 0.24/0.66      inference('split', [status(esa)], ['198'])).
% 0.24/0.66  thf('216', plain,
% 0.24/0.66      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.24/0.66         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.24/0.66          | ~ (r1_waybel_7 @ X9 @ X11 @ X10)
% 0.24/0.66          | ~ (r2_hidden @ X8 @ X11)
% 0.24/0.66          | ~ (m1_subset_1 @ X11 @ 
% 0.24/0.66               (k1_zfmisc_1 @ 
% 0.24/0.66                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X9)))))
% 0.24/0.66          | ~ (v13_waybel_0 @ X11 @ (k3_yellow_1 @ (k2_struct_0 @ X9)))
% 0.24/0.66          | ~ (v2_waybel_0 @ X11 @ (k3_yellow_1 @ (k2_struct_0 @ X9)))
% 0.24/0.66          | ~ (v1_subset_1 @ X11 @ 
% 0.24/0.66               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X9))))
% 0.24/0.66          | (v1_xboole_0 @ X11)
% 0.24/0.66          | (r2_hidden @ X10 @ (k2_pre_topc @ X9 @ X8))
% 0.24/0.66          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.24/0.66          | ~ (l1_pre_topc @ X9)
% 0.24/0.66          | ~ (v2_pre_topc @ X9)
% 0.24/0.66          | (v2_struct_0 @ X9))),
% 0.24/0.66      inference('cnf', [status(esa)], [t27_yellow19])).
% 0.24/0.66  thf('217', plain,
% 0.24/0.66      ((![X0 : $i, X1 : $i]:
% 0.24/0.66          ((v2_struct_0 @ sk_A)
% 0.24/0.66           | ~ (v2_pre_topc @ sk_A)
% 0.24/0.66           | ~ (l1_pre_topc @ sk_A)
% 0.24/0.66           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.66           | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ X1))
% 0.24/0.66           | (v1_xboole_0 @ sk_C_1)
% 0.24/0.66           | ~ (v1_subset_1 @ sk_C_1 @ 
% 0.24/0.66                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.24/0.66           | ~ (v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66           | ~ (v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66           | ~ (r2_hidden @ X1 @ sk_C_1)
% 0.24/0.66           | ~ (r1_waybel_7 @ sk_A @ sk_C_1 @ X0)
% 0.24/0.66           | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.24/0.66         <= (((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.66               (k1_zfmisc_1 @ 
% 0.24/0.66                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))))),
% 0.24/0.66      inference('sup-', [status(thm)], ['215', '216'])).
% 0.24/0.66  thf('218', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('219', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('220', plain,
% 0.24/0.66      ((![X0 : $i, X1 : $i]:
% 0.24/0.66          ((v2_struct_0 @ sk_A)
% 0.24/0.66           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.66           | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ X1))
% 0.24/0.66           | (v1_xboole_0 @ sk_C_1)
% 0.24/0.66           | ~ (v1_subset_1 @ sk_C_1 @ 
% 0.24/0.66                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.24/0.66           | ~ (v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66           | ~ (v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66           | ~ (r2_hidden @ X1 @ sk_C_1)
% 0.24/0.66           | ~ (r1_waybel_7 @ sk_A @ sk_C_1 @ X0)
% 0.24/0.66           | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.24/0.66         <= (((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.66               (k1_zfmisc_1 @ 
% 0.24/0.66                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))))),
% 0.24/0.66      inference('demod', [status(thm)], ['217', '218', '219'])).
% 0.24/0.66  thf('221', plain,
% 0.24/0.66      ((![X0 : $i, X1 : $i]:
% 0.24/0.66          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.24/0.66           | ~ (r1_waybel_7 @ sk_A @ sk_C_1 @ X1)
% 0.24/0.66           | ~ (r2_hidden @ X0 @ sk_C_1)
% 0.24/0.66           | ~ (v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66           | ~ (v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66           | (v1_xboole_0 @ sk_C_1)
% 0.24/0.66           | (r2_hidden @ X1 @ (k2_pre_topc @ sk_A @ X0))
% 0.24/0.66           | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.24/0.66           | (v2_struct_0 @ sk_A)))
% 0.24/0.66         <= (((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.66               (k1_zfmisc_1 @ 
% 0.24/0.66                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.66             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.66               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.66      inference('sup-', [status(thm)], ['214', '220'])).
% 0.24/0.66  thf('222', plain,
% 0.24/0.66      ((![X0 : $i, X1 : $i]:
% 0.24/0.66          ((v2_struct_0 @ sk_A)
% 0.24/0.66           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.66           | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ X1))
% 0.24/0.66           | (v1_xboole_0 @ sk_C_1)
% 0.24/0.66           | ~ (v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.24/0.66           | ~ (r2_hidden @ X1 @ sk_C_1)
% 0.24/0.66           | ~ (r1_waybel_7 @ sk_A @ sk_C_1 @ X0)
% 0.24/0.66           | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.24/0.66         <= (((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.66               (k1_zfmisc_1 @ 
% 0.24/0.66                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.66             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.66             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.66               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.66      inference('sup-', [status(thm)], ['213', '221'])).
% 0.24/0.66  thf('223', plain,
% 0.24/0.66      ((![X0 : $i, X1 : $i]:
% 0.24/0.66          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.24/0.66           | ~ (r1_waybel_7 @ sk_A @ sk_C_1 @ X1)
% 0.24/0.66           | ~ (r2_hidden @ X0 @ sk_C_1)
% 0.24/0.66           | (v1_xboole_0 @ sk_C_1)
% 0.24/0.66           | (r2_hidden @ X1 @ (k2_pre_topc @ sk_A @ X0))
% 0.24/0.66           | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.24/0.66           | (v2_struct_0 @ sk_A)))
% 0.24/0.66         <= (((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.66               (k1_zfmisc_1 @ 
% 0.24/0.66                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.66             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.66             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.66             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.66               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.66      inference('sup-', [status(thm)], ['212', '222'])).
% 0.24/0.66  thf('224', plain,
% 0.24/0.66      ((![X0 : $i]:
% 0.24/0.66          ((v2_struct_0 @ sk_A)
% 0.24/0.66           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.66           | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.24/0.66           | (v1_xboole_0 @ sk_C_1)
% 0.24/0.66           | ~ (r2_hidden @ sk_B @ sk_C_1)
% 0.24/0.66           | ~ (r1_waybel_7 @ sk_A @ sk_C_1 @ X0)))
% 0.24/0.66         <= (((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.66               (k1_zfmisc_1 @ 
% 0.24/0.66                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.66             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.66             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.66             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.66               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.66      inference('sup-', [status(thm)], ['211', '223'])).
% 0.24/0.66  thf('225', plain,
% 0.24/0.66      ((![X0 : $i]:
% 0.24/0.66          (~ (r1_waybel_7 @ sk_A @ sk_C_1 @ X0)
% 0.24/0.66           | (v1_xboole_0 @ sk_C_1)
% 0.24/0.66           | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.24/0.66           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.66           | (v2_struct_0 @ sk_A)))
% 0.24/0.66         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.24/0.66             ((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.66               (k1_zfmisc_1 @ 
% 0.24/0.66                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.66             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.66             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.66             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.66               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.66      inference('sup-', [status(thm)], ['210', '224'])).
% 0.24/0.66  thf('226', plain,
% 0.24/0.66      ((((v2_struct_0 @ sk_A)
% 0.24/0.66         | ~ (m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))
% 0.24/0.66         | (r2_hidden @ sk_D_3 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.24/0.66         | (v1_xboole_0 @ sk_C_1)))
% 0.24/0.66         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.24/0.66             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.24/0.66             ((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.66               (k1_zfmisc_1 @ 
% 0.24/0.66                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.66             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.66             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.66             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.66               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.66      inference('sup-', [status(thm)], ['209', '225'])).
% 0.24/0.66  thf('227', plain,
% 0.24/0.66      ((((v1_xboole_0 @ sk_C_1)
% 0.24/0.66         | (r2_hidden @ sk_D_3 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.24/0.66         | (v2_struct_0 @ sk_A)))
% 0.24/0.66         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.24/0.66             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.24/0.66             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.24/0.66             ((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.66               (k1_zfmisc_1 @ 
% 0.24/0.66                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.66             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.66             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.66             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.66               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.66      inference('sup-', [status(thm)], ['208', '226'])).
% 0.24/0.66  thf('228', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('229', plain,
% 0.24/0.66      ((((r2_hidden @ sk_D_3 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.24/0.66         | (v1_xboole_0 @ sk_C_1)))
% 0.24/0.66         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.24/0.66             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.24/0.66             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.24/0.66             ((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.66               (k1_zfmisc_1 @ 
% 0.24/0.66                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.66             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.66             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.66             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.66               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.66      inference('clc', [status(thm)], ['227', '228'])).
% 0.24/0.66  thf('230', plain,
% 0.24/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('231', plain,
% 0.24/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.66         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.24/0.66          | ~ (r2_hidden @ X2 @ (k2_pre_topc @ X1 @ X0))
% 0.24/0.66          | (r3_waybel_9 @ X1 @ (sk_D @ X2 @ X0 @ X1) @ X2)
% 0.24/0.66          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.24/0.66          | ~ (l1_pre_topc @ X1)
% 0.24/0.66          | ~ (v2_pre_topc @ X1)
% 0.24/0.66          | (v2_struct_0 @ X1))),
% 0.24/0.66      inference('cnf', [status(esa)], [t23_yellow19])).
% 0.24/0.66  thf('232', plain,
% 0.24/0.66      (![X0 : $i]:
% 0.24/0.66         ((v2_struct_0 @ sk_A)
% 0.24/0.66          | ~ (v2_pre_topc @ sk_A)
% 0.24/0.66          | ~ (l1_pre_topc @ sk_A)
% 0.24/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.66          | (r3_waybel_9 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ X0)
% 0.24/0.66          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.24/0.66      inference('sup-', [status(thm)], ['230', '231'])).
% 0.24/0.66  thf('233', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('234', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('235', plain,
% 0.24/0.66      (![X0 : $i]:
% 0.24/0.66         ((v2_struct_0 @ sk_A)
% 0.24/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.66          | (r3_waybel_9 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ X0)
% 0.24/0.66          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.24/0.66      inference('demod', [status(thm)], ['232', '233', '234'])).
% 0.24/0.66  thf('236', plain,
% 0.24/0.66      ((((v1_xboole_0 @ sk_C_1)
% 0.24/0.66         | (r3_waybel_9 @ sk_A @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ sk_D_3)
% 0.24/0.66         | ~ (m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))
% 0.24/0.66         | (v2_struct_0 @ sk_A)))
% 0.24/0.66         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.24/0.66             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.24/0.66             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.24/0.66             ((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.66               (k1_zfmisc_1 @ 
% 0.24/0.66                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.66             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.66             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.66             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.66               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.66      inference('sup-', [status(thm)], ['229', '235'])).
% 0.24/0.66  thf('237', plain,
% 0.24/0.66      (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A)))
% 0.24/0.66         <= (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))))),
% 0.24/0.66      inference('split', [status(esa)], ['192'])).
% 0.24/0.66  thf('238', plain,
% 0.24/0.66      ((((v1_xboole_0 @ sk_C_1)
% 0.24/0.66         | (r3_waybel_9 @ sk_A @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ sk_D_3)
% 0.24/0.66         | (v2_struct_0 @ sk_A)))
% 0.24/0.66         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.24/0.66             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.24/0.66             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.24/0.66             ((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.66               (k1_zfmisc_1 @ 
% 0.24/0.66                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.66             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.66             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.66             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.66               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.66      inference('demod', [status(thm)], ['236', '237'])).
% 0.24/0.66  thf('239', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('240', plain,
% 0.24/0.66      ((((r3_waybel_9 @ sk_A @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ sk_D_3)
% 0.24/0.66         | (v1_xboole_0 @ sk_C_1)))
% 0.24/0.66         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.24/0.66             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.24/0.66             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.24/0.66             ((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.66               (k1_zfmisc_1 @ 
% 0.24/0.66                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.66             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.66             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.66             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.66               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.66      inference('clc', [status(thm)], ['238', '239'])).
% 0.24/0.66  thf('241', plain,
% 0.24/0.66      ((((r2_hidden @ sk_D_3 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.24/0.66         | (v1_xboole_0 @ sk_C_1)))
% 0.24/0.66         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.24/0.66             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.24/0.66             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.24/0.66             ((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.66               (k1_zfmisc_1 @ 
% 0.24/0.66                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.66             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.66             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.66             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.66               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.66      inference('clc', [status(thm)], ['227', '228'])).
% 0.24/0.66  thf('242', plain,
% 0.24/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('243', plain,
% 0.24/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.66         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.24/0.66          | ~ (r2_hidden @ X2 @ (k2_pre_topc @ X1 @ X0))
% 0.24/0.66          | (v7_waybel_0 @ (sk_D @ X2 @ X0 @ X1))
% 0.24/0.66          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.24/0.66          | ~ (l1_pre_topc @ X1)
% 0.24/0.66          | ~ (v2_pre_topc @ X1)
% 0.24/0.66          | (v2_struct_0 @ X1))),
% 0.24/0.66      inference('cnf', [status(esa)], [t23_yellow19])).
% 0.24/0.66  thf('244', plain,
% 0.24/0.66      (![X0 : $i]:
% 0.24/0.66         ((v2_struct_0 @ sk_A)
% 0.24/0.66          | ~ (v2_pre_topc @ sk_A)
% 0.24/0.66          | ~ (l1_pre_topc @ sk_A)
% 0.24/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.66          | (v7_waybel_0 @ (sk_D @ X0 @ sk_B @ sk_A))
% 0.24/0.66          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.24/0.66      inference('sup-', [status(thm)], ['242', '243'])).
% 0.24/0.66  thf('245', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('246', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('247', plain,
% 0.24/0.66      (![X0 : $i]:
% 0.24/0.66         ((v2_struct_0 @ sk_A)
% 0.24/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.66          | (v7_waybel_0 @ (sk_D @ X0 @ sk_B @ sk_A))
% 0.24/0.66          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.24/0.66      inference('demod', [status(thm)], ['244', '245', '246'])).
% 0.24/0.66  thf('248', plain,
% 0.24/0.66      ((((v1_xboole_0 @ sk_C_1)
% 0.24/0.66         | (v7_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.24/0.66         | ~ (m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))
% 0.24/0.66         | (v2_struct_0 @ sk_A)))
% 0.24/0.66         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.24/0.66             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.24/0.66             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.24/0.66             ((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.66               (k1_zfmisc_1 @ 
% 0.24/0.66                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.66             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.66             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.66             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.66               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.66      inference('sup-', [status(thm)], ['241', '247'])).
% 0.24/0.66  thf('249', plain,
% 0.24/0.66      (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A)))
% 0.24/0.66         <= (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))))),
% 0.24/0.66      inference('split', [status(esa)], ['192'])).
% 0.24/0.66  thf('250', plain,
% 0.24/0.66      ((((v1_xboole_0 @ sk_C_1)
% 0.24/0.66         | (v7_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.24/0.66         | (v2_struct_0 @ sk_A)))
% 0.24/0.66         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.24/0.66             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.24/0.66             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.24/0.66             ((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.66               (k1_zfmisc_1 @ 
% 0.24/0.66                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.66             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.66             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.66             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.66               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.66      inference('demod', [status(thm)], ['248', '249'])).
% 0.24/0.66  thf('251', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('252', plain,
% 0.24/0.66      ((((v7_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A)) | (v1_xboole_0 @ sk_C_1)))
% 0.24/0.66         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.24/0.66             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.24/0.66             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.24/0.66             ((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.66               (k1_zfmisc_1 @ 
% 0.24/0.66                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.66             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.66             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.66             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.66               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.66      inference('clc', [status(thm)], ['250', '251'])).
% 0.24/0.66  thf('253', plain,
% 0.24/0.66      ((((r2_hidden @ sk_D_3 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.24/0.66         | (v1_xboole_0 @ sk_C_1)))
% 0.24/0.66         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.24/0.66             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.24/0.66             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.24/0.66             ((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.66               (k1_zfmisc_1 @ 
% 0.24/0.66                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.66             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.66             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.66             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.66               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.66      inference('clc', [status(thm)], ['227', '228'])).
% 0.24/0.66  thf('254', plain,
% 0.24/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('255', plain,
% 0.24/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.66         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.24/0.66          | ~ (r2_hidden @ X2 @ (k2_pre_topc @ X1 @ X0))
% 0.24/0.66          | (v4_orders_2 @ (sk_D @ X2 @ X0 @ X1))
% 0.24/0.66          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.24/0.66          | ~ (l1_pre_topc @ X1)
% 0.24/0.66          | ~ (v2_pre_topc @ X1)
% 0.24/0.66          | (v2_struct_0 @ X1))),
% 0.24/0.66      inference('cnf', [status(esa)], [t23_yellow19])).
% 0.24/0.66  thf('256', plain,
% 0.24/0.66      (![X0 : $i]:
% 0.24/0.66         ((v2_struct_0 @ sk_A)
% 0.24/0.66          | ~ (v2_pre_topc @ sk_A)
% 0.24/0.66          | ~ (l1_pre_topc @ sk_A)
% 0.24/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.66          | (v4_orders_2 @ (sk_D @ X0 @ sk_B @ sk_A))
% 0.24/0.66          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.24/0.66      inference('sup-', [status(thm)], ['254', '255'])).
% 0.24/0.66  thf('257', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('258', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.66  thf('259', plain,
% 0.24/0.66      (![X0 : $i]:
% 0.24/0.66         ((v2_struct_0 @ sk_A)
% 0.24/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.66          | (v4_orders_2 @ (sk_D @ X0 @ sk_B @ sk_A))
% 0.24/0.66          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.24/0.66      inference('demod', [status(thm)], ['256', '257', '258'])).
% 0.24/0.66  thf('260', plain,
% 0.24/0.66      ((((v1_xboole_0 @ sk_C_1)
% 0.24/0.66         | (v4_orders_2 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.24/0.66         | ~ (m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))
% 0.24/0.66         | (v2_struct_0 @ sk_A)))
% 0.24/0.66         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.24/0.66             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.24/0.66             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.24/0.66             ((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.66               (k1_zfmisc_1 @ 
% 0.24/0.67                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.67             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.67      inference('sup-', [status(thm)], ['253', '259'])).
% 0.24/0.67  thf('261', plain,
% 0.24/0.67      (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A)))
% 0.24/0.67         <= (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))))),
% 0.24/0.67      inference('split', [status(esa)], ['192'])).
% 0.24/0.67  thf('262', plain,
% 0.24/0.67      ((((v1_xboole_0 @ sk_C_1)
% 0.24/0.67         | (v4_orders_2 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.24/0.67         | (v2_struct_0 @ sk_A)))
% 0.24/0.67         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.24/0.67             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (k1_zfmisc_1 @ 
% 0.24/0.67                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.67             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.67      inference('demod', [status(thm)], ['260', '261'])).
% 0.24/0.67  thf('263', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.67  thf('264', plain,
% 0.24/0.67      ((((v4_orders_2 @ (sk_D @ sk_D_3 @ sk_B @ sk_A)) | (v1_xboole_0 @ sk_C_1)))
% 0.24/0.67         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.24/0.67             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (k1_zfmisc_1 @ 
% 0.24/0.67                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.67             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.67      inference('clc', [status(thm)], ['262', '263'])).
% 0.24/0.67  thf('265', plain,
% 0.24/0.67      ((((r2_hidden @ sk_D_3 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.24/0.67         | (v1_xboole_0 @ sk_C_1)))
% 0.24/0.67         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.24/0.67             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (k1_zfmisc_1 @ 
% 0.24/0.67                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.67             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.67      inference('clc', [status(thm)], ['227', '228'])).
% 0.24/0.67  thf('266', plain,
% 0.24/0.67      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.67  thf('267', plain,
% 0.24/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.67         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.24/0.67          | ~ (r2_hidden @ X2 @ (k2_pre_topc @ X1 @ X0))
% 0.24/0.67          | (l1_waybel_0 @ (sk_D @ X2 @ X0 @ X1) @ X1)
% 0.24/0.67          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.24/0.67          | ~ (l1_pre_topc @ X1)
% 0.24/0.67          | ~ (v2_pre_topc @ X1)
% 0.24/0.67          | (v2_struct_0 @ X1))),
% 0.24/0.67      inference('cnf', [status(esa)], [t23_yellow19])).
% 0.24/0.67  thf('268', plain,
% 0.24/0.67      (![X0 : $i]:
% 0.24/0.67         ((v2_struct_0 @ sk_A)
% 0.24/0.67          | ~ (v2_pre_topc @ sk_A)
% 0.24/0.67          | ~ (l1_pre_topc @ sk_A)
% 0.24/0.67          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.67          | (l1_waybel_0 @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A)
% 0.24/0.67          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.24/0.67      inference('sup-', [status(thm)], ['266', '267'])).
% 0.24/0.67  thf('269', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.67  thf('270', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.67  thf('271', plain,
% 0.24/0.67      (![X0 : $i]:
% 0.24/0.67         ((v2_struct_0 @ sk_A)
% 0.24/0.67          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.67          | (l1_waybel_0 @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A)
% 0.24/0.67          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.24/0.67      inference('demod', [status(thm)], ['268', '269', '270'])).
% 0.24/0.67  thf('272', plain,
% 0.24/0.67      ((((v1_xboole_0 @ sk_C_1)
% 0.24/0.67         | (l1_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ sk_A)
% 0.24/0.67         | ~ (m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))
% 0.24/0.67         | (v2_struct_0 @ sk_A)))
% 0.24/0.67         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.24/0.67             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (k1_zfmisc_1 @ 
% 0.24/0.67                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.67             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.67      inference('sup-', [status(thm)], ['265', '271'])).
% 0.24/0.67  thf('273', plain,
% 0.24/0.67      (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A)))
% 0.24/0.67         <= (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))))),
% 0.24/0.67      inference('split', [status(esa)], ['192'])).
% 0.24/0.67  thf('274', plain,
% 0.24/0.67      ((((v1_xboole_0 @ sk_C_1)
% 0.24/0.67         | (l1_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ sk_A)
% 0.24/0.67         | (v2_struct_0 @ sk_A)))
% 0.24/0.67         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.24/0.67             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (k1_zfmisc_1 @ 
% 0.24/0.67                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.67             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.67      inference('demod', [status(thm)], ['272', '273'])).
% 0.24/0.67  thf('275', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.67  thf('276', plain,
% 0.24/0.67      ((((l1_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ sk_A)
% 0.24/0.67         | (v1_xboole_0 @ sk_C_1)))
% 0.24/0.67         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.24/0.67             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (k1_zfmisc_1 @ 
% 0.24/0.67                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.67             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.67      inference('clc', [status(thm)], ['274', '275'])).
% 0.24/0.67  thf('277', plain,
% 0.24/0.67      ((((r2_hidden @ sk_D_3 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.24/0.67         | (v1_xboole_0 @ sk_C_1)))
% 0.24/0.67         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.24/0.67             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (k1_zfmisc_1 @ 
% 0.24/0.67                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.67             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.67      inference('clc', [status(thm)], ['227', '228'])).
% 0.24/0.67  thf('278', plain,
% 0.24/0.67      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.67  thf('279', plain,
% 0.24/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.67         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.24/0.67          | ~ (r2_hidden @ X2 @ (k2_pre_topc @ X1 @ X0))
% 0.24/0.67          | (r1_waybel_0 @ X1 @ (sk_D @ X2 @ X0 @ X1) @ X0)
% 0.24/0.67          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.24/0.67          | ~ (l1_pre_topc @ X1)
% 0.24/0.67          | ~ (v2_pre_topc @ X1)
% 0.24/0.67          | (v2_struct_0 @ X1))),
% 0.24/0.67      inference('cnf', [status(esa)], [t23_yellow19])).
% 0.24/0.67  thf('280', plain,
% 0.24/0.67      (![X0 : $i]:
% 0.24/0.67         ((v2_struct_0 @ sk_A)
% 0.24/0.67          | ~ (v2_pre_topc @ sk_A)
% 0.24/0.67          | ~ (l1_pre_topc @ sk_A)
% 0.24/0.67          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.67          | (r1_waybel_0 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_B)
% 0.24/0.67          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.24/0.67      inference('sup-', [status(thm)], ['278', '279'])).
% 0.24/0.67  thf('281', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.67  thf('282', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.67  thf('283', plain,
% 0.24/0.67      (![X0 : $i]:
% 0.24/0.67         ((v2_struct_0 @ sk_A)
% 0.24/0.67          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.67          | (r1_waybel_0 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_B)
% 0.24/0.67          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.24/0.67      inference('demod', [status(thm)], ['280', '281', '282'])).
% 0.24/0.67  thf('284', plain,
% 0.24/0.67      ((((v1_xboole_0 @ sk_C_1)
% 0.24/0.67         | (r1_waybel_0 @ sk_A @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ sk_B)
% 0.24/0.67         | ~ (m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))
% 0.24/0.67         | (v2_struct_0 @ sk_A)))
% 0.24/0.67         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.24/0.67             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (k1_zfmisc_1 @ 
% 0.24/0.67                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.67             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.67      inference('sup-', [status(thm)], ['277', '283'])).
% 0.24/0.67  thf('285', plain,
% 0.24/0.67      (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A)))
% 0.24/0.67         <= (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))))),
% 0.24/0.67      inference('split', [status(esa)], ['192'])).
% 0.24/0.67  thf('286', plain,
% 0.24/0.67      ((((v1_xboole_0 @ sk_C_1)
% 0.24/0.67         | (r1_waybel_0 @ sk_A @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ sk_B)
% 0.24/0.67         | (v2_struct_0 @ sk_A)))
% 0.24/0.67         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.24/0.67             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (k1_zfmisc_1 @ 
% 0.24/0.67                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.67             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.67      inference('demod', [status(thm)], ['284', '285'])).
% 0.24/0.67  thf('287', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.67  thf('288', plain,
% 0.24/0.67      ((((r1_waybel_0 @ sk_A @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ sk_B)
% 0.24/0.67         | (v1_xboole_0 @ sk_C_1)))
% 0.24/0.67         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.24/0.67             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (k1_zfmisc_1 @ 
% 0.24/0.67                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.67             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.67      inference('clc', [status(thm)], ['286', '287'])).
% 0.24/0.67  thf('289', plain,
% 0.24/0.67      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.24/0.67      inference('split', [status(esa)], ['0'])).
% 0.24/0.67  thf('290', plain,
% 0.24/0.67      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.67  thf('291', plain,
% 0.24/0.67      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.24/0.67         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.24/0.67          | ~ (v4_pre_topc @ X4 @ X5)
% 0.24/0.67          | ~ (r1_waybel_0 @ X5 @ X6 @ X4)
% 0.24/0.67          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X5))
% 0.24/0.67          | (r2_hidden @ X7 @ X4)
% 0.24/0.67          | ~ (r3_waybel_9 @ X5 @ X6 @ X7)
% 0.24/0.67          | ~ (l1_waybel_0 @ X6 @ X5)
% 0.24/0.67          | ~ (v7_waybel_0 @ X6)
% 0.24/0.67          | ~ (v4_orders_2 @ X6)
% 0.24/0.67          | (v2_struct_0 @ X6)
% 0.24/0.67          | ~ (l1_pre_topc @ X5)
% 0.24/0.67          | ~ (v2_pre_topc @ X5)
% 0.24/0.67          | (v2_struct_0 @ X5))),
% 0.24/0.67      inference('cnf', [status(esa)], [t25_yellow19])).
% 0.24/0.67  thf('292', plain,
% 0.24/0.67      (![X0 : $i, X1 : $i]:
% 0.24/0.67         ((v2_struct_0 @ sk_A)
% 0.24/0.67          | ~ (v2_pre_topc @ sk_A)
% 0.24/0.67          | ~ (l1_pre_topc @ sk_A)
% 0.24/0.67          | (v2_struct_0 @ X0)
% 0.24/0.67          | ~ (v4_orders_2 @ X0)
% 0.24/0.67          | ~ (v7_waybel_0 @ X0)
% 0.24/0.67          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.24/0.67          | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 0.24/0.67          | (r2_hidden @ X1 @ sk_B)
% 0.24/0.67          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.24/0.67          | ~ (r1_waybel_0 @ sk_A @ X0 @ sk_B)
% 0.24/0.67          | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.67      inference('sup-', [status(thm)], ['290', '291'])).
% 0.24/0.67  thf('293', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.67  thf('294', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.67  thf('295', plain,
% 0.24/0.67      (![X0 : $i, X1 : $i]:
% 0.24/0.67         ((v2_struct_0 @ sk_A)
% 0.24/0.67          | (v2_struct_0 @ X0)
% 0.24/0.67          | ~ (v4_orders_2 @ X0)
% 0.24/0.67          | ~ (v7_waybel_0 @ X0)
% 0.24/0.67          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.24/0.67          | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 0.24/0.67          | (r2_hidden @ X1 @ sk_B)
% 0.24/0.67          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.24/0.67          | ~ (r1_waybel_0 @ sk_A @ X0 @ sk_B)
% 0.24/0.67          | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.67      inference('demod', [status(thm)], ['292', '293', '294'])).
% 0.24/0.67  thf('296', plain,
% 0.24/0.67      ((![X0 : $i, X1 : $i]:
% 0.24/0.67          (~ (r1_waybel_0 @ sk_A @ X0 @ sk_B)
% 0.24/0.67           | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.24/0.67           | (r2_hidden @ X1 @ sk_B)
% 0.24/0.67           | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 0.24/0.67           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.24/0.67           | ~ (v7_waybel_0 @ X0)
% 0.24/0.67           | ~ (v4_orders_2 @ X0)
% 0.24/0.67           | (v2_struct_0 @ X0)
% 0.24/0.67           | (v2_struct_0 @ sk_A)))
% 0.24/0.67         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.24/0.67      inference('sup-', [status(thm)], ['289', '295'])).
% 0.24/0.67  thf('297', plain,
% 0.24/0.67      ((![X0 : $i]:
% 0.24/0.67          ((v1_xboole_0 @ sk_C_1)
% 0.24/0.67           | (v2_struct_0 @ sk_A)
% 0.24/0.67           | (v2_struct_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.24/0.67           | ~ (v4_orders_2 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.24/0.67           | ~ (v7_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.24/0.67           | ~ (l1_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ sk_A)
% 0.24/0.67           | ~ (r3_waybel_9 @ sk_A @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ X0)
% 0.24/0.67           | (r2_hidden @ X0 @ sk_B)
% 0.24/0.67           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.24/0.67         <= (((v4_pre_topc @ sk_B @ sk_A)) & 
% 0.24/0.67             ((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.24/0.67             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (k1_zfmisc_1 @ 
% 0.24/0.67                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.67             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.67      inference('sup-', [status(thm)], ['288', '296'])).
% 0.24/0.67  thf('298', plain,
% 0.24/0.67      ((![X0 : $i]:
% 0.24/0.67          ((v1_xboole_0 @ sk_C_1)
% 0.24/0.67           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.67           | (r2_hidden @ X0 @ sk_B)
% 0.24/0.67           | ~ (r3_waybel_9 @ sk_A @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ X0)
% 0.24/0.67           | ~ (v7_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.24/0.67           | ~ (v4_orders_2 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.24/0.67           | (v2_struct_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.24/0.67           | (v2_struct_0 @ sk_A)
% 0.24/0.67           | (v1_xboole_0 @ sk_C_1)))
% 0.24/0.67         <= (((v4_pre_topc @ sk_B @ sk_A)) & 
% 0.24/0.67             ((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.24/0.67             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (k1_zfmisc_1 @ 
% 0.24/0.67                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.67             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.67      inference('sup-', [status(thm)], ['276', '297'])).
% 0.24/0.67  thf('299', plain,
% 0.24/0.67      ((![X0 : $i]:
% 0.24/0.67          ((v2_struct_0 @ sk_A)
% 0.24/0.67           | (v2_struct_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.24/0.67           | ~ (v4_orders_2 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.24/0.67           | ~ (v7_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.24/0.67           | ~ (r3_waybel_9 @ sk_A @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ X0)
% 0.24/0.67           | (r2_hidden @ X0 @ sk_B)
% 0.24/0.67           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.67           | (v1_xboole_0 @ sk_C_1)))
% 0.24/0.67         <= (((v4_pre_topc @ sk_B @ sk_A)) & 
% 0.24/0.67             ((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.24/0.67             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (k1_zfmisc_1 @ 
% 0.24/0.67                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.67             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.67      inference('simplify', [status(thm)], ['298'])).
% 0.24/0.67  thf('300', plain,
% 0.24/0.67      ((![X0 : $i]:
% 0.24/0.67          ((v1_xboole_0 @ sk_C_1)
% 0.24/0.67           | (v1_xboole_0 @ sk_C_1)
% 0.24/0.67           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.67           | (r2_hidden @ X0 @ sk_B)
% 0.24/0.67           | ~ (r3_waybel_9 @ sk_A @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ X0)
% 0.24/0.67           | ~ (v7_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.24/0.67           | (v2_struct_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.24/0.67           | (v2_struct_0 @ sk_A)))
% 0.24/0.67         <= (((v4_pre_topc @ sk_B @ sk_A)) & 
% 0.24/0.67             ((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.24/0.67             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (k1_zfmisc_1 @ 
% 0.24/0.67                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.67             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.67      inference('sup-', [status(thm)], ['264', '299'])).
% 0.24/0.67  thf('301', plain,
% 0.24/0.67      ((![X0 : $i]:
% 0.24/0.67          ((v2_struct_0 @ sk_A)
% 0.24/0.67           | (v2_struct_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.24/0.67           | ~ (v7_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.24/0.67           | ~ (r3_waybel_9 @ sk_A @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ X0)
% 0.24/0.67           | (r2_hidden @ X0 @ sk_B)
% 0.24/0.67           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.67           | (v1_xboole_0 @ sk_C_1)))
% 0.24/0.67         <= (((v4_pre_topc @ sk_B @ sk_A)) & 
% 0.24/0.67             ((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.24/0.67             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (k1_zfmisc_1 @ 
% 0.24/0.67                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.67             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.67      inference('simplify', [status(thm)], ['300'])).
% 0.24/0.67  thf('302', plain,
% 0.24/0.67      ((![X0 : $i]:
% 0.24/0.67          ((v1_xboole_0 @ sk_C_1)
% 0.24/0.67           | (v1_xboole_0 @ sk_C_1)
% 0.24/0.67           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.67           | (r2_hidden @ X0 @ sk_B)
% 0.24/0.67           | ~ (r3_waybel_9 @ sk_A @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ X0)
% 0.24/0.67           | (v2_struct_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.24/0.67           | (v2_struct_0 @ sk_A)))
% 0.24/0.67         <= (((v4_pre_topc @ sk_B @ sk_A)) & 
% 0.24/0.67             ((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.24/0.67             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (k1_zfmisc_1 @ 
% 0.24/0.67                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.67             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.67      inference('sup-', [status(thm)], ['252', '301'])).
% 0.24/0.67  thf('303', plain,
% 0.24/0.67      ((![X0 : $i]:
% 0.24/0.67          ((v2_struct_0 @ sk_A)
% 0.24/0.67           | (v2_struct_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.24/0.67           | ~ (r3_waybel_9 @ sk_A @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ X0)
% 0.24/0.67           | (r2_hidden @ X0 @ sk_B)
% 0.24/0.67           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.67           | (v1_xboole_0 @ sk_C_1)))
% 0.24/0.67         <= (((v4_pre_topc @ sk_B @ sk_A)) & 
% 0.24/0.67             ((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.24/0.67             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (k1_zfmisc_1 @ 
% 0.24/0.67                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.67             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.67      inference('simplify', [status(thm)], ['302'])).
% 0.24/0.67  thf('304', plain,
% 0.24/0.67      ((((v1_xboole_0 @ sk_C_1)
% 0.24/0.67         | (v1_xboole_0 @ sk_C_1)
% 0.24/0.67         | ~ (m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))
% 0.24/0.67         | (r2_hidden @ sk_D_3 @ sk_B)
% 0.24/0.67         | (v2_struct_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.24/0.67         | (v2_struct_0 @ sk_A)))
% 0.24/0.67         <= (((v4_pre_topc @ sk_B @ sk_A)) & 
% 0.24/0.67             ((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.24/0.67             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (k1_zfmisc_1 @ 
% 0.24/0.67                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.67             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.67      inference('sup-', [status(thm)], ['240', '303'])).
% 0.24/0.67  thf('305', plain,
% 0.24/0.67      (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A)))
% 0.24/0.67         <= (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))))),
% 0.24/0.67      inference('split', [status(esa)], ['192'])).
% 0.24/0.67  thf('306', plain,
% 0.24/0.67      ((((v1_xboole_0 @ sk_C_1)
% 0.24/0.67         | (v1_xboole_0 @ sk_C_1)
% 0.24/0.67         | (r2_hidden @ sk_D_3 @ sk_B)
% 0.24/0.67         | (v2_struct_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.24/0.67         | (v2_struct_0 @ sk_A)))
% 0.24/0.67         <= (((v4_pre_topc @ sk_B @ sk_A)) & 
% 0.24/0.67             ((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.24/0.67             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (k1_zfmisc_1 @ 
% 0.24/0.67                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.67             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.67      inference('demod', [status(thm)], ['304', '305'])).
% 0.24/0.67  thf('307', plain,
% 0.24/0.67      ((((v2_struct_0 @ sk_A)
% 0.24/0.67         | (v2_struct_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.24/0.67         | (r2_hidden @ sk_D_3 @ sk_B)
% 0.24/0.67         | (v1_xboole_0 @ sk_C_1)))
% 0.24/0.67         <= (((v4_pre_topc @ sk_B @ sk_A)) & 
% 0.24/0.67             ((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.24/0.67             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (k1_zfmisc_1 @ 
% 0.24/0.67                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.67             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.67      inference('simplify', [status(thm)], ['306'])).
% 0.24/0.67  thf('308', plain,
% 0.24/0.67      ((((r2_hidden @ sk_D_3 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.24/0.67         | (v1_xboole_0 @ sk_C_1)))
% 0.24/0.67         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.24/0.67             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (k1_zfmisc_1 @ 
% 0.24/0.67                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.67             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.67      inference('clc', [status(thm)], ['227', '228'])).
% 0.24/0.67  thf('309', plain,
% 0.24/0.67      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.67  thf('310', plain,
% 0.24/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.67         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.24/0.67          | ~ (r2_hidden @ X2 @ (k2_pre_topc @ X1 @ X0))
% 0.24/0.67          | ~ (v2_struct_0 @ (sk_D @ X2 @ X0 @ X1))
% 0.24/0.67          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.24/0.67          | ~ (l1_pre_topc @ X1)
% 0.24/0.67          | ~ (v2_pre_topc @ X1)
% 0.24/0.67          | (v2_struct_0 @ X1))),
% 0.24/0.67      inference('cnf', [status(esa)], [t23_yellow19])).
% 0.24/0.67  thf('311', plain,
% 0.24/0.67      (![X0 : $i]:
% 0.24/0.67         ((v2_struct_0 @ sk_A)
% 0.24/0.67          | ~ (v2_pre_topc @ sk_A)
% 0.24/0.67          | ~ (l1_pre_topc @ sk_A)
% 0.24/0.67          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.67          | ~ (v2_struct_0 @ (sk_D @ X0 @ sk_B @ sk_A))
% 0.24/0.67          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.24/0.67      inference('sup-', [status(thm)], ['309', '310'])).
% 0.24/0.67  thf('312', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.67  thf('313', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.67  thf('314', plain,
% 0.24/0.67      (![X0 : $i]:
% 0.24/0.67         ((v2_struct_0 @ sk_A)
% 0.24/0.67          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.67          | ~ (v2_struct_0 @ (sk_D @ X0 @ sk_B @ sk_A))
% 0.24/0.67          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.24/0.67      inference('demod', [status(thm)], ['311', '312', '313'])).
% 0.24/0.67  thf('315', plain,
% 0.24/0.67      ((((v1_xboole_0 @ sk_C_1)
% 0.24/0.67         | ~ (v2_struct_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.24/0.67         | ~ (m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))
% 0.24/0.67         | (v2_struct_0 @ sk_A)))
% 0.24/0.67         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.24/0.67             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (k1_zfmisc_1 @ 
% 0.24/0.67                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.67             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.67      inference('sup-', [status(thm)], ['308', '314'])).
% 0.24/0.67  thf('316', plain,
% 0.24/0.67      (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A)))
% 0.24/0.67         <= (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))))),
% 0.24/0.67      inference('split', [status(esa)], ['192'])).
% 0.24/0.67  thf('317', plain,
% 0.24/0.67      ((((v1_xboole_0 @ sk_C_1)
% 0.24/0.67         | ~ (v2_struct_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.24/0.67         | (v2_struct_0 @ sk_A)))
% 0.24/0.67         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.24/0.67             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (k1_zfmisc_1 @ 
% 0.24/0.67                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.67             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.67      inference('demod', [status(thm)], ['315', '316'])).
% 0.24/0.67  thf('318', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.67  thf('319', plain,
% 0.24/0.67      (((~ (v2_struct_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.24/0.67         | (v1_xboole_0 @ sk_C_1)))
% 0.24/0.67         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.24/0.67             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (k1_zfmisc_1 @ 
% 0.24/0.67                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.67             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.67      inference('clc', [status(thm)], ['317', '318'])).
% 0.24/0.67  thf('320', plain,
% 0.24/0.67      ((((v1_xboole_0 @ sk_C_1)
% 0.24/0.67         | (r2_hidden @ sk_D_3 @ sk_B)
% 0.24/0.67         | (v2_struct_0 @ sk_A)
% 0.24/0.67         | (v1_xboole_0 @ sk_C_1)))
% 0.24/0.67         <= (((v4_pre_topc @ sk_B @ sk_A)) & 
% 0.24/0.67             ((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.24/0.67             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (k1_zfmisc_1 @ 
% 0.24/0.67                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.67             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.67      inference('sup-', [status(thm)], ['307', '319'])).
% 0.24/0.67  thf('321', plain,
% 0.24/0.67      ((((v2_struct_0 @ sk_A)
% 0.24/0.67         | (r2_hidden @ sk_D_3 @ sk_B)
% 0.24/0.67         | (v1_xboole_0 @ sk_C_1)))
% 0.24/0.67         <= (((v4_pre_topc @ sk_B @ sk_A)) & 
% 0.24/0.67             ((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.24/0.67             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (k1_zfmisc_1 @ 
% 0.24/0.67                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.67             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.67      inference('simplify', [status(thm)], ['320'])).
% 0.24/0.67  thf('322', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.67  thf('323', plain,
% 0.24/0.67      ((((v1_xboole_0 @ sk_C_1) | (r2_hidden @ sk_D_3 @ sk_B)))
% 0.24/0.67         <= (((v4_pre_topc @ sk_B @ sk_A)) & 
% 0.24/0.67             ((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.24/0.67             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (k1_zfmisc_1 @ 
% 0.24/0.67                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.67             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.67      inference('clc', [status(thm)], ['321', '322'])).
% 0.24/0.67  thf('324', plain,
% 0.24/0.67      ((~ (r2_hidden @ sk_D_3 @ sk_B)) <= (~ ((r2_hidden @ sk_D_3 @ sk_B)))),
% 0.24/0.67      inference('split', [status(esa)], ['194'])).
% 0.24/0.67  thf('325', plain,
% 0.24/0.67      (((v1_xboole_0 @ sk_C_1))
% 0.24/0.67         <= (~ ((r2_hidden @ sk_D_3 @ sk_B)) & 
% 0.24/0.67             ((v4_pre_topc @ sk_B @ sk_A)) & 
% 0.24/0.67             ((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.24/0.67             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.24/0.67             ((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (k1_zfmisc_1 @ 
% 0.24/0.67                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.24/0.67             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.24/0.67             ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.67               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.24/0.67      inference('sup-', [status(thm)], ['323', '324'])).
% 0.24/0.67  thf('326', plain,
% 0.24/0.67      ((~ (v1_xboole_0 @ sk_C_1)) <= (~ ((v1_xboole_0 @ sk_C_1)))),
% 0.24/0.67      inference('split', [status(esa)], ['206'])).
% 0.24/0.67  thf('327', plain,
% 0.24/0.67      (~ ((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.24/0.67       ~ ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) | 
% 0.24/0.67       ~ ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) | 
% 0.24/0.67       ~
% 0.24/0.67       ((v1_subset_1 @ sk_C_1 @ 
% 0.24/0.67         (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))) | 
% 0.24/0.67       ~ ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) | 
% 0.24/0.67       ~
% 0.24/0.67       ((m1_subset_1 @ sk_C_1 @ 
% 0.24/0.67         (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) | 
% 0.24/0.67       ~ ((r2_hidden @ sk_B @ sk_C_1)) | 
% 0.24/0.67       ~ ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) | 
% 0.24/0.67       ((r2_hidden @ sk_D_3 @ sk_B)) | ((v1_xboole_0 @ sk_C_1))),
% 0.24/0.67      inference('sup-', [status(thm)], ['325', '326'])).
% 0.24/0.67  thf('328', plain, ($false),
% 0.24/0.67      inference('sat_resolution*', [status(thm)],
% 0.24/0.67                ['1', '190', '191', '193', '195', '197', '199', '201', '203', 
% 0.24/0.67                 '205', '207', '327'])).
% 0.24/0.67  
% 0.24/0.67  % SZS output end Refutation
% 0.24/0.67  
% 0.24/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
