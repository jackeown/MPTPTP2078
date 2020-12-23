%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.30CII8nzTE

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:56 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  388 (1981 expanded)
%              Number of leaves         :   34 ( 529 expanded)
%              Depth                    :   47
%              Number of atoms          : 8117 (65130 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   21 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(r1_waybel_7_type,type,(
    r1_waybel_7: $i > $i > $i > $o )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_yellow_6_type,type,(
    v3_yellow_6: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(t26_yellow19,axiom,(
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
                  & ( v3_yellow_6 @ C @ A )
                  & ( l1_waybel_0 @ C @ A ) )
               => ( ( r1_waybel_0 @ A @ C @ B )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_hidden @ D @ ( k10_yellow_6 @ A @ C ) )
                       => ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X4 @ X5 ) @ ( u1_struct_0 @ X5 ) )
      | ( v4_pre_topc @ X4 @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t26_yellow19])).

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
    inference(cnf,[status(esa)],[t26_yellow19])).

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
    inference(cnf,[status(esa)],[t26_yellow19])).

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
      | ( v3_yellow_6 @ ( sk_C @ X4 @ X5 ) @ X5 )
      | ( v4_pre_topc @ X4 @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t26_yellow19])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( v3_yellow_6 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
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
    | ( v3_yellow_6 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v3_yellow_6 @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( l1_waybel_0 @ ( sk_C @ X4 @ X5 ) @ X5 )
      | ( v4_pre_topc @ X4 @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t26_yellow19])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( l1_waybel_0 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
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
    | ( l1_waybel_0 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( l1_waybel_0 @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( r1_waybel_0 @ X5 @ ( sk_C @ X4 @ X5 ) @ X4 )
      | ( v4_pre_topc @ X4 @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t26_yellow19])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_waybel_0 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ),
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
    | ( r1_waybel_0 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( r1_waybel_0 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( r2_hidden @ ( sk_D_1 @ X4 @ X5 ) @ ( k10_yellow_6 @ X5 @ ( sk_C @ X4 @ X5 ) ) )
      | ( v4_pre_topc @ X4 @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t26_yellow19])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_C @ sk_B @ sk_A ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_yellow19,axiom,(
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

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k10_yellow_6 @ X1 @ X3 ) )
      | ~ ( r1_waybel_0 @ X1 @ X3 @ X0 )
      | ~ ( l1_waybel_0 @ X3 @ X1 )
      | ~ ( v3_yellow_6 @ X3 @ X1 )
      | ~ ( v7_waybel_0 @ X3 )
      | ~ ( v4_orders_2 @ X3 )
      | ( v2_struct_0 @ X3 )
      | ( r2_hidden @ X2 @ ( k2_pre_topc @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t24_yellow19])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v7_waybel_0 @ X1 )
      | ~ ( v3_yellow_6 @ X1 @ sk_A )
      | ~ ( l1_waybel_0 @ X1 @ sk_A )
      | ~ ( r1_waybel_0 @ sk_A @ X1 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v7_waybel_0 @ X1 )
      | ~ ( v3_yellow_6 @ X1 @ sk_A )
      | ~ ( l1_waybel_0 @ X1 @ sk_A )
      | ~ ( r1_waybel_0 @ sk_A @ X1 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ X1 ) ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ sk_B @ sk_A )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ~ ( r1_waybel_0 @ sk_A @ X0 @ sk_B )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v3_yellow_6 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','64'])).

thf('66',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v7_waybel_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v3_yellow_6 @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( l1_waybel_0 @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r1_waybel_0 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['57','65'])).

thf('67',plain,
    ( ~ ( r1_waybel_0 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
    | ~ ( l1_waybel_0 @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( v3_yellow_6 @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( v7_waybel_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v7_waybel_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v3_yellow_6 @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( l1_waybel_0 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['49','67'])).

thf('69',plain,
    ( ~ ( l1_waybel_0 @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( v3_yellow_6 @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( v7_waybel_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v7_waybel_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v3_yellow_6 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['41','69'])).

thf('71',plain,
    ( ~ ( v3_yellow_6 @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( v7_waybel_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v7_waybel_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','71'])).

thf('73',plain,
    ( ~ ( v7_waybel_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','73'])).

thf('75',plain,
    ( ~ ( v4_orders_2 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','75'])).

thf('77',plain,
    ( ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('79',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('80',plain,
    ( ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['76'])).

thf('81',plain,(
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

thf('82',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( r2_hidden @ X10 @ ( k2_pre_topc @ X9 @ X8 ) )
      | ( r1_waybel_7 @ X9 @ ( sk_D_2 @ X10 @ X8 @ X9 ) @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t27_yellow19])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r1_waybel_7 @ sk_A @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( sk_D_1 @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['80','86'])).

thf('88',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_waybel_7 @ sk_A @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( sk_D_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r1_waybel_7 @ sk_A @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( sk_D_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','88'])).

thf('90',plain,
    ( ( r1_waybel_7 @ sk_A @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( sk_D_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('92',plain,
    ( ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['76'])).

thf('93',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( r2_hidden @ X10 @ ( k2_pre_topc @ X9 @ X8 ) )
      | ( r2_hidden @ X8 @ ( sk_D_2 @ X10 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t27_yellow19])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['92','98'])).

thf('100',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['91','100'])).

thf('102',plain,
    ( ( r2_hidden @ sk_B @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('104',plain,
    ( ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['76'])).

thf('105',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( r2_hidden @ X10 @ ( k2_pre_topc @ X9 @ X8 ) )
      | ( v2_waybel_0 @ ( sk_D_2 @ X10 @ X8 @ X9 ) @ ( k3_yellow_1 @ ( k2_struct_0 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t27_yellow19])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_waybel_0 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_waybel_0 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_waybel_0 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['104','110'])).

thf('112',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_waybel_0 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_waybel_0 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['103','112'])).

thf('114',plain,
    ( ( v2_waybel_0 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('116',plain,
    ( ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['76'])).

thf('117',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( r2_hidden @ X10 @ ( k2_pre_topc @ X9 @ X8 ) )
      | ( v13_waybel_0 @ ( sk_D_2 @ X10 @ X8 @ X9 ) @ ( k3_yellow_1 @ ( k2_struct_0 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t27_yellow19])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v13_waybel_0 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v13_waybel_0 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('123',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v13_waybel_0 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['116','122'])).

thf('124',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v13_waybel_0 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v13_waybel_0 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['115','124'])).

thf('126',plain,
    ( ( v13_waybel_0 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('128',plain,
    ( ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['76'])).

thf('129',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( r2_hidden @ X10 @ ( k2_pre_topc @ X9 @ X8 ) )
      | ( v1_subset_1 @ ( sk_D_2 @ X10 @ X8 @ X9 ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X9 ) ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t27_yellow19])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_subset_1 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
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
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_subset_1 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['131','132','133'])).

thf('135',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v1_subset_1 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['128','134'])).

thf('136',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_subset_1 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v1_subset_1 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['127','136'])).

thf('138',plain,
    ( ( v1_subset_1 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('140',plain,
    ( ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['76'])).

thf('141',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( r2_hidden @ X10 @ ( k2_pre_topc @ X9 @ X8 ) )
      | ( m1_subset_1 @ ( sk_D_2 @ X10 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X9 ) ) ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t27_yellow19])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['143','144','145'])).

thf('147',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['140','146'])).

thf('148',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['139','148'])).

thf('150',plain,
    ( ( m1_subset_1 @ ( sk_D_2 @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,
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

thf('152',plain,
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
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,
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
    inference('sup-',[status(thm)],['138','152'])).

thf('154',plain,
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
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,
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
    inference('sup-',[status(thm)],['126','154'])).

thf('156',plain,
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
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,
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
    inference('sup-',[status(thm)],['114','156'])).

thf('158',plain,
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
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,
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
    inference('sup-',[status(thm)],['102','158'])).

thf('160',plain,
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
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,
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
    inference('sup-',[status(thm)],['90','160'])).

thf('162',plain,
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
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,
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
    inference('sup-',[status(thm)],['78','162'])).

thf('164',plain,
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
    inference(simplify,[status(thm)],['163'])).

thf('165',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( r2_hidden @ X10 @ ( k2_pre_topc @ X9 @ X8 ) )
      | ~ ( v1_xboole_0 @ ( sk_D_2 @ X10 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t27_yellow19])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) )
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
      | ~ ( v1_xboole_0 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['167','168','169'])).

thf('171',plain,
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
    inference('sup-',[status(thm)],['164','170'])).

thf('172',plain,
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
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,
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
    inference('sup-',[status(thm)],['77','172'])).

thf('174',plain,
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
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,
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
    inference('sup-',[status(thm)],['9','174'])).

thf('176',plain,
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
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X4 @ X5 ) @ X4 )
      | ( v4_pre_topc @ X4 @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t26_yellow19])).

thf('179',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B ) ),
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
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['179','180','181'])).

thf('183',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ~ ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['182','183'])).

thf('185',plain,
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
    inference('sup-',[status(thm)],['176','184'])).

thf('186',plain,
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
    inference(simplify,[status(thm)],['185'])).

thf('187',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( v2_struct_0 @ ( sk_C @ X4 @ X5 ) )
      | ( v4_pre_topc @ X4 @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t26_yellow19])).

thf('189',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['189','190','191'])).

thf('193',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ~ ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['192','193'])).

thf('195',plain,
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
    inference(clc,[status(thm)],['186','194'])).

thf('196',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
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
    inference(clc,[status(thm)],['195','196'])).

thf('198',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['198'])).

thf('200',plain,
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
    inference('sup-',[status(thm)],['197','199'])).

thf('201',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['198'])).

thf('202',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['202'])).

thf('204',plain,
    ( ~ ( r2_hidden @ sk_D_3 @ sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,
    ( ~ ( r2_hidden @ sk_D_3 @ sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['204'])).

thf('206',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['206'])).

thf('208',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['208'])).

thf('210',plain,
    ( ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,
    ( ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['210'])).

thf('212',plain,
    ( ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,
    ( ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['212'])).

thf('214',plain,
    ( ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,
    ( ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['214'])).

thf('216',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['216'])).

thf('218',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['202'])).

thf('219',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
   <= ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 ) ),
    inference(split,[status(esa)],['206'])).

thf('220',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
   <= ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['198'])).

thf('221',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,
    ( ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['212'])).

thf('223',plain,
    ( ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['210'])).

thf('224',plain,
    ( ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
   <= ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['214'])).

thf('225',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['208'])).

thf('226',plain,(
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

thf('227',plain,
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
    inference('sup-',[status(thm)],['225','226'])).

thf('228',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,
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
    inference(demod,[status(thm)],['227','228','229'])).

thf('231',plain,
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
    inference('sup-',[status(thm)],['224','230'])).

thf('232',plain,
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
    inference('sup-',[status(thm)],['223','231'])).

thf('233',plain,
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
    inference('sup-',[status(thm)],['222','232'])).

thf('234',plain,
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
    inference('sup-',[status(thm)],['221','233'])).

thf('235',plain,
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
    inference('sup-',[status(thm)],['220','234'])).

thf('236',plain,
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
    inference('sup-',[status(thm)],['219','235'])).

thf('237',plain,
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
    inference('sup-',[status(thm)],['218','236'])).

thf('238',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,
    ( ( ( r2_hidden @ sk_D_3 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['237','238'])).

thf('240',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k2_pre_topc @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ ( k10_yellow_6 @ X1 @ ( sk_D @ X2 @ X0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t24_yellow19])).

thf('242',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['240','241'])).

thf('243',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['242','243','244'])).

thf('246',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( r2_hidden @ sk_D_3 @ ( k10_yellow_6 @ sk_A @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) ) )
      | ~ ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['239','245'])).

thf('247',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['202'])).

thf('248',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( r2_hidden @ sk_D_3 @ ( k10_yellow_6 @ sk_A @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['246','247'])).

thf('249',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('250',plain,
    ( ( ( r2_hidden @ sk_D_3 @ ( k10_yellow_6 @ sk_A @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['248','249'])).

thf('251',plain,
    ( ( ( r2_hidden @ sk_D_3 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['237','238'])).

thf('252',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k2_pre_topc @ X1 @ X0 ) )
      | ( v7_waybel_0 @ ( sk_D @ X2 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t24_yellow19])).

thf('254',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['252','253'])).

thf('255',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('257',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['254','255','256'])).

thf('258',plain,
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
    inference('sup-',[status(thm)],['251','257'])).

thf('259',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['202'])).

thf('260',plain,
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
    inference(demod,[status(thm)],['258','259'])).

thf('261',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,
    ( ( ( v7_waybel_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['260','261'])).

thf('263',plain,
    ( ( ( r2_hidden @ sk_D_3 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['237','238'])).

thf('264',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k2_pre_topc @ X1 @ X0 ) )
      | ( v4_orders_2 @ ( sk_D @ X2 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t24_yellow19])).

thf('266',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v4_orders_2 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['264','265'])).

thf('267',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('268',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('269',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v4_orders_2 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['266','267','268'])).

thf('270',plain,
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
    inference('sup-',[status(thm)],['263','269'])).

thf('271',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['202'])).

thf('272',plain,
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
    inference(demod,[status(thm)],['270','271'])).

thf('273',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('274',plain,
    ( ( ( v4_orders_2 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['272','273'])).

thf('275',plain,
    ( ( ( r2_hidden @ sk_D_3 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['237','238'])).

thf('276',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('277',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k2_pre_topc @ X1 @ X0 ) )
      | ( l1_waybel_0 @ ( sk_D @ X2 @ X0 @ X1 ) @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t24_yellow19])).

thf('278',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['276','277'])).

thf('279',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('280',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['278','279','280'])).

thf('282',plain,
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
    inference('sup-',[status(thm)],['275','281'])).

thf('283',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['202'])).

thf('284',plain,
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
    inference(demod,[status(thm)],['282','283'])).

thf('285',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('286',plain,
    ( ( ( l1_waybel_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['284','285'])).

thf('287',plain,
    ( ( ( r2_hidden @ sk_D_3 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['237','238'])).

thf('288',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('289',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k2_pre_topc @ X1 @ X0 ) )
      | ( v3_yellow_6 @ ( sk_D @ X2 @ X0 @ X1 ) @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t24_yellow19])).

thf('290',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v3_yellow_6 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['288','289'])).

thf('291',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('292',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('293',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v3_yellow_6 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['290','291','292'])).

thf('294',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( v3_yellow_6 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['287','293'])).

thf('295',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['202'])).

thf('296',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( v3_yellow_6 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['294','295'])).

thf('297',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('298',plain,
    ( ( ( v3_yellow_6 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['296','297'])).

thf('299',plain,
    ( ( ( r2_hidden @ sk_D_3 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['237','238'])).

thf('300',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('301',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k2_pre_topc @ X1 @ X0 ) )
      | ( r1_waybel_0 @ X1 @ ( sk_D @ X2 @ X0 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t24_yellow19])).

thf('302',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_0 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['300','301'])).

thf('303',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('304',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('305',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_0 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['302','303','304'])).

thf('306',plain,
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
    inference('sup-',[status(thm)],['299','305'])).

thf('307',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['202'])).

thf('308',plain,
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
    inference(demod,[status(thm)],['306','307'])).

thf('309',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('310',plain,
    ( ( ( r1_waybel_0 @ sk_A @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['308','309'])).

thf('311',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('312',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('313',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( v4_pre_topc @ X4 @ X5 )
      | ~ ( r1_waybel_0 @ X5 @ X6 @ X4 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X5 ) )
      | ( r2_hidden @ X7 @ X4 )
      | ~ ( r2_hidden @ X7 @ ( k10_yellow_6 @ X5 @ X6 ) )
      | ~ ( l1_waybel_0 @ X6 @ X5 )
      | ~ ( v3_yellow_6 @ X6 @ X5 )
      | ~ ( v7_waybel_0 @ X6 )
      | ~ ( v4_orders_2 @ X6 )
      | ( v2_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t26_yellow19])).

thf('314',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v3_yellow_6 @ X0 @ sk_A )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( r2_hidden @ X1 @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_waybel_0 @ sk_A @ X0 @ sk_B )
      | ~ ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['312','313'])).

thf('315',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('316',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('317',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v3_yellow_6 @ X0 @ sk_A )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( r2_hidden @ X1 @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_waybel_0 @ sk_A @ X0 @ sk_B )
      | ~ ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['314','315','316'])).

thf('318',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_waybel_0 @ sk_A @ X0 @ sk_B )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X1 @ sk_B )
        | ~ ( r2_hidden @ X1 @ ( k10_yellow_6 @ sk_A @ X0 ) )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ~ ( v3_yellow_6 @ X0 @ sk_A )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['311','317'])).

thf('319',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ sk_C_1 )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( v4_orders_2 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( v7_waybel_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( v3_yellow_6 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ sk_A )
        | ~ ( l1_waybel_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) ) )
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
    inference('sup-',[status(thm)],['310','318'])).

thf('320',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ sk_C_1 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) ) )
        | ~ ( l1_waybel_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ sk_A )
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
    inference('sup-',[status(thm)],['298','319'])).

thf('321',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( v4_orders_2 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( v7_waybel_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( l1_waybel_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) ) )
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
    inference(simplify,[status(thm)],['320'])).

thf('322',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ sk_C_1 )
        | ( v1_xboole_0 @ sk_C_1 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) ) )
        | ~ ( v7_waybel_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( v4_orders_2 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
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
    inference('sup-',[status(thm)],['286','321'])).

thf('323',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( v4_orders_2 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( v7_waybel_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) ) )
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
    inference(simplify,[status(thm)],['322'])).

thf('324',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ sk_C_1 )
        | ( v1_xboole_0 @ sk_C_1 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) ) )
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
    inference('sup-',[status(thm)],['274','323'])).

thf('325',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( v7_waybel_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) ) )
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
    inference(simplify,[status(thm)],['324'])).

thf('326',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ sk_C_1 )
        | ( v1_xboole_0 @ sk_C_1 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) ) )
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
    inference('sup-',[status(thm)],['262','325'])).

thf('327',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) ) )
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
    inference(simplify,[status(thm)],['326'])).

thf('328',plain,
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
    inference('sup-',[status(thm)],['250','327'])).

thf('329',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['202'])).

thf('330',plain,
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
    inference(demod,[status(thm)],['328','329'])).

thf('331',plain,
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
    inference(simplify,[status(thm)],['330'])).

thf('332',plain,
    ( ( ( r2_hidden @ sk_D_3 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['237','238'])).

thf('333',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('334',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k2_pre_topc @ X1 @ X0 ) )
      | ~ ( v2_struct_0 @ ( sk_D @ X2 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t24_yellow19])).

thf('335',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['333','334'])).

thf('336',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('337',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('338',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['335','336','337'])).

thf('339',plain,
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
    inference('sup-',[status(thm)],['332','338'])).

thf('340',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['202'])).

thf('341',plain,
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
    inference(demod,[status(thm)],['339','340'])).

thf('342',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('343',plain,
    ( ( ~ ( v2_struct_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['341','342'])).

thf('344',plain,
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
    inference('sup-',[status(thm)],['331','343'])).

thf('345',plain,
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
    inference(simplify,[status(thm)],['344'])).

thf('346',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('347',plain,
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
    inference(clc,[status(thm)],['345','346'])).

thf('348',plain,
    ( ~ ( r2_hidden @ sk_D_3 @ sk_B )
   <= ~ ( r2_hidden @ sk_D_3 @ sk_B ) ),
    inference(split,[status(esa)],['204'])).

thf('349',plain,
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
    inference('sup-',[status(thm)],['347','348'])).

thf('350',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
   <= ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(split,[status(esa)],['216'])).

thf('351',plain,
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
    inference('sup-',[status(thm)],['349','350'])).

thf('352',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','200','201','203','205','207','209','211','213','215','217','351'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.30CII8nzTE
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:18:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.59  % Solved by: fo/fo7.sh
% 0.38/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.59  % done 230 iterations in 0.124s
% 0.38/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.59  % SZS output start Refutation
% 0.38/0.59  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.38/0.59  thf(k10_yellow_6_type, type, k10_yellow_6: $i > $i > $i).
% 0.38/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.59  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.59  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.38/0.59  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.38/0.59  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.38/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.59  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.38/0.59  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.38/0.59  thf(r1_waybel_7_type, type, r1_waybel_7: $i > $i > $i > $o).
% 0.38/0.59  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.38/0.59  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.38/0.59  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.59  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.59  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.38/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.59  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.38/0.59  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.38/0.59  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.38/0.59  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.38/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.59  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.38/0.59  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.38/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.59  thf(v3_yellow_6_type, type, v3_yellow_6: $i > $i > $o).
% 0.38/0.59  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 0.38/0.59  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.38/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.59  thf(t29_yellow19, conjecture,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.59       ( ![B:$i]:
% 0.38/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.59           ( ( v4_pre_topc @ B @ A ) <=>
% 0.38/0.59             ( ![C:$i]:
% 0.38/0.59               ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.38/0.59                   ( v1_subset_1 @
% 0.38/0.59                     C @ 
% 0.38/0.59                     ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.38/0.59                   ( v2_waybel_0 @ C @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.38/0.59                   ( v13_waybel_0 @ C @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.38/0.59                   ( m1_subset_1 @
% 0.38/0.59                     C @ 
% 0.38/0.59                     ( k1_zfmisc_1 @
% 0.38/0.59                       ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.38/0.59                 ( ( r2_hidden @ B @ C ) =>
% 0.38/0.59                   ( ![D:$i]:
% 0.38/0.59                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.59                       ( ( r1_waybel_7 @ A @ C @ D ) => ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.59    (~( ![A:$i]:
% 0.38/0.59        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.59            ( l1_pre_topc @ A ) ) =>
% 0.38/0.59          ( ![B:$i]:
% 0.38/0.59            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.59              ( ( v4_pre_topc @ B @ A ) <=>
% 0.38/0.59                ( ![C:$i]:
% 0.38/0.59                  ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.38/0.59                      ( v1_subset_1 @
% 0.38/0.59                        C @ 
% 0.38/0.59                        ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.38/0.59                      ( v2_waybel_0 @ C @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.38/0.59                      ( v13_waybel_0 @
% 0.38/0.59                        C @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.38/0.59                      ( m1_subset_1 @
% 0.38/0.59                        C @ 
% 0.38/0.59                        ( k1_zfmisc_1 @
% 0.38/0.59                          ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.38/0.59                    ( ( r2_hidden @ B @ C ) =>
% 0.38/0.59                      ( ![D:$i]:
% 0.38/0.59                        ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.59                          ( ( r1_waybel_7 @ A @ C @ D ) =>
% 0.38/0.59                            ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ) ) )),
% 0.38/0.59    inference('cnf.neg', [status(esa)], [t29_yellow19])).
% 0.38/0.59  thf('0', plain,
% 0.38/0.59      (![X12 : $i, X13 : $i]:
% 0.38/0.59         ((v1_xboole_0 @ X12)
% 0.38/0.59          | ~ (v1_subset_1 @ X12 @ 
% 0.38/0.59               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.38/0.59          | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.59          | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.59          | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.59               (k1_zfmisc_1 @ 
% 0.38/0.59                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.38/0.59          | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.38/0.59          | (r2_hidden @ X13 @ sk_B)
% 0.38/0.59          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.38/0.59          | ~ (r2_hidden @ sk_B @ X12)
% 0.38/0.59          | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('1', plain,
% 0.38/0.59      ((![X12 : $i, X13 : $i]:
% 0.38/0.59          ((v1_xboole_0 @ X12)
% 0.38/0.59           | ~ (v1_subset_1 @ X12 @ 
% 0.38/0.59                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.38/0.59           | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.59           | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.59           | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.59                (k1_zfmisc_1 @ 
% 0.38/0.59                 (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.38/0.59           | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.38/0.59           | (r2_hidden @ X13 @ sk_B)
% 0.38/0.59           | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.38/0.59           | ~ (r2_hidden @ sk_B @ X12))) | 
% 0.38/0.59       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('split', [status(esa)], ['0'])).
% 0.38/0.59  thf('2', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(t26_yellow19, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.59       ( ![B:$i]:
% 0.38/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.59           ( ( v4_pre_topc @ B @ A ) <=>
% 0.38/0.59             ( ![C:$i]:
% 0.38/0.59               ( ( ( ~( v2_struct_0 @ C ) ) & ( v4_orders_2 @ C ) & 
% 0.38/0.59                   ( v7_waybel_0 @ C ) & ( v3_yellow_6 @ C @ A ) & 
% 0.38/0.59                   ( l1_waybel_0 @ C @ A ) ) =>
% 0.38/0.59                 ( ( r1_waybel_0 @ A @ C @ B ) =>
% 0.38/0.59                   ( ![D:$i]:
% 0.38/0.59                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.59                       ( ( r2_hidden @ D @ ( k10_yellow_6 @ A @ C ) ) =>
% 0.38/0.59                         ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.59  thf('3', plain,
% 0.38/0.59      (![X4 : $i, X5 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.38/0.59          | (m1_subset_1 @ (sk_D_1 @ X4 @ X5) @ (u1_struct_0 @ X5))
% 0.38/0.59          | (v4_pre_topc @ X4 @ X5)
% 0.38/0.59          | ~ (l1_pre_topc @ X5)
% 0.38/0.59          | ~ (v2_pre_topc @ X5)
% 0.38/0.59          | (v2_struct_0 @ X5))),
% 0.38/0.59      inference('cnf', [status(esa)], [t26_yellow19])).
% 0.38/0.59  thf('4', plain,
% 0.38/0.59      (((v2_struct_0 @ sk_A)
% 0.38/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.59  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('7', plain,
% 0.38/0.59      (((v2_struct_0 @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.38/0.59  thf('8', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('9', plain,
% 0.38/0.59      (((m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('clc', [status(thm)], ['7', '8'])).
% 0.38/0.59  thf('10', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('11', plain,
% 0.38/0.59      (![X4 : $i, X5 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.38/0.59          | (v4_orders_2 @ (sk_C @ X4 @ X5))
% 0.38/0.59          | (v4_pre_topc @ X4 @ X5)
% 0.38/0.59          | ~ (l1_pre_topc @ X5)
% 0.38/0.59          | ~ (v2_pre_topc @ X5)
% 0.38/0.59          | (v2_struct_0 @ X5))),
% 0.38/0.59      inference('cnf', [status(esa)], [t26_yellow19])).
% 0.38/0.59  thf('12', plain,
% 0.38/0.59      (((v2_struct_0 @ sk_A)
% 0.38/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (v4_orders_2 @ (sk_C @ sk_B @ sk_A)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['10', '11'])).
% 0.38/0.59  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('15', plain,
% 0.38/0.59      (((v2_struct_0 @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (v4_orders_2 @ (sk_C @ sk_B @ sk_A)))),
% 0.38/0.59      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.38/0.59  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('17', plain,
% 0.38/0.59      (((v4_orders_2 @ (sk_C @ sk_B @ sk_A)) | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('clc', [status(thm)], ['15', '16'])).
% 0.38/0.59  thf('18', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('19', plain,
% 0.38/0.59      (![X4 : $i, X5 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.38/0.59          | (v7_waybel_0 @ (sk_C @ X4 @ X5))
% 0.38/0.59          | (v4_pre_topc @ X4 @ X5)
% 0.38/0.59          | ~ (l1_pre_topc @ X5)
% 0.38/0.59          | ~ (v2_pre_topc @ X5)
% 0.38/0.59          | (v2_struct_0 @ X5))),
% 0.38/0.59      inference('cnf', [status(esa)], [t26_yellow19])).
% 0.38/0.59  thf('20', plain,
% 0.38/0.59      (((v2_struct_0 @ sk_A)
% 0.38/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (v7_waybel_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['18', '19'])).
% 0.38/0.59  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('23', plain,
% 0.38/0.59      (((v2_struct_0 @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (v7_waybel_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.38/0.59      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.38/0.59  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('25', plain,
% 0.38/0.59      (((v7_waybel_0 @ (sk_C @ sk_B @ sk_A)) | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('clc', [status(thm)], ['23', '24'])).
% 0.38/0.59  thf('26', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('27', plain,
% 0.38/0.59      (![X4 : $i, X5 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.38/0.59          | (v3_yellow_6 @ (sk_C @ X4 @ X5) @ X5)
% 0.38/0.59          | (v4_pre_topc @ X4 @ X5)
% 0.38/0.59          | ~ (l1_pre_topc @ X5)
% 0.38/0.59          | ~ (v2_pre_topc @ X5)
% 0.38/0.59          | (v2_struct_0 @ X5))),
% 0.38/0.59      inference('cnf', [status(esa)], [t26_yellow19])).
% 0.38/0.59  thf('28', plain,
% 0.38/0.59      (((v2_struct_0 @ sk_A)
% 0.38/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (v3_yellow_6 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['26', '27'])).
% 0.38/0.59  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('31', plain,
% 0.38/0.59      (((v2_struct_0 @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (v3_yellow_6 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.38/0.59      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.38/0.59  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('33', plain,
% 0.38/0.59      (((v3_yellow_6 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('clc', [status(thm)], ['31', '32'])).
% 0.38/0.59  thf('34', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('35', plain,
% 0.38/0.59      (![X4 : $i, X5 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.38/0.59          | (l1_waybel_0 @ (sk_C @ X4 @ X5) @ X5)
% 0.38/0.59          | (v4_pre_topc @ X4 @ X5)
% 0.38/0.59          | ~ (l1_pre_topc @ X5)
% 0.38/0.59          | ~ (v2_pre_topc @ X5)
% 0.38/0.59          | (v2_struct_0 @ X5))),
% 0.38/0.59      inference('cnf', [status(esa)], [t26_yellow19])).
% 0.38/0.59  thf('36', plain,
% 0.38/0.59      (((v2_struct_0 @ sk_A)
% 0.38/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (l1_waybel_0 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['34', '35'])).
% 0.38/0.59  thf('37', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('39', plain,
% 0.38/0.59      (((v2_struct_0 @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (l1_waybel_0 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.38/0.59      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.38/0.59  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('41', plain,
% 0.38/0.59      (((l1_waybel_0 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('clc', [status(thm)], ['39', '40'])).
% 0.38/0.59  thf('42', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('43', plain,
% 0.38/0.59      (![X4 : $i, X5 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.38/0.59          | (r1_waybel_0 @ X5 @ (sk_C @ X4 @ X5) @ X4)
% 0.38/0.59          | (v4_pre_topc @ X4 @ X5)
% 0.38/0.59          | ~ (l1_pre_topc @ X5)
% 0.38/0.59          | ~ (v2_pre_topc @ X5)
% 0.38/0.59          | (v2_struct_0 @ X5))),
% 0.38/0.59      inference('cnf', [status(esa)], [t26_yellow19])).
% 0.38/0.59  thf('44', plain,
% 0.38/0.59      (((v2_struct_0 @ sk_A)
% 0.38/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (r1_waybel_0 @ sk_A @ (sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.38/0.59      inference('sup-', [status(thm)], ['42', '43'])).
% 0.38/0.59  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('47', plain,
% 0.38/0.59      (((v2_struct_0 @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (r1_waybel_0 @ sk_A @ (sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.38/0.59      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.38/0.59  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('49', plain,
% 0.38/0.59      (((r1_waybel_0 @ sk_A @ (sk_C @ sk_B @ sk_A) @ sk_B)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('clc', [status(thm)], ['47', '48'])).
% 0.38/0.59  thf('50', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('51', plain,
% 0.38/0.59      (![X4 : $i, X5 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.38/0.59          | (r2_hidden @ (sk_D_1 @ X4 @ X5) @ 
% 0.38/0.59             (k10_yellow_6 @ X5 @ (sk_C @ X4 @ X5)))
% 0.38/0.59          | (v4_pre_topc @ X4 @ X5)
% 0.38/0.59          | ~ (l1_pre_topc @ X5)
% 0.38/0.59          | ~ (v2_pre_topc @ X5)
% 0.38/0.59          | (v2_struct_0 @ X5))),
% 0.38/0.59      inference('cnf', [status(esa)], [t26_yellow19])).
% 0.38/0.59  thf('52', plain,
% 0.38/0.59      (((v2_struct_0 @ sk_A)
% 0.38/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ 
% 0.38/0.59           (k10_yellow_6 @ sk_A @ (sk_C @ sk_B @ sk_A))))),
% 0.38/0.59      inference('sup-', [status(thm)], ['50', '51'])).
% 0.38/0.59  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('55', plain,
% 0.38/0.59      (((v2_struct_0 @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ 
% 0.38/0.59           (k10_yellow_6 @ sk_A @ (sk_C @ sk_B @ sk_A))))),
% 0.38/0.59      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.38/0.59  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('57', plain,
% 0.38/0.59      (((r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ 
% 0.38/0.59         (k10_yellow_6 @ sk_A @ (sk_C @ sk_B @ sk_A)))
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('clc', [status(thm)], ['55', '56'])).
% 0.38/0.59  thf('58', plain,
% 0.38/0.59      (((m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('clc', [status(thm)], ['7', '8'])).
% 0.38/0.59  thf('59', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(t24_yellow19, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.59       ( ![B:$i]:
% 0.38/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.59           ( ![C:$i]:
% 0.38/0.59             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.59               ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) ) <=>
% 0.38/0.59                 ( ?[D:$i]:
% 0.38/0.59                   ( ( r2_hidden @ C @ ( k10_yellow_6 @ A @ D ) ) & 
% 0.38/0.59                     ( r1_waybel_0 @ A @ D @ B ) & ( l1_waybel_0 @ D @ A ) & 
% 0.38/0.59                     ( v3_yellow_6 @ D @ A ) & ( v7_waybel_0 @ D ) & 
% 0.38/0.59                     ( v4_orders_2 @ D ) & ( ~( v2_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.59  thf('60', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.38/0.59          | ~ (r2_hidden @ X2 @ (k10_yellow_6 @ X1 @ X3))
% 0.38/0.59          | ~ (r1_waybel_0 @ X1 @ X3 @ X0)
% 0.38/0.59          | ~ (l1_waybel_0 @ X3 @ X1)
% 0.38/0.59          | ~ (v3_yellow_6 @ X3 @ X1)
% 0.38/0.59          | ~ (v7_waybel_0 @ X3)
% 0.38/0.59          | ~ (v4_orders_2 @ X3)
% 0.38/0.59          | (v2_struct_0 @ X3)
% 0.38/0.59          | (r2_hidden @ X2 @ (k2_pre_topc @ X1 @ X0))
% 0.38/0.59          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.38/0.59          | ~ (l1_pre_topc @ X1)
% 0.38/0.59          | ~ (v2_pre_topc @ X1)
% 0.38/0.59          | (v2_struct_0 @ X1))),
% 0.38/0.59      inference('cnf', [status(esa)], [t24_yellow19])).
% 0.38/0.59  thf('61', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((v2_struct_0 @ sk_A)
% 0.38/0.59          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.59          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.59          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.38/0.59          | (v2_struct_0 @ X1)
% 0.38/0.59          | ~ (v4_orders_2 @ X1)
% 0.38/0.59          | ~ (v7_waybel_0 @ X1)
% 0.38/0.59          | ~ (v3_yellow_6 @ X1 @ sk_A)
% 0.38/0.59          | ~ (l1_waybel_0 @ X1 @ sk_A)
% 0.38/0.59          | ~ (r1_waybel_0 @ sk_A @ X1 @ sk_B)
% 0.38/0.59          | ~ (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ X1)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['59', '60'])).
% 0.38/0.59  thf('62', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('64', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((v2_struct_0 @ sk_A)
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.59          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.38/0.59          | (v2_struct_0 @ X1)
% 0.38/0.59          | ~ (v4_orders_2 @ X1)
% 0.38/0.59          | ~ (v7_waybel_0 @ X1)
% 0.38/0.59          | ~ (v3_yellow_6 @ X1 @ sk_A)
% 0.38/0.59          | ~ (l1_waybel_0 @ X1 @ sk_A)
% 0.38/0.59          | ~ (r1_waybel_0 @ sk_A @ X1 @ sk_B)
% 0.38/0.59          | ~ (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ X1)))),
% 0.38/0.59      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.38/0.59  thf('65', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59          | ~ (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 0.38/0.59          | ~ (r1_waybel_0 @ sk_A @ X0 @ sk_B)
% 0.38/0.59          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.38/0.59          | ~ (v3_yellow_6 @ X0 @ sk_A)
% 0.38/0.59          | ~ (v7_waybel_0 @ X0)
% 0.38/0.59          | ~ (v4_orders_2 @ X0)
% 0.38/0.59          | (v2_struct_0 @ X0)
% 0.38/0.59          | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.38/0.59          | (v2_struct_0 @ sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['58', '64'])).
% 0.38/0.59  thf('66', plain,
% 0.38/0.59      (((v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.38/0.59        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | ~ (v4_orders_2 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | ~ (v7_waybel_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | ~ (v3_yellow_6 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.38/0.59        | ~ (l1_waybel_0 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.38/0.59        | ~ (r1_waybel_0 @ sk_A @ (sk_C @ sk_B @ sk_A) @ sk_B)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['57', '65'])).
% 0.38/0.59  thf('67', plain,
% 0.38/0.59      ((~ (r1_waybel_0 @ sk_A @ (sk_C @ sk_B @ sk_A) @ sk_B)
% 0.38/0.59        | ~ (l1_waybel_0 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.38/0.59        | ~ (v3_yellow_6 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.38/0.59        | ~ (v7_waybel_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | ~ (v4_orders_2 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('simplify', [status(thm)], ['66'])).
% 0.38/0.59  thf('68', plain,
% 0.38/0.59      (((v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.38/0.59        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | ~ (v4_orders_2 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | ~ (v7_waybel_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | ~ (v3_yellow_6 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.38/0.59        | ~ (l1_waybel_0 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['49', '67'])).
% 0.38/0.59  thf('69', plain,
% 0.38/0.59      ((~ (l1_waybel_0 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.38/0.59        | ~ (v3_yellow_6 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.38/0.59        | ~ (v7_waybel_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | ~ (v4_orders_2 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('simplify', [status(thm)], ['68'])).
% 0.38/0.59  thf('70', plain,
% 0.38/0.59      (((v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.38/0.59        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | ~ (v4_orders_2 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | ~ (v7_waybel_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | ~ (v3_yellow_6 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['41', '69'])).
% 0.38/0.59  thf('71', plain,
% 0.38/0.59      ((~ (v3_yellow_6 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.38/0.59        | ~ (v7_waybel_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | ~ (v4_orders_2 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('simplify', [status(thm)], ['70'])).
% 0.38/0.59  thf('72', plain,
% 0.38/0.59      (((v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.38/0.59        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | ~ (v4_orders_2 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | ~ (v7_waybel_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['33', '71'])).
% 0.38/0.59  thf('73', plain,
% 0.38/0.59      ((~ (v7_waybel_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | ~ (v4_orders_2 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('simplify', [status(thm)], ['72'])).
% 0.38/0.59  thf('74', plain,
% 0.38/0.59      (((v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.38/0.59        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | ~ (v4_orders_2 @ (sk_C @ sk_B @ sk_A)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['25', '73'])).
% 0.38/0.59  thf('75', plain,
% 0.38/0.59      ((~ (v4_orders_2 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('simplify', [status(thm)], ['74'])).
% 0.38/0.59  thf('76', plain,
% 0.38/0.59      (((v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.38/0.59        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['17', '75'])).
% 0.38/0.59  thf('77', plain,
% 0.38/0.59      (((v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('simplify', [status(thm)], ['76'])).
% 0.38/0.59  thf('78', plain,
% 0.38/0.59      (((m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('clc', [status(thm)], ['7', '8'])).
% 0.38/0.59  thf('79', plain,
% 0.38/0.59      (((m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('clc', [status(thm)], ['7', '8'])).
% 0.38/0.59  thf('80', plain,
% 0.38/0.59      (((v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('simplify', [status(thm)], ['76'])).
% 0.38/0.59  thf('81', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(t27_yellow19, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.59       ( ![B:$i]:
% 0.38/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.59           ( ![C:$i]:
% 0.38/0.59             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.59               ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) ) <=>
% 0.38/0.59                 ( ?[D:$i]:
% 0.38/0.59                   ( ( r1_waybel_7 @ A @ D @ C ) & ( r2_hidden @ B @ D ) & 
% 0.38/0.59                     ( m1_subset_1 @
% 0.38/0.59                       D @ 
% 0.38/0.59                       ( k1_zfmisc_1 @
% 0.38/0.59                         ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) & 
% 0.38/0.59                     ( v13_waybel_0 @ D @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.38/0.59                     ( v2_waybel_0 @ D @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.38/0.59                     ( v1_subset_1 @
% 0.38/0.59                       D @ 
% 0.38/0.59                       ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.38/0.59                     ( ~( v1_xboole_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.59  thf('82', plain,
% 0.38/0.59      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.38/0.59          | ~ (r2_hidden @ X10 @ (k2_pre_topc @ X9 @ X8))
% 0.38/0.59          | (r1_waybel_7 @ X9 @ (sk_D_2 @ X10 @ X8 @ X9) @ X10)
% 0.38/0.59          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.38/0.59          | ~ (l1_pre_topc @ X9)
% 0.38/0.59          | ~ (v2_pre_topc @ X9)
% 0.38/0.59          | (v2_struct_0 @ X9))),
% 0.38/0.59      inference('cnf', [status(esa)], [t27_yellow19])).
% 0.38/0.59  thf('83', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((v2_struct_0 @ sk_A)
% 0.38/0.59          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.59          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.59          | (r1_waybel_7 @ sk_A @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ X0)
% 0.38/0.59          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['81', '82'])).
% 0.38/0.59  thf('84', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('86', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((v2_struct_0 @ sk_A)
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.59          | (r1_waybel_7 @ sk_A @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ X0)
% 0.38/0.59          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.38/0.59      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.38/0.59  thf('87', plain,
% 0.38/0.59      (((v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | (r1_waybel_7 @ sk_A @ 
% 0.38/0.59           (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.38/0.59           (sk_D_1 @ sk_B @ sk_A))
% 0.38/0.59        | ~ (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.38/0.59        | (v2_struct_0 @ sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['80', '86'])).
% 0.38/0.59  thf('88', plain,
% 0.38/0.59      ((~ (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.38/0.59        | (r1_waybel_7 @ sk_A @ 
% 0.38/0.59           (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.38/0.59           (sk_D_1 @ sk_B @ sk_A))
% 0.38/0.59        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('simplify', [status(thm)], ['87'])).
% 0.38/0.59  thf('89', plain,
% 0.38/0.59      (((v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | (r1_waybel_7 @ sk_A @ 
% 0.38/0.59           (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.38/0.59           (sk_D_1 @ sk_B @ sk_A)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['79', '88'])).
% 0.38/0.59  thf('90', plain,
% 0.38/0.59      (((r1_waybel_7 @ sk_A @ 
% 0.38/0.59         (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.38/0.59         (sk_D_1 @ sk_B @ sk_A))
% 0.38/0.59        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('simplify', [status(thm)], ['89'])).
% 0.38/0.59  thf('91', plain,
% 0.38/0.59      (((m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('clc', [status(thm)], ['7', '8'])).
% 0.38/0.59  thf('92', plain,
% 0.38/0.59      (((v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('simplify', [status(thm)], ['76'])).
% 0.38/0.59  thf('93', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('94', plain,
% 0.38/0.59      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.38/0.59          | ~ (r2_hidden @ X10 @ (k2_pre_topc @ X9 @ X8))
% 0.38/0.59          | (r2_hidden @ X8 @ (sk_D_2 @ X10 @ X8 @ X9))
% 0.38/0.59          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.38/0.59          | ~ (l1_pre_topc @ X9)
% 0.38/0.59          | ~ (v2_pre_topc @ X9)
% 0.38/0.59          | (v2_struct_0 @ X9))),
% 0.38/0.59      inference('cnf', [status(esa)], [t27_yellow19])).
% 0.38/0.59  thf('95', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((v2_struct_0 @ sk_A)
% 0.38/0.59          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.59          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.59          | (r2_hidden @ sk_B @ (sk_D_2 @ X0 @ sk_B @ sk_A))
% 0.38/0.59          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['93', '94'])).
% 0.38/0.59  thf('96', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('98', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((v2_struct_0 @ sk_A)
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.59          | (r2_hidden @ sk_B @ (sk_D_2 @ X0 @ sk_B @ sk_A))
% 0.38/0.59          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.38/0.59      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.38/0.59  thf('99', plain,
% 0.38/0.59      (((v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | (r2_hidden @ sk_B @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.38/0.59        | ~ (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.38/0.59        | (v2_struct_0 @ sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['92', '98'])).
% 0.38/0.59  thf('100', plain,
% 0.38/0.59      ((~ (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.38/0.59        | (r2_hidden @ sk_B @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.38/0.59        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('simplify', [status(thm)], ['99'])).
% 0.38/0.59  thf('101', plain,
% 0.38/0.59      (((v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | (r2_hidden @ sk_B @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['91', '100'])).
% 0.38/0.59  thf('102', plain,
% 0.38/0.59      (((r2_hidden @ sk_B @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.38/0.59        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('simplify', [status(thm)], ['101'])).
% 0.38/0.59  thf('103', plain,
% 0.38/0.59      (((m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('clc', [status(thm)], ['7', '8'])).
% 0.38/0.59  thf('104', plain,
% 0.38/0.59      (((v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('simplify', [status(thm)], ['76'])).
% 0.38/0.59  thf('105', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('106', plain,
% 0.38/0.59      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.38/0.59          | ~ (r2_hidden @ X10 @ (k2_pre_topc @ X9 @ X8))
% 0.38/0.59          | (v2_waybel_0 @ (sk_D_2 @ X10 @ X8 @ X9) @ 
% 0.38/0.59             (k3_yellow_1 @ (k2_struct_0 @ X9)))
% 0.38/0.59          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.38/0.59          | ~ (l1_pre_topc @ X9)
% 0.38/0.59          | ~ (v2_pre_topc @ X9)
% 0.38/0.59          | (v2_struct_0 @ X9))),
% 0.38/0.59      inference('cnf', [status(esa)], [t27_yellow19])).
% 0.38/0.59  thf('107', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((v2_struct_0 @ sk_A)
% 0.38/0.59          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.59          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.59          | (v2_waybel_0 @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ 
% 0.38/0.59             (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.59          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['105', '106'])).
% 0.38/0.59  thf('108', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('109', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('110', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((v2_struct_0 @ sk_A)
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.59          | (v2_waybel_0 @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ 
% 0.38/0.59             (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.59          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.38/0.59      inference('demod', [status(thm)], ['107', '108', '109'])).
% 0.38/0.59  thf('111', plain,
% 0.38/0.59      (((v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | (v2_waybel_0 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.38/0.59           (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.59        | ~ (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.38/0.59        | (v2_struct_0 @ sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['104', '110'])).
% 0.38/0.59  thf('112', plain,
% 0.38/0.59      ((~ (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.38/0.59        | (v2_waybel_0 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.38/0.59           (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.59        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('simplify', [status(thm)], ['111'])).
% 0.38/0.59  thf('113', plain,
% 0.38/0.59      (((v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | (v2_waybel_0 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.38/0.59           (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.38/0.59      inference('sup-', [status(thm)], ['103', '112'])).
% 0.38/0.59  thf('114', plain,
% 0.38/0.59      (((v2_waybel_0 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.38/0.59         (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.59        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('simplify', [status(thm)], ['113'])).
% 0.38/0.59  thf('115', plain,
% 0.38/0.59      (((m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('clc', [status(thm)], ['7', '8'])).
% 0.38/0.59  thf('116', plain,
% 0.38/0.59      (((v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('simplify', [status(thm)], ['76'])).
% 0.38/0.59  thf('117', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('118', plain,
% 0.38/0.59      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.38/0.59          | ~ (r2_hidden @ X10 @ (k2_pre_topc @ X9 @ X8))
% 0.38/0.59          | (v13_waybel_0 @ (sk_D_2 @ X10 @ X8 @ X9) @ 
% 0.38/0.59             (k3_yellow_1 @ (k2_struct_0 @ X9)))
% 0.38/0.59          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.38/0.59          | ~ (l1_pre_topc @ X9)
% 0.38/0.59          | ~ (v2_pre_topc @ X9)
% 0.38/0.59          | (v2_struct_0 @ X9))),
% 0.38/0.59      inference('cnf', [status(esa)], [t27_yellow19])).
% 0.38/0.59  thf('119', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((v2_struct_0 @ sk_A)
% 0.38/0.59          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.59          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.59          | (v13_waybel_0 @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ 
% 0.38/0.59             (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.59          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['117', '118'])).
% 0.38/0.59  thf('120', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('121', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('122', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((v2_struct_0 @ sk_A)
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.59          | (v13_waybel_0 @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ 
% 0.38/0.59             (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.59          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.38/0.59      inference('demod', [status(thm)], ['119', '120', '121'])).
% 0.38/0.59  thf('123', plain,
% 0.38/0.59      (((v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | (v13_waybel_0 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.38/0.59           (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.59        | ~ (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.38/0.59        | (v2_struct_0 @ sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['116', '122'])).
% 0.38/0.59  thf('124', plain,
% 0.38/0.59      ((~ (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.38/0.59        | (v13_waybel_0 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.38/0.59           (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.59        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('simplify', [status(thm)], ['123'])).
% 0.38/0.59  thf('125', plain,
% 0.38/0.59      (((v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | (v13_waybel_0 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.38/0.59           (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.38/0.59      inference('sup-', [status(thm)], ['115', '124'])).
% 0.38/0.59  thf('126', plain,
% 0.38/0.59      (((v13_waybel_0 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.38/0.59         (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.59        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('simplify', [status(thm)], ['125'])).
% 0.38/0.59  thf('127', plain,
% 0.38/0.59      (((m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('clc', [status(thm)], ['7', '8'])).
% 0.38/0.59  thf('128', plain,
% 0.38/0.59      (((v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('simplify', [status(thm)], ['76'])).
% 0.38/0.59  thf('129', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('130', plain,
% 0.38/0.59      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.38/0.59          | ~ (r2_hidden @ X10 @ (k2_pre_topc @ X9 @ X8))
% 0.38/0.59          | (v1_subset_1 @ (sk_D_2 @ X10 @ X8 @ X9) @ 
% 0.38/0.59             (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X9))))
% 0.38/0.59          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.38/0.59          | ~ (l1_pre_topc @ X9)
% 0.38/0.59          | ~ (v2_pre_topc @ X9)
% 0.38/0.59          | (v2_struct_0 @ X9))),
% 0.38/0.59      inference('cnf', [status(esa)], [t27_yellow19])).
% 0.38/0.59  thf('131', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((v2_struct_0 @ sk_A)
% 0.38/0.59          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.59          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.59          | (v1_subset_1 @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ 
% 0.38/0.59             (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.38/0.59          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['129', '130'])).
% 0.38/0.59  thf('132', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('133', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('134', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((v2_struct_0 @ sk_A)
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.59          | (v1_subset_1 @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ 
% 0.38/0.59             (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.38/0.59          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.38/0.59      inference('demod', [status(thm)], ['131', '132', '133'])).
% 0.38/0.59  thf('135', plain,
% 0.38/0.59      (((v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | (v1_subset_1 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.38/0.59           (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.38/0.59        | ~ (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.38/0.59        | (v2_struct_0 @ sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['128', '134'])).
% 0.38/0.59  thf('136', plain,
% 0.38/0.59      ((~ (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.38/0.59        | (v1_subset_1 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.38/0.59           (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.38/0.59        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('simplify', [status(thm)], ['135'])).
% 0.38/0.59  thf('137', plain,
% 0.38/0.59      (((v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | (v1_subset_1 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.38/0.59           (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.38/0.59      inference('sup-', [status(thm)], ['127', '136'])).
% 0.38/0.59  thf('138', plain,
% 0.38/0.59      (((v1_subset_1 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.38/0.59         (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.38/0.59        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('simplify', [status(thm)], ['137'])).
% 0.38/0.59  thf('139', plain,
% 0.38/0.59      (((m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('clc', [status(thm)], ['7', '8'])).
% 0.38/0.59  thf('140', plain,
% 0.38/0.59      (((v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('simplify', [status(thm)], ['76'])).
% 0.38/0.59  thf('141', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('142', plain,
% 0.38/0.59      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.38/0.59          | ~ (r2_hidden @ X10 @ (k2_pre_topc @ X9 @ X8))
% 0.38/0.59          | (m1_subset_1 @ (sk_D_2 @ X10 @ X8 @ X9) @ 
% 0.38/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X9)))))
% 0.38/0.59          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.38/0.59          | ~ (l1_pre_topc @ X9)
% 0.38/0.59          | ~ (v2_pre_topc @ X9)
% 0.38/0.59          | (v2_struct_0 @ X9))),
% 0.38/0.59      inference('cnf', [status(esa)], [t27_yellow19])).
% 0.38/0.59  thf('143', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((v2_struct_0 @ sk_A)
% 0.38/0.59          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.59          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.59          | (m1_subset_1 @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ 
% 0.38/0.59             (k1_zfmisc_1 @ 
% 0.38/0.59              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.38/0.59          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['141', '142'])).
% 0.38/0.59  thf('144', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('145', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('146', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((v2_struct_0 @ sk_A)
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.59          | (m1_subset_1 @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ 
% 0.38/0.59             (k1_zfmisc_1 @ 
% 0.38/0.59              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.38/0.59          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.38/0.59      inference('demod', [status(thm)], ['143', '144', '145'])).
% 0.38/0.59  thf('147', plain,
% 0.38/0.59      (((v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | (m1_subset_1 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.38/0.59           (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.38/0.59        | ~ (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.38/0.59        | (v2_struct_0 @ sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['140', '146'])).
% 0.38/0.59  thf('148', plain,
% 0.38/0.59      ((~ (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.38/0.59        | (m1_subset_1 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.38/0.59           (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.38/0.59        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('simplify', [status(thm)], ['147'])).
% 0.38/0.59  thf('149', plain,
% 0.38/0.59      (((v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | (m1_subset_1 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.38/0.59           (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.59      inference('sup-', [status(thm)], ['139', '148'])).
% 0.38/0.59  thf('150', plain,
% 0.38/0.59      (((m1_subset_1 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.38/0.59         (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.38/0.59        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59        | (v2_struct_0 @ sk_A)
% 0.38/0.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.59      inference('simplify', [status(thm)], ['149'])).
% 0.38/0.59  thf('151', plain,
% 0.38/0.59      ((![X12 : $i, X13 : $i]:
% 0.38/0.59          ((v1_xboole_0 @ X12)
% 0.38/0.59           | ~ (v1_subset_1 @ X12 @ 
% 0.38/0.59                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.38/0.59           | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.59           | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.59           | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.59                (k1_zfmisc_1 @ 
% 0.38/0.59                 (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.38/0.59           | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.38/0.59           | (r2_hidden @ X13 @ sk_B)
% 0.38/0.59           | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.38/0.59           | ~ (r2_hidden @ sk_B @ X12)))
% 0.38/0.59         <= ((![X12 : $i, X13 : $i]:
% 0.38/0.59                ((v1_xboole_0 @ X12)
% 0.38/0.59                 | ~ (v1_subset_1 @ X12 @ 
% 0.38/0.59                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.38/0.59                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.59                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.59                 | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.59                      (k1_zfmisc_1 @ 
% 0.38/0.59                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.38/0.59                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.38/0.59                 | (r2_hidden @ X13 @ sk_B)
% 0.38/0.59                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.38/0.59                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.38/0.59      inference('split', [status(esa)], ['0'])).
% 0.38/0.59  thf('152', plain,
% 0.38/0.59      ((![X0 : $i]:
% 0.38/0.59          ((v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59           | (v2_struct_0 @ sk_A)
% 0.38/0.59           | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59           | ~ (r2_hidden @ sk_B @ 
% 0.38/0.59                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.38/0.59           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.59           | (r2_hidden @ X0 @ sk_B)
% 0.38/0.59           | ~ (r1_waybel_7 @ sk_A @ 
% 0.38/0.59                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ X0)
% 0.38/0.59           | ~ (v13_waybel_0 @ 
% 0.38/0.59                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.38/0.59                (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.59           | ~ (v2_waybel_0 @ 
% 0.38/0.59                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.38/0.59                (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.59           | ~ (v1_subset_1 @ 
% 0.38/0.59                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.38/0.59                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.38/0.59           | (v1_xboole_0 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))))
% 0.38/0.59         <= ((![X12 : $i, X13 : $i]:
% 0.38/0.59                ((v1_xboole_0 @ X12)
% 0.38/0.59                 | ~ (v1_subset_1 @ X12 @ 
% 0.38/0.59                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.38/0.59                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.59                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.59                 | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.59                      (k1_zfmisc_1 @ 
% 0.38/0.59                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.38/0.59                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.38/0.59                 | (r2_hidden @ X13 @ sk_B)
% 0.38/0.59                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.38/0.59                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.38/0.59      inference('sup-', [status(thm)], ['150', '151'])).
% 0.38/0.59  thf('153', plain,
% 0.38/0.59      ((![X0 : $i]:
% 0.38/0.59          ((v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59           | (v2_struct_0 @ sk_A)
% 0.38/0.59           | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59           | (v1_xboole_0 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.38/0.59           | ~ (v2_waybel_0 @ 
% 0.38/0.59                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.38/0.59                (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.59           | ~ (v13_waybel_0 @ 
% 0.38/0.59                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.38/0.59                (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.59           | ~ (r1_waybel_7 @ sk_A @ 
% 0.38/0.59                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ X0)
% 0.38/0.59           | (r2_hidden @ X0 @ sk_B)
% 0.38/0.59           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.59           | ~ (r2_hidden @ sk_B @ 
% 0.38/0.59                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.38/0.59           | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59           | (v2_struct_0 @ sk_A)
% 0.38/0.59           | (v4_pre_topc @ sk_B @ sk_A)))
% 0.38/0.59         <= ((![X12 : $i, X13 : $i]:
% 0.38/0.59                ((v1_xboole_0 @ X12)
% 0.38/0.59                 | ~ (v1_subset_1 @ X12 @ 
% 0.38/0.59                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.38/0.59                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.59                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.59                 | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.59                      (k1_zfmisc_1 @ 
% 0.38/0.59                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.38/0.59                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.38/0.59                 | (r2_hidden @ X13 @ sk_B)
% 0.38/0.59                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.38/0.59                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.38/0.59      inference('sup-', [status(thm)], ['138', '152'])).
% 0.38/0.59  thf('154', plain,
% 0.38/0.59      ((![X0 : $i]:
% 0.38/0.59          (~ (r2_hidden @ sk_B @ 
% 0.38/0.59              (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.38/0.59           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.59           | (r2_hidden @ X0 @ sk_B)
% 0.38/0.59           | ~ (r1_waybel_7 @ sk_A @ 
% 0.38/0.59                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ X0)
% 0.38/0.59           | ~ (v13_waybel_0 @ 
% 0.38/0.59                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.38/0.59                (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.59           | ~ (v2_waybel_0 @ 
% 0.38/0.59                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.38/0.59                (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.59           | (v1_xboole_0 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.38/0.59           | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59           | (v2_struct_0 @ sk_A)
% 0.38/0.59           | (v4_pre_topc @ sk_B @ sk_A)))
% 0.38/0.59         <= ((![X12 : $i, X13 : $i]:
% 0.38/0.59                ((v1_xboole_0 @ X12)
% 0.38/0.59                 | ~ (v1_subset_1 @ X12 @ 
% 0.38/0.59                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.38/0.59                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.59                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.59                 | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.59                      (k1_zfmisc_1 @ 
% 0.38/0.59                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.38/0.59                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.38/0.59                 | (r2_hidden @ X13 @ sk_B)
% 0.38/0.59                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.38/0.59                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.38/0.59      inference('simplify', [status(thm)], ['153'])).
% 0.38/0.59  thf('155', plain,
% 0.38/0.59      ((![X0 : $i]:
% 0.38/0.59          ((v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59           | (v2_struct_0 @ sk_A)
% 0.38/0.59           | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.59           | (v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.59           | (v2_struct_0 @ sk_A)
% 0.38/0.60           | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.60           | (v1_xboole_0 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.38/0.60           | ~ (v2_waybel_0 @ 
% 0.38/0.60                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.38/0.60                (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60           | ~ (r1_waybel_7 @ sk_A @ 
% 0.38/0.60                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ X0)
% 0.38/0.60           | (r2_hidden @ X0 @ sk_B)
% 0.38/0.60           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.60           | ~ (r2_hidden @ sk_B @ 
% 0.38/0.60                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))))
% 0.38/0.60         <= ((![X12 : $i, X13 : $i]:
% 0.38/0.60                ((v1_xboole_0 @ X12)
% 0.38/0.60                 | ~ (v1_subset_1 @ X12 @ 
% 0.38/0.60                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.38/0.60                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60                 | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.60                      (k1_zfmisc_1 @ 
% 0.38/0.60                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.38/0.60                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.38/0.60                 | (r2_hidden @ X13 @ sk_B)
% 0.38/0.60                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.38/0.60                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['126', '154'])).
% 0.38/0.60  thf('156', plain,
% 0.38/0.60      ((![X0 : $i]:
% 0.38/0.60          (~ (r2_hidden @ sk_B @ 
% 0.38/0.60              (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.38/0.60           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.60           | (r2_hidden @ X0 @ sk_B)
% 0.38/0.60           | ~ (r1_waybel_7 @ sk_A @ 
% 0.38/0.60                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ X0)
% 0.38/0.60           | ~ (v2_waybel_0 @ 
% 0.38/0.60                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.38/0.60                (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60           | (v1_xboole_0 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.38/0.60           | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.60           | (v2_struct_0 @ sk_A)
% 0.38/0.60           | (v4_pre_topc @ sk_B @ sk_A)))
% 0.38/0.60         <= ((![X12 : $i, X13 : $i]:
% 0.38/0.60                ((v1_xboole_0 @ X12)
% 0.38/0.60                 | ~ (v1_subset_1 @ X12 @ 
% 0.38/0.60                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.38/0.60                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60                 | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.60                      (k1_zfmisc_1 @ 
% 0.38/0.60                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.38/0.60                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.38/0.60                 | (r2_hidden @ X13 @ sk_B)
% 0.38/0.60                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.38/0.60                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.38/0.60      inference('simplify', [status(thm)], ['155'])).
% 0.38/0.60  thf('157', plain,
% 0.38/0.60      ((![X0 : $i]:
% 0.38/0.60          ((v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.60           | (v2_struct_0 @ sk_A)
% 0.38/0.60           | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.60           | (v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.60           | (v2_struct_0 @ sk_A)
% 0.38/0.60           | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.60           | (v1_xboole_0 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.38/0.60           | ~ (r1_waybel_7 @ sk_A @ 
% 0.38/0.60                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ X0)
% 0.38/0.60           | (r2_hidden @ X0 @ sk_B)
% 0.38/0.60           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.60           | ~ (r2_hidden @ sk_B @ 
% 0.38/0.60                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))))
% 0.38/0.60         <= ((![X12 : $i, X13 : $i]:
% 0.38/0.60                ((v1_xboole_0 @ X12)
% 0.38/0.60                 | ~ (v1_subset_1 @ X12 @ 
% 0.38/0.60                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.38/0.60                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60                 | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.60                      (k1_zfmisc_1 @ 
% 0.38/0.60                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.38/0.60                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.38/0.60                 | (r2_hidden @ X13 @ sk_B)
% 0.38/0.60                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.38/0.60                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['114', '156'])).
% 0.38/0.60  thf('158', plain,
% 0.38/0.60      ((![X0 : $i]:
% 0.38/0.60          (~ (r2_hidden @ sk_B @ 
% 0.38/0.60              (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.38/0.60           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.60           | (r2_hidden @ X0 @ sk_B)
% 0.38/0.60           | ~ (r1_waybel_7 @ sk_A @ 
% 0.38/0.60                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ X0)
% 0.38/0.60           | (v1_xboole_0 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.38/0.60           | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.60           | (v2_struct_0 @ sk_A)
% 0.38/0.60           | (v4_pre_topc @ sk_B @ sk_A)))
% 0.38/0.60         <= ((![X12 : $i, X13 : $i]:
% 0.38/0.60                ((v1_xboole_0 @ X12)
% 0.38/0.60                 | ~ (v1_subset_1 @ X12 @ 
% 0.38/0.60                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.38/0.60                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60                 | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.60                      (k1_zfmisc_1 @ 
% 0.38/0.60                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.38/0.60                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.38/0.60                 | (r2_hidden @ X13 @ sk_B)
% 0.38/0.60                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.38/0.60                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.38/0.60      inference('simplify', [status(thm)], ['157'])).
% 0.38/0.60  thf('159', plain,
% 0.38/0.60      ((![X0 : $i]:
% 0.38/0.60          ((v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.60           | (v2_struct_0 @ sk_A)
% 0.38/0.60           | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.60           | (v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.60           | (v2_struct_0 @ sk_A)
% 0.38/0.60           | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.60           | (v1_xboole_0 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.38/0.60           | ~ (r1_waybel_7 @ sk_A @ 
% 0.38/0.60                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ X0)
% 0.38/0.60           | (r2_hidden @ X0 @ sk_B)
% 0.38/0.60           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.38/0.60         <= ((![X12 : $i, X13 : $i]:
% 0.38/0.60                ((v1_xboole_0 @ X12)
% 0.38/0.60                 | ~ (v1_subset_1 @ X12 @ 
% 0.38/0.60                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.38/0.60                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60                 | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.60                      (k1_zfmisc_1 @ 
% 0.38/0.60                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.38/0.60                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.38/0.60                 | (r2_hidden @ X13 @ sk_B)
% 0.38/0.60                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.38/0.60                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['102', '158'])).
% 0.38/0.60  thf('160', plain,
% 0.38/0.60      ((![X0 : $i]:
% 0.38/0.60          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.60           | (r2_hidden @ X0 @ sk_B)
% 0.38/0.60           | ~ (r1_waybel_7 @ sk_A @ 
% 0.38/0.60                (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A) @ X0)
% 0.38/0.60           | (v1_xboole_0 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.38/0.60           | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.60           | (v2_struct_0 @ sk_A)
% 0.38/0.60           | (v4_pre_topc @ sk_B @ sk_A)))
% 0.38/0.60         <= ((![X12 : $i, X13 : $i]:
% 0.38/0.60                ((v1_xboole_0 @ X12)
% 0.38/0.60                 | ~ (v1_subset_1 @ X12 @ 
% 0.38/0.60                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.38/0.60                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60                 | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.60                      (k1_zfmisc_1 @ 
% 0.38/0.60                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.38/0.60                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.38/0.60                 | (r2_hidden @ X13 @ sk_B)
% 0.38/0.60                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.38/0.60                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.38/0.60      inference('simplify', [status(thm)], ['159'])).
% 0.38/0.60  thf('161', plain,
% 0.38/0.60      ((((v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.60         | (v2_struct_0 @ sk_A)
% 0.38/0.60         | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.60         | (v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.60         | (v2_struct_0 @ sk_A)
% 0.38/0.60         | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.60         | (v1_xboole_0 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.38/0.60         | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ sk_B)
% 0.38/0.60         | ~ (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.38/0.60         <= ((![X12 : $i, X13 : $i]:
% 0.38/0.60                ((v1_xboole_0 @ X12)
% 0.38/0.60                 | ~ (v1_subset_1 @ X12 @ 
% 0.38/0.60                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.38/0.60                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60                 | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.60                      (k1_zfmisc_1 @ 
% 0.38/0.60                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.38/0.60                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.38/0.60                 | (r2_hidden @ X13 @ sk_B)
% 0.38/0.60                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.38/0.60                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['90', '160'])).
% 0.38/0.60  thf('162', plain,
% 0.38/0.60      (((~ (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.38/0.60         | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ sk_B)
% 0.38/0.60         | (v1_xboole_0 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.38/0.60         | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.60         | (v2_struct_0 @ sk_A)
% 0.38/0.60         | (v4_pre_topc @ sk_B @ sk_A)))
% 0.38/0.60         <= ((![X12 : $i, X13 : $i]:
% 0.38/0.60                ((v1_xboole_0 @ X12)
% 0.38/0.60                 | ~ (v1_subset_1 @ X12 @ 
% 0.38/0.60                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.38/0.60                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60                 | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.60                      (k1_zfmisc_1 @ 
% 0.38/0.60                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.38/0.60                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.38/0.60                 | (r2_hidden @ X13 @ sk_B)
% 0.38/0.60                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.38/0.60                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.38/0.60      inference('simplify', [status(thm)], ['161'])).
% 0.38/0.60  thf('163', plain,
% 0.38/0.60      ((((v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.60         | (v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.60         | (v2_struct_0 @ sk_A)
% 0.38/0.60         | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.60         | (v1_xboole_0 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.38/0.60         | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ sk_B)))
% 0.38/0.60         <= ((![X12 : $i, X13 : $i]:
% 0.38/0.60                ((v1_xboole_0 @ X12)
% 0.38/0.60                 | ~ (v1_subset_1 @ X12 @ 
% 0.38/0.60                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.38/0.60                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60                 | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.60                      (k1_zfmisc_1 @ 
% 0.38/0.60                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.38/0.60                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.38/0.60                 | (r2_hidden @ X13 @ sk_B)
% 0.38/0.60                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.38/0.60                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['78', '162'])).
% 0.38/0.60  thf('164', plain,
% 0.38/0.60      ((((r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ sk_B)
% 0.38/0.60         | (v1_xboole_0 @ (sk_D_2 @ (sk_D_1 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.38/0.60         | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.60         | (v2_struct_0 @ sk_A)
% 0.38/0.60         | (v4_pre_topc @ sk_B @ sk_A)))
% 0.38/0.60         <= ((![X12 : $i, X13 : $i]:
% 0.38/0.60                ((v1_xboole_0 @ X12)
% 0.38/0.60                 | ~ (v1_subset_1 @ X12 @ 
% 0.38/0.60                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.38/0.60                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60                 | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.60                      (k1_zfmisc_1 @ 
% 0.38/0.60                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.38/0.60                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.38/0.60                 | (r2_hidden @ X13 @ sk_B)
% 0.38/0.60                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.38/0.60                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.38/0.60      inference('simplify', [status(thm)], ['163'])).
% 0.38/0.60  thf('165', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('166', plain,
% 0.38/0.60      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.38/0.60          | ~ (r2_hidden @ X10 @ (k2_pre_topc @ X9 @ X8))
% 0.38/0.60          | ~ (v1_xboole_0 @ (sk_D_2 @ X10 @ X8 @ X9))
% 0.38/0.60          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.38/0.60          | ~ (l1_pre_topc @ X9)
% 0.38/0.60          | ~ (v2_pre_topc @ X9)
% 0.38/0.60          | (v2_struct_0 @ X9))),
% 0.38/0.60      inference('cnf', [status(esa)], [t27_yellow19])).
% 0.38/0.60  thf('167', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_A)
% 0.38/0.60          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.60          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.60          | ~ (v1_xboole_0 @ (sk_D_2 @ X0 @ sk_B @ sk_A))
% 0.38/0.60          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['165', '166'])).
% 0.38/0.60  thf('168', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('169', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('170', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_A)
% 0.38/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.60          | ~ (v1_xboole_0 @ (sk_D_2 @ X0 @ sk_B @ sk_A))
% 0.38/0.60          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.38/0.60      inference('demod', [status(thm)], ['167', '168', '169'])).
% 0.38/0.60  thf('171', plain,
% 0.38/0.60      ((((v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.60         | (v2_struct_0 @ sk_A)
% 0.38/0.60         | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.60         | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ sk_B)
% 0.38/0.60         | ~ (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.38/0.60         | ~ (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.38/0.60         | (v2_struct_0 @ sk_A)))
% 0.38/0.60         <= ((![X12 : $i, X13 : $i]:
% 0.38/0.60                ((v1_xboole_0 @ X12)
% 0.38/0.60                 | ~ (v1_subset_1 @ X12 @ 
% 0.38/0.60                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.38/0.60                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60                 | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.60                      (k1_zfmisc_1 @ 
% 0.38/0.60                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.38/0.60                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.38/0.60                 | (r2_hidden @ X13 @ sk_B)
% 0.38/0.60                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.38/0.60                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['164', '170'])).
% 0.38/0.60  thf('172', plain,
% 0.38/0.60      (((~ (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.38/0.60         | ~ (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.38/0.60         | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ sk_B)
% 0.38/0.60         | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.60         | (v2_struct_0 @ sk_A)
% 0.38/0.60         | (v4_pre_topc @ sk_B @ sk_A)))
% 0.38/0.60         <= ((![X12 : $i, X13 : $i]:
% 0.38/0.60                ((v1_xboole_0 @ X12)
% 0.38/0.60                 | ~ (v1_subset_1 @ X12 @ 
% 0.38/0.60                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.38/0.60                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60                 | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.60                      (k1_zfmisc_1 @ 
% 0.38/0.60                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.38/0.60                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.38/0.60                 | (r2_hidden @ X13 @ sk_B)
% 0.38/0.60                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.38/0.60                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.38/0.60      inference('simplify', [status(thm)], ['171'])).
% 0.38/0.60  thf('173', plain,
% 0.38/0.60      ((((v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.60         | (v2_struct_0 @ sk_A)
% 0.38/0.60         | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.60         | (v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.60         | (v2_struct_0 @ sk_A)
% 0.38/0.60         | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.60         | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ sk_B)
% 0.38/0.60         | ~ (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.38/0.60         <= ((![X12 : $i, X13 : $i]:
% 0.38/0.60                ((v1_xboole_0 @ X12)
% 0.38/0.60                 | ~ (v1_subset_1 @ X12 @ 
% 0.38/0.60                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.38/0.60                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60                 | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.60                      (k1_zfmisc_1 @ 
% 0.38/0.60                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.38/0.60                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.38/0.60                 | (r2_hidden @ X13 @ sk_B)
% 0.38/0.60                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.38/0.60                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['77', '172'])).
% 0.38/0.60  thf('174', plain,
% 0.38/0.60      (((~ (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.38/0.60         | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ sk_B)
% 0.38/0.60         | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.60         | (v2_struct_0 @ sk_A)
% 0.38/0.60         | (v4_pre_topc @ sk_B @ sk_A)))
% 0.38/0.60         <= ((![X12 : $i, X13 : $i]:
% 0.38/0.60                ((v1_xboole_0 @ X12)
% 0.38/0.60                 | ~ (v1_subset_1 @ X12 @ 
% 0.38/0.60                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.38/0.60                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60                 | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.60                      (k1_zfmisc_1 @ 
% 0.38/0.60                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.38/0.60                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.38/0.60                 | (r2_hidden @ X13 @ sk_B)
% 0.38/0.60                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.38/0.60                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.38/0.60      inference('simplify', [status(thm)], ['173'])).
% 0.38/0.60  thf('175', plain,
% 0.38/0.60      ((((v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.60         | (v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.60         | (v2_struct_0 @ sk_A)
% 0.38/0.60         | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.60         | (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ sk_B)))
% 0.38/0.60         <= ((![X12 : $i, X13 : $i]:
% 0.38/0.60                ((v1_xboole_0 @ X12)
% 0.38/0.60                 | ~ (v1_subset_1 @ X12 @ 
% 0.38/0.60                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.38/0.60                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60                 | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.60                      (k1_zfmisc_1 @ 
% 0.38/0.60                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.38/0.60                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.38/0.60                 | (r2_hidden @ X13 @ sk_B)
% 0.38/0.60                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.38/0.60                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['9', '174'])).
% 0.38/0.60  thf('176', plain,
% 0.38/0.60      ((((r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ sk_B)
% 0.38/0.60         | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.60         | (v2_struct_0 @ sk_A)
% 0.38/0.60         | (v4_pre_topc @ sk_B @ sk_A)))
% 0.38/0.60         <= ((![X12 : $i, X13 : $i]:
% 0.38/0.60                ((v1_xboole_0 @ X12)
% 0.38/0.60                 | ~ (v1_subset_1 @ X12 @ 
% 0.38/0.60                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.38/0.60                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60                 | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.60                      (k1_zfmisc_1 @ 
% 0.38/0.60                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.38/0.60                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.38/0.60                 | (r2_hidden @ X13 @ sk_B)
% 0.38/0.60                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.38/0.60                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.38/0.60      inference('simplify', [status(thm)], ['175'])).
% 0.38/0.60  thf('177', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('178', plain,
% 0.38/0.60      (![X4 : $i, X5 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.38/0.60          | ~ (r2_hidden @ (sk_D_1 @ X4 @ X5) @ X4)
% 0.38/0.60          | (v4_pre_topc @ X4 @ X5)
% 0.38/0.60          | ~ (l1_pre_topc @ X5)
% 0.38/0.60          | ~ (v2_pre_topc @ X5)
% 0.38/0.60          | (v2_struct_0 @ X5))),
% 0.38/0.60      inference('cnf', [status(esa)], [t26_yellow19])).
% 0.38/0.60  thf('179', plain,
% 0.38/0.60      (((v2_struct_0 @ sk_A)
% 0.38/0.60        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.60        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.60        | (v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.60        | ~ (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ sk_B))),
% 0.38/0.60      inference('sup-', [status(thm)], ['177', '178'])).
% 0.38/0.60  thf('180', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('181', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('182', plain,
% 0.38/0.60      (((v2_struct_0 @ sk_A)
% 0.38/0.60        | (v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.60        | ~ (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ sk_B))),
% 0.38/0.60      inference('demod', [status(thm)], ['179', '180', '181'])).
% 0.38/0.60  thf('183', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('184', plain,
% 0.38/0.60      ((~ (r2_hidden @ (sk_D_1 @ sk_B @ sk_A) @ sk_B)
% 0.38/0.60        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.60      inference('clc', [status(thm)], ['182', '183'])).
% 0.38/0.60  thf('185', plain,
% 0.38/0.60      ((((v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.60         | (v2_struct_0 @ sk_A)
% 0.38/0.60         | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.60         | (v4_pre_topc @ sk_B @ sk_A)))
% 0.38/0.60         <= ((![X12 : $i, X13 : $i]:
% 0.38/0.60                ((v1_xboole_0 @ X12)
% 0.38/0.60                 | ~ (v1_subset_1 @ X12 @ 
% 0.38/0.60                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.38/0.60                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60                 | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.60                      (k1_zfmisc_1 @ 
% 0.38/0.60                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.38/0.60                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.38/0.60                 | (r2_hidden @ X13 @ sk_B)
% 0.38/0.60                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.38/0.60                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['176', '184'])).
% 0.38/0.60  thf('186', plain,
% 0.38/0.60      ((((v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.60         | (v2_struct_0 @ sk_A)
% 0.38/0.60         | (v4_pre_topc @ sk_B @ sk_A)))
% 0.38/0.60         <= ((![X12 : $i, X13 : $i]:
% 0.38/0.60                ((v1_xboole_0 @ X12)
% 0.38/0.60                 | ~ (v1_subset_1 @ X12 @ 
% 0.38/0.60                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.38/0.60                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60                 | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.60                      (k1_zfmisc_1 @ 
% 0.38/0.60                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.38/0.60                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.38/0.60                 | (r2_hidden @ X13 @ sk_B)
% 0.38/0.60                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.38/0.60                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.38/0.60      inference('simplify', [status(thm)], ['185'])).
% 0.38/0.60  thf('187', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('188', plain,
% 0.38/0.60      (![X4 : $i, X5 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.38/0.60          | ~ (v2_struct_0 @ (sk_C @ X4 @ X5))
% 0.38/0.60          | (v4_pre_topc @ X4 @ X5)
% 0.38/0.60          | ~ (l1_pre_topc @ X5)
% 0.38/0.60          | ~ (v2_pre_topc @ X5)
% 0.38/0.60          | (v2_struct_0 @ X5))),
% 0.38/0.60      inference('cnf', [status(esa)], [t26_yellow19])).
% 0.38/0.60  thf('189', plain,
% 0.38/0.60      (((v2_struct_0 @ sk_A)
% 0.38/0.60        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.60        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.60        | (v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.60        | ~ (v2_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['187', '188'])).
% 0.38/0.60  thf('190', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('191', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('192', plain,
% 0.38/0.60      (((v2_struct_0 @ sk_A)
% 0.38/0.60        | (v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.60        | ~ (v2_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.38/0.60      inference('demod', [status(thm)], ['189', '190', '191'])).
% 0.38/0.60  thf('193', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('194', plain,
% 0.38/0.60      ((~ (v2_struct_0 @ (sk_C @ sk_B @ sk_A)) | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.60      inference('clc', [status(thm)], ['192', '193'])).
% 0.38/0.60  thf('195', plain,
% 0.38/0.60      ((((v4_pre_topc @ sk_B @ sk_A) | (v2_struct_0 @ sk_A)))
% 0.38/0.60         <= ((![X12 : $i, X13 : $i]:
% 0.38/0.60                ((v1_xboole_0 @ X12)
% 0.38/0.60                 | ~ (v1_subset_1 @ X12 @ 
% 0.38/0.60                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.38/0.60                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60                 | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.60                      (k1_zfmisc_1 @ 
% 0.38/0.60                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.38/0.60                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.38/0.60                 | (r2_hidden @ X13 @ sk_B)
% 0.38/0.60                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.38/0.60                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.38/0.60      inference('clc', [status(thm)], ['186', '194'])).
% 0.38/0.60  thf('196', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('197', plain,
% 0.38/0.60      (((v4_pre_topc @ sk_B @ sk_A))
% 0.38/0.60         <= ((![X12 : $i, X13 : $i]:
% 0.38/0.60                ((v1_xboole_0 @ X12)
% 0.38/0.60                 | ~ (v1_subset_1 @ X12 @ 
% 0.38/0.60                      (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.38/0.60                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60                 | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.60                      (k1_zfmisc_1 @ 
% 0.38/0.60                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.38/0.60                 | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.38/0.60                 | (r2_hidden @ X13 @ sk_B)
% 0.38/0.60                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.38/0.60                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.38/0.60      inference('clc', [status(thm)], ['195', '196'])).
% 0.38/0.60  thf('198', plain,
% 0.38/0.60      (((r2_hidden @ sk_B @ sk_C_1) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('199', plain,
% 0.38/0.60      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.38/0.60      inference('split', [status(esa)], ['198'])).
% 0.38/0.60  thf('200', plain,
% 0.38/0.60      (~
% 0.38/0.60       (![X12 : $i, X13 : $i]:
% 0.38/0.60          ((v1_xboole_0 @ X12)
% 0.38/0.60           | ~ (v1_subset_1 @ X12 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.38/0.60           | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60           | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60           | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.60                (k1_zfmisc_1 @ 
% 0.38/0.60                 (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.38/0.60           | ~ (r1_waybel_7 @ sk_A @ X12 @ X13)
% 0.38/0.60           | (r2_hidden @ X13 @ sk_B)
% 0.38/0.60           | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.38/0.60           | ~ (r2_hidden @ sk_B @ X12))) | 
% 0.38/0.60       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.60      inference('sup-', [status(thm)], ['197', '199'])).
% 0.38/0.60  thf('201', plain,
% 0.38/0.60      (((r2_hidden @ sk_B @ sk_C_1)) | ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.60      inference('split', [status(esa)], ['198'])).
% 0.38/0.60  thf('202', plain,
% 0.38/0.60      (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))
% 0.38/0.60        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('203', plain,
% 0.38/0.60      (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) | 
% 0.38/0.60       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.60      inference('split', [status(esa)], ['202'])).
% 0.38/0.60  thf('204', plain,
% 0.38/0.60      ((~ (r2_hidden @ sk_D_3 @ sk_B) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('205', plain,
% 0.38/0.60      (~ ((r2_hidden @ sk_D_3 @ sk_B)) | ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.60      inference('split', [status(esa)], ['204'])).
% 0.38/0.60  thf('206', plain,
% 0.38/0.60      (((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('207', plain,
% 0.38/0.60      (((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) | 
% 0.38/0.60       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.60      inference('split', [status(esa)], ['206'])).
% 0.38/0.60  thf('208', plain,
% 0.38/0.60      (((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60         (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.38/0.60        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('209', plain,
% 0.38/0.60      (((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60         (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) | 
% 0.38/0.60       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.60      inference('split', [status(esa)], ['208'])).
% 0.38/0.60  thf('210', plain,
% 0.38/0.60      (((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('211', plain,
% 0.38/0.60      (((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) | 
% 0.38/0.60       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.60      inference('split', [status(esa)], ['210'])).
% 0.38/0.60  thf('212', plain,
% 0.38/0.60      (((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('213', plain,
% 0.38/0.60      (((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) | 
% 0.38/0.60       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.60      inference('split', [status(esa)], ['212'])).
% 0.38/0.60  thf('214', plain,
% 0.38/0.60      (((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60         (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.38/0.60        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('215', plain,
% 0.38/0.60      (((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60         (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))) | 
% 0.38/0.60       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.60      inference('split', [status(esa)], ['214'])).
% 0.38/0.60  thf('216', plain,
% 0.38/0.60      ((~ (v1_xboole_0 @ sk_C_1) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('217', plain,
% 0.38/0.60      (~ ((v1_xboole_0 @ sk_C_1)) | ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.60      inference('split', [status(esa)], ['216'])).
% 0.38/0.60  thf('218', plain,
% 0.38/0.60      (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A)))
% 0.38/0.60         <= (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.60      inference('split', [status(esa)], ['202'])).
% 0.38/0.60  thf('219', plain,
% 0.38/0.60      (((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3))
% 0.38/0.60         <= (((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)))),
% 0.38/0.60      inference('split', [status(esa)], ['206'])).
% 0.38/0.60  thf('220', plain,
% 0.38/0.60      (((r2_hidden @ sk_B @ sk_C_1)) <= (((r2_hidden @ sk_B @ sk_C_1)))),
% 0.38/0.60      inference('split', [status(esa)], ['198'])).
% 0.38/0.60  thf('221', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('222', plain,
% 0.38/0.60      (((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.38/0.60         <= (((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.38/0.60      inference('split', [status(esa)], ['212'])).
% 0.38/0.60  thf('223', plain,
% 0.38/0.60      (((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.38/0.60         <= (((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.38/0.60      inference('split', [status(esa)], ['210'])).
% 0.38/0.60  thf('224', plain,
% 0.38/0.60      (((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60         (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.38/0.60         <= (((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('split', [status(esa)], ['214'])).
% 0.38/0.60  thf('225', plain,
% 0.38/0.60      (((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60         (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))
% 0.38/0.60         <= (((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))))),
% 0.38/0.60      inference('split', [status(esa)], ['208'])).
% 0.38/0.60  thf('226', plain,
% 0.38/0.60      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.38/0.60          | ~ (r1_waybel_7 @ X9 @ X11 @ X10)
% 0.38/0.60          | ~ (r2_hidden @ X8 @ X11)
% 0.38/0.60          | ~ (m1_subset_1 @ X11 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X9)))))
% 0.38/0.60          | ~ (v13_waybel_0 @ X11 @ (k3_yellow_1 @ (k2_struct_0 @ X9)))
% 0.38/0.60          | ~ (v2_waybel_0 @ X11 @ (k3_yellow_1 @ (k2_struct_0 @ X9)))
% 0.38/0.60          | ~ (v1_subset_1 @ X11 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X9))))
% 0.38/0.60          | (v1_xboole_0 @ X11)
% 0.38/0.60          | (r2_hidden @ X10 @ (k2_pre_topc @ X9 @ X8))
% 0.38/0.60          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.38/0.60          | ~ (l1_pre_topc @ X9)
% 0.38/0.60          | ~ (v2_pre_topc @ X9)
% 0.38/0.60          | (v2_struct_0 @ X9))),
% 0.38/0.60      inference('cnf', [status(esa)], [t27_yellow19])).
% 0.38/0.60  thf('227', plain,
% 0.38/0.60      ((![X0 : $i, X1 : $i]:
% 0.38/0.60          ((v2_struct_0 @ sk_A)
% 0.38/0.60           | ~ (v2_pre_topc @ sk_A)
% 0.38/0.60           | ~ (l1_pre_topc @ sk_A)
% 0.38/0.60           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.60           | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ X1))
% 0.38/0.60           | (v1_xboole_0 @ sk_C_1)
% 0.38/0.60           | ~ (v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.38/0.60           | ~ (v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60           | ~ (v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60           | ~ (r2_hidden @ X1 @ sk_C_1)
% 0.38/0.60           | ~ (r1_waybel_7 @ sk_A @ sk_C_1 @ X0)
% 0.38/0.60           | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.38/0.60         <= (((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['225', '226'])).
% 0.38/0.60  thf('228', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('229', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('230', plain,
% 0.38/0.60      ((![X0 : $i, X1 : $i]:
% 0.38/0.60          ((v2_struct_0 @ sk_A)
% 0.38/0.60           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.60           | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ X1))
% 0.38/0.60           | (v1_xboole_0 @ sk_C_1)
% 0.38/0.60           | ~ (v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.38/0.60           | ~ (v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60           | ~ (v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60           | ~ (r2_hidden @ X1 @ sk_C_1)
% 0.38/0.60           | ~ (r1_waybel_7 @ sk_A @ sk_C_1 @ X0)
% 0.38/0.60           | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.38/0.60         <= (((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))))),
% 0.38/0.60      inference('demod', [status(thm)], ['227', '228', '229'])).
% 0.38/0.60  thf('231', plain,
% 0.38/0.60      ((![X0 : $i, X1 : $i]:
% 0.38/0.60          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.60           | ~ (r1_waybel_7 @ sk_A @ sk_C_1 @ X1)
% 0.38/0.60           | ~ (r2_hidden @ X0 @ sk_C_1)
% 0.38/0.60           | ~ (v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60           | ~ (v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60           | (v1_xboole_0 @ sk_C_1)
% 0.38/0.60           | (r2_hidden @ X1 @ (k2_pre_topc @ sk_A @ X0))
% 0.38/0.60           | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.38/0.60           | (v2_struct_0 @ sk_A)))
% 0.38/0.60         <= (((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['224', '230'])).
% 0.38/0.60  thf('232', plain,
% 0.38/0.60      ((![X0 : $i, X1 : $i]:
% 0.38/0.60          ((v2_struct_0 @ sk_A)
% 0.38/0.60           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.60           | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ X1))
% 0.38/0.60           | (v1_xboole_0 @ sk_C_1)
% 0.38/0.60           | ~ (v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.38/0.60           | ~ (r2_hidden @ X1 @ sk_C_1)
% 0.38/0.60           | ~ (r1_waybel_7 @ sk_A @ sk_C_1 @ X0)
% 0.38/0.60           | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.38/0.60         <= (((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['223', '231'])).
% 0.38/0.60  thf('233', plain,
% 0.38/0.60      ((![X0 : $i, X1 : $i]:
% 0.38/0.60          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.60           | ~ (r1_waybel_7 @ sk_A @ sk_C_1 @ X1)
% 0.38/0.60           | ~ (r2_hidden @ X0 @ sk_C_1)
% 0.38/0.60           | (v1_xboole_0 @ sk_C_1)
% 0.38/0.60           | (r2_hidden @ X1 @ (k2_pre_topc @ sk_A @ X0))
% 0.38/0.60           | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.38/0.60           | (v2_struct_0 @ sk_A)))
% 0.38/0.60         <= (((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['222', '232'])).
% 0.38/0.60  thf('234', plain,
% 0.38/0.60      ((![X0 : $i]:
% 0.38/0.60          ((v2_struct_0 @ sk_A)
% 0.38/0.60           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.60           | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.38/0.60           | (v1_xboole_0 @ sk_C_1)
% 0.38/0.60           | ~ (r2_hidden @ sk_B @ sk_C_1)
% 0.38/0.60           | ~ (r1_waybel_7 @ sk_A @ sk_C_1 @ X0)))
% 0.38/0.60         <= (((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['221', '233'])).
% 0.38/0.60  thf('235', plain,
% 0.38/0.60      ((![X0 : $i]:
% 0.38/0.60          (~ (r1_waybel_7 @ sk_A @ sk_C_1 @ X0)
% 0.38/0.60           | (v1_xboole_0 @ sk_C_1)
% 0.38/0.60           | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.38/0.60           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.60           | (v2_struct_0 @ sk_A)))
% 0.38/0.60         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['220', '234'])).
% 0.38/0.60  thf('236', plain,
% 0.38/0.60      ((((v2_struct_0 @ sk_A)
% 0.38/0.60         | ~ (m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))
% 0.38/0.60         | (r2_hidden @ sk_D_3 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.38/0.60         | (v1_xboole_0 @ sk_C_1)))
% 0.38/0.60         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['219', '235'])).
% 0.38/0.60  thf('237', plain,
% 0.38/0.60      ((((v1_xboole_0 @ sk_C_1)
% 0.38/0.60         | (r2_hidden @ sk_D_3 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.38/0.60         | (v2_struct_0 @ sk_A)))
% 0.38/0.60         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['218', '236'])).
% 0.38/0.60  thf('238', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('239', plain,
% 0.38/0.60      ((((r2_hidden @ sk_D_3 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.38/0.60         | (v1_xboole_0 @ sk_C_1)))
% 0.38/0.60         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('clc', [status(thm)], ['237', '238'])).
% 0.38/0.60  thf('240', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('241', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.38/0.60          | ~ (r2_hidden @ X2 @ (k2_pre_topc @ X1 @ X0))
% 0.38/0.60          | (r2_hidden @ X2 @ (k10_yellow_6 @ X1 @ (sk_D @ X2 @ X0 @ X1)))
% 0.38/0.60          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.38/0.60          | ~ (l1_pre_topc @ X1)
% 0.38/0.60          | ~ (v2_pre_topc @ X1)
% 0.38/0.60          | (v2_struct_0 @ X1))),
% 0.38/0.60      inference('cnf', [status(esa)], [t24_yellow19])).
% 0.38/0.60  thf('242', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_A)
% 0.38/0.60          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.60          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.60          | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A)))
% 0.38/0.60          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['240', '241'])).
% 0.38/0.60  thf('243', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('244', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('245', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_A)
% 0.38/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.60          | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A)))
% 0.38/0.60          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.38/0.60      inference('demod', [status(thm)], ['242', '243', '244'])).
% 0.38/0.60  thf('246', plain,
% 0.38/0.60      ((((v1_xboole_0 @ sk_C_1)
% 0.38/0.60         | (r2_hidden @ sk_D_3 @ 
% 0.38/0.60            (k10_yellow_6 @ sk_A @ (sk_D @ sk_D_3 @ sk_B @ sk_A)))
% 0.38/0.60         | ~ (m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))
% 0.38/0.60         | (v2_struct_0 @ sk_A)))
% 0.38/0.60         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['239', '245'])).
% 0.38/0.60  thf('247', plain,
% 0.38/0.60      (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A)))
% 0.38/0.60         <= (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.60      inference('split', [status(esa)], ['202'])).
% 0.38/0.60  thf('248', plain,
% 0.38/0.60      ((((v1_xboole_0 @ sk_C_1)
% 0.38/0.60         | (r2_hidden @ sk_D_3 @ 
% 0.38/0.60            (k10_yellow_6 @ sk_A @ (sk_D @ sk_D_3 @ sk_B @ sk_A)))
% 0.38/0.60         | (v2_struct_0 @ sk_A)))
% 0.38/0.60         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('demod', [status(thm)], ['246', '247'])).
% 0.38/0.60  thf('249', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('250', plain,
% 0.38/0.60      ((((r2_hidden @ sk_D_3 @ 
% 0.38/0.60          (k10_yellow_6 @ sk_A @ (sk_D @ sk_D_3 @ sk_B @ sk_A)))
% 0.38/0.60         | (v1_xboole_0 @ sk_C_1)))
% 0.38/0.60         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('clc', [status(thm)], ['248', '249'])).
% 0.38/0.60  thf('251', plain,
% 0.38/0.60      ((((r2_hidden @ sk_D_3 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.38/0.60         | (v1_xboole_0 @ sk_C_1)))
% 0.38/0.60         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('clc', [status(thm)], ['237', '238'])).
% 0.38/0.60  thf('252', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('253', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.38/0.60          | ~ (r2_hidden @ X2 @ (k2_pre_topc @ X1 @ X0))
% 0.38/0.60          | (v7_waybel_0 @ (sk_D @ X2 @ X0 @ X1))
% 0.38/0.60          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.38/0.60          | ~ (l1_pre_topc @ X1)
% 0.38/0.60          | ~ (v2_pre_topc @ X1)
% 0.38/0.60          | (v2_struct_0 @ X1))),
% 0.38/0.60      inference('cnf', [status(esa)], [t24_yellow19])).
% 0.38/0.60  thf('254', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_A)
% 0.38/0.60          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.60          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.60          | (v7_waybel_0 @ (sk_D @ X0 @ sk_B @ sk_A))
% 0.38/0.60          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['252', '253'])).
% 0.38/0.60  thf('255', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('256', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('257', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_A)
% 0.38/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.60          | (v7_waybel_0 @ (sk_D @ X0 @ sk_B @ sk_A))
% 0.38/0.60          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.38/0.60      inference('demod', [status(thm)], ['254', '255', '256'])).
% 0.38/0.60  thf('258', plain,
% 0.38/0.60      ((((v1_xboole_0 @ sk_C_1)
% 0.38/0.60         | (v7_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.38/0.60         | ~ (m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))
% 0.38/0.60         | (v2_struct_0 @ sk_A)))
% 0.38/0.60         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['251', '257'])).
% 0.38/0.60  thf('259', plain,
% 0.38/0.60      (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A)))
% 0.38/0.60         <= (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.60      inference('split', [status(esa)], ['202'])).
% 0.38/0.60  thf('260', plain,
% 0.38/0.60      ((((v1_xboole_0 @ sk_C_1)
% 0.38/0.60         | (v7_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.38/0.60         | (v2_struct_0 @ sk_A)))
% 0.38/0.60         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('demod', [status(thm)], ['258', '259'])).
% 0.38/0.60  thf('261', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('262', plain,
% 0.38/0.60      ((((v7_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A)) | (v1_xboole_0 @ sk_C_1)))
% 0.38/0.60         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('clc', [status(thm)], ['260', '261'])).
% 0.38/0.60  thf('263', plain,
% 0.38/0.60      ((((r2_hidden @ sk_D_3 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.38/0.60         | (v1_xboole_0 @ sk_C_1)))
% 0.38/0.60         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('clc', [status(thm)], ['237', '238'])).
% 0.38/0.60  thf('264', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('265', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.38/0.60          | ~ (r2_hidden @ X2 @ (k2_pre_topc @ X1 @ X0))
% 0.38/0.60          | (v4_orders_2 @ (sk_D @ X2 @ X0 @ X1))
% 0.38/0.60          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.38/0.60          | ~ (l1_pre_topc @ X1)
% 0.38/0.60          | ~ (v2_pre_topc @ X1)
% 0.38/0.60          | (v2_struct_0 @ X1))),
% 0.38/0.60      inference('cnf', [status(esa)], [t24_yellow19])).
% 0.38/0.60  thf('266', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_A)
% 0.38/0.60          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.60          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.60          | (v4_orders_2 @ (sk_D @ X0 @ sk_B @ sk_A))
% 0.38/0.60          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['264', '265'])).
% 0.38/0.60  thf('267', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('268', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('269', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_A)
% 0.38/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.60          | (v4_orders_2 @ (sk_D @ X0 @ sk_B @ sk_A))
% 0.38/0.60          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.38/0.60      inference('demod', [status(thm)], ['266', '267', '268'])).
% 0.38/0.60  thf('270', plain,
% 0.38/0.60      ((((v1_xboole_0 @ sk_C_1)
% 0.38/0.60         | (v4_orders_2 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.38/0.60         | ~ (m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))
% 0.38/0.60         | (v2_struct_0 @ sk_A)))
% 0.38/0.60         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['263', '269'])).
% 0.38/0.60  thf('271', plain,
% 0.38/0.60      (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A)))
% 0.38/0.60         <= (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.60      inference('split', [status(esa)], ['202'])).
% 0.38/0.60  thf('272', plain,
% 0.38/0.60      ((((v1_xboole_0 @ sk_C_1)
% 0.38/0.60         | (v4_orders_2 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.38/0.60         | (v2_struct_0 @ sk_A)))
% 0.38/0.60         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('demod', [status(thm)], ['270', '271'])).
% 0.38/0.60  thf('273', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('274', plain,
% 0.38/0.60      ((((v4_orders_2 @ (sk_D @ sk_D_3 @ sk_B @ sk_A)) | (v1_xboole_0 @ sk_C_1)))
% 0.38/0.60         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('clc', [status(thm)], ['272', '273'])).
% 0.38/0.60  thf('275', plain,
% 0.38/0.60      ((((r2_hidden @ sk_D_3 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.38/0.60         | (v1_xboole_0 @ sk_C_1)))
% 0.38/0.60         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('clc', [status(thm)], ['237', '238'])).
% 0.38/0.60  thf('276', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('277', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.38/0.60          | ~ (r2_hidden @ X2 @ (k2_pre_topc @ X1 @ X0))
% 0.38/0.60          | (l1_waybel_0 @ (sk_D @ X2 @ X0 @ X1) @ X1)
% 0.38/0.60          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.38/0.60          | ~ (l1_pre_topc @ X1)
% 0.38/0.60          | ~ (v2_pre_topc @ X1)
% 0.38/0.60          | (v2_struct_0 @ X1))),
% 0.38/0.60      inference('cnf', [status(esa)], [t24_yellow19])).
% 0.38/0.60  thf('278', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_A)
% 0.38/0.60          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.60          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.60          | (l1_waybel_0 @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A)
% 0.38/0.60          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['276', '277'])).
% 0.38/0.60  thf('279', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('280', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('281', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_A)
% 0.38/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.60          | (l1_waybel_0 @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A)
% 0.38/0.60          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.38/0.60      inference('demod', [status(thm)], ['278', '279', '280'])).
% 0.38/0.60  thf('282', plain,
% 0.38/0.60      ((((v1_xboole_0 @ sk_C_1)
% 0.38/0.60         | (l1_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ sk_A)
% 0.38/0.60         | ~ (m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))
% 0.38/0.60         | (v2_struct_0 @ sk_A)))
% 0.38/0.60         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['275', '281'])).
% 0.38/0.60  thf('283', plain,
% 0.38/0.60      (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A)))
% 0.38/0.60         <= (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.60      inference('split', [status(esa)], ['202'])).
% 0.38/0.60  thf('284', plain,
% 0.38/0.60      ((((v1_xboole_0 @ sk_C_1)
% 0.38/0.60         | (l1_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ sk_A)
% 0.38/0.60         | (v2_struct_0 @ sk_A)))
% 0.38/0.60         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('demod', [status(thm)], ['282', '283'])).
% 0.38/0.60  thf('285', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('286', plain,
% 0.38/0.60      ((((l1_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ sk_A)
% 0.38/0.60         | (v1_xboole_0 @ sk_C_1)))
% 0.38/0.60         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('clc', [status(thm)], ['284', '285'])).
% 0.38/0.60  thf('287', plain,
% 0.38/0.60      ((((r2_hidden @ sk_D_3 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.38/0.60         | (v1_xboole_0 @ sk_C_1)))
% 0.38/0.60         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('clc', [status(thm)], ['237', '238'])).
% 0.38/0.60  thf('288', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('289', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.38/0.60          | ~ (r2_hidden @ X2 @ (k2_pre_topc @ X1 @ X0))
% 0.38/0.60          | (v3_yellow_6 @ (sk_D @ X2 @ X0 @ X1) @ X1)
% 0.38/0.60          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.38/0.60          | ~ (l1_pre_topc @ X1)
% 0.38/0.60          | ~ (v2_pre_topc @ X1)
% 0.38/0.60          | (v2_struct_0 @ X1))),
% 0.38/0.60      inference('cnf', [status(esa)], [t24_yellow19])).
% 0.38/0.60  thf('290', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_A)
% 0.38/0.60          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.60          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.60          | (v3_yellow_6 @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A)
% 0.38/0.60          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['288', '289'])).
% 0.38/0.60  thf('291', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('292', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('293', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_A)
% 0.38/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.60          | (v3_yellow_6 @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A)
% 0.38/0.60          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.38/0.60      inference('demod', [status(thm)], ['290', '291', '292'])).
% 0.38/0.60  thf('294', plain,
% 0.38/0.60      ((((v1_xboole_0 @ sk_C_1)
% 0.38/0.60         | (v3_yellow_6 @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ sk_A)
% 0.38/0.60         | ~ (m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))
% 0.38/0.60         | (v2_struct_0 @ sk_A)))
% 0.38/0.60         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['287', '293'])).
% 0.38/0.60  thf('295', plain,
% 0.38/0.60      (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A)))
% 0.38/0.60         <= (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.60      inference('split', [status(esa)], ['202'])).
% 0.38/0.60  thf('296', plain,
% 0.38/0.60      ((((v1_xboole_0 @ sk_C_1)
% 0.38/0.60         | (v3_yellow_6 @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ sk_A)
% 0.38/0.60         | (v2_struct_0 @ sk_A)))
% 0.38/0.60         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('demod', [status(thm)], ['294', '295'])).
% 0.38/0.60  thf('297', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('298', plain,
% 0.38/0.60      ((((v3_yellow_6 @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ sk_A)
% 0.38/0.60         | (v1_xboole_0 @ sk_C_1)))
% 0.38/0.60         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('clc', [status(thm)], ['296', '297'])).
% 0.38/0.60  thf('299', plain,
% 0.38/0.60      ((((r2_hidden @ sk_D_3 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.38/0.60         | (v1_xboole_0 @ sk_C_1)))
% 0.38/0.60         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('clc', [status(thm)], ['237', '238'])).
% 0.38/0.60  thf('300', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('301', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.38/0.60          | ~ (r2_hidden @ X2 @ (k2_pre_topc @ X1 @ X0))
% 0.38/0.60          | (r1_waybel_0 @ X1 @ (sk_D @ X2 @ X0 @ X1) @ X0)
% 0.38/0.60          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.38/0.60          | ~ (l1_pre_topc @ X1)
% 0.38/0.60          | ~ (v2_pre_topc @ X1)
% 0.38/0.60          | (v2_struct_0 @ X1))),
% 0.38/0.60      inference('cnf', [status(esa)], [t24_yellow19])).
% 0.38/0.60  thf('302', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_A)
% 0.38/0.60          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.60          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.60          | (r1_waybel_0 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_B)
% 0.38/0.60          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['300', '301'])).
% 0.38/0.60  thf('303', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('304', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('305', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_A)
% 0.38/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.60          | (r1_waybel_0 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_B)
% 0.38/0.60          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.38/0.60      inference('demod', [status(thm)], ['302', '303', '304'])).
% 0.38/0.60  thf('306', plain,
% 0.38/0.60      ((((v1_xboole_0 @ sk_C_1)
% 0.38/0.60         | (r1_waybel_0 @ sk_A @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ sk_B)
% 0.38/0.60         | ~ (m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))
% 0.38/0.60         | (v2_struct_0 @ sk_A)))
% 0.38/0.60         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['299', '305'])).
% 0.38/0.60  thf('307', plain,
% 0.38/0.60      (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A)))
% 0.38/0.60         <= (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.60      inference('split', [status(esa)], ['202'])).
% 0.38/0.60  thf('308', plain,
% 0.38/0.60      ((((v1_xboole_0 @ sk_C_1)
% 0.38/0.60         | (r1_waybel_0 @ sk_A @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ sk_B)
% 0.38/0.60         | (v2_struct_0 @ sk_A)))
% 0.38/0.60         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('demod', [status(thm)], ['306', '307'])).
% 0.38/0.60  thf('309', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('310', plain,
% 0.38/0.60      ((((r1_waybel_0 @ sk_A @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ sk_B)
% 0.38/0.60         | (v1_xboole_0 @ sk_C_1)))
% 0.38/0.60         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('clc', [status(thm)], ['308', '309'])).
% 0.38/0.60  thf('311', plain,
% 0.38/0.60      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.38/0.60      inference('split', [status(esa)], ['0'])).
% 0.38/0.60  thf('312', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('313', plain,
% 0.38/0.60      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.38/0.60          | ~ (v4_pre_topc @ X4 @ X5)
% 0.38/0.60          | ~ (r1_waybel_0 @ X5 @ X6 @ X4)
% 0.38/0.60          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X5))
% 0.38/0.60          | (r2_hidden @ X7 @ X4)
% 0.38/0.60          | ~ (r2_hidden @ X7 @ (k10_yellow_6 @ X5 @ X6))
% 0.38/0.60          | ~ (l1_waybel_0 @ X6 @ X5)
% 0.38/0.60          | ~ (v3_yellow_6 @ X6 @ X5)
% 0.38/0.60          | ~ (v7_waybel_0 @ X6)
% 0.38/0.60          | ~ (v4_orders_2 @ X6)
% 0.38/0.60          | (v2_struct_0 @ X6)
% 0.38/0.60          | ~ (l1_pre_topc @ X5)
% 0.38/0.60          | ~ (v2_pre_topc @ X5)
% 0.38/0.60          | (v2_struct_0 @ X5))),
% 0.38/0.60      inference('cnf', [status(esa)], [t26_yellow19])).
% 0.38/0.60  thf('314', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_A)
% 0.38/0.60          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.60          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.60          | (v2_struct_0 @ X0)
% 0.38/0.60          | ~ (v4_orders_2 @ X0)
% 0.38/0.60          | ~ (v7_waybel_0 @ X0)
% 0.38/0.60          | ~ (v3_yellow_6 @ X0 @ sk_A)
% 0.38/0.60          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.38/0.60          | ~ (r2_hidden @ X1 @ (k10_yellow_6 @ sk_A @ X0))
% 0.38/0.60          | (r2_hidden @ X1 @ sk_B)
% 0.38/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.38/0.60          | ~ (r1_waybel_0 @ sk_A @ X0 @ sk_B)
% 0.38/0.60          | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.60      inference('sup-', [status(thm)], ['312', '313'])).
% 0.38/0.60  thf('315', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('316', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('317', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_A)
% 0.38/0.60          | (v2_struct_0 @ X0)
% 0.38/0.60          | ~ (v4_orders_2 @ X0)
% 0.38/0.60          | ~ (v7_waybel_0 @ X0)
% 0.38/0.60          | ~ (v3_yellow_6 @ X0 @ sk_A)
% 0.38/0.60          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.38/0.60          | ~ (r2_hidden @ X1 @ (k10_yellow_6 @ sk_A @ X0))
% 0.38/0.60          | (r2_hidden @ X1 @ sk_B)
% 0.38/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.38/0.60          | ~ (r1_waybel_0 @ sk_A @ X0 @ sk_B)
% 0.38/0.60          | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.60      inference('demod', [status(thm)], ['314', '315', '316'])).
% 0.38/0.60  thf('318', plain,
% 0.38/0.60      ((![X0 : $i, X1 : $i]:
% 0.38/0.60          (~ (r1_waybel_0 @ sk_A @ X0 @ sk_B)
% 0.38/0.60           | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.38/0.60           | (r2_hidden @ X1 @ sk_B)
% 0.38/0.60           | ~ (r2_hidden @ X1 @ (k10_yellow_6 @ sk_A @ X0))
% 0.38/0.60           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.38/0.60           | ~ (v3_yellow_6 @ X0 @ sk_A)
% 0.38/0.60           | ~ (v7_waybel_0 @ X0)
% 0.38/0.60           | ~ (v4_orders_2 @ X0)
% 0.38/0.60           | (v2_struct_0 @ X0)
% 0.38/0.60           | (v2_struct_0 @ sk_A)))
% 0.38/0.60         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['311', '317'])).
% 0.38/0.60  thf('319', plain,
% 0.38/0.60      ((![X0 : $i]:
% 0.38/0.60          ((v1_xboole_0 @ sk_C_1)
% 0.38/0.60           | (v2_struct_0 @ sk_A)
% 0.38/0.60           | (v2_struct_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.38/0.60           | ~ (v4_orders_2 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.38/0.60           | ~ (v7_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.38/0.60           | ~ (v3_yellow_6 @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ sk_A)
% 0.38/0.60           | ~ (l1_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ sk_A)
% 0.38/0.60           | ~ (r2_hidden @ X0 @ 
% 0.38/0.60                (k10_yellow_6 @ sk_A @ (sk_D @ sk_D_3 @ sk_B @ sk_A)))
% 0.38/0.60           | (r2_hidden @ X0 @ sk_B)
% 0.38/0.60           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.38/0.60         <= (((v4_pre_topc @ sk_B @ sk_A)) & 
% 0.38/0.60             ((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['310', '318'])).
% 0.38/0.60  thf('320', plain,
% 0.38/0.60      ((![X0 : $i]:
% 0.38/0.60          ((v1_xboole_0 @ sk_C_1)
% 0.38/0.60           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.60           | (r2_hidden @ X0 @ sk_B)
% 0.38/0.60           | ~ (r2_hidden @ X0 @ 
% 0.38/0.60                (k10_yellow_6 @ sk_A @ (sk_D @ sk_D_3 @ sk_B @ sk_A)))
% 0.38/0.60           | ~ (l1_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ sk_A)
% 0.38/0.60           | ~ (v7_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.38/0.60           | ~ (v4_orders_2 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.38/0.60           | (v2_struct_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.38/0.60           | (v2_struct_0 @ sk_A)
% 0.38/0.60           | (v1_xboole_0 @ sk_C_1)))
% 0.38/0.60         <= (((v4_pre_topc @ sk_B @ sk_A)) & 
% 0.38/0.60             ((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['298', '319'])).
% 0.38/0.60  thf('321', plain,
% 0.38/0.60      ((![X0 : $i]:
% 0.38/0.60          ((v2_struct_0 @ sk_A)
% 0.38/0.60           | (v2_struct_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.38/0.60           | ~ (v4_orders_2 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.38/0.60           | ~ (v7_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.38/0.60           | ~ (l1_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ sk_A)
% 0.38/0.60           | ~ (r2_hidden @ X0 @ 
% 0.38/0.60                (k10_yellow_6 @ sk_A @ (sk_D @ sk_D_3 @ sk_B @ sk_A)))
% 0.38/0.60           | (r2_hidden @ X0 @ sk_B)
% 0.38/0.60           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.60           | (v1_xboole_0 @ sk_C_1)))
% 0.38/0.60         <= (((v4_pre_topc @ sk_B @ sk_A)) & 
% 0.38/0.60             ((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('simplify', [status(thm)], ['320'])).
% 0.38/0.60  thf('322', plain,
% 0.38/0.60      ((![X0 : $i]:
% 0.38/0.60          ((v1_xboole_0 @ sk_C_1)
% 0.38/0.60           | (v1_xboole_0 @ sk_C_1)
% 0.38/0.60           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.60           | (r2_hidden @ X0 @ sk_B)
% 0.38/0.60           | ~ (r2_hidden @ X0 @ 
% 0.38/0.60                (k10_yellow_6 @ sk_A @ (sk_D @ sk_D_3 @ sk_B @ sk_A)))
% 0.38/0.60           | ~ (v7_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.38/0.60           | ~ (v4_orders_2 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.38/0.60           | (v2_struct_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.38/0.60           | (v2_struct_0 @ sk_A)))
% 0.38/0.60         <= (((v4_pre_topc @ sk_B @ sk_A)) & 
% 0.38/0.60             ((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['286', '321'])).
% 0.38/0.60  thf('323', plain,
% 0.38/0.60      ((![X0 : $i]:
% 0.38/0.60          ((v2_struct_0 @ sk_A)
% 0.38/0.60           | (v2_struct_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.38/0.60           | ~ (v4_orders_2 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.38/0.60           | ~ (v7_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.38/0.60           | ~ (r2_hidden @ X0 @ 
% 0.38/0.60                (k10_yellow_6 @ sk_A @ (sk_D @ sk_D_3 @ sk_B @ sk_A)))
% 0.38/0.60           | (r2_hidden @ X0 @ sk_B)
% 0.38/0.60           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.60           | (v1_xboole_0 @ sk_C_1)))
% 0.38/0.60         <= (((v4_pre_topc @ sk_B @ sk_A)) & 
% 0.38/0.60             ((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('simplify', [status(thm)], ['322'])).
% 0.38/0.60  thf('324', plain,
% 0.38/0.60      ((![X0 : $i]:
% 0.38/0.60          ((v1_xboole_0 @ sk_C_1)
% 0.38/0.60           | (v1_xboole_0 @ sk_C_1)
% 0.38/0.60           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.60           | (r2_hidden @ X0 @ sk_B)
% 0.38/0.60           | ~ (r2_hidden @ X0 @ 
% 0.38/0.60                (k10_yellow_6 @ sk_A @ (sk_D @ sk_D_3 @ sk_B @ sk_A)))
% 0.38/0.60           | ~ (v7_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.38/0.60           | (v2_struct_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.38/0.60           | (v2_struct_0 @ sk_A)))
% 0.38/0.60         <= (((v4_pre_topc @ sk_B @ sk_A)) & 
% 0.38/0.60             ((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['274', '323'])).
% 0.38/0.60  thf('325', plain,
% 0.38/0.60      ((![X0 : $i]:
% 0.38/0.60          ((v2_struct_0 @ sk_A)
% 0.38/0.60           | (v2_struct_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.38/0.60           | ~ (v7_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.38/0.60           | ~ (r2_hidden @ X0 @ 
% 0.38/0.60                (k10_yellow_6 @ sk_A @ (sk_D @ sk_D_3 @ sk_B @ sk_A)))
% 0.38/0.60           | (r2_hidden @ X0 @ sk_B)
% 0.38/0.60           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.60           | (v1_xboole_0 @ sk_C_1)))
% 0.38/0.60         <= (((v4_pre_topc @ sk_B @ sk_A)) & 
% 0.38/0.60             ((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('simplify', [status(thm)], ['324'])).
% 0.38/0.60  thf('326', plain,
% 0.38/0.60      ((![X0 : $i]:
% 0.38/0.60          ((v1_xboole_0 @ sk_C_1)
% 0.38/0.60           | (v1_xboole_0 @ sk_C_1)
% 0.38/0.60           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.60           | (r2_hidden @ X0 @ sk_B)
% 0.38/0.60           | ~ (r2_hidden @ X0 @ 
% 0.38/0.60                (k10_yellow_6 @ sk_A @ (sk_D @ sk_D_3 @ sk_B @ sk_A)))
% 0.38/0.60           | (v2_struct_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.38/0.60           | (v2_struct_0 @ sk_A)))
% 0.38/0.60         <= (((v4_pre_topc @ sk_B @ sk_A)) & 
% 0.38/0.60             ((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['262', '325'])).
% 0.38/0.60  thf('327', plain,
% 0.38/0.60      ((![X0 : $i]:
% 0.38/0.60          ((v2_struct_0 @ sk_A)
% 0.38/0.60           | (v2_struct_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.38/0.60           | ~ (r2_hidden @ X0 @ 
% 0.38/0.60                (k10_yellow_6 @ sk_A @ (sk_D @ sk_D_3 @ sk_B @ sk_A)))
% 0.38/0.60           | (r2_hidden @ X0 @ sk_B)
% 0.38/0.60           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.60           | (v1_xboole_0 @ sk_C_1)))
% 0.38/0.60         <= (((v4_pre_topc @ sk_B @ sk_A)) & 
% 0.38/0.60             ((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('simplify', [status(thm)], ['326'])).
% 0.38/0.60  thf('328', plain,
% 0.38/0.60      ((((v1_xboole_0 @ sk_C_1)
% 0.38/0.60         | (v1_xboole_0 @ sk_C_1)
% 0.38/0.60         | ~ (m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))
% 0.38/0.60         | (r2_hidden @ sk_D_3 @ sk_B)
% 0.38/0.60         | (v2_struct_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.38/0.60         | (v2_struct_0 @ sk_A)))
% 0.38/0.60         <= (((v4_pre_topc @ sk_B @ sk_A)) & 
% 0.38/0.60             ((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['250', '327'])).
% 0.38/0.60  thf('329', plain,
% 0.38/0.60      (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A)))
% 0.38/0.60         <= (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.60      inference('split', [status(esa)], ['202'])).
% 0.38/0.60  thf('330', plain,
% 0.38/0.60      ((((v1_xboole_0 @ sk_C_1)
% 0.38/0.60         | (v1_xboole_0 @ sk_C_1)
% 0.38/0.60         | (r2_hidden @ sk_D_3 @ sk_B)
% 0.38/0.60         | (v2_struct_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.38/0.60         | (v2_struct_0 @ sk_A)))
% 0.38/0.60         <= (((v4_pre_topc @ sk_B @ sk_A)) & 
% 0.38/0.60             ((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('demod', [status(thm)], ['328', '329'])).
% 0.38/0.60  thf('331', plain,
% 0.38/0.60      ((((v2_struct_0 @ sk_A)
% 0.38/0.60         | (v2_struct_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.38/0.60         | (r2_hidden @ sk_D_3 @ sk_B)
% 0.38/0.60         | (v1_xboole_0 @ sk_C_1)))
% 0.38/0.60         <= (((v4_pre_topc @ sk_B @ sk_A)) & 
% 0.38/0.60             ((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('simplify', [status(thm)], ['330'])).
% 0.38/0.60  thf('332', plain,
% 0.38/0.60      ((((r2_hidden @ sk_D_3 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.38/0.60         | (v1_xboole_0 @ sk_C_1)))
% 0.38/0.60         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('clc', [status(thm)], ['237', '238'])).
% 0.38/0.60  thf('333', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('334', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.38/0.60          | ~ (r2_hidden @ X2 @ (k2_pre_topc @ X1 @ X0))
% 0.38/0.60          | ~ (v2_struct_0 @ (sk_D @ X2 @ X0 @ X1))
% 0.38/0.60          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.38/0.60          | ~ (l1_pre_topc @ X1)
% 0.38/0.60          | ~ (v2_pre_topc @ X1)
% 0.38/0.60          | (v2_struct_0 @ X1))),
% 0.38/0.60      inference('cnf', [status(esa)], [t24_yellow19])).
% 0.38/0.60  thf('335', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_A)
% 0.38/0.60          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.60          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.60          | ~ (v2_struct_0 @ (sk_D @ X0 @ sk_B @ sk_A))
% 0.38/0.60          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['333', '334'])).
% 0.38/0.60  thf('336', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('337', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('338', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_A)
% 0.38/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.60          | ~ (v2_struct_0 @ (sk_D @ X0 @ sk_B @ sk_A))
% 0.38/0.60          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.38/0.60      inference('demod', [status(thm)], ['335', '336', '337'])).
% 0.38/0.60  thf('339', plain,
% 0.38/0.60      ((((v1_xboole_0 @ sk_C_1)
% 0.38/0.60         | ~ (v2_struct_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.38/0.60         | ~ (m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))
% 0.38/0.60         | (v2_struct_0 @ sk_A)))
% 0.38/0.60         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['332', '338'])).
% 0.38/0.60  thf('340', plain,
% 0.38/0.60      (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A)))
% 0.38/0.60         <= (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.60      inference('split', [status(esa)], ['202'])).
% 0.38/0.60  thf('341', plain,
% 0.38/0.60      ((((v1_xboole_0 @ sk_C_1)
% 0.38/0.60         | ~ (v2_struct_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.38/0.60         | (v2_struct_0 @ sk_A)))
% 0.38/0.60         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('demod', [status(thm)], ['339', '340'])).
% 0.38/0.60  thf('342', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('343', plain,
% 0.38/0.60      (((~ (v2_struct_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.38/0.60         | (v1_xboole_0 @ sk_C_1)))
% 0.38/0.60         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('clc', [status(thm)], ['341', '342'])).
% 0.38/0.60  thf('344', plain,
% 0.38/0.60      ((((v1_xboole_0 @ sk_C_1)
% 0.38/0.60         | (r2_hidden @ sk_D_3 @ sk_B)
% 0.38/0.60         | (v2_struct_0 @ sk_A)
% 0.38/0.60         | (v1_xboole_0 @ sk_C_1)))
% 0.38/0.60         <= (((v4_pre_topc @ sk_B @ sk_A)) & 
% 0.38/0.60             ((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['331', '343'])).
% 0.38/0.60  thf('345', plain,
% 0.38/0.60      ((((v2_struct_0 @ sk_A)
% 0.38/0.60         | (r2_hidden @ sk_D_3 @ sk_B)
% 0.38/0.60         | (v1_xboole_0 @ sk_C_1)))
% 0.38/0.60         <= (((v4_pre_topc @ sk_B @ sk_A)) & 
% 0.38/0.60             ((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('simplify', [status(thm)], ['344'])).
% 0.38/0.60  thf('346', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('347', plain,
% 0.38/0.60      ((((v1_xboole_0 @ sk_C_1) | (r2_hidden @ sk_D_3 @ sk_B)))
% 0.38/0.60         <= (((v4_pre_topc @ sk_B @ sk_A)) & 
% 0.38/0.60             ((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('clc', [status(thm)], ['345', '346'])).
% 0.38/0.60  thf('348', plain,
% 0.38/0.60      ((~ (r2_hidden @ sk_D_3 @ sk_B)) <= (~ ((r2_hidden @ sk_D_3 @ sk_B)))),
% 0.38/0.60      inference('split', [status(esa)], ['204'])).
% 0.38/0.60  thf('349', plain,
% 0.38/0.60      (((v1_xboole_0 @ sk_C_1))
% 0.38/0.60         <= (~ ((r2_hidden @ sk_D_3 @ sk_B)) & 
% 0.38/0.60             ((v4_pre_topc @ sk_B @ sk_A)) & 
% 0.38/0.60             ((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.38/0.60             ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.38/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (k1_zfmisc_1 @ 
% 0.38/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.38/0.60             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.38/0.60             ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['347', '348'])).
% 0.38/0.60  thf('350', plain,
% 0.38/0.60      ((~ (v1_xboole_0 @ sk_C_1)) <= (~ ((v1_xboole_0 @ sk_C_1)))),
% 0.38/0.60      inference('split', [status(esa)], ['216'])).
% 0.38/0.60  thf('351', plain,
% 0.38/0.60      (~ ((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.38/0.60       ~ ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) | 
% 0.38/0.60       ~ ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) | 
% 0.38/0.60       ~
% 0.38/0.60       ((v1_subset_1 @ sk_C_1 @ 
% 0.38/0.60         (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))) | 
% 0.38/0.60       ~ ((r1_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) | 
% 0.38/0.60       ~
% 0.38/0.60       ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.60         (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) | 
% 0.38/0.60       ~ ((r2_hidden @ sk_B @ sk_C_1)) | 
% 0.38/0.60       ~ ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) | 
% 0.38/0.60       ((r2_hidden @ sk_D_3 @ sk_B)) | ((v1_xboole_0 @ sk_C_1))),
% 0.38/0.60      inference('sup-', [status(thm)], ['349', '350'])).
% 0.38/0.60  thf('352', plain, ($false),
% 0.38/0.60      inference('sat_resolution*', [status(thm)],
% 0.38/0.60                ['1', '200', '201', '203', '205', '207', '209', '211', '213', 
% 0.38/0.60                 '215', '217', '351'])).
% 0.38/0.60  
% 0.38/0.60  % SZS output end Refutation
% 0.38/0.60  
% 0.38/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
