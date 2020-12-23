%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.p5qe1SNZNx

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:56 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :  383 (1974 expanded)
%              Number of leaves         :   30 ( 524 expanded)
%              Depth                    :   49
%              Number of atoms          : 8464 (66193 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   21 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_waybel_7_type,type,(
    r1_waybel_7: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v3_waybel_7_type,type,(
    v3_waybel_7: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_waybel_7_type,type,(
    r2_waybel_7: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(t30_yellow19,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ! [C: $i] :
                ( ( ~ ( v1_xboole_0 @ C )
                  & ( v2_waybel_0 @ C @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
                  & ( v13_waybel_0 @ C @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
                  & ( v3_waybel_7 @ C @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )
               => ( ( r2_hidden @ B @ C )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_waybel_7 @ A @ C @ D )
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
                    & ( v2_waybel_0 @ C @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
                    & ( v13_waybel_0 @ C @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
                    & ( v3_waybel_7 @ C @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
                    & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )
                 => ( ( r2_hidden @ B @ C )
                   => ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                       => ( ( r2_waybel_7 @ A @ C @ D )
                         => ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t30_yellow19])).

thf('0',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v1_xboole_0 @ X12 )
      | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( v3_waybel_7 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ~ ( r2_waybel_7 @ sk_A @ X12 @ X13 )
      | ( r2_hidden @ X13 @ sk_B )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ sk_B @ X12 )
      | ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v3_waybel_7 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r2_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_yellow19,axiom,(
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

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( m1_subset_1 @ ( sk_D_2 @ X8 @ X9 ) @ ( u1_struct_0 @ X9 ) )
      | ( v4_pre_topc @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t29_yellow19])).

thf('4',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
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
    | ( m1_subset_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( m1_subset_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( r2_hidden @ X8 @ ( sk_C @ X8 @ X9 ) )
      | ( v4_pre_topc @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t29_yellow19])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( r2_hidden @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) ),
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
    | ( r2_hidden @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( r2_hidden @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( m1_subset_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( r1_waybel_7 @ X9 @ ( sk_C @ X8 @ X9 ) @ ( sk_D_2 @ X8 @ X9 ) )
      | ( v4_pre_topc @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t29_yellow19])).

thf('22',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_waybel_7 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ ( sk_D_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_waybel_7 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ ( sk_D_2 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( r1_waybel_7 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ ( sk_D_2 @ sk_B @ sk_A ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v13_waybel_0 @ ( sk_C @ X8 @ X9 ) @ ( k3_yellow_1 @ ( k2_struct_0 @ X9 ) ) )
      | ( v4_pre_topc @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t29_yellow19])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( v13_waybel_0 @ ( sk_C @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( v13_waybel_0 @ ( sk_C @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v13_waybel_0 @ ( sk_C @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v2_waybel_0 @ ( sk_C @ X8 @ X9 ) @ ( k3_yellow_1 @ ( k2_struct_0 @ X9 ) ) )
      | ( v4_pre_topc @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t29_yellow19])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_waybel_0 @ ( sk_C @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_waybel_0 @ ( sk_C @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v2_waybel_0 @ ( sk_C @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v1_subset_1 @ ( sk_C @ X8 @ X9 ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X9 ) ) ) )
      | ( v4_pre_topc @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t29_yellow19])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( v1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( v1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( m1_subset_1 @ ( sk_C @ X8 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X9 ) ) ) ) )
      | ( v4_pre_topc @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t29_yellow19])).

thf('54',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['57','58'])).

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

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r1_waybel_7 @ X1 @ X3 @ X2 )
      | ~ ( r2_hidden @ X0 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X1 ) ) ) ) )
      | ~ ( v13_waybel_0 @ X3 @ ( k3_yellow_1 @ ( k2_struct_0 @ X1 ) ) )
      | ~ ( v2_waybel_0 @ X3 @ ( k3_yellow_1 @ ( k2_struct_0 @ X1 ) ) )
      | ~ ( v1_subset_1 @ X3 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X1 ) ) ) )
      | ( v1_xboole_0 @ X3 )
      | ( r2_hidden @ X2 @ ( k2_pre_topc @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t27_yellow19])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ X1 ) )
      | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ ( sk_C @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( v13_waybel_0 @ ( sk_C @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X1 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( r1_waybel_7 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ X1 ) )
      | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ ( sk_C @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( v13_waybel_0 @ ( sk_C @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X1 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( r1_waybel_7 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_pre_topc @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_waybel_7 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ X1 )
      | ~ ( r2_hidden @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( v13_waybel_0 @ ( sk_C @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( v2_waybel_0 @ ( sk_C @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ X1 @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( v2_waybel_0 @ ( sk_C @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( v13_waybel_0 @ ( sk_C @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( r1_waybel_7 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_pre_topc @ sk_B @ sk_A )
      | ( v4_pre_topc @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_waybel_7 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ X1 )
      | ~ ( r2_hidden @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( v13_waybel_0 @ ( sk_C @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ X1 @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( v13_waybel_0 @ ( sk_C @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( r1_waybel_7 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_pre_topc @ sk_B @ sk_A )
      | ( v4_pre_topc @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_waybel_7 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ X1 )
      | ~ ( r2_hidden @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ X1 @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( r1_waybel_7 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ sk_B @ sk_A )
      | ( v4_pre_topc @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_2 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D_2 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ sk_B @ sk_A )
      | ( v4_pre_topc @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_2 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_D_2 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_2 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','74'])).

thf('76',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D_2 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['17','75'])).

thf('77',plain,
    ( ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_2 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( m1_subset_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('79',plain,
    ( ( m1_subset_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('80',plain,
    ( ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_2 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['76'])).

thf('81',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_yellow19,axiom,(
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
                    ( ( r2_waybel_7 @ A @ D @ C )
                    & ( r2_hidden @ B @ D )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) )
                    & ( v3_waybel_7 @ D @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
                    & ( v13_waybel_0 @ D @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
                    & ( v2_waybel_0 @ D @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
                    & ~ ( v1_xboole_0 @ D ) ) ) ) ) ) )).

thf('82',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( r2_hidden @ X6 @ ( k2_pre_topc @ X5 @ X4 ) )
      | ( r2_waybel_7 @ X5 @ ( sk_D_1 @ X6 @ X4 @ X5 ) @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_yellow19])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_waybel_7 @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 )
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
      | ( r2_waybel_7 @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r2_waybel_7 @ sk_A @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( sk_D_2 @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['80','86'])).

thf('88',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_waybel_7 @ sk_A @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( sk_D_2 @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r2_waybel_7 @ sk_A @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( sk_D_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','88'])).

thf('90',plain,
    ( ( r2_waybel_7 @ sk_A @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( sk_D_2 @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,
    ( ( m1_subset_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('92',plain,
    ( ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_2 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['76'])).

thf('93',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( r2_hidden @ X6 @ ( k2_pre_topc @ X5 @ X4 ) )
      | ( r2_hidden @ X4 @ ( sk_D_1 @ X6 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_yellow19])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
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
      | ( r2_hidden @ sk_B @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['92','98'])).

thf('100',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['91','100'])).

thf('102',plain,
    ( ( r2_hidden @ sk_B @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,
    ( ( m1_subset_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('104',plain,
    ( ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_2 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['76'])).

thf('105',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( r2_hidden @ X6 @ ( k2_pre_topc @ X5 @ X4 ) )
      | ( v2_waybel_0 @ ( sk_D_1 @ X6 @ X4 @ X5 ) @ ( k3_yellow_1 @ ( k2_struct_0 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_yellow19])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_waybel_0 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
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
      | ( v2_waybel_0 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_waybel_0 @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['104','110'])).

thf('112',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_waybel_0 @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_waybel_0 @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['103','112'])).

thf('114',plain,
    ( ( v2_waybel_0 @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,
    ( ( m1_subset_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('116',plain,
    ( ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_2 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['76'])).

thf('117',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( r2_hidden @ X6 @ ( k2_pre_topc @ X5 @ X4 ) )
      | ( v13_waybel_0 @ ( sk_D_1 @ X6 @ X4 @ X5 ) @ ( k3_yellow_1 @ ( k2_struct_0 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_yellow19])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v13_waybel_0 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
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
      | ( v13_waybel_0 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('123',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v13_waybel_0 @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['116','122'])).

thf('124',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v13_waybel_0 @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v13_waybel_0 @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['115','124'])).

thf('126',plain,
    ( ( v13_waybel_0 @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,
    ( ( m1_subset_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('128',plain,
    ( ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_2 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['76'])).

thf('129',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( r2_hidden @ X6 @ ( k2_pre_topc @ X5 @ X4 ) )
      | ( v3_waybel_7 @ ( sk_D_1 @ X6 @ X4 @ X5 ) @ ( k3_yellow_1 @ ( k2_struct_0 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_yellow19])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v3_waybel_7 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
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
      | ( v3_waybel_7 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['131','132','133'])).

thf('135',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v3_waybel_7 @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['128','134'])).

thf('136',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v3_waybel_7 @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v3_waybel_7 @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['127','136'])).

thf('138',plain,
    ( ( v3_waybel_7 @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,
    ( ( m1_subset_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('140',plain,
    ( ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_2 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['76'])).

thf('141',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( r2_hidden @ X6 @ ( k2_pre_topc @ X5 @ X4 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X6 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X5 ) ) ) ) )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_yellow19])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
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
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['143','144','145'])).

thf('147',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ~ ( m1_subset_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['140','146'])).

thf('148',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['139','148'])).

thf('150',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,
    ( ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v3_waybel_7 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r2_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v3_waybel_7 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r2_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('152',plain,
    ( ! [X0: $i] :
        ( ( v4_pre_topc @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r2_waybel_7 @ sk_A @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ X0 )
        | ~ ( v3_waybel_7 @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v2_waybel_0 @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ( v1_xboole_0 @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v3_waybel_7 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r2_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,
    ( ! [X0: $i] :
        ( ( v4_pre_topc @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
        | ( v1_xboole_0 @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
        | ~ ( v2_waybel_0 @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( r2_waybel_7 @ sk_A @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ X0 )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
        | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v3_waybel_7 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r2_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference('sup-',[status(thm)],['138','152'])).

thf('154',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_B @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r2_waybel_7 @ sk_A @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ X0 )
        | ~ ( v13_waybel_0 @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v2_waybel_0 @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ( v1_xboole_0 @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
        | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v3_waybel_7 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r2_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,
    ( ! [X0: $i] :
        ( ( v4_pre_topc @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
        | ( v4_pre_topc @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
        | ( v1_xboole_0 @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
        | ~ ( v2_waybel_0 @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( r2_waybel_7 @ sk_A @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ X0 )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v3_waybel_7 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r2_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference('sup-',[status(thm)],['126','154'])).

thf('156',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_B @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r2_waybel_7 @ sk_A @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ X0 )
        | ~ ( v2_waybel_0 @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ( v1_xboole_0 @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
        | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v3_waybel_7 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r2_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,
    ( ! [X0: $i] :
        ( ( v4_pre_topc @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
        | ( v4_pre_topc @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
        | ( v1_xboole_0 @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
        | ~ ( r2_waybel_7 @ sk_A @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ X0 )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v3_waybel_7 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r2_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference('sup-',[status(thm)],['114','156'])).

thf('158',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_B @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r2_waybel_7 @ sk_A @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ X0 )
        | ( v1_xboole_0 @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
        | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v3_waybel_7 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r2_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,
    ( ! [X0: $i] :
        ( ( v4_pre_topc @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
        | ( v4_pre_topc @ sk_B @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
        | ( v1_xboole_0 @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
        | ~ ( r2_waybel_7 @ sk_A @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ X0 )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v3_waybel_7 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r2_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference('sup-',[status(thm)],['102','158'])).

thf('160',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r2_waybel_7 @ sk_A @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) @ X0 )
        | ( v1_xboole_0 @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
        | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v3_waybel_7 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r2_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,
    ( ( ( v4_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v4_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v3_waybel_7 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r2_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference('sup-',[status(thm)],['90','160'])).

thf('162',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v3_waybel_7 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r2_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,
    ( ( ( v4_pre_topc @ sk_B @ sk_A )
      | ( v4_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v3_waybel_7 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r2_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference('sup-',[status(thm)],['78','162'])).

thf('164',plain,
    ( ( ( r2_hidden @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ ( sk_D_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v3_waybel_7 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r2_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference(simplify,[status(thm)],['163'])).

thf('165',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( r2_hidden @ X6 @ ( k2_pre_topc @ X5 @ X4 ) )
      | ~ ( v1_xboole_0 @ ( sk_D_1 @ X6 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_yellow19])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
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
      | ~ ( v1_xboole_0 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['167','168','169'])).

thf('171',plain,
    ( ( ( v4_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r2_hidden @ ( sk_D_2 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v3_waybel_7 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r2_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference('sup-',[status(thm)],['164','170'])).

thf('172',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ ( sk_D_2 @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v3_waybel_7 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r2_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,
    ( ( ( v4_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v4_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v3_waybel_7 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r2_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference('sup-',[status(thm)],['77','172'])).

thf('174',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_D_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v3_waybel_7 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r2_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,
    ( ( ( v4_pre_topc @ sk_B @ sk_A )
      | ( v4_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v3_waybel_7 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r2_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference('sup-',[status(thm)],['9','174'])).

thf('176',plain,
    ( ( ( r2_hidden @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v3_waybel_7 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r2_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( r2_hidden @ ( sk_D_2 @ X8 @ X9 ) @ X8 )
      | ( v4_pre_topc @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t29_yellow19])).

thf('179',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ~ ( r2_hidden @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B ) ),
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
    | ~ ( r2_hidden @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['179','180','181'])).

thf('183',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ~ ( r2_hidden @ ( sk_D_2 @ sk_B @ sk_A ) @ sk_B )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['182','183'])).

thf('185',plain,
    ( ( ( v4_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v3_waybel_7 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r2_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference('sup-',[status(thm)],['176','184'])).

thf('186',plain,
    ( ( ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v3_waybel_7 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r2_waybel_7 @ sk_A @ X12 @ X13 )
        | ( r2_hidden @ X13 @ sk_B )
        | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ sk_B @ X12 ) ) ),
    inference(simplify,[status(thm)],['185'])).

thf('187',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v1_xboole_0 @ ( sk_C @ X8 @ X9 ) )
      | ( v4_pre_topc @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t29_yellow19])).

thf('189',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
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
    | ~ ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['189','190','191'])).

thf('193',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ~ ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['192','193'])).

thf('195',plain,
    ( ( ( v4_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X12: $i,X13: $i] :
        ( ( v1_xboole_0 @ X12 )
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v3_waybel_7 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r2_waybel_7 @ sk_A @ X12 @ X13 )
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
        | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v3_waybel_7 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
        | ~ ( r2_waybel_7 @ sk_A @ X12 @ X13 )
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
          | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
          | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
          | ~ ( v3_waybel_7 @ X12 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
          | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
          | ~ ( r2_waybel_7 @ sk_A @ X12 @ X13 )
          | ( r2_hidden @ X13 @ sk_B )
          | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ sk_B @ X12 ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['197','199'])).

thf('201',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['201'])).

thf('203',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['198'])).

thf('204',plain,
    ( ~ ( r2_hidden @ sk_D_3 @ sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,
    ( ~ ( r2_hidden @ sk_D_3 @ sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['204'])).

thf('206',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
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
    ( ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,
    ( ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['210'])).

thf('212',plain,
    ( ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,
    ( ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['212'])).

thf('214',plain,
    ( ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,
    ( ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
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
    inference(split,[status(esa)],['201'])).

thf('219',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
   <= ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 ) ),
    inference(split,[status(esa)],['206'])).

thf('220',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
   <= ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['198'])).

thf('221',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,
    ( ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['212'])).

thf('223',plain,
    ( ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['210'])).

thf('224',plain,
    ( ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['214'])).

thf('225',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['208'])).

thf('226',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( r2_waybel_7 @ X5 @ X7 @ X6 )
      | ~ ( r2_hidden @ X4 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X5 ) ) ) ) )
      | ~ ( v3_waybel_7 @ X7 @ ( k3_yellow_1 @ ( k2_struct_0 @ X5 ) ) )
      | ~ ( v13_waybel_0 @ X7 @ ( k3_yellow_1 @ ( k2_struct_0 @ X5 ) ) )
      | ~ ( v2_waybel_0 @ X7 @ ( k3_yellow_1 @ ( k2_struct_0 @ X5 ) ) )
      | ( v1_xboole_0 @ X7 )
      | ( r2_hidden @ X6 @ ( k2_pre_topc @ X5 @ X4 ) )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_yellow19])).

thf('227',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ X1 ) )
        | ( v1_xboole_0 @ sk_C_1 )
        | ~ ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( r2_hidden @ X1 @ sk_C_1 )
        | ~ ( r2_waybel_7 @ sk_A @ sk_C_1 @ X0 )
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
        | ~ ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( r2_hidden @ X1 @ sk_C_1 )
        | ~ ( r2_waybel_7 @ sk_A @ sk_C_1 @ X0 )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['227','228','229'])).

thf('231',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( r2_waybel_7 @ sk_A @ sk_C_1 @ X1 )
        | ~ ( r2_hidden @ X0 @ sk_C_1 )
        | ~ ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ( v1_xboole_0 @ sk_C_1 )
        | ( r2_hidden @ X1 @ ( k2_pre_topc @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['224','230'])).

thf('232',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ X1 ) )
        | ( v1_xboole_0 @ sk_C_1 )
        | ~ ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( r2_hidden @ X1 @ sk_C_1 )
        | ~ ( r2_waybel_7 @ sk_A @ sk_C_1 @ X0 )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['223','231'])).

thf('233',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( r2_waybel_7 @ sk_A @ sk_C_1 @ X1 )
        | ~ ( r2_hidden @ X0 @ sk_C_1 )
        | ( v1_xboole_0 @ sk_C_1 )
        | ( r2_hidden @ X1 @ ( k2_pre_topc @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['222','232'])).

thf('234',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
        | ( v1_xboole_0 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ sk_C_1 )
        | ~ ( r2_waybel_7 @ sk_A @ sk_C_1 @ X0 ) )
   <= ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['221','233'])).

thf('235',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_waybel_7 @ sk_A @ sk_C_1 @ X0 )
        | ( v1_xboole_0 @ sk_C_1 )
        | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['220','234'])).

thf('236',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_D_3 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['219','235'])).

thf('237',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( r2_hidden @ sk_D_3 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['218','236'])).

thf('238',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,
    ( ( ( r2_hidden @ sk_D_3 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['237','238'])).

thf('240',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('241',plain,
    ( ( ( r2_hidden @ sk_D_3 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['237','238'])).

thf('242',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k2_pre_topc @ X1 @ X0 ) )
      | ( r2_hidden @ X0 @ ( sk_D @ X2 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t27_yellow19])).

thf('244',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
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
      | ( r2_hidden @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['244','245','246'])).

thf('248',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( r2_hidden @ sk_B @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['241','247'])).

thf('249',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['201'])).

thf('250',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( r2_hidden @ sk_B @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['248','249'])).

thf('251',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,
    ( ( ( r2_hidden @ sk_B @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['250','251'])).

thf('253',plain,
    ( ( ( r2_hidden @ sk_D_3 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['237','238'])).

thf('254',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k2_pre_topc @ X1 @ X0 ) )
      | ( r1_waybel_7 @ X1 @ ( sk_D @ X2 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t27_yellow19])).

thf('256',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 )
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
      | ( r1_waybel_7 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['256','257','258'])).

thf('260',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( r1_waybel_7 @ sk_A @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ sk_D_3 )
      | ~ ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['253','259'])).

thf('261',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['201'])).

thf('262',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( r1_waybel_7 @ sk_A @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ sk_D_3 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['260','261'])).

thf('263',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,
    ( ( ( r1_waybel_7 @ sk_A @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ sk_D_3 )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['262','263'])).

thf('265',plain,
    ( ( ( r2_hidden @ sk_D_3 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['237','238'])).

thf('266',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k2_pre_topc @ X1 @ X0 ) )
      | ( v13_waybel_0 @ ( sk_D @ X2 @ X0 @ X1 ) @ ( k3_yellow_1 @ ( k2_struct_0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t27_yellow19])).

thf('268',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v13_waybel_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
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
      | ( v13_waybel_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['268','269','270'])).

thf('272',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( v13_waybel_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['265','271'])).

thf('273',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['201'])).

thf('274',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( v13_waybel_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['272','273'])).

thf('275',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,
    ( ( ( v13_waybel_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['274','275'])).

thf('277',plain,
    ( ( ( r2_hidden @ sk_D_3 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['237','238'])).

thf('278',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k2_pre_topc @ X1 @ X0 ) )
      | ( v2_waybel_0 @ ( sk_D @ X2 @ X0 @ X1 ) @ ( k3_yellow_1 @ ( k2_struct_0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t27_yellow19])).

thf('280',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_waybel_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
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
      | ( v2_waybel_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['280','281','282'])).

thf('284',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( v2_waybel_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['277','283'])).

thf('285',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['201'])).

thf('286',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( v2_waybel_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['284','285'])).

thf('287',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('288',plain,
    ( ( ( v2_waybel_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['286','287'])).

thf('289',plain,
    ( ( ( r2_hidden @ sk_D_3 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['237','238'])).

thf('290',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('291',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k2_pre_topc @ X1 @ X0 ) )
      | ( v1_subset_1 @ ( sk_D @ X2 @ X0 @ X1 ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X1 ) ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t27_yellow19])).

thf('292',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['290','291'])).

thf('293',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('294',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('295',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['292','293','294'])).

thf('296',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( v1_subset_1 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['289','295'])).

thf('297',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['201'])).

thf('298',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( v1_subset_1 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['296','297'])).

thf('299',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('300',plain,
    ( ( ( v1_subset_1 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['298','299'])).

thf('301',plain,
    ( ( ( r2_hidden @ sk_D_3 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['237','238'])).

thf('302',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('303',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k2_pre_topc @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ X2 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X1 ) ) ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t27_yellow19])).

thf('304',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['302','303'])).

thf('305',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('306',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('307',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['304','305','306'])).

thf('308',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ~ ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['301','307'])).

thf('309',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['201'])).

thf('310',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['308','309'])).

thf('311',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('312',plain,
    ( ( ( m1_subset_1 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['310','311'])).

thf('313',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v4_pre_topc @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X9 ) )
      | ( r2_hidden @ X11 @ X8 )
      | ~ ( r1_waybel_7 @ X9 @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X9 ) ) ) ) )
      | ~ ( v13_waybel_0 @ X10 @ ( k3_yellow_1 @ ( k2_struct_0 @ X9 ) ) )
      | ~ ( v2_waybel_0 @ X10 @ ( k3_yellow_1 @ ( k2_struct_0 @ X9 ) ) )
      | ~ ( v1_subset_1 @ X10 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X9 ) ) ) )
      | ( v1_xboole_0 @ X10 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t29_yellow19])).

thf('314',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v1_xboole_0 @ sk_C_1 )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v1_xboole_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( v1_subset_1 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_waybel_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( r1_waybel_7 @ sk_A @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ X0 )
        | ( r2_hidden @ X0 @ X1 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X1 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( v4_pre_topc @ X1 @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['312','313'])).

thf('315',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('316',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('317',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v1_xboole_0 @ sk_C_1 )
        | ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( v1_subset_1 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
        | ~ ( v2_waybel_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( r1_waybel_7 @ sk_A @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ X0 )
        | ( r2_hidden @ X0 @ X1 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X1 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( v4_pre_topc @ X1 @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['314','315','316'])).

thf('318',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v1_xboole_0 @ sk_C_1 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v4_pre_topc @ X0 @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X1 @ X0 )
        | ~ ( r1_waybel_7 @ sk_A @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ X1 )
        | ~ ( v13_waybel_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v2_waybel_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ( v1_xboole_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['300','317'])).

thf('319',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( v2_waybel_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( v13_waybel_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( r1_waybel_7 @ sk_A @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ X1 )
        | ( r2_hidden @ X1 @ X0 )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( v4_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['318'])).

thf('320',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v1_xboole_0 @ sk_C_1 )
        | ( v1_xboole_0 @ sk_C_1 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v4_pre_topc @ X0 @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X1 @ X0 )
        | ~ ( r1_waybel_7 @ sk_A @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ X1 )
        | ~ ( v13_waybel_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ( v1_xboole_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['288','319'])).

thf('321',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( v13_waybel_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( r1_waybel_7 @ sk_A @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ X1 )
        | ( r2_hidden @ X1 @ X0 )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( v4_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['320'])).

thf('322',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v1_xboole_0 @ sk_C_1 )
        | ( v1_xboole_0 @ sk_C_1 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v4_pre_topc @ X0 @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X1 @ X0 )
        | ~ ( r1_waybel_7 @ sk_A @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ X1 )
        | ( v1_xboole_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['276','321'])).

thf('323',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( r1_waybel_7 @ sk_A @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) @ X1 )
        | ( r2_hidden @ X1 @ X0 )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( v4_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['322'])).

thf('324',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ sk_C_1 )
        | ( v1_xboole_0 @ sk_C_1 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v4_pre_topc @ X0 @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ sk_D_3 @ X0 )
        | ( v1_xboole_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['264','323'])).

thf('325',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['201'])).

thf('326',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ sk_C_1 )
        | ( v1_xboole_0 @ sk_C_1 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v4_pre_topc @ X0 @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ( r2_hidden @ sk_D_3 @ X0 )
        | ( v1_xboole_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['324','325'])).

thf('327',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ( r2_hidden @ sk_D_3 @ X0 )
        | ~ ( r2_hidden @ X0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
        | ~ ( v4_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['326'])).

thf('328',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v4_pre_topc @ sk_B @ sk_A )
      | ( r2_hidden @ sk_D_3 @ sk_B )
      | ( v1_xboole_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['252','327'])).

thf('329',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('330',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v4_pre_topc @ sk_B @ sk_A )
      | ( r2_hidden @ sk_D_3 @ sk_B )
      | ( v1_xboole_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['328','329'])).

thf('331',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
      | ( r2_hidden @ sk_D_3 @ sk_B )
      | ~ ( v4_pre_topc @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['330'])).

thf('332',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( r2_hidden @ sk_D_3 @ sk_B )
      | ( v1_xboole_0 @ ( sk_D @ sk_D_3 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v4_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['240','331'])).

thf('333',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('334',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k2_pre_topc @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( sk_D @ X2 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t27_yellow19])).

thf('335',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
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
      | ~ ( v1_xboole_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['335','336','337'])).

thf('339',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_D_3 @ sk_B )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( r2_hidden @ sk_D_3 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v4_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['332','338'])).

thf('340',plain,
    ( ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['201'])).

thf('341',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_D_3 @ sk_B )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( r2_hidden @ sk_D_3 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v4_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['339','340'])).

thf('342',plain,
    ( ( ~ ( r2_hidden @ sk_D_3 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( r2_hidden @ sk_D_3 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v4_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['341'])).

thf('343',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_D_3 @ sk_B )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( v4_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['239','342'])).

thf('344',plain,
    ( ( ( r2_hidden @ sk_D_3 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( v4_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['343'])).

thf('345',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('346',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( r2_hidden @ sk_D_3 @ sk_B ) )
   <= ( ( v4_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['344','345'])).

thf('347',plain,
    ( ~ ( r2_hidden @ sk_D_3 @ sk_B )
   <= ~ ( r2_hidden @ sk_D_3 @ sk_B ) ),
    inference(split,[status(esa)],['204'])).

thf('348',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
   <= ( ~ ( r2_hidden @ sk_D_3 @ sk_B )
      & ( v4_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      & ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      & ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['346','347'])).

thf('349',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
   <= ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(split,[status(esa)],['216'])).

thf('350',plain,
    ( ~ ( v13_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v2_waybel_0 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v3_waybel_7 @ sk_C_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ~ ( r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3 )
    | ~ ( m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_C_1 )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r2_hidden @ sk_D_3 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['348','349'])).

thf('351',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','200','202','203','205','207','209','211','213','215','217','350'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.p5qe1SNZNx
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:38:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.51/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.51/0.73  % Solved by: fo/fo7.sh
% 0.51/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.73  % done 325 iterations in 0.250s
% 0.51/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.51/0.73  % SZS output start Refutation
% 0.51/0.73  thf(r1_waybel_7_type, type, r1_waybel_7: $i > $i > $i > $o).
% 0.51/0.73  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.51/0.73  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 0.51/0.73  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.51/0.73  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.51/0.73  thf(v3_waybel_7_type, type, v3_waybel_7: $i > $i > $o).
% 0.51/0.73  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.51/0.73  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.51/0.73  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.51/0.73  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.51/0.73  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.51/0.73  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.51/0.73  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.51/0.73  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.51/0.73  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.51/0.73  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.51/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.51/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.73  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.51/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.51/0.73  thf(r2_waybel_7_type, type, r2_waybel_7: $i > $i > $i > $o).
% 0.51/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.51/0.73  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.51/0.73  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.51/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.51/0.73  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.51/0.73  thf(t30_yellow19, conjecture,
% 0.51/0.73    (![A:$i]:
% 0.51/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.51/0.73       ( ![B:$i]:
% 0.51/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.73           ( ( v4_pre_topc @ B @ A ) <=>
% 0.51/0.73             ( ![C:$i]:
% 0.51/0.73               ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.51/0.73                   ( v2_waybel_0 @ C @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.51/0.73                   ( v13_waybel_0 @ C @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.51/0.73                   ( v3_waybel_7 @ C @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.51/0.73                   ( m1_subset_1 @
% 0.51/0.73                     C @ 
% 0.51/0.73                     ( k1_zfmisc_1 @
% 0.51/0.73                       ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.51/0.73                 ( ( r2_hidden @ B @ C ) =>
% 0.51/0.73                   ( ![D:$i]:
% 0.51/0.73                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.73                       ( ( r2_waybel_7 @ A @ C @ D ) => ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.51/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.73    (~( ![A:$i]:
% 0.51/0.73        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.51/0.73            ( l1_pre_topc @ A ) ) =>
% 0.51/0.73          ( ![B:$i]:
% 0.51/0.73            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.73              ( ( v4_pre_topc @ B @ A ) <=>
% 0.51/0.73                ( ![C:$i]:
% 0.51/0.73                  ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.51/0.73                      ( v2_waybel_0 @ C @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.51/0.73                      ( v13_waybel_0 @
% 0.51/0.73                        C @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.51/0.73                      ( v3_waybel_7 @ C @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.51/0.73                      ( m1_subset_1 @
% 0.51/0.73                        C @ 
% 0.51/0.73                        ( k1_zfmisc_1 @
% 0.51/0.73                          ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.51/0.73                    ( ( r2_hidden @ B @ C ) =>
% 0.51/0.73                      ( ![D:$i]:
% 0.51/0.73                        ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.73                          ( ( r2_waybel_7 @ A @ C @ D ) =>
% 0.51/0.73                            ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ) ) )),
% 0.51/0.73    inference('cnf.neg', [status(esa)], [t30_yellow19])).
% 0.51/0.73  thf('0', plain,
% 0.51/0.73      (![X12 : $i, X13 : $i]:
% 0.51/0.73         ((v1_xboole_0 @ X12)
% 0.51/0.73          | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.73          | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.73          | ~ (v3_waybel_7 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.73          | ~ (m1_subset_1 @ X12 @ 
% 0.51/0.73               (k1_zfmisc_1 @ 
% 0.51/0.73                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.51/0.73          | ~ (r2_waybel_7 @ sk_A @ X12 @ X13)
% 0.51/0.73          | (r2_hidden @ X13 @ sk_B)
% 0.51/0.73          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.51/0.73          | ~ (r2_hidden @ sk_B @ X12)
% 0.51/0.73          | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('1', plain,
% 0.51/0.73      ((![X12 : $i, X13 : $i]:
% 0.51/0.73          ((v1_xboole_0 @ X12)
% 0.51/0.73           | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.73           | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.73           | ~ (v3_waybel_7 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.73           | ~ (m1_subset_1 @ X12 @ 
% 0.51/0.73                (k1_zfmisc_1 @ 
% 0.51/0.73                 (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.51/0.73           | ~ (r2_waybel_7 @ sk_A @ X12 @ X13)
% 0.51/0.73           | (r2_hidden @ X13 @ sk_B)
% 0.51/0.73           | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.51/0.73           | ~ (r2_hidden @ sk_B @ X12))) | 
% 0.51/0.73       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.73      inference('split', [status(esa)], ['0'])).
% 0.51/0.73  thf('2', plain,
% 0.51/0.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf(t29_yellow19, axiom,
% 0.51/0.73    (![A:$i]:
% 0.51/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.51/0.73       ( ![B:$i]:
% 0.51/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.73           ( ( v4_pre_topc @ B @ A ) <=>
% 0.51/0.73             ( ![C:$i]:
% 0.51/0.73               ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.51/0.73                   ( v1_subset_1 @
% 0.51/0.73                     C @ 
% 0.51/0.73                     ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.51/0.73                   ( v2_waybel_0 @ C @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.51/0.73                   ( v13_waybel_0 @ C @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.51/0.73                   ( m1_subset_1 @
% 0.51/0.73                     C @ 
% 0.51/0.73                     ( k1_zfmisc_1 @
% 0.51/0.73                       ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.51/0.73                 ( ( r2_hidden @ B @ C ) =>
% 0.51/0.73                   ( ![D:$i]:
% 0.51/0.73                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.73                       ( ( r1_waybel_7 @ A @ C @ D ) => ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.51/0.73  thf('3', plain,
% 0.51/0.73      (![X8 : $i, X9 : $i]:
% 0.51/0.73         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.51/0.73          | (m1_subset_1 @ (sk_D_2 @ X8 @ X9) @ (u1_struct_0 @ X9))
% 0.51/0.73          | (v4_pre_topc @ X8 @ X9)
% 0.51/0.73          | ~ (l1_pre_topc @ X9)
% 0.51/0.73          | ~ (v2_pre_topc @ X9)
% 0.51/0.73          | (v2_struct_0 @ X9))),
% 0.51/0.73      inference('cnf', [status(esa)], [t29_yellow19])).
% 0.51/0.73  thf('4', plain,
% 0.51/0.73      (((v2_struct_0 @ sk_A)
% 0.51/0.73        | ~ (v2_pre_topc @ sk_A)
% 0.51/0.73        | ~ (l1_pre_topc @ sk_A)
% 0.51/0.73        | (v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.73        | (m1_subset_1 @ (sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.51/0.73      inference('sup-', [status(thm)], ['2', '3'])).
% 0.51/0.73  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('7', plain,
% 0.51/0.73      (((v2_struct_0 @ sk_A)
% 0.51/0.73        | (v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.73        | (m1_subset_1 @ (sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.51/0.73      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.51/0.73  thf('8', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('9', plain,
% 0.51/0.73      (((m1_subset_1 @ (sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.51/0.73        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.73      inference('clc', [status(thm)], ['7', '8'])).
% 0.51/0.73  thf('10', plain,
% 0.51/0.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('11', plain,
% 0.51/0.73      (![X8 : $i, X9 : $i]:
% 0.51/0.73         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.51/0.73          | (r2_hidden @ X8 @ (sk_C @ X8 @ X9))
% 0.51/0.73          | (v4_pre_topc @ X8 @ X9)
% 0.51/0.73          | ~ (l1_pre_topc @ X9)
% 0.51/0.73          | ~ (v2_pre_topc @ X9)
% 0.51/0.73          | (v2_struct_0 @ X9))),
% 0.51/0.73      inference('cnf', [status(esa)], [t29_yellow19])).
% 0.51/0.73  thf('12', plain,
% 0.51/0.73      (((v2_struct_0 @ sk_A)
% 0.51/0.73        | ~ (v2_pre_topc @ sk_A)
% 0.51/0.73        | ~ (l1_pre_topc @ sk_A)
% 0.51/0.73        | (v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.73        | (r2_hidden @ sk_B @ (sk_C @ sk_B @ sk_A)))),
% 0.51/0.73      inference('sup-', [status(thm)], ['10', '11'])).
% 0.51/0.73  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('15', plain,
% 0.51/0.73      (((v2_struct_0 @ sk_A)
% 0.51/0.73        | (v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.73        | (r2_hidden @ sk_B @ (sk_C @ sk_B @ sk_A)))),
% 0.51/0.73      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.51/0.73  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('17', plain,
% 0.51/0.73      (((r2_hidden @ sk_B @ (sk_C @ sk_B @ sk_A)) | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.73      inference('clc', [status(thm)], ['15', '16'])).
% 0.51/0.73  thf('18', plain,
% 0.51/0.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('19', plain,
% 0.51/0.73      (((m1_subset_1 @ (sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.51/0.73        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.73      inference('clc', [status(thm)], ['7', '8'])).
% 0.51/0.73  thf('20', plain,
% 0.51/0.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('21', plain,
% 0.51/0.73      (![X8 : $i, X9 : $i]:
% 0.51/0.73         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.51/0.73          | (r1_waybel_7 @ X9 @ (sk_C @ X8 @ X9) @ (sk_D_2 @ X8 @ X9))
% 0.51/0.73          | (v4_pre_topc @ X8 @ X9)
% 0.51/0.73          | ~ (l1_pre_topc @ X9)
% 0.51/0.73          | ~ (v2_pre_topc @ X9)
% 0.51/0.73          | (v2_struct_0 @ X9))),
% 0.51/0.73      inference('cnf', [status(esa)], [t29_yellow19])).
% 0.51/0.73  thf('22', plain,
% 0.51/0.73      (((v2_struct_0 @ sk_A)
% 0.51/0.73        | ~ (v2_pre_topc @ sk_A)
% 0.51/0.73        | ~ (l1_pre_topc @ sk_A)
% 0.51/0.73        | (v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.73        | (r1_waybel_7 @ sk_A @ (sk_C @ sk_B @ sk_A) @ (sk_D_2 @ sk_B @ sk_A)))),
% 0.51/0.73      inference('sup-', [status(thm)], ['20', '21'])).
% 0.51/0.73  thf('23', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('25', plain,
% 0.51/0.73      (((v2_struct_0 @ sk_A)
% 0.51/0.73        | (v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.73        | (r1_waybel_7 @ sk_A @ (sk_C @ sk_B @ sk_A) @ (sk_D_2 @ sk_B @ sk_A)))),
% 0.51/0.73      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.51/0.73  thf('26', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('27', plain,
% 0.51/0.73      (((r1_waybel_7 @ sk_A @ (sk_C @ sk_B @ sk_A) @ (sk_D_2 @ sk_B @ sk_A))
% 0.51/0.73        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.73      inference('clc', [status(thm)], ['25', '26'])).
% 0.51/0.73  thf('28', plain,
% 0.51/0.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('29', plain,
% 0.51/0.73      (![X8 : $i, X9 : $i]:
% 0.51/0.73         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.51/0.73          | (v13_waybel_0 @ (sk_C @ X8 @ X9) @ 
% 0.51/0.73             (k3_yellow_1 @ (k2_struct_0 @ X9)))
% 0.51/0.73          | (v4_pre_topc @ X8 @ X9)
% 0.51/0.73          | ~ (l1_pre_topc @ X9)
% 0.51/0.73          | ~ (v2_pre_topc @ X9)
% 0.51/0.73          | (v2_struct_0 @ X9))),
% 0.51/0.73      inference('cnf', [status(esa)], [t29_yellow19])).
% 0.51/0.73  thf('30', plain,
% 0.51/0.73      (((v2_struct_0 @ sk_A)
% 0.51/0.73        | ~ (v2_pre_topc @ sk_A)
% 0.51/0.73        | ~ (l1_pre_topc @ sk_A)
% 0.51/0.73        | (v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.73        | (v13_waybel_0 @ (sk_C @ sk_B @ sk_A) @ 
% 0.51/0.73           (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.51/0.73      inference('sup-', [status(thm)], ['28', '29'])).
% 0.51/0.73  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('33', plain,
% 0.51/0.73      (((v2_struct_0 @ sk_A)
% 0.51/0.73        | (v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.73        | (v13_waybel_0 @ (sk_C @ sk_B @ sk_A) @ 
% 0.51/0.73           (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.51/0.73      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.51/0.73  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('35', plain,
% 0.51/0.73      (((v13_waybel_0 @ (sk_C @ sk_B @ sk_A) @ 
% 0.51/0.73         (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.73        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.73      inference('clc', [status(thm)], ['33', '34'])).
% 0.51/0.73  thf('36', plain,
% 0.51/0.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('37', plain,
% 0.51/0.73      (![X8 : $i, X9 : $i]:
% 0.51/0.73         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.51/0.73          | (v2_waybel_0 @ (sk_C @ X8 @ X9) @ 
% 0.51/0.73             (k3_yellow_1 @ (k2_struct_0 @ X9)))
% 0.51/0.73          | (v4_pre_topc @ X8 @ X9)
% 0.51/0.73          | ~ (l1_pre_topc @ X9)
% 0.51/0.73          | ~ (v2_pre_topc @ X9)
% 0.51/0.73          | (v2_struct_0 @ X9))),
% 0.51/0.73      inference('cnf', [status(esa)], [t29_yellow19])).
% 0.51/0.73  thf('38', plain,
% 0.51/0.73      (((v2_struct_0 @ sk_A)
% 0.51/0.73        | ~ (v2_pre_topc @ sk_A)
% 0.51/0.73        | ~ (l1_pre_topc @ sk_A)
% 0.51/0.73        | (v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.73        | (v2_waybel_0 @ (sk_C @ sk_B @ sk_A) @ 
% 0.51/0.73           (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.51/0.73      inference('sup-', [status(thm)], ['36', '37'])).
% 0.51/0.73  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('41', plain,
% 0.51/0.73      (((v2_struct_0 @ sk_A)
% 0.51/0.73        | (v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.73        | (v2_waybel_0 @ (sk_C @ sk_B @ sk_A) @ 
% 0.51/0.73           (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.51/0.73      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.51/0.73  thf('42', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('43', plain,
% 0.51/0.73      (((v2_waybel_0 @ (sk_C @ sk_B @ sk_A) @ 
% 0.51/0.73         (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.73        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.73      inference('clc', [status(thm)], ['41', '42'])).
% 0.51/0.73  thf('44', plain,
% 0.51/0.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('45', plain,
% 0.51/0.73      (![X8 : $i, X9 : $i]:
% 0.51/0.73         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.51/0.73          | (v1_subset_1 @ (sk_C @ X8 @ X9) @ 
% 0.51/0.73             (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X9))))
% 0.51/0.73          | (v4_pre_topc @ X8 @ X9)
% 0.51/0.73          | ~ (l1_pre_topc @ X9)
% 0.51/0.73          | ~ (v2_pre_topc @ X9)
% 0.51/0.73          | (v2_struct_0 @ X9))),
% 0.51/0.73      inference('cnf', [status(esa)], [t29_yellow19])).
% 0.51/0.73  thf('46', plain,
% 0.51/0.73      (((v2_struct_0 @ sk_A)
% 0.51/0.73        | ~ (v2_pre_topc @ sk_A)
% 0.51/0.73        | ~ (l1_pre_topc @ sk_A)
% 0.51/0.73        | (v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.73        | (v1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.51/0.73           (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.73      inference('sup-', [status(thm)], ['44', '45'])).
% 0.51/0.73  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('49', plain,
% 0.51/0.73      (((v2_struct_0 @ sk_A)
% 0.51/0.73        | (v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.73        | (v1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.51/0.73           (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.73      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.51/0.73  thf('50', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('51', plain,
% 0.51/0.73      (((v1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.51/0.73         (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.51/0.73        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.73      inference('clc', [status(thm)], ['49', '50'])).
% 0.51/0.73  thf('52', plain,
% 0.51/0.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('53', plain,
% 0.51/0.73      (![X8 : $i, X9 : $i]:
% 0.51/0.73         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.51/0.73          | (m1_subset_1 @ (sk_C @ X8 @ X9) @ 
% 0.51/0.73             (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X9)))))
% 0.51/0.73          | (v4_pre_topc @ X8 @ X9)
% 0.51/0.73          | ~ (l1_pre_topc @ X9)
% 0.51/0.73          | ~ (v2_pre_topc @ X9)
% 0.51/0.73          | (v2_struct_0 @ X9))),
% 0.51/0.73      inference('cnf', [status(esa)], [t29_yellow19])).
% 0.51/0.73  thf('54', plain,
% 0.51/0.73      (((v2_struct_0 @ sk_A)
% 0.51/0.73        | ~ (v2_pre_topc @ sk_A)
% 0.51/0.73        | ~ (l1_pre_topc @ sk_A)
% 0.51/0.73        | (v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.73        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.51/0.73           (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.51/0.73      inference('sup-', [status(thm)], ['52', '53'])).
% 0.51/0.73  thf('55', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('57', plain,
% 0.51/0.73      (((v2_struct_0 @ sk_A)
% 0.51/0.73        | (v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.73        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.51/0.73           (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.51/0.73      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.51/0.73  thf('58', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('59', plain,
% 0.51/0.73      (((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.51/0.73         (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.51/0.73        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.73      inference('clc', [status(thm)], ['57', '58'])).
% 0.51/0.73  thf(t27_yellow19, axiom,
% 0.51/0.73    (![A:$i]:
% 0.51/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.51/0.73       ( ![B:$i]:
% 0.51/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.73           ( ![C:$i]:
% 0.51/0.73             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.73               ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) ) <=>
% 0.51/0.73                 ( ?[D:$i]:
% 0.51/0.73                   ( ( r1_waybel_7 @ A @ D @ C ) & ( r2_hidden @ B @ D ) & 
% 0.51/0.73                     ( m1_subset_1 @
% 0.51/0.73                       D @ 
% 0.51/0.73                       ( k1_zfmisc_1 @
% 0.51/0.73                         ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) & 
% 0.51/0.73                     ( v13_waybel_0 @ D @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.51/0.73                     ( v2_waybel_0 @ D @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.51/0.73                     ( v1_subset_1 @
% 0.51/0.73                       D @ 
% 0.51/0.73                       ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.51/0.73                     ( ~( v1_xboole_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.51/0.73  thf('60', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.51/0.73         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.51/0.73          | ~ (r1_waybel_7 @ X1 @ X3 @ X2)
% 0.51/0.73          | ~ (r2_hidden @ X0 @ X3)
% 0.51/0.73          | ~ (m1_subset_1 @ X3 @ 
% 0.51/0.73               (k1_zfmisc_1 @ 
% 0.51/0.73                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X1)))))
% 0.51/0.73          | ~ (v13_waybel_0 @ X3 @ (k3_yellow_1 @ (k2_struct_0 @ X1)))
% 0.51/0.73          | ~ (v2_waybel_0 @ X3 @ (k3_yellow_1 @ (k2_struct_0 @ X1)))
% 0.51/0.73          | ~ (v1_subset_1 @ X3 @ 
% 0.51/0.73               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X1))))
% 0.51/0.73          | (v1_xboole_0 @ X3)
% 0.51/0.73          | (r2_hidden @ X2 @ (k2_pre_topc @ X1 @ X0))
% 0.51/0.73          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.51/0.73          | ~ (l1_pre_topc @ X1)
% 0.51/0.73          | ~ (v2_pre_topc @ X1)
% 0.51/0.73          | (v2_struct_0 @ X1))),
% 0.51/0.73      inference('cnf', [status(esa)], [t27_yellow19])).
% 0.51/0.73  thf('61', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         ((v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.73          | (v2_struct_0 @ sk_A)
% 0.51/0.73          | ~ (v2_pre_topc @ sk_A)
% 0.51/0.73          | ~ (l1_pre_topc @ sk_A)
% 0.51/0.73          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.73          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ X1))
% 0.51/0.73          | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.73          | ~ (v1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.51/0.73               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.51/0.73          | ~ (v2_waybel_0 @ (sk_C @ sk_B @ sk_A) @ 
% 0.51/0.73               (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.73          | ~ (v13_waybel_0 @ (sk_C @ sk_B @ sk_A) @ 
% 0.51/0.73               (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.73          | ~ (r2_hidden @ X1 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.73          | ~ (r1_waybel_7 @ sk_A @ (sk_C @ sk_B @ sk_A) @ X0)
% 0.51/0.73          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.51/0.73      inference('sup-', [status(thm)], ['59', '60'])).
% 0.51/0.73  thf('62', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('64', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         ((v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.73          | (v2_struct_0 @ sk_A)
% 0.51/0.73          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.73          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ X1))
% 0.51/0.73          | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.73          | ~ (v1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.51/0.73               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.51/0.73          | ~ (v2_waybel_0 @ (sk_C @ sk_B @ sk_A) @ 
% 0.51/0.73               (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.73          | ~ (v13_waybel_0 @ (sk_C @ sk_B @ sk_A) @ 
% 0.51/0.73               (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.73          | ~ (r2_hidden @ X1 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.73          | ~ (r1_waybel_7 @ sk_A @ (sk_C @ sk_B @ sk_A) @ X0)
% 0.51/0.73          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.51/0.73      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.51/0.73  thf('65', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         ((v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.73          | ~ (r1_waybel_7 @ sk_A @ (sk_C @ sk_B @ sk_A) @ X1)
% 0.51/0.73          | ~ (r2_hidden @ X0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.73          | ~ (v13_waybel_0 @ (sk_C @ sk_B @ sk_A) @ 
% 0.51/0.73               (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.73          | ~ (v2_waybel_0 @ (sk_C @ sk_B @ sk_A) @ 
% 0.51/0.73               (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.73          | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.73          | (r2_hidden @ X1 @ (k2_pre_topc @ sk_A @ X0))
% 0.51/0.73          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.51/0.73          | (v2_struct_0 @ sk_A)
% 0.51/0.73          | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.73      inference('sup-', [status(thm)], ['51', '64'])).
% 0.51/0.73  thf('66', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         ((v2_struct_0 @ sk_A)
% 0.51/0.73          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.51/0.73          | (r2_hidden @ X1 @ (k2_pre_topc @ sk_A @ X0))
% 0.51/0.73          | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.73          | ~ (v2_waybel_0 @ (sk_C @ sk_B @ sk_A) @ 
% 0.51/0.73               (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.73          | ~ (v13_waybel_0 @ (sk_C @ sk_B @ sk_A) @ 
% 0.51/0.73               (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.73          | ~ (r2_hidden @ X0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.73          | ~ (r1_waybel_7 @ sk_A @ (sk_C @ sk_B @ sk_A) @ X1)
% 0.51/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.73          | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.73      inference('simplify', [status(thm)], ['65'])).
% 0.51/0.73  thf('67', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         ((v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.73          | (v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.73          | ~ (r1_waybel_7 @ sk_A @ (sk_C @ sk_B @ sk_A) @ X1)
% 0.51/0.73          | ~ (r2_hidden @ X0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.73          | ~ (v13_waybel_0 @ (sk_C @ sk_B @ sk_A) @ 
% 0.51/0.73               (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.73          | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.73          | (r2_hidden @ X1 @ (k2_pre_topc @ sk_A @ X0))
% 0.51/0.73          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.51/0.73          | (v2_struct_0 @ sk_A))),
% 0.51/0.73      inference('sup-', [status(thm)], ['43', '66'])).
% 0.51/0.73  thf('68', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         ((v2_struct_0 @ sk_A)
% 0.51/0.73          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.51/0.73          | (r2_hidden @ X1 @ (k2_pre_topc @ sk_A @ X0))
% 0.51/0.73          | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.73          | ~ (v13_waybel_0 @ (sk_C @ sk_B @ sk_A) @ 
% 0.51/0.73               (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.73          | ~ (r2_hidden @ X0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.73          | ~ (r1_waybel_7 @ sk_A @ (sk_C @ sk_B @ sk_A) @ X1)
% 0.51/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.73          | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.73      inference('simplify', [status(thm)], ['67'])).
% 0.51/0.73  thf('69', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         ((v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.73          | (v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.74          | ~ (r1_waybel_7 @ sk_A @ (sk_C @ sk_B @ sk_A) @ X1)
% 0.51/0.74          | ~ (r2_hidden @ X0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74          | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74          | (r2_hidden @ X1 @ (k2_pre_topc @ sk_A @ X0))
% 0.51/0.74          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.51/0.74          | (v2_struct_0 @ sk_A))),
% 0.51/0.74      inference('sup-', [status(thm)], ['35', '68'])).
% 0.51/0.74  thf('70', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]:
% 0.51/0.74         ((v2_struct_0 @ sk_A)
% 0.51/0.74          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.51/0.74          | (r2_hidden @ X1 @ (k2_pre_topc @ sk_A @ X0))
% 0.51/0.74          | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74          | ~ (r2_hidden @ X0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74          | ~ (r1_waybel_7 @ sk_A @ (sk_C @ sk_B @ sk_A) @ X1)
% 0.51/0.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.74          | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('simplify', [status(thm)], ['69'])).
% 0.51/0.74  thf('71', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74          | (v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.74          | ~ (r2_hidden @ X0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74          | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74          | (r2_hidden @ (sk_D_2 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ X0))
% 0.51/0.74          | ~ (m1_subset_1 @ (sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.51/0.74          | (v2_struct_0 @ sk_A))),
% 0.51/0.74      inference('sup-', [status(thm)], ['27', '70'])).
% 0.51/0.74  thf('72', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((v2_struct_0 @ sk_A)
% 0.51/0.74          | ~ (m1_subset_1 @ (sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.51/0.74          | (r2_hidden @ (sk_D_2 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ X0))
% 0.51/0.74          | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74          | ~ (r2_hidden @ X0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.74          | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('simplify', [status(thm)], ['71'])).
% 0.51/0.74  thf('73', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74          | (v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.74          | ~ (r2_hidden @ X0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74          | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74          | (r2_hidden @ (sk_D_2 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ X0))
% 0.51/0.74          | (v2_struct_0 @ sk_A))),
% 0.51/0.74      inference('sup-', [status(thm)], ['19', '72'])).
% 0.51/0.74  thf('74', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((v2_struct_0 @ sk_A)
% 0.51/0.74          | (r2_hidden @ (sk_D_2 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ X0))
% 0.51/0.74          | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74          | ~ (r2_hidden @ X0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.74          | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('simplify', [status(thm)], ['73'])).
% 0.51/0.74  thf('75', plain,
% 0.51/0.74      (((v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74        | ~ (r2_hidden @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74        | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74        | (r2_hidden @ (sk_D_2 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.51/0.74        | (v2_struct_0 @ sk_A))),
% 0.51/0.74      inference('sup-', [status(thm)], ['18', '74'])).
% 0.51/0.74  thf('76', plain,
% 0.51/0.74      (((v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74        | (v2_struct_0 @ sk_A)
% 0.51/0.74        | (r2_hidden @ (sk_D_2 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.51/0.74        | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('sup-', [status(thm)], ['17', '75'])).
% 0.51/0.74  thf('77', plain,
% 0.51/0.74      (((v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74        | (r2_hidden @ (sk_D_2 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.51/0.74        | (v2_struct_0 @ sk_A)
% 0.51/0.74        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('simplify', [status(thm)], ['76'])).
% 0.51/0.74  thf('78', plain,
% 0.51/0.74      (((m1_subset_1 @ (sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.51/0.74        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('clc', [status(thm)], ['7', '8'])).
% 0.51/0.74  thf('79', plain,
% 0.51/0.74      (((m1_subset_1 @ (sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.51/0.74        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('clc', [status(thm)], ['7', '8'])).
% 0.51/0.74  thf('80', plain,
% 0.51/0.74      (((v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74        | (r2_hidden @ (sk_D_2 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.51/0.74        | (v2_struct_0 @ sk_A)
% 0.51/0.74        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('simplify', [status(thm)], ['76'])).
% 0.51/0.74  thf('81', plain,
% 0.51/0.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf(t28_yellow19, axiom,
% 0.51/0.74    (![A:$i]:
% 0.51/0.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.51/0.74       ( ![B:$i]:
% 0.51/0.74         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.74           ( ![C:$i]:
% 0.51/0.74             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.74               ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) ) <=>
% 0.51/0.74                 ( ?[D:$i]:
% 0.51/0.74                   ( ( r2_waybel_7 @ A @ D @ C ) & ( r2_hidden @ B @ D ) & 
% 0.51/0.74                     ( m1_subset_1 @
% 0.51/0.74                       D @ 
% 0.51/0.74                       ( k1_zfmisc_1 @
% 0.51/0.74                         ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) & 
% 0.51/0.74                     ( v3_waybel_7 @ D @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.51/0.74                     ( v13_waybel_0 @ D @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.51/0.74                     ( v2_waybel_0 @ D @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.51/0.74                     ( ~( v1_xboole_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.51/0.74  thf('82', plain,
% 0.51/0.74      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.51/0.74         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.51/0.74          | ~ (r2_hidden @ X6 @ (k2_pre_topc @ X5 @ X4))
% 0.51/0.74          | (r2_waybel_7 @ X5 @ (sk_D_1 @ X6 @ X4 @ X5) @ X6)
% 0.51/0.74          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.51/0.74          | ~ (l1_pre_topc @ X5)
% 0.51/0.74          | ~ (v2_pre_topc @ X5)
% 0.51/0.74          | (v2_struct_0 @ X5))),
% 0.51/0.74      inference('cnf', [status(esa)], [t28_yellow19])).
% 0.51/0.74  thf('83', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((v2_struct_0 @ sk_A)
% 0.51/0.74          | ~ (v2_pre_topc @ sk_A)
% 0.51/0.74          | ~ (l1_pre_topc @ sk_A)
% 0.51/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74          | (r2_waybel_7 @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0)
% 0.51/0.74          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['81', '82'])).
% 0.51/0.74  thf('84', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('86', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((v2_struct_0 @ sk_A)
% 0.51/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74          | (r2_waybel_7 @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0)
% 0.51/0.74          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.51/0.74      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.51/0.74  thf('87', plain,
% 0.51/0.74      (((v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74        | (v2_struct_0 @ sk_A)
% 0.51/0.74        | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74        | (r2_waybel_7 @ sk_A @ 
% 0.51/0.74           (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.51/0.74           (sk_D_2 @ sk_B @ sk_A))
% 0.51/0.74        | ~ (m1_subset_1 @ (sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.51/0.74        | (v2_struct_0 @ sk_A))),
% 0.51/0.74      inference('sup-', [status(thm)], ['80', '86'])).
% 0.51/0.74  thf('88', plain,
% 0.51/0.74      ((~ (m1_subset_1 @ (sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.51/0.74        | (r2_waybel_7 @ sk_A @ 
% 0.51/0.74           (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.51/0.74           (sk_D_2 @ sk_B @ sk_A))
% 0.51/0.74        | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74        | (v2_struct_0 @ sk_A)
% 0.51/0.74        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('simplify', [status(thm)], ['87'])).
% 0.51/0.74  thf('89', plain,
% 0.51/0.74      (((v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74        | (v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74        | (v2_struct_0 @ sk_A)
% 0.51/0.74        | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74        | (r2_waybel_7 @ sk_A @ 
% 0.51/0.74           (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.51/0.74           (sk_D_2 @ sk_B @ sk_A)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['79', '88'])).
% 0.51/0.74  thf('90', plain,
% 0.51/0.74      (((r2_waybel_7 @ sk_A @ 
% 0.51/0.74         (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.51/0.74         (sk_D_2 @ sk_B @ sk_A))
% 0.51/0.74        | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74        | (v2_struct_0 @ sk_A)
% 0.51/0.74        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('simplify', [status(thm)], ['89'])).
% 0.51/0.74  thf('91', plain,
% 0.51/0.74      (((m1_subset_1 @ (sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.51/0.74        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('clc', [status(thm)], ['7', '8'])).
% 0.51/0.74  thf('92', plain,
% 0.51/0.74      (((v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74        | (r2_hidden @ (sk_D_2 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.51/0.74        | (v2_struct_0 @ sk_A)
% 0.51/0.74        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('simplify', [status(thm)], ['76'])).
% 0.51/0.74  thf('93', plain,
% 0.51/0.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('94', plain,
% 0.51/0.74      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.51/0.74         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.51/0.74          | ~ (r2_hidden @ X6 @ (k2_pre_topc @ X5 @ X4))
% 0.51/0.74          | (r2_hidden @ X4 @ (sk_D_1 @ X6 @ X4 @ X5))
% 0.51/0.74          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.51/0.74          | ~ (l1_pre_topc @ X5)
% 0.51/0.74          | ~ (v2_pre_topc @ X5)
% 0.51/0.74          | (v2_struct_0 @ X5))),
% 0.51/0.74      inference('cnf', [status(esa)], [t28_yellow19])).
% 0.51/0.74  thf('95', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((v2_struct_0 @ sk_A)
% 0.51/0.74          | ~ (v2_pre_topc @ sk_A)
% 0.51/0.74          | ~ (l1_pre_topc @ sk_A)
% 0.51/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74          | (r2_hidden @ sk_B @ (sk_D_1 @ X0 @ sk_B @ sk_A))
% 0.51/0.74          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['93', '94'])).
% 0.51/0.74  thf('96', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('98', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((v2_struct_0 @ sk_A)
% 0.51/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74          | (r2_hidden @ sk_B @ (sk_D_1 @ X0 @ sk_B @ sk_A))
% 0.51/0.74          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.51/0.74      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.51/0.74  thf('99', plain,
% 0.51/0.74      (((v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74        | (v2_struct_0 @ sk_A)
% 0.51/0.74        | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74        | (r2_hidden @ sk_B @ (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.51/0.74        | ~ (m1_subset_1 @ (sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.51/0.74        | (v2_struct_0 @ sk_A))),
% 0.51/0.74      inference('sup-', [status(thm)], ['92', '98'])).
% 0.51/0.74  thf('100', plain,
% 0.51/0.74      ((~ (m1_subset_1 @ (sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.51/0.74        | (r2_hidden @ sk_B @ (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.51/0.74        | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74        | (v2_struct_0 @ sk_A)
% 0.51/0.74        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('simplify', [status(thm)], ['99'])).
% 0.51/0.74  thf('101', plain,
% 0.51/0.74      (((v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74        | (v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74        | (v2_struct_0 @ sk_A)
% 0.51/0.74        | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74        | (r2_hidden @ sk_B @ (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['91', '100'])).
% 0.51/0.74  thf('102', plain,
% 0.51/0.74      (((r2_hidden @ sk_B @ (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.51/0.74        | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74        | (v2_struct_0 @ sk_A)
% 0.51/0.74        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('simplify', [status(thm)], ['101'])).
% 0.51/0.74  thf('103', plain,
% 0.51/0.74      (((m1_subset_1 @ (sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.51/0.74        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('clc', [status(thm)], ['7', '8'])).
% 0.51/0.74  thf('104', plain,
% 0.51/0.74      (((v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74        | (r2_hidden @ (sk_D_2 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.51/0.74        | (v2_struct_0 @ sk_A)
% 0.51/0.74        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('simplify', [status(thm)], ['76'])).
% 0.51/0.74  thf('105', plain,
% 0.51/0.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('106', plain,
% 0.51/0.74      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.51/0.74         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.51/0.74          | ~ (r2_hidden @ X6 @ (k2_pre_topc @ X5 @ X4))
% 0.51/0.74          | (v2_waybel_0 @ (sk_D_1 @ X6 @ X4 @ X5) @ 
% 0.51/0.74             (k3_yellow_1 @ (k2_struct_0 @ X5)))
% 0.51/0.74          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.51/0.74          | ~ (l1_pre_topc @ X5)
% 0.51/0.74          | ~ (v2_pre_topc @ X5)
% 0.51/0.74          | (v2_struct_0 @ X5))),
% 0.51/0.74      inference('cnf', [status(esa)], [t28_yellow19])).
% 0.51/0.74  thf('107', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((v2_struct_0 @ sk_A)
% 0.51/0.74          | ~ (v2_pre_topc @ sk_A)
% 0.51/0.74          | ~ (l1_pre_topc @ sk_A)
% 0.51/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74          | (v2_waybel_0 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ 
% 0.51/0.74             (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['105', '106'])).
% 0.51/0.74  thf('108', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('109', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('110', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((v2_struct_0 @ sk_A)
% 0.51/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74          | (v2_waybel_0 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ 
% 0.51/0.74             (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.51/0.74      inference('demod', [status(thm)], ['107', '108', '109'])).
% 0.51/0.74  thf('111', plain,
% 0.51/0.74      (((v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74        | (v2_struct_0 @ sk_A)
% 0.51/0.74        | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74        | (v2_waybel_0 @ (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.51/0.74           (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74        | ~ (m1_subset_1 @ (sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.51/0.74        | (v2_struct_0 @ sk_A))),
% 0.51/0.74      inference('sup-', [status(thm)], ['104', '110'])).
% 0.51/0.74  thf('112', plain,
% 0.51/0.74      ((~ (m1_subset_1 @ (sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.51/0.74        | (v2_waybel_0 @ (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.51/0.74           (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74        | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74        | (v2_struct_0 @ sk_A)
% 0.51/0.74        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('simplify', [status(thm)], ['111'])).
% 0.51/0.74  thf('113', plain,
% 0.51/0.74      (((v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74        | (v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74        | (v2_struct_0 @ sk_A)
% 0.51/0.74        | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74        | (v2_waybel_0 @ (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.51/0.74           (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['103', '112'])).
% 0.51/0.74  thf('114', plain,
% 0.51/0.74      (((v2_waybel_0 @ (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.51/0.74         (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74        | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74        | (v2_struct_0 @ sk_A)
% 0.51/0.74        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('simplify', [status(thm)], ['113'])).
% 0.51/0.74  thf('115', plain,
% 0.51/0.74      (((m1_subset_1 @ (sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.51/0.74        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('clc', [status(thm)], ['7', '8'])).
% 0.51/0.74  thf('116', plain,
% 0.51/0.74      (((v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74        | (r2_hidden @ (sk_D_2 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.51/0.74        | (v2_struct_0 @ sk_A)
% 0.51/0.74        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('simplify', [status(thm)], ['76'])).
% 0.51/0.74  thf('117', plain,
% 0.51/0.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('118', plain,
% 0.51/0.74      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.51/0.74         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.51/0.74          | ~ (r2_hidden @ X6 @ (k2_pre_topc @ X5 @ X4))
% 0.51/0.74          | (v13_waybel_0 @ (sk_D_1 @ X6 @ X4 @ X5) @ 
% 0.51/0.74             (k3_yellow_1 @ (k2_struct_0 @ X5)))
% 0.51/0.74          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.51/0.74          | ~ (l1_pre_topc @ X5)
% 0.51/0.74          | ~ (v2_pre_topc @ X5)
% 0.51/0.74          | (v2_struct_0 @ X5))),
% 0.51/0.74      inference('cnf', [status(esa)], [t28_yellow19])).
% 0.51/0.74  thf('119', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((v2_struct_0 @ sk_A)
% 0.51/0.74          | ~ (v2_pre_topc @ sk_A)
% 0.51/0.74          | ~ (l1_pre_topc @ sk_A)
% 0.51/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74          | (v13_waybel_0 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ 
% 0.51/0.74             (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['117', '118'])).
% 0.51/0.74  thf('120', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('121', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('122', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((v2_struct_0 @ sk_A)
% 0.51/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74          | (v13_waybel_0 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ 
% 0.51/0.74             (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.51/0.74      inference('demod', [status(thm)], ['119', '120', '121'])).
% 0.51/0.74  thf('123', plain,
% 0.51/0.74      (((v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74        | (v2_struct_0 @ sk_A)
% 0.51/0.74        | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74        | (v13_waybel_0 @ (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.51/0.74           (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74        | ~ (m1_subset_1 @ (sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.51/0.74        | (v2_struct_0 @ sk_A))),
% 0.51/0.74      inference('sup-', [status(thm)], ['116', '122'])).
% 0.51/0.74  thf('124', plain,
% 0.51/0.74      ((~ (m1_subset_1 @ (sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.51/0.74        | (v13_waybel_0 @ (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.51/0.74           (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74        | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74        | (v2_struct_0 @ sk_A)
% 0.51/0.74        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('simplify', [status(thm)], ['123'])).
% 0.51/0.74  thf('125', plain,
% 0.51/0.74      (((v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74        | (v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74        | (v2_struct_0 @ sk_A)
% 0.51/0.74        | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74        | (v13_waybel_0 @ (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.51/0.74           (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['115', '124'])).
% 0.51/0.74  thf('126', plain,
% 0.51/0.74      (((v13_waybel_0 @ (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.51/0.74         (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74        | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74        | (v2_struct_0 @ sk_A)
% 0.51/0.74        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('simplify', [status(thm)], ['125'])).
% 0.51/0.74  thf('127', plain,
% 0.51/0.74      (((m1_subset_1 @ (sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.51/0.74        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('clc', [status(thm)], ['7', '8'])).
% 0.51/0.74  thf('128', plain,
% 0.51/0.74      (((v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74        | (r2_hidden @ (sk_D_2 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.51/0.74        | (v2_struct_0 @ sk_A)
% 0.51/0.74        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('simplify', [status(thm)], ['76'])).
% 0.51/0.74  thf('129', plain,
% 0.51/0.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('130', plain,
% 0.51/0.74      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.51/0.74         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.51/0.74          | ~ (r2_hidden @ X6 @ (k2_pre_topc @ X5 @ X4))
% 0.51/0.74          | (v3_waybel_7 @ (sk_D_1 @ X6 @ X4 @ X5) @ 
% 0.51/0.74             (k3_yellow_1 @ (k2_struct_0 @ X5)))
% 0.51/0.74          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.51/0.74          | ~ (l1_pre_topc @ X5)
% 0.51/0.74          | ~ (v2_pre_topc @ X5)
% 0.51/0.74          | (v2_struct_0 @ X5))),
% 0.51/0.74      inference('cnf', [status(esa)], [t28_yellow19])).
% 0.51/0.74  thf('131', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((v2_struct_0 @ sk_A)
% 0.51/0.74          | ~ (v2_pre_topc @ sk_A)
% 0.51/0.74          | ~ (l1_pre_topc @ sk_A)
% 0.51/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74          | (v3_waybel_7 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ 
% 0.51/0.74             (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['129', '130'])).
% 0.51/0.74  thf('132', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('133', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('134', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((v2_struct_0 @ sk_A)
% 0.51/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74          | (v3_waybel_7 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ 
% 0.51/0.74             (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.51/0.74      inference('demod', [status(thm)], ['131', '132', '133'])).
% 0.51/0.74  thf('135', plain,
% 0.51/0.74      (((v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74        | (v2_struct_0 @ sk_A)
% 0.51/0.74        | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74        | (v3_waybel_7 @ (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.51/0.74           (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74        | ~ (m1_subset_1 @ (sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.51/0.74        | (v2_struct_0 @ sk_A))),
% 0.51/0.74      inference('sup-', [status(thm)], ['128', '134'])).
% 0.51/0.74  thf('136', plain,
% 0.51/0.74      ((~ (m1_subset_1 @ (sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.51/0.74        | (v3_waybel_7 @ (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.51/0.74           (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74        | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74        | (v2_struct_0 @ sk_A)
% 0.51/0.74        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('simplify', [status(thm)], ['135'])).
% 0.51/0.74  thf('137', plain,
% 0.51/0.74      (((v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74        | (v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74        | (v2_struct_0 @ sk_A)
% 0.51/0.74        | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74        | (v3_waybel_7 @ (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.51/0.74           (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['127', '136'])).
% 0.51/0.74  thf('138', plain,
% 0.51/0.74      (((v3_waybel_7 @ (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.51/0.74         (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74        | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74        | (v2_struct_0 @ sk_A)
% 0.51/0.74        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('simplify', [status(thm)], ['137'])).
% 0.51/0.74  thf('139', plain,
% 0.51/0.74      (((m1_subset_1 @ (sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.51/0.74        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('clc', [status(thm)], ['7', '8'])).
% 0.51/0.74  thf('140', plain,
% 0.51/0.74      (((v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74        | (r2_hidden @ (sk_D_2 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.51/0.74        | (v2_struct_0 @ sk_A)
% 0.51/0.74        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('simplify', [status(thm)], ['76'])).
% 0.51/0.74  thf('141', plain,
% 0.51/0.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('142', plain,
% 0.51/0.74      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.51/0.74         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.51/0.74          | ~ (r2_hidden @ X6 @ (k2_pre_topc @ X5 @ X4))
% 0.51/0.74          | (m1_subset_1 @ (sk_D_1 @ X6 @ X4 @ X5) @ 
% 0.51/0.74             (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X5)))))
% 0.51/0.74          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.51/0.74          | ~ (l1_pre_topc @ X5)
% 0.51/0.74          | ~ (v2_pre_topc @ X5)
% 0.51/0.74          | (v2_struct_0 @ X5))),
% 0.51/0.74      inference('cnf', [status(esa)], [t28_yellow19])).
% 0.51/0.74  thf('143', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((v2_struct_0 @ sk_A)
% 0.51/0.74          | ~ (v2_pre_topc @ sk_A)
% 0.51/0.74          | ~ (l1_pre_topc @ sk_A)
% 0.51/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ 
% 0.51/0.74             (k1_zfmisc_1 @ 
% 0.51/0.74              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.51/0.74          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['141', '142'])).
% 0.51/0.74  thf('144', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('145', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('146', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((v2_struct_0 @ sk_A)
% 0.51/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ 
% 0.51/0.74             (k1_zfmisc_1 @ 
% 0.51/0.74              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.51/0.74          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.51/0.74      inference('demod', [status(thm)], ['143', '144', '145'])).
% 0.51/0.74  thf('147', plain,
% 0.51/0.74      (((v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74        | (v2_struct_0 @ sk_A)
% 0.51/0.74        | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74        | (m1_subset_1 @ (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.51/0.74           (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.51/0.74        | ~ (m1_subset_1 @ (sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.51/0.74        | (v2_struct_0 @ sk_A))),
% 0.51/0.74      inference('sup-', [status(thm)], ['140', '146'])).
% 0.51/0.74  thf('148', plain,
% 0.51/0.74      ((~ (m1_subset_1 @ (sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.51/0.74        | (m1_subset_1 @ (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.51/0.74           (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.51/0.74        | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74        | (v2_struct_0 @ sk_A)
% 0.51/0.74        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('simplify', [status(thm)], ['147'])).
% 0.51/0.74  thf('149', plain,
% 0.51/0.74      (((v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74        | (v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74        | (v2_struct_0 @ sk_A)
% 0.51/0.74        | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74        | (m1_subset_1 @ (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.51/0.74           (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['139', '148'])).
% 0.51/0.74  thf('150', plain,
% 0.51/0.74      (((m1_subset_1 @ (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.51/0.74         (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.51/0.74        | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74        | (v2_struct_0 @ sk_A)
% 0.51/0.74        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('simplify', [status(thm)], ['149'])).
% 0.51/0.74  thf('151', plain,
% 0.51/0.74      ((![X12 : $i, X13 : $i]:
% 0.51/0.74          ((v1_xboole_0 @ X12)
% 0.51/0.74           | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74           | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74           | ~ (v3_waybel_7 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74           | ~ (m1_subset_1 @ X12 @ 
% 0.51/0.74                (k1_zfmisc_1 @ 
% 0.51/0.74                 (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.51/0.74           | ~ (r2_waybel_7 @ sk_A @ X12 @ X13)
% 0.51/0.74           | (r2_hidden @ X13 @ sk_B)
% 0.51/0.74           | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.51/0.74           | ~ (r2_hidden @ sk_B @ X12)))
% 0.51/0.74         <= ((![X12 : $i, X13 : $i]:
% 0.51/0.74                ((v1_xboole_0 @ X12)
% 0.51/0.74                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v3_waybel_7 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (m1_subset_1 @ X12 @ 
% 0.51/0.74                      (k1_zfmisc_1 @ 
% 0.51/0.74                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.51/0.74                 | ~ (r2_waybel_7 @ sk_A @ X12 @ X13)
% 0.51/0.74                 | (r2_hidden @ X13 @ sk_B)
% 0.51/0.74                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.51/0.74                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.51/0.74      inference('split', [status(esa)], ['0'])).
% 0.51/0.74  thf('152', plain,
% 0.51/0.74      ((![X0 : $i]:
% 0.51/0.74          ((v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74           | (v2_struct_0 @ sk_A)
% 0.51/0.74           | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74           | ~ (r2_hidden @ sk_B @ 
% 0.51/0.74                (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.51/0.74           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74           | (r2_hidden @ X0 @ sk_B)
% 0.51/0.74           | ~ (r2_waybel_7 @ sk_A @ 
% 0.51/0.74                (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A) @ X0)
% 0.51/0.74           | ~ (v3_waybel_7 @ 
% 0.51/0.74                (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.51/0.74                (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74           | ~ (v13_waybel_0 @ 
% 0.51/0.74                (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.51/0.74                (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74           | ~ (v2_waybel_0 @ 
% 0.51/0.74                (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.51/0.74                (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74           | (v1_xboole_0 @ (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A))))
% 0.51/0.74         <= ((![X12 : $i, X13 : $i]:
% 0.51/0.74                ((v1_xboole_0 @ X12)
% 0.51/0.74                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v3_waybel_7 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (m1_subset_1 @ X12 @ 
% 0.51/0.74                      (k1_zfmisc_1 @ 
% 0.51/0.74                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.51/0.74                 | ~ (r2_waybel_7 @ sk_A @ X12 @ X13)
% 0.51/0.74                 | (r2_hidden @ X13 @ sk_B)
% 0.51/0.74                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.51/0.74                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['150', '151'])).
% 0.51/0.74  thf('153', plain,
% 0.51/0.74      ((![X0 : $i]:
% 0.51/0.74          ((v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74           | (v2_struct_0 @ sk_A)
% 0.51/0.74           | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74           | (v1_xboole_0 @ (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.51/0.74           | ~ (v2_waybel_0 @ 
% 0.51/0.74                (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.51/0.74                (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74           | ~ (v13_waybel_0 @ 
% 0.51/0.74                (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.51/0.74                (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74           | ~ (r2_waybel_7 @ sk_A @ 
% 0.51/0.74                (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A) @ X0)
% 0.51/0.74           | (r2_hidden @ X0 @ sk_B)
% 0.51/0.74           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74           | ~ (r2_hidden @ sk_B @ 
% 0.51/0.74                (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.51/0.74           | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74           | (v2_struct_0 @ sk_A)
% 0.51/0.74           | (v4_pre_topc @ sk_B @ sk_A)))
% 0.51/0.74         <= ((![X12 : $i, X13 : $i]:
% 0.51/0.74                ((v1_xboole_0 @ X12)
% 0.51/0.74                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v3_waybel_7 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (m1_subset_1 @ X12 @ 
% 0.51/0.74                      (k1_zfmisc_1 @ 
% 0.51/0.74                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.51/0.74                 | ~ (r2_waybel_7 @ sk_A @ X12 @ X13)
% 0.51/0.74                 | (r2_hidden @ X13 @ sk_B)
% 0.51/0.74                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.51/0.74                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['138', '152'])).
% 0.51/0.74  thf('154', plain,
% 0.51/0.74      ((![X0 : $i]:
% 0.51/0.74          (~ (r2_hidden @ sk_B @ 
% 0.51/0.74              (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.51/0.74           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74           | (r2_hidden @ X0 @ sk_B)
% 0.51/0.74           | ~ (r2_waybel_7 @ sk_A @ 
% 0.51/0.74                (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A) @ X0)
% 0.51/0.74           | ~ (v13_waybel_0 @ 
% 0.51/0.74                (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.51/0.74                (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74           | ~ (v2_waybel_0 @ 
% 0.51/0.74                (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.51/0.74                (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74           | (v1_xboole_0 @ (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.51/0.74           | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74           | (v2_struct_0 @ sk_A)
% 0.51/0.74           | (v4_pre_topc @ sk_B @ sk_A)))
% 0.51/0.74         <= ((![X12 : $i, X13 : $i]:
% 0.51/0.74                ((v1_xboole_0 @ X12)
% 0.51/0.74                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v3_waybel_7 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (m1_subset_1 @ X12 @ 
% 0.51/0.74                      (k1_zfmisc_1 @ 
% 0.51/0.74                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.51/0.74                 | ~ (r2_waybel_7 @ sk_A @ X12 @ X13)
% 0.51/0.74                 | (r2_hidden @ X13 @ sk_B)
% 0.51/0.74                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.51/0.74                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.51/0.74      inference('simplify', [status(thm)], ['153'])).
% 0.51/0.74  thf('155', plain,
% 0.51/0.74      ((![X0 : $i]:
% 0.51/0.74          ((v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74           | (v2_struct_0 @ sk_A)
% 0.51/0.74           | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74           | (v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74           | (v2_struct_0 @ sk_A)
% 0.51/0.74           | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74           | (v1_xboole_0 @ (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.51/0.74           | ~ (v2_waybel_0 @ 
% 0.51/0.74                (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.51/0.74                (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74           | ~ (r2_waybel_7 @ sk_A @ 
% 0.51/0.74                (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A) @ X0)
% 0.51/0.74           | (r2_hidden @ X0 @ sk_B)
% 0.51/0.74           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74           | ~ (r2_hidden @ sk_B @ 
% 0.51/0.74                (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A))))
% 0.51/0.74         <= ((![X12 : $i, X13 : $i]:
% 0.51/0.74                ((v1_xboole_0 @ X12)
% 0.51/0.74                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v3_waybel_7 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (m1_subset_1 @ X12 @ 
% 0.51/0.74                      (k1_zfmisc_1 @ 
% 0.51/0.74                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.51/0.74                 | ~ (r2_waybel_7 @ sk_A @ X12 @ X13)
% 0.51/0.74                 | (r2_hidden @ X13 @ sk_B)
% 0.51/0.74                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.51/0.74                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['126', '154'])).
% 0.51/0.74  thf('156', plain,
% 0.51/0.74      ((![X0 : $i]:
% 0.51/0.74          (~ (r2_hidden @ sk_B @ 
% 0.51/0.74              (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.51/0.74           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74           | (r2_hidden @ X0 @ sk_B)
% 0.51/0.74           | ~ (r2_waybel_7 @ sk_A @ 
% 0.51/0.74                (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A) @ X0)
% 0.51/0.74           | ~ (v2_waybel_0 @ 
% 0.51/0.74                (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A) @ 
% 0.51/0.74                (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74           | (v1_xboole_0 @ (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.51/0.74           | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74           | (v2_struct_0 @ sk_A)
% 0.51/0.74           | (v4_pre_topc @ sk_B @ sk_A)))
% 0.51/0.74         <= ((![X12 : $i, X13 : $i]:
% 0.51/0.74                ((v1_xboole_0 @ X12)
% 0.51/0.74                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v3_waybel_7 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (m1_subset_1 @ X12 @ 
% 0.51/0.74                      (k1_zfmisc_1 @ 
% 0.51/0.74                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.51/0.74                 | ~ (r2_waybel_7 @ sk_A @ X12 @ X13)
% 0.51/0.74                 | (r2_hidden @ X13 @ sk_B)
% 0.51/0.74                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.51/0.74                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.51/0.74      inference('simplify', [status(thm)], ['155'])).
% 0.51/0.74  thf('157', plain,
% 0.51/0.74      ((![X0 : $i]:
% 0.51/0.74          ((v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74           | (v2_struct_0 @ sk_A)
% 0.51/0.74           | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74           | (v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74           | (v2_struct_0 @ sk_A)
% 0.51/0.74           | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74           | (v1_xboole_0 @ (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.51/0.74           | ~ (r2_waybel_7 @ sk_A @ 
% 0.51/0.74                (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A) @ X0)
% 0.51/0.74           | (r2_hidden @ X0 @ sk_B)
% 0.51/0.74           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74           | ~ (r2_hidden @ sk_B @ 
% 0.51/0.74                (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A))))
% 0.51/0.74         <= ((![X12 : $i, X13 : $i]:
% 0.51/0.74                ((v1_xboole_0 @ X12)
% 0.51/0.74                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v3_waybel_7 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (m1_subset_1 @ X12 @ 
% 0.51/0.74                      (k1_zfmisc_1 @ 
% 0.51/0.74                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.51/0.74                 | ~ (r2_waybel_7 @ sk_A @ X12 @ X13)
% 0.51/0.74                 | (r2_hidden @ X13 @ sk_B)
% 0.51/0.74                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.51/0.74                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['114', '156'])).
% 0.51/0.74  thf('158', plain,
% 0.51/0.74      ((![X0 : $i]:
% 0.51/0.74          (~ (r2_hidden @ sk_B @ 
% 0.51/0.74              (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.51/0.74           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74           | (r2_hidden @ X0 @ sk_B)
% 0.51/0.74           | ~ (r2_waybel_7 @ sk_A @ 
% 0.51/0.74                (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A) @ X0)
% 0.51/0.74           | (v1_xboole_0 @ (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.51/0.74           | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74           | (v2_struct_0 @ sk_A)
% 0.51/0.74           | (v4_pre_topc @ sk_B @ sk_A)))
% 0.51/0.74         <= ((![X12 : $i, X13 : $i]:
% 0.51/0.74                ((v1_xboole_0 @ X12)
% 0.51/0.74                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v3_waybel_7 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (m1_subset_1 @ X12 @ 
% 0.51/0.74                      (k1_zfmisc_1 @ 
% 0.51/0.74                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.51/0.74                 | ~ (r2_waybel_7 @ sk_A @ X12 @ X13)
% 0.51/0.74                 | (r2_hidden @ X13 @ sk_B)
% 0.51/0.74                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.51/0.74                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.51/0.74      inference('simplify', [status(thm)], ['157'])).
% 0.51/0.74  thf('159', plain,
% 0.51/0.74      ((![X0 : $i]:
% 0.51/0.74          ((v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74           | (v2_struct_0 @ sk_A)
% 0.51/0.74           | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74           | (v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74           | (v2_struct_0 @ sk_A)
% 0.51/0.74           | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74           | (v1_xboole_0 @ (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.51/0.74           | ~ (r2_waybel_7 @ sk_A @ 
% 0.51/0.74                (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A) @ X0)
% 0.51/0.74           | (r2_hidden @ X0 @ sk_B)
% 0.51/0.74           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.51/0.74         <= ((![X12 : $i, X13 : $i]:
% 0.51/0.74                ((v1_xboole_0 @ X12)
% 0.51/0.74                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v3_waybel_7 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (m1_subset_1 @ X12 @ 
% 0.51/0.74                      (k1_zfmisc_1 @ 
% 0.51/0.74                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.51/0.74                 | ~ (r2_waybel_7 @ sk_A @ X12 @ X13)
% 0.51/0.74                 | (r2_hidden @ X13 @ sk_B)
% 0.51/0.74                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.51/0.74                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['102', '158'])).
% 0.51/0.74  thf('160', plain,
% 0.51/0.74      ((![X0 : $i]:
% 0.51/0.74          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74           | (r2_hidden @ X0 @ sk_B)
% 0.51/0.74           | ~ (r2_waybel_7 @ sk_A @ 
% 0.51/0.74                (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A) @ X0)
% 0.51/0.74           | (v1_xboole_0 @ (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.51/0.74           | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74           | (v2_struct_0 @ sk_A)
% 0.51/0.74           | (v4_pre_topc @ sk_B @ sk_A)))
% 0.51/0.74         <= ((![X12 : $i, X13 : $i]:
% 0.51/0.74                ((v1_xboole_0 @ X12)
% 0.51/0.74                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v3_waybel_7 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (m1_subset_1 @ X12 @ 
% 0.51/0.74                      (k1_zfmisc_1 @ 
% 0.51/0.74                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.51/0.74                 | ~ (r2_waybel_7 @ sk_A @ X12 @ X13)
% 0.51/0.74                 | (r2_hidden @ X13 @ sk_B)
% 0.51/0.74                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.51/0.74                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.51/0.74      inference('simplify', [status(thm)], ['159'])).
% 0.51/0.74  thf('161', plain,
% 0.51/0.74      ((((v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74         | (v2_struct_0 @ sk_A)
% 0.51/0.74         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74         | (v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74         | (v2_struct_0 @ sk_A)
% 0.51/0.74         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74         | (v1_xboole_0 @ (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.51/0.74         | (r2_hidden @ (sk_D_2 @ sk_B @ sk_A) @ sk_B)
% 0.51/0.74         | ~ (m1_subset_1 @ (sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.51/0.74         <= ((![X12 : $i, X13 : $i]:
% 0.51/0.74                ((v1_xboole_0 @ X12)
% 0.51/0.74                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v3_waybel_7 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (m1_subset_1 @ X12 @ 
% 0.51/0.74                      (k1_zfmisc_1 @ 
% 0.51/0.74                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.51/0.74                 | ~ (r2_waybel_7 @ sk_A @ X12 @ X13)
% 0.51/0.74                 | (r2_hidden @ X13 @ sk_B)
% 0.51/0.74                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.51/0.74                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['90', '160'])).
% 0.51/0.74  thf('162', plain,
% 0.51/0.74      (((~ (m1_subset_1 @ (sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.51/0.74         | (r2_hidden @ (sk_D_2 @ sk_B @ sk_A) @ sk_B)
% 0.51/0.74         | (v1_xboole_0 @ (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.51/0.74         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74         | (v2_struct_0 @ sk_A)
% 0.51/0.74         | (v4_pre_topc @ sk_B @ sk_A)))
% 0.51/0.74         <= ((![X12 : $i, X13 : $i]:
% 0.51/0.74                ((v1_xboole_0 @ X12)
% 0.51/0.74                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v3_waybel_7 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (m1_subset_1 @ X12 @ 
% 0.51/0.74                      (k1_zfmisc_1 @ 
% 0.51/0.74                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.51/0.74                 | ~ (r2_waybel_7 @ sk_A @ X12 @ X13)
% 0.51/0.74                 | (r2_hidden @ X13 @ sk_B)
% 0.51/0.74                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.51/0.74                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.51/0.74      inference('simplify', [status(thm)], ['161'])).
% 0.51/0.74  thf('163', plain,
% 0.51/0.74      ((((v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74         | (v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74         | (v2_struct_0 @ sk_A)
% 0.51/0.74         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74         | (v1_xboole_0 @ (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.51/0.74         | (r2_hidden @ (sk_D_2 @ sk_B @ sk_A) @ sk_B)))
% 0.51/0.74         <= ((![X12 : $i, X13 : $i]:
% 0.51/0.74                ((v1_xboole_0 @ X12)
% 0.51/0.74                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v3_waybel_7 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (m1_subset_1 @ X12 @ 
% 0.51/0.74                      (k1_zfmisc_1 @ 
% 0.51/0.74                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.51/0.74                 | ~ (r2_waybel_7 @ sk_A @ X12 @ X13)
% 0.51/0.74                 | (r2_hidden @ X13 @ sk_B)
% 0.51/0.74                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.51/0.74                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['78', '162'])).
% 0.51/0.74  thf('164', plain,
% 0.51/0.74      ((((r2_hidden @ (sk_D_2 @ sk_B @ sk_A) @ sk_B)
% 0.51/0.74         | (v1_xboole_0 @ (sk_D_1 @ (sk_D_2 @ sk_B @ sk_A) @ sk_B @ sk_A))
% 0.51/0.74         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74         | (v2_struct_0 @ sk_A)
% 0.51/0.74         | (v4_pre_topc @ sk_B @ sk_A)))
% 0.51/0.74         <= ((![X12 : $i, X13 : $i]:
% 0.51/0.74                ((v1_xboole_0 @ X12)
% 0.51/0.74                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v3_waybel_7 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (m1_subset_1 @ X12 @ 
% 0.51/0.74                      (k1_zfmisc_1 @ 
% 0.51/0.74                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.51/0.74                 | ~ (r2_waybel_7 @ sk_A @ X12 @ X13)
% 0.51/0.74                 | (r2_hidden @ X13 @ sk_B)
% 0.51/0.74                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.51/0.74                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.51/0.74      inference('simplify', [status(thm)], ['163'])).
% 0.51/0.74  thf('165', plain,
% 0.51/0.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('166', plain,
% 0.51/0.74      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.51/0.74         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.51/0.74          | ~ (r2_hidden @ X6 @ (k2_pre_topc @ X5 @ X4))
% 0.51/0.74          | ~ (v1_xboole_0 @ (sk_D_1 @ X6 @ X4 @ X5))
% 0.51/0.74          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.51/0.74          | ~ (l1_pre_topc @ X5)
% 0.51/0.74          | ~ (v2_pre_topc @ X5)
% 0.51/0.74          | (v2_struct_0 @ X5))),
% 0.51/0.74      inference('cnf', [status(esa)], [t28_yellow19])).
% 0.51/0.74  thf('167', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((v2_struct_0 @ sk_A)
% 0.51/0.74          | ~ (v2_pre_topc @ sk_A)
% 0.51/0.74          | ~ (l1_pre_topc @ sk_A)
% 0.51/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74          | ~ (v1_xboole_0 @ (sk_D_1 @ X0 @ sk_B @ sk_A))
% 0.51/0.74          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['165', '166'])).
% 0.51/0.74  thf('168', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('169', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('170', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((v2_struct_0 @ sk_A)
% 0.51/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74          | ~ (v1_xboole_0 @ (sk_D_1 @ X0 @ sk_B @ sk_A))
% 0.51/0.74          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.51/0.74      inference('demod', [status(thm)], ['167', '168', '169'])).
% 0.51/0.74  thf('171', plain,
% 0.51/0.74      ((((v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74         | (v2_struct_0 @ sk_A)
% 0.51/0.74         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74         | (r2_hidden @ (sk_D_2 @ sk_B @ sk_A) @ sk_B)
% 0.51/0.74         | ~ (r2_hidden @ (sk_D_2 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.51/0.74         | ~ (m1_subset_1 @ (sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.51/0.74         | (v2_struct_0 @ sk_A)))
% 0.51/0.74         <= ((![X12 : $i, X13 : $i]:
% 0.51/0.74                ((v1_xboole_0 @ X12)
% 0.51/0.74                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v3_waybel_7 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (m1_subset_1 @ X12 @ 
% 0.51/0.74                      (k1_zfmisc_1 @ 
% 0.51/0.74                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.51/0.74                 | ~ (r2_waybel_7 @ sk_A @ X12 @ X13)
% 0.51/0.74                 | (r2_hidden @ X13 @ sk_B)
% 0.51/0.74                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.51/0.74                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['164', '170'])).
% 0.51/0.74  thf('172', plain,
% 0.51/0.74      (((~ (m1_subset_1 @ (sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.51/0.74         | ~ (r2_hidden @ (sk_D_2 @ sk_B @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.51/0.74         | (r2_hidden @ (sk_D_2 @ sk_B @ sk_A) @ sk_B)
% 0.51/0.74         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74         | (v2_struct_0 @ sk_A)
% 0.51/0.74         | (v4_pre_topc @ sk_B @ sk_A)))
% 0.51/0.74         <= ((![X12 : $i, X13 : $i]:
% 0.51/0.74                ((v1_xboole_0 @ X12)
% 0.51/0.74                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v3_waybel_7 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (m1_subset_1 @ X12 @ 
% 0.51/0.74                      (k1_zfmisc_1 @ 
% 0.51/0.74                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.51/0.74                 | ~ (r2_waybel_7 @ sk_A @ X12 @ X13)
% 0.51/0.74                 | (r2_hidden @ X13 @ sk_B)
% 0.51/0.74                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.51/0.74                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.51/0.74      inference('simplify', [status(thm)], ['171'])).
% 0.51/0.74  thf('173', plain,
% 0.51/0.74      ((((v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74         | (v2_struct_0 @ sk_A)
% 0.51/0.74         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74         | (v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74         | (v2_struct_0 @ sk_A)
% 0.51/0.74         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74         | (r2_hidden @ (sk_D_2 @ sk_B @ sk_A) @ sk_B)
% 0.51/0.74         | ~ (m1_subset_1 @ (sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.51/0.74         <= ((![X12 : $i, X13 : $i]:
% 0.51/0.74                ((v1_xboole_0 @ X12)
% 0.51/0.74                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v3_waybel_7 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (m1_subset_1 @ X12 @ 
% 0.51/0.74                      (k1_zfmisc_1 @ 
% 0.51/0.74                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.51/0.74                 | ~ (r2_waybel_7 @ sk_A @ X12 @ X13)
% 0.51/0.74                 | (r2_hidden @ X13 @ sk_B)
% 0.51/0.74                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.51/0.74                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['77', '172'])).
% 0.51/0.74  thf('174', plain,
% 0.51/0.74      (((~ (m1_subset_1 @ (sk_D_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.51/0.74         | (r2_hidden @ (sk_D_2 @ sk_B @ sk_A) @ sk_B)
% 0.51/0.74         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74         | (v2_struct_0 @ sk_A)
% 0.51/0.74         | (v4_pre_topc @ sk_B @ sk_A)))
% 0.51/0.74         <= ((![X12 : $i, X13 : $i]:
% 0.51/0.74                ((v1_xboole_0 @ X12)
% 0.51/0.74                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v3_waybel_7 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (m1_subset_1 @ X12 @ 
% 0.51/0.74                      (k1_zfmisc_1 @ 
% 0.51/0.74                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.51/0.74                 | ~ (r2_waybel_7 @ sk_A @ X12 @ X13)
% 0.51/0.74                 | (r2_hidden @ X13 @ sk_B)
% 0.51/0.74                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.51/0.74                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.51/0.74      inference('simplify', [status(thm)], ['173'])).
% 0.51/0.74  thf('175', plain,
% 0.51/0.74      ((((v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74         | (v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74         | (v2_struct_0 @ sk_A)
% 0.51/0.74         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74         | (r2_hidden @ (sk_D_2 @ sk_B @ sk_A) @ sk_B)))
% 0.51/0.74         <= ((![X12 : $i, X13 : $i]:
% 0.51/0.74                ((v1_xboole_0 @ X12)
% 0.51/0.74                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v3_waybel_7 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (m1_subset_1 @ X12 @ 
% 0.51/0.74                      (k1_zfmisc_1 @ 
% 0.51/0.74                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.51/0.74                 | ~ (r2_waybel_7 @ sk_A @ X12 @ X13)
% 0.51/0.74                 | (r2_hidden @ X13 @ sk_B)
% 0.51/0.74                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.51/0.74                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['9', '174'])).
% 0.51/0.74  thf('176', plain,
% 0.51/0.74      ((((r2_hidden @ (sk_D_2 @ sk_B @ sk_A) @ sk_B)
% 0.51/0.74         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74         | (v2_struct_0 @ sk_A)
% 0.51/0.74         | (v4_pre_topc @ sk_B @ sk_A)))
% 0.51/0.74         <= ((![X12 : $i, X13 : $i]:
% 0.51/0.74                ((v1_xboole_0 @ X12)
% 0.51/0.74                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v3_waybel_7 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (m1_subset_1 @ X12 @ 
% 0.51/0.74                      (k1_zfmisc_1 @ 
% 0.51/0.74                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.51/0.74                 | ~ (r2_waybel_7 @ sk_A @ X12 @ X13)
% 0.51/0.74                 | (r2_hidden @ X13 @ sk_B)
% 0.51/0.74                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.51/0.74                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.51/0.74      inference('simplify', [status(thm)], ['175'])).
% 0.51/0.74  thf('177', plain,
% 0.51/0.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('178', plain,
% 0.51/0.74      (![X8 : $i, X9 : $i]:
% 0.51/0.74         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.51/0.74          | ~ (r2_hidden @ (sk_D_2 @ X8 @ X9) @ X8)
% 0.51/0.74          | (v4_pre_topc @ X8 @ X9)
% 0.51/0.74          | ~ (l1_pre_topc @ X9)
% 0.51/0.74          | ~ (v2_pre_topc @ X9)
% 0.51/0.74          | (v2_struct_0 @ X9))),
% 0.51/0.74      inference('cnf', [status(esa)], [t29_yellow19])).
% 0.51/0.74  thf('179', plain,
% 0.51/0.74      (((v2_struct_0 @ sk_A)
% 0.51/0.74        | ~ (v2_pre_topc @ sk_A)
% 0.51/0.74        | ~ (l1_pre_topc @ sk_A)
% 0.51/0.74        | (v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74        | ~ (r2_hidden @ (sk_D_2 @ sk_B @ sk_A) @ sk_B))),
% 0.51/0.74      inference('sup-', [status(thm)], ['177', '178'])).
% 0.51/0.74  thf('180', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('181', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('182', plain,
% 0.51/0.74      (((v2_struct_0 @ sk_A)
% 0.51/0.74        | (v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74        | ~ (r2_hidden @ (sk_D_2 @ sk_B @ sk_A) @ sk_B))),
% 0.51/0.74      inference('demod', [status(thm)], ['179', '180', '181'])).
% 0.51/0.74  thf('183', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('184', plain,
% 0.51/0.74      ((~ (r2_hidden @ (sk_D_2 @ sk_B @ sk_A) @ sk_B)
% 0.51/0.74        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('clc', [status(thm)], ['182', '183'])).
% 0.51/0.74  thf('185', plain,
% 0.51/0.74      ((((v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74         | (v2_struct_0 @ sk_A)
% 0.51/0.74         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74         | (v4_pre_topc @ sk_B @ sk_A)))
% 0.51/0.74         <= ((![X12 : $i, X13 : $i]:
% 0.51/0.74                ((v1_xboole_0 @ X12)
% 0.51/0.74                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v3_waybel_7 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (m1_subset_1 @ X12 @ 
% 0.51/0.74                      (k1_zfmisc_1 @ 
% 0.51/0.74                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.51/0.74                 | ~ (r2_waybel_7 @ sk_A @ X12 @ X13)
% 0.51/0.74                 | (r2_hidden @ X13 @ sk_B)
% 0.51/0.74                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.51/0.74                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['176', '184'])).
% 0.51/0.74  thf('186', plain,
% 0.51/0.74      ((((v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.51/0.74         | (v2_struct_0 @ sk_A)
% 0.51/0.74         | (v4_pre_topc @ sk_B @ sk_A)))
% 0.51/0.74         <= ((![X12 : $i, X13 : $i]:
% 0.51/0.74                ((v1_xboole_0 @ X12)
% 0.51/0.74                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v3_waybel_7 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (m1_subset_1 @ X12 @ 
% 0.51/0.74                      (k1_zfmisc_1 @ 
% 0.51/0.74                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.51/0.74                 | ~ (r2_waybel_7 @ sk_A @ X12 @ X13)
% 0.51/0.74                 | (r2_hidden @ X13 @ sk_B)
% 0.51/0.74                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.51/0.74                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.51/0.74      inference('simplify', [status(thm)], ['185'])).
% 0.51/0.74  thf('187', plain,
% 0.51/0.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('188', plain,
% 0.51/0.74      (![X8 : $i, X9 : $i]:
% 0.51/0.74         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.51/0.74          | ~ (v1_xboole_0 @ (sk_C @ X8 @ X9))
% 0.51/0.74          | (v4_pre_topc @ X8 @ X9)
% 0.51/0.74          | ~ (l1_pre_topc @ X9)
% 0.51/0.74          | ~ (v2_pre_topc @ X9)
% 0.51/0.74          | (v2_struct_0 @ X9))),
% 0.51/0.74      inference('cnf', [status(esa)], [t29_yellow19])).
% 0.51/0.74  thf('189', plain,
% 0.51/0.74      (((v2_struct_0 @ sk_A)
% 0.51/0.74        | ~ (v2_pre_topc @ sk_A)
% 0.51/0.74        | ~ (l1_pre_topc @ sk_A)
% 0.51/0.74        | (v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74        | ~ (v1_xboole_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['187', '188'])).
% 0.51/0.74  thf('190', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('191', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('192', plain,
% 0.51/0.74      (((v2_struct_0 @ sk_A)
% 0.51/0.74        | (v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74        | ~ (v1_xboole_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.51/0.74      inference('demod', [status(thm)], ['189', '190', '191'])).
% 0.51/0.74  thf('193', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('194', plain,
% 0.51/0.74      ((~ (v1_xboole_0 @ (sk_C @ sk_B @ sk_A)) | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('clc', [status(thm)], ['192', '193'])).
% 0.51/0.74  thf('195', plain,
% 0.51/0.74      ((((v4_pre_topc @ sk_B @ sk_A) | (v2_struct_0 @ sk_A)))
% 0.51/0.74         <= ((![X12 : $i, X13 : $i]:
% 0.51/0.74                ((v1_xboole_0 @ X12)
% 0.51/0.74                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v3_waybel_7 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (m1_subset_1 @ X12 @ 
% 0.51/0.74                      (k1_zfmisc_1 @ 
% 0.51/0.74                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.51/0.74                 | ~ (r2_waybel_7 @ sk_A @ X12 @ X13)
% 0.51/0.74                 | (r2_hidden @ X13 @ sk_B)
% 0.51/0.74                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.51/0.74                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.51/0.74      inference('clc', [status(thm)], ['186', '194'])).
% 0.51/0.74  thf('196', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('197', plain,
% 0.51/0.74      (((v4_pre_topc @ sk_B @ sk_A))
% 0.51/0.74         <= ((![X12 : $i, X13 : $i]:
% 0.51/0.74                ((v1_xboole_0 @ X12)
% 0.51/0.74                 | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (v3_waybel_7 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74                 | ~ (m1_subset_1 @ X12 @ 
% 0.51/0.74                      (k1_zfmisc_1 @ 
% 0.51/0.74                       (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.51/0.74                 | ~ (r2_waybel_7 @ sk_A @ X12 @ X13)
% 0.51/0.74                 | (r2_hidden @ X13 @ sk_B)
% 0.51/0.74                 | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.51/0.74                 | ~ (r2_hidden @ sk_B @ X12))))),
% 0.51/0.74      inference('clc', [status(thm)], ['195', '196'])).
% 0.51/0.74  thf('198', plain,
% 0.51/0.74      (((r2_hidden @ sk_B @ sk_C_1) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('199', plain,
% 0.51/0.74      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.51/0.74      inference('split', [status(esa)], ['198'])).
% 0.51/0.74  thf('200', plain,
% 0.51/0.74      (~
% 0.51/0.74       (![X12 : $i, X13 : $i]:
% 0.51/0.74          ((v1_xboole_0 @ X12)
% 0.51/0.74           | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74           | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74           | ~ (v3_waybel_7 @ X12 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74           | ~ (m1_subset_1 @ X12 @ 
% 0.51/0.74                (k1_zfmisc_1 @ 
% 0.51/0.74                 (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.51/0.74           | ~ (r2_waybel_7 @ sk_A @ X12 @ X13)
% 0.51/0.74           | (r2_hidden @ X13 @ sk_B)
% 0.51/0.74           | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ sk_A))
% 0.51/0.74           | ~ (r2_hidden @ sk_B @ X12))) | 
% 0.51/0.74       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('sup-', [status(thm)], ['197', '199'])).
% 0.51/0.74  thf('201', plain,
% 0.51/0.74      (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))
% 0.51/0.74        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('202', plain,
% 0.51/0.74      (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) | 
% 0.51/0.74       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('split', [status(esa)], ['201'])).
% 0.51/0.74  thf('203', plain,
% 0.51/0.74      (((r2_hidden @ sk_B @ sk_C_1)) | ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('split', [status(esa)], ['198'])).
% 0.51/0.74  thf('204', plain,
% 0.51/0.74      ((~ (r2_hidden @ sk_D_3 @ sk_B) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('205', plain,
% 0.51/0.74      (~ ((r2_hidden @ sk_D_3 @ sk_B)) | ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('split', [status(esa)], ['204'])).
% 0.51/0.74  thf('206', plain,
% 0.51/0.74      (((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('207', plain,
% 0.51/0.74      (((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) | 
% 0.51/0.74       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('split', [status(esa)], ['206'])).
% 0.51/0.74  thf('208', plain,
% 0.51/0.74      (((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74         (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.51/0.74        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('209', plain,
% 0.51/0.74      (((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74         (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) | 
% 0.51/0.74       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('split', [status(esa)], ['208'])).
% 0.51/0.74  thf('210', plain,
% 0.51/0.74      (((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('211', plain,
% 0.51/0.74      (((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) | 
% 0.51/0.74       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('split', [status(esa)], ['210'])).
% 0.51/0.74  thf('212', plain,
% 0.51/0.74      (((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('213', plain,
% 0.51/0.74      (((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) | 
% 0.51/0.74       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('split', [status(esa)], ['212'])).
% 0.51/0.74  thf('214', plain,
% 0.51/0.74      (((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('215', plain,
% 0.51/0.74      (((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) | 
% 0.51/0.74       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('split', [status(esa)], ['214'])).
% 0.51/0.74  thf('216', plain,
% 0.51/0.74      ((~ (v1_xboole_0 @ sk_C_1) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('217', plain,
% 0.51/0.74      (~ ((v1_xboole_0 @ sk_C_1)) | ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.74      inference('split', [status(esa)], ['216'])).
% 0.51/0.74  thf('218', plain,
% 0.51/0.74      (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A)))
% 0.51/0.74         <= (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))))),
% 0.51/0.74      inference('split', [status(esa)], ['201'])).
% 0.51/0.74  thf('219', plain,
% 0.51/0.74      (((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3))
% 0.51/0.74         <= (((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)))),
% 0.51/0.74      inference('split', [status(esa)], ['206'])).
% 0.51/0.74  thf('220', plain,
% 0.51/0.74      (((r2_hidden @ sk_B @ sk_C_1)) <= (((r2_hidden @ sk_B @ sk_C_1)))),
% 0.51/0.74      inference('split', [status(esa)], ['198'])).
% 0.51/0.74  thf('221', plain,
% 0.51/0.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('222', plain,
% 0.51/0.74      (((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.51/0.74         <= (((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('split', [status(esa)], ['212'])).
% 0.51/0.74  thf('223', plain,
% 0.51/0.74      (((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.51/0.74         <= (((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('split', [status(esa)], ['210'])).
% 0.51/0.74  thf('224', plain,
% 0.51/0.74      (((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.51/0.74         <= (((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('split', [status(esa)], ['214'])).
% 0.51/0.74  thf('225', plain,
% 0.51/0.74      (((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74         (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))))
% 0.51/0.74         <= (((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))))),
% 0.51/0.74      inference('split', [status(esa)], ['208'])).
% 0.51/0.74  thf('226', plain,
% 0.51/0.74      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.51/0.74         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.51/0.74          | ~ (r2_waybel_7 @ X5 @ X7 @ X6)
% 0.51/0.74          | ~ (r2_hidden @ X4 @ X7)
% 0.51/0.74          | ~ (m1_subset_1 @ X7 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X5)))))
% 0.51/0.74          | ~ (v3_waybel_7 @ X7 @ (k3_yellow_1 @ (k2_struct_0 @ X5)))
% 0.51/0.74          | ~ (v13_waybel_0 @ X7 @ (k3_yellow_1 @ (k2_struct_0 @ X5)))
% 0.51/0.74          | ~ (v2_waybel_0 @ X7 @ (k3_yellow_1 @ (k2_struct_0 @ X5)))
% 0.51/0.74          | (v1_xboole_0 @ X7)
% 0.51/0.74          | (r2_hidden @ X6 @ (k2_pre_topc @ X5 @ X4))
% 0.51/0.74          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.51/0.74          | ~ (l1_pre_topc @ X5)
% 0.51/0.74          | ~ (v2_pre_topc @ X5)
% 0.51/0.74          | (v2_struct_0 @ X5))),
% 0.51/0.74      inference('cnf', [status(esa)], [t28_yellow19])).
% 0.51/0.74  thf('227', plain,
% 0.51/0.74      ((![X0 : $i, X1 : $i]:
% 0.51/0.74          ((v2_struct_0 @ sk_A)
% 0.51/0.74           | ~ (v2_pre_topc @ sk_A)
% 0.51/0.74           | ~ (l1_pre_topc @ sk_A)
% 0.51/0.74           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74           | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ X1))
% 0.51/0.74           | (v1_xboole_0 @ sk_C_1)
% 0.51/0.74           | ~ (v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74           | ~ (v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74           | ~ (v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74           | ~ (r2_hidden @ X1 @ sk_C_1)
% 0.51/0.74           | ~ (r2_waybel_7 @ sk_A @ sk_C_1 @ X0)
% 0.51/0.74           | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.51/0.74         <= (((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['225', '226'])).
% 0.51/0.74  thf('228', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('229', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('230', plain,
% 0.51/0.74      ((![X0 : $i, X1 : $i]:
% 0.51/0.74          ((v2_struct_0 @ sk_A)
% 0.51/0.74           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74           | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ X1))
% 0.51/0.74           | (v1_xboole_0 @ sk_C_1)
% 0.51/0.74           | ~ (v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74           | ~ (v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74           | ~ (v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74           | ~ (r2_hidden @ X1 @ sk_C_1)
% 0.51/0.74           | ~ (r2_waybel_7 @ sk_A @ sk_C_1 @ X0)
% 0.51/0.74           | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.51/0.74         <= (((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))))),
% 0.51/0.74      inference('demod', [status(thm)], ['227', '228', '229'])).
% 0.51/0.74  thf('231', plain,
% 0.51/0.74      ((![X0 : $i, X1 : $i]:
% 0.51/0.74          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.74           | ~ (r2_waybel_7 @ sk_A @ sk_C_1 @ X1)
% 0.51/0.74           | ~ (r2_hidden @ X0 @ sk_C_1)
% 0.51/0.74           | ~ (v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74           | ~ (v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74           | (v1_xboole_0 @ sk_C_1)
% 0.51/0.74           | (r2_hidden @ X1 @ (k2_pre_topc @ sk_A @ X0))
% 0.51/0.74           | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.51/0.74           | (v2_struct_0 @ sk_A)))
% 0.51/0.74         <= (((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['224', '230'])).
% 0.51/0.74  thf('232', plain,
% 0.51/0.74      ((![X0 : $i, X1 : $i]:
% 0.51/0.74          ((v2_struct_0 @ sk_A)
% 0.51/0.74           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74           | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ X1))
% 0.51/0.74           | (v1_xboole_0 @ sk_C_1)
% 0.51/0.74           | ~ (v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74           | ~ (r2_hidden @ X1 @ sk_C_1)
% 0.51/0.74           | ~ (r2_waybel_7 @ sk_A @ sk_C_1 @ X0)
% 0.51/0.74           | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.51/0.74         <= (((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['223', '231'])).
% 0.51/0.74  thf('233', plain,
% 0.51/0.74      ((![X0 : $i, X1 : $i]:
% 0.51/0.74          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.74           | ~ (r2_waybel_7 @ sk_A @ sk_C_1 @ X1)
% 0.51/0.74           | ~ (r2_hidden @ X0 @ sk_C_1)
% 0.51/0.74           | (v1_xboole_0 @ sk_C_1)
% 0.51/0.74           | (r2_hidden @ X1 @ (k2_pre_topc @ sk_A @ X0))
% 0.51/0.74           | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.51/0.74           | (v2_struct_0 @ sk_A)))
% 0.51/0.74         <= (((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['222', '232'])).
% 0.51/0.74  thf('234', plain,
% 0.51/0.74      ((![X0 : $i]:
% 0.51/0.74          ((v2_struct_0 @ sk_A)
% 0.51/0.74           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74           | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.51/0.74           | (v1_xboole_0 @ sk_C_1)
% 0.51/0.74           | ~ (r2_hidden @ sk_B @ sk_C_1)
% 0.51/0.74           | ~ (r2_waybel_7 @ sk_A @ sk_C_1 @ X0)))
% 0.51/0.74         <= (((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['221', '233'])).
% 0.51/0.74  thf('235', plain,
% 0.51/0.74      ((![X0 : $i]:
% 0.51/0.74          (~ (r2_waybel_7 @ sk_A @ sk_C_1 @ X0)
% 0.51/0.74           | (v1_xboole_0 @ sk_C_1)
% 0.51/0.74           | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.51/0.74           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74           | (v2_struct_0 @ sk_A)))
% 0.51/0.74         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['220', '234'])).
% 0.51/0.74  thf('236', plain,
% 0.51/0.74      ((((v2_struct_0 @ sk_A)
% 0.51/0.74         | ~ (m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))
% 0.51/0.74         | (r2_hidden @ sk_D_3 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.51/0.74         | (v1_xboole_0 @ sk_C_1)))
% 0.51/0.74         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['219', '235'])).
% 0.51/0.74  thf('237', plain,
% 0.51/0.74      ((((v1_xboole_0 @ sk_C_1)
% 0.51/0.74         | (r2_hidden @ sk_D_3 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.51/0.74         | (v2_struct_0 @ sk_A)))
% 0.51/0.74         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['218', '236'])).
% 0.51/0.74  thf('238', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('239', plain,
% 0.51/0.74      ((((r2_hidden @ sk_D_3 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.51/0.74         | (v1_xboole_0 @ sk_C_1)))
% 0.51/0.74         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('clc', [status(thm)], ['237', '238'])).
% 0.51/0.74  thf('240', plain,
% 0.51/0.74      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.51/0.74      inference('split', [status(esa)], ['0'])).
% 0.51/0.74  thf('241', plain,
% 0.51/0.74      ((((r2_hidden @ sk_D_3 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.51/0.74         | (v1_xboole_0 @ sk_C_1)))
% 0.51/0.74         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('clc', [status(thm)], ['237', '238'])).
% 0.51/0.74  thf('242', plain,
% 0.51/0.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('243', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.74         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.51/0.74          | ~ (r2_hidden @ X2 @ (k2_pre_topc @ X1 @ X0))
% 0.51/0.74          | (r2_hidden @ X0 @ (sk_D @ X2 @ X0 @ X1))
% 0.51/0.74          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.51/0.74          | ~ (l1_pre_topc @ X1)
% 0.51/0.74          | ~ (v2_pre_topc @ X1)
% 0.51/0.74          | (v2_struct_0 @ X1))),
% 0.51/0.74      inference('cnf', [status(esa)], [t27_yellow19])).
% 0.51/0.74  thf('244', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((v2_struct_0 @ sk_A)
% 0.51/0.74          | ~ (v2_pre_topc @ sk_A)
% 0.51/0.74          | ~ (l1_pre_topc @ sk_A)
% 0.51/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74          | (r2_hidden @ sk_B @ (sk_D @ X0 @ sk_B @ sk_A))
% 0.51/0.74          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['242', '243'])).
% 0.51/0.74  thf('245', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('246', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('247', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((v2_struct_0 @ sk_A)
% 0.51/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74          | (r2_hidden @ sk_B @ (sk_D @ X0 @ sk_B @ sk_A))
% 0.51/0.74          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.51/0.74      inference('demod', [status(thm)], ['244', '245', '246'])).
% 0.51/0.74  thf('248', plain,
% 0.51/0.74      ((((v1_xboole_0 @ sk_C_1)
% 0.51/0.74         | (r2_hidden @ sk_B @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.51/0.74         | ~ (m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))
% 0.51/0.74         | (v2_struct_0 @ sk_A)))
% 0.51/0.74         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['241', '247'])).
% 0.51/0.74  thf('249', plain,
% 0.51/0.74      (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A)))
% 0.51/0.74         <= (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))))),
% 0.51/0.74      inference('split', [status(esa)], ['201'])).
% 0.51/0.74  thf('250', plain,
% 0.51/0.74      ((((v1_xboole_0 @ sk_C_1)
% 0.51/0.74         | (r2_hidden @ sk_B @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.51/0.74         | (v2_struct_0 @ sk_A)))
% 0.51/0.74         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('demod', [status(thm)], ['248', '249'])).
% 0.51/0.74  thf('251', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('252', plain,
% 0.51/0.74      ((((r2_hidden @ sk_B @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.51/0.74         | (v1_xboole_0 @ sk_C_1)))
% 0.51/0.74         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('clc', [status(thm)], ['250', '251'])).
% 0.51/0.74  thf('253', plain,
% 0.51/0.74      ((((r2_hidden @ sk_D_3 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.51/0.74         | (v1_xboole_0 @ sk_C_1)))
% 0.51/0.74         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('clc', [status(thm)], ['237', '238'])).
% 0.51/0.74  thf('254', plain,
% 0.51/0.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('255', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.74         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.51/0.74          | ~ (r2_hidden @ X2 @ (k2_pre_topc @ X1 @ X0))
% 0.51/0.74          | (r1_waybel_7 @ X1 @ (sk_D @ X2 @ X0 @ X1) @ X2)
% 0.51/0.74          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.51/0.74          | ~ (l1_pre_topc @ X1)
% 0.51/0.74          | ~ (v2_pre_topc @ X1)
% 0.51/0.74          | (v2_struct_0 @ X1))),
% 0.51/0.74      inference('cnf', [status(esa)], [t27_yellow19])).
% 0.51/0.74  thf('256', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((v2_struct_0 @ sk_A)
% 0.51/0.74          | ~ (v2_pre_topc @ sk_A)
% 0.51/0.74          | ~ (l1_pre_topc @ sk_A)
% 0.51/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74          | (r1_waybel_7 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ X0)
% 0.51/0.74          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['254', '255'])).
% 0.51/0.74  thf('257', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('258', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('259', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((v2_struct_0 @ sk_A)
% 0.51/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74          | (r1_waybel_7 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ X0)
% 0.51/0.74          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.51/0.74      inference('demod', [status(thm)], ['256', '257', '258'])).
% 0.51/0.74  thf('260', plain,
% 0.51/0.74      ((((v1_xboole_0 @ sk_C_1)
% 0.51/0.74         | (r1_waybel_7 @ sk_A @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ sk_D_3)
% 0.51/0.74         | ~ (m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))
% 0.51/0.74         | (v2_struct_0 @ sk_A)))
% 0.51/0.74         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['253', '259'])).
% 0.51/0.74  thf('261', plain,
% 0.51/0.74      (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A)))
% 0.51/0.74         <= (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))))),
% 0.51/0.74      inference('split', [status(esa)], ['201'])).
% 0.51/0.74  thf('262', plain,
% 0.51/0.74      ((((v1_xboole_0 @ sk_C_1)
% 0.51/0.74         | (r1_waybel_7 @ sk_A @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ sk_D_3)
% 0.51/0.74         | (v2_struct_0 @ sk_A)))
% 0.51/0.74         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('demod', [status(thm)], ['260', '261'])).
% 0.51/0.74  thf('263', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('264', plain,
% 0.51/0.74      ((((r1_waybel_7 @ sk_A @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ sk_D_3)
% 0.51/0.74         | (v1_xboole_0 @ sk_C_1)))
% 0.51/0.74         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('clc', [status(thm)], ['262', '263'])).
% 0.51/0.74  thf('265', plain,
% 0.51/0.74      ((((r2_hidden @ sk_D_3 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.51/0.74         | (v1_xboole_0 @ sk_C_1)))
% 0.51/0.74         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('clc', [status(thm)], ['237', '238'])).
% 0.51/0.74  thf('266', plain,
% 0.51/0.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('267', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.74         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.51/0.74          | ~ (r2_hidden @ X2 @ (k2_pre_topc @ X1 @ X0))
% 0.51/0.74          | (v13_waybel_0 @ (sk_D @ X2 @ X0 @ X1) @ 
% 0.51/0.74             (k3_yellow_1 @ (k2_struct_0 @ X1)))
% 0.51/0.74          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.51/0.74          | ~ (l1_pre_topc @ X1)
% 0.51/0.74          | ~ (v2_pre_topc @ X1)
% 0.51/0.74          | (v2_struct_0 @ X1))),
% 0.51/0.74      inference('cnf', [status(esa)], [t27_yellow19])).
% 0.51/0.74  thf('268', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((v2_struct_0 @ sk_A)
% 0.51/0.74          | ~ (v2_pre_topc @ sk_A)
% 0.51/0.74          | ~ (l1_pre_topc @ sk_A)
% 0.51/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74          | (v13_waybel_0 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.51/0.74             (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['266', '267'])).
% 0.51/0.74  thf('269', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('270', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('271', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((v2_struct_0 @ sk_A)
% 0.51/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74          | (v13_waybel_0 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.51/0.74             (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.51/0.74      inference('demod', [status(thm)], ['268', '269', '270'])).
% 0.51/0.74  thf('272', plain,
% 0.51/0.74      ((((v1_xboole_0 @ sk_C_1)
% 0.51/0.74         | (v13_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ 
% 0.51/0.74            (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74         | ~ (m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))
% 0.51/0.74         | (v2_struct_0 @ sk_A)))
% 0.51/0.74         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['265', '271'])).
% 0.51/0.74  thf('273', plain,
% 0.51/0.74      (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A)))
% 0.51/0.74         <= (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))))),
% 0.51/0.74      inference('split', [status(esa)], ['201'])).
% 0.51/0.74  thf('274', plain,
% 0.51/0.74      ((((v1_xboole_0 @ sk_C_1)
% 0.51/0.74         | (v13_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ 
% 0.51/0.74            (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74         | (v2_struct_0 @ sk_A)))
% 0.51/0.74         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('demod', [status(thm)], ['272', '273'])).
% 0.51/0.74  thf('275', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('276', plain,
% 0.51/0.74      ((((v13_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ 
% 0.51/0.74          (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74         | (v1_xboole_0 @ sk_C_1)))
% 0.51/0.74         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('clc', [status(thm)], ['274', '275'])).
% 0.51/0.74  thf('277', plain,
% 0.51/0.74      ((((r2_hidden @ sk_D_3 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.51/0.74         | (v1_xboole_0 @ sk_C_1)))
% 0.51/0.74         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('clc', [status(thm)], ['237', '238'])).
% 0.51/0.74  thf('278', plain,
% 0.51/0.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('279', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.74         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.51/0.74          | ~ (r2_hidden @ X2 @ (k2_pre_topc @ X1 @ X0))
% 0.51/0.74          | (v2_waybel_0 @ (sk_D @ X2 @ X0 @ X1) @ 
% 0.51/0.74             (k3_yellow_1 @ (k2_struct_0 @ X1)))
% 0.51/0.74          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.51/0.74          | ~ (l1_pre_topc @ X1)
% 0.51/0.74          | ~ (v2_pre_topc @ X1)
% 0.51/0.74          | (v2_struct_0 @ X1))),
% 0.51/0.74      inference('cnf', [status(esa)], [t27_yellow19])).
% 0.51/0.74  thf('280', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((v2_struct_0 @ sk_A)
% 0.51/0.74          | ~ (v2_pre_topc @ sk_A)
% 0.51/0.74          | ~ (l1_pre_topc @ sk_A)
% 0.51/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74          | (v2_waybel_0 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.51/0.74             (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['278', '279'])).
% 0.51/0.74  thf('281', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('282', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('283', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((v2_struct_0 @ sk_A)
% 0.51/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74          | (v2_waybel_0 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.51/0.74             (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.51/0.74      inference('demod', [status(thm)], ['280', '281', '282'])).
% 0.51/0.74  thf('284', plain,
% 0.51/0.74      ((((v1_xboole_0 @ sk_C_1)
% 0.51/0.74         | (v2_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ 
% 0.51/0.74            (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74         | ~ (m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))
% 0.51/0.74         | (v2_struct_0 @ sk_A)))
% 0.51/0.74         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['277', '283'])).
% 0.51/0.74  thf('285', plain,
% 0.51/0.74      (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A)))
% 0.51/0.74         <= (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))))),
% 0.51/0.74      inference('split', [status(esa)], ['201'])).
% 0.51/0.74  thf('286', plain,
% 0.51/0.74      ((((v1_xboole_0 @ sk_C_1)
% 0.51/0.74         | (v2_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ 
% 0.51/0.74            (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74         | (v2_struct_0 @ sk_A)))
% 0.51/0.74         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('demod', [status(thm)], ['284', '285'])).
% 0.51/0.74  thf('287', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('288', plain,
% 0.51/0.74      ((((v2_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ 
% 0.51/0.74          (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74         | (v1_xboole_0 @ sk_C_1)))
% 0.51/0.74         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('clc', [status(thm)], ['286', '287'])).
% 0.51/0.74  thf('289', plain,
% 0.51/0.74      ((((r2_hidden @ sk_D_3 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.51/0.74         | (v1_xboole_0 @ sk_C_1)))
% 0.51/0.74         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('clc', [status(thm)], ['237', '238'])).
% 0.51/0.74  thf('290', plain,
% 0.51/0.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('291', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.74         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.51/0.74          | ~ (r2_hidden @ X2 @ (k2_pre_topc @ X1 @ X0))
% 0.51/0.74          | (v1_subset_1 @ (sk_D @ X2 @ X0 @ X1) @ 
% 0.51/0.74             (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X1))))
% 0.51/0.74          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.51/0.74          | ~ (l1_pre_topc @ X1)
% 0.51/0.74          | ~ (v2_pre_topc @ X1)
% 0.51/0.74          | (v2_struct_0 @ X1))),
% 0.51/0.74      inference('cnf', [status(esa)], [t27_yellow19])).
% 0.51/0.74  thf('292', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((v2_struct_0 @ sk_A)
% 0.51/0.74          | ~ (v2_pre_topc @ sk_A)
% 0.51/0.74          | ~ (l1_pre_topc @ sk_A)
% 0.51/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74          | (v1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.51/0.74             (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.51/0.74          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['290', '291'])).
% 0.51/0.74  thf('293', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('294', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('295', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((v2_struct_0 @ sk_A)
% 0.51/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74          | (v1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.51/0.74             (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.51/0.74          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.51/0.74      inference('demod', [status(thm)], ['292', '293', '294'])).
% 0.51/0.74  thf('296', plain,
% 0.51/0.74      ((((v1_xboole_0 @ sk_C_1)
% 0.51/0.74         | (v1_subset_1 @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ 
% 0.51/0.74            (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.51/0.74         | ~ (m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))
% 0.51/0.74         | (v2_struct_0 @ sk_A)))
% 0.51/0.74         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['289', '295'])).
% 0.51/0.74  thf('297', plain,
% 0.51/0.74      (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A)))
% 0.51/0.74         <= (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))))),
% 0.51/0.74      inference('split', [status(esa)], ['201'])).
% 0.51/0.74  thf('298', plain,
% 0.51/0.74      ((((v1_xboole_0 @ sk_C_1)
% 0.51/0.74         | (v1_subset_1 @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ 
% 0.51/0.74            (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.51/0.74         | (v2_struct_0 @ sk_A)))
% 0.51/0.74         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('demod', [status(thm)], ['296', '297'])).
% 0.51/0.74  thf('299', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('300', plain,
% 0.51/0.74      ((((v1_subset_1 @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ 
% 0.51/0.74          (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.51/0.74         | (v1_xboole_0 @ sk_C_1)))
% 0.51/0.74         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('clc', [status(thm)], ['298', '299'])).
% 0.51/0.74  thf('301', plain,
% 0.51/0.74      ((((r2_hidden @ sk_D_3 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.51/0.74         | (v1_xboole_0 @ sk_C_1)))
% 0.51/0.74         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('clc', [status(thm)], ['237', '238'])).
% 0.51/0.74  thf('302', plain,
% 0.51/0.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('303', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.74         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.51/0.74          | ~ (r2_hidden @ X2 @ (k2_pre_topc @ X1 @ X0))
% 0.51/0.74          | (m1_subset_1 @ (sk_D @ X2 @ X0 @ X1) @ 
% 0.51/0.74             (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X1)))))
% 0.51/0.74          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.51/0.74          | ~ (l1_pre_topc @ X1)
% 0.51/0.74          | ~ (v2_pre_topc @ X1)
% 0.51/0.74          | (v2_struct_0 @ X1))),
% 0.51/0.74      inference('cnf', [status(esa)], [t27_yellow19])).
% 0.51/0.74  thf('304', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((v2_struct_0 @ sk_A)
% 0.51/0.74          | ~ (v2_pre_topc @ sk_A)
% 0.51/0.74          | ~ (l1_pre_topc @ sk_A)
% 0.51/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.51/0.74             (k1_zfmisc_1 @ 
% 0.51/0.74              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.51/0.74          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['302', '303'])).
% 0.51/0.74  thf('305', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('306', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('307', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((v2_struct_0 @ sk_A)
% 0.51/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.51/0.74             (k1_zfmisc_1 @ 
% 0.51/0.74              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.51/0.74          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.51/0.74      inference('demod', [status(thm)], ['304', '305', '306'])).
% 0.51/0.74  thf('308', plain,
% 0.51/0.74      ((((v1_xboole_0 @ sk_C_1)
% 0.51/0.74         | (m1_subset_1 @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ 
% 0.51/0.74            (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.51/0.74         | ~ (m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))
% 0.51/0.74         | (v2_struct_0 @ sk_A)))
% 0.51/0.74         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['301', '307'])).
% 0.51/0.74  thf('309', plain,
% 0.51/0.74      (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A)))
% 0.51/0.74         <= (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))))),
% 0.51/0.74      inference('split', [status(esa)], ['201'])).
% 0.51/0.74  thf('310', plain,
% 0.51/0.74      ((((v1_xboole_0 @ sk_C_1)
% 0.51/0.74         | (m1_subset_1 @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ 
% 0.51/0.74            (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.51/0.74         | (v2_struct_0 @ sk_A)))
% 0.51/0.74         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('demod', [status(thm)], ['308', '309'])).
% 0.51/0.74  thf('311', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('312', plain,
% 0.51/0.74      ((((m1_subset_1 @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ 
% 0.51/0.74          (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))
% 0.51/0.74         | (v1_xboole_0 @ sk_C_1)))
% 0.51/0.74         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('clc', [status(thm)], ['310', '311'])).
% 0.51/0.74  thf('313', plain,
% 0.51/0.74      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.51/0.74         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.51/0.74          | ~ (v4_pre_topc @ X8 @ X9)
% 0.51/0.74          | ~ (r2_hidden @ X8 @ X10)
% 0.51/0.74          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X9))
% 0.51/0.74          | (r2_hidden @ X11 @ X8)
% 0.51/0.74          | ~ (r1_waybel_7 @ X9 @ X10 @ X11)
% 0.51/0.74          | ~ (m1_subset_1 @ X10 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X9)))))
% 0.51/0.74          | ~ (v13_waybel_0 @ X10 @ (k3_yellow_1 @ (k2_struct_0 @ X9)))
% 0.51/0.74          | ~ (v2_waybel_0 @ X10 @ (k3_yellow_1 @ (k2_struct_0 @ X9)))
% 0.51/0.74          | ~ (v1_subset_1 @ X10 @ 
% 0.51/0.74               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X9))))
% 0.51/0.74          | (v1_xboole_0 @ X10)
% 0.51/0.74          | ~ (l1_pre_topc @ X9)
% 0.51/0.74          | ~ (v2_pre_topc @ X9)
% 0.51/0.74          | (v2_struct_0 @ X9))),
% 0.51/0.74      inference('cnf', [status(esa)], [t29_yellow19])).
% 0.51/0.74  thf('314', plain,
% 0.51/0.74      ((![X0 : $i, X1 : $i]:
% 0.51/0.74          ((v1_xboole_0 @ sk_C_1)
% 0.51/0.74           | (v2_struct_0 @ sk_A)
% 0.51/0.74           | ~ (v2_pre_topc @ sk_A)
% 0.51/0.74           | ~ (l1_pre_topc @ sk_A)
% 0.51/0.74           | (v1_xboole_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.51/0.74           | ~ (v1_subset_1 @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.51/0.74           | ~ (v2_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ 
% 0.51/0.74                (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74           | ~ (v13_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ 
% 0.51/0.74                (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74           | ~ (r1_waybel_7 @ sk_A @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ X0)
% 0.51/0.74           | (r2_hidden @ X0 @ X1)
% 0.51/0.74           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74           | ~ (r2_hidden @ X1 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.51/0.74           | ~ (v4_pre_topc @ X1 @ sk_A)
% 0.51/0.74           | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.51/0.74         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['312', '313'])).
% 0.51/0.74  thf('315', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('316', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('317', plain,
% 0.51/0.74      ((![X0 : $i, X1 : $i]:
% 0.51/0.74          ((v1_xboole_0 @ sk_C_1)
% 0.51/0.74           | (v2_struct_0 @ sk_A)
% 0.51/0.74           | (v1_xboole_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.51/0.74           | ~ (v1_subset_1 @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.51/0.74           | ~ (v2_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ 
% 0.51/0.74                (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74           | ~ (v13_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ 
% 0.51/0.74                (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74           | ~ (r1_waybel_7 @ sk_A @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ X0)
% 0.51/0.74           | (r2_hidden @ X0 @ X1)
% 0.51/0.74           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74           | ~ (r2_hidden @ X1 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.51/0.74           | ~ (v4_pre_topc @ X1 @ sk_A)
% 0.51/0.74           | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.51/0.74         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('demod', [status(thm)], ['314', '315', '316'])).
% 0.51/0.74  thf('318', plain,
% 0.51/0.74      ((![X0 : $i, X1 : $i]:
% 0.51/0.74          ((v1_xboole_0 @ sk_C_1)
% 0.51/0.74           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.74           | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.51/0.74           | ~ (r2_hidden @ X0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.51/0.74           | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.51/0.74           | (r2_hidden @ X1 @ X0)
% 0.51/0.74           | ~ (r1_waybel_7 @ sk_A @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ X1)
% 0.51/0.74           | ~ (v13_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ 
% 0.51/0.74                (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74           | ~ (v2_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ 
% 0.51/0.74                (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74           | (v1_xboole_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.51/0.74           | (v2_struct_0 @ sk_A)
% 0.51/0.74           | (v1_xboole_0 @ sk_C_1)))
% 0.51/0.74         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['300', '317'])).
% 0.51/0.74  thf('319', plain,
% 0.51/0.74      ((![X0 : $i, X1 : $i]:
% 0.51/0.74          ((v2_struct_0 @ sk_A)
% 0.51/0.74           | (v1_xboole_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.51/0.74           | ~ (v2_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ 
% 0.51/0.74                (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74           | ~ (v13_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ 
% 0.51/0.74                (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74           | ~ (r1_waybel_7 @ sk_A @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ X1)
% 0.51/0.74           | (r2_hidden @ X1 @ X0)
% 0.51/0.74           | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.51/0.74           | ~ (r2_hidden @ X0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.51/0.74           | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.51/0.74           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.74           | (v1_xboole_0 @ sk_C_1)))
% 0.51/0.74         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('simplify', [status(thm)], ['318'])).
% 0.51/0.74  thf('320', plain,
% 0.51/0.74      ((![X0 : $i, X1 : $i]:
% 0.51/0.74          ((v1_xboole_0 @ sk_C_1)
% 0.51/0.74           | (v1_xboole_0 @ sk_C_1)
% 0.51/0.74           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.74           | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.51/0.74           | ~ (r2_hidden @ X0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.51/0.74           | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.51/0.74           | (r2_hidden @ X1 @ X0)
% 0.51/0.74           | ~ (r1_waybel_7 @ sk_A @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ X1)
% 0.51/0.74           | ~ (v13_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ 
% 0.51/0.74                (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74           | (v1_xboole_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.51/0.74           | (v2_struct_0 @ sk_A)))
% 0.51/0.74         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['288', '319'])).
% 0.51/0.74  thf('321', plain,
% 0.51/0.74      ((![X0 : $i, X1 : $i]:
% 0.51/0.74          ((v2_struct_0 @ sk_A)
% 0.51/0.74           | (v1_xboole_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.51/0.74           | ~ (v13_waybel_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ 
% 0.51/0.74                (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.51/0.74           | ~ (r1_waybel_7 @ sk_A @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ X1)
% 0.51/0.74           | (r2_hidden @ X1 @ X0)
% 0.51/0.74           | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.51/0.74           | ~ (r2_hidden @ X0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.51/0.74           | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.51/0.74           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.74           | (v1_xboole_0 @ sk_C_1)))
% 0.51/0.74         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('simplify', [status(thm)], ['320'])).
% 0.51/0.74  thf('322', plain,
% 0.51/0.74      ((![X0 : $i, X1 : $i]:
% 0.51/0.74          ((v1_xboole_0 @ sk_C_1)
% 0.51/0.74           | (v1_xboole_0 @ sk_C_1)
% 0.51/0.74           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.74           | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.51/0.74           | ~ (r2_hidden @ X0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.51/0.74           | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.51/0.74           | (r2_hidden @ X1 @ X0)
% 0.51/0.74           | ~ (r1_waybel_7 @ sk_A @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ X1)
% 0.51/0.74           | (v1_xboole_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.51/0.74           | (v2_struct_0 @ sk_A)))
% 0.51/0.74         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['276', '321'])).
% 0.51/0.74  thf('323', plain,
% 0.51/0.74      ((![X0 : $i, X1 : $i]:
% 0.51/0.74          ((v2_struct_0 @ sk_A)
% 0.51/0.74           | (v1_xboole_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.51/0.74           | ~ (r1_waybel_7 @ sk_A @ (sk_D @ sk_D_3 @ sk_B @ sk_A) @ X1)
% 0.51/0.74           | (r2_hidden @ X1 @ X0)
% 0.51/0.74           | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.51/0.74           | ~ (r2_hidden @ X0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.51/0.74           | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.51/0.74           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.74           | (v1_xboole_0 @ sk_C_1)))
% 0.51/0.74         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('simplify', [status(thm)], ['322'])).
% 0.51/0.74  thf('324', plain,
% 0.51/0.74      ((![X0 : $i]:
% 0.51/0.74          ((v1_xboole_0 @ sk_C_1)
% 0.51/0.74           | (v1_xboole_0 @ sk_C_1)
% 0.51/0.74           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.74           | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.51/0.74           | ~ (r2_hidden @ X0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.51/0.74           | ~ (m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))
% 0.51/0.74           | (r2_hidden @ sk_D_3 @ X0)
% 0.51/0.74           | (v1_xboole_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.51/0.74           | (v2_struct_0 @ sk_A)))
% 0.51/0.74         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['264', '323'])).
% 0.51/0.74  thf('325', plain,
% 0.51/0.74      (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A)))
% 0.51/0.74         <= (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))))),
% 0.51/0.74      inference('split', [status(esa)], ['201'])).
% 0.51/0.74  thf('326', plain,
% 0.51/0.74      ((![X0 : $i]:
% 0.51/0.74          ((v1_xboole_0 @ sk_C_1)
% 0.51/0.74           | (v1_xboole_0 @ sk_C_1)
% 0.51/0.74           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.74           | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.51/0.74           | ~ (r2_hidden @ X0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.51/0.74           | (r2_hidden @ sk_D_3 @ X0)
% 0.51/0.74           | (v1_xboole_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.51/0.74           | (v2_struct_0 @ sk_A)))
% 0.51/0.74         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('demod', [status(thm)], ['324', '325'])).
% 0.51/0.74  thf('327', plain,
% 0.51/0.74      ((![X0 : $i]:
% 0.51/0.74          ((v2_struct_0 @ sk_A)
% 0.51/0.74           | (v1_xboole_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.51/0.74           | (r2_hidden @ sk_D_3 @ X0)
% 0.51/0.74           | ~ (r2_hidden @ X0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.51/0.74           | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.51/0.74           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.74           | (v1_xboole_0 @ sk_C_1)))
% 0.51/0.74         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('simplify', [status(thm)], ['326'])).
% 0.51/0.74  thf('328', plain,
% 0.51/0.74      ((((v1_xboole_0 @ sk_C_1)
% 0.51/0.74         | (v1_xboole_0 @ sk_C_1)
% 0.51/0.74         | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.74         | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74         | (r2_hidden @ sk_D_3 @ sk_B)
% 0.51/0.74         | (v1_xboole_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.51/0.74         | (v2_struct_0 @ sk_A)))
% 0.51/0.74         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['252', '327'])).
% 0.51/0.74  thf('329', plain,
% 0.51/0.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('330', plain,
% 0.51/0.74      ((((v1_xboole_0 @ sk_C_1)
% 0.51/0.74         | (v1_xboole_0 @ sk_C_1)
% 0.51/0.74         | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74         | (r2_hidden @ sk_D_3 @ sk_B)
% 0.51/0.74         | (v1_xboole_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.51/0.74         | (v2_struct_0 @ sk_A)))
% 0.51/0.74         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('demod', [status(thm)], ['328', '329'])).
% 0.51/0.74  thf('331', plain,
% 0.51/0.74      ((((v2_struct_0 @ sk_A)
% 0.51/0.74         | (v1_xboole_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.51/0.74         | (r2_hidden @ sk_D_3 @ sk_B)
% 0.51/0.74         | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.51/0.74         | (v1_xboole_0 @ sk_C_1)))
% 0.51/0.74         <= (((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('simplify', [status(thm)], ['330'])).
% 0.51/0.74  thf('332', plain,
% 0.51/0.74      ((((v1_xboole_0 @ sk_C_1)
% 0.51/0.74         | (r2_hidden @ sk_D_3 @ sk_B)
% 0.51/0.74         | (v1_xboole_0 @ (sk_D @ sk_D_3 @ sk_B @ sk_A))
% 0.51/0.74         | (v2_struct_0 @ sk_A)))
% 0.51/0.74         <= (((v4_pre_topc @ sk_B @ sk_A)) & 
% 0.51/0.74             ((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['240', '331'])).
% 0.51/0.74  thf('333', plain,
% 0.51/0.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('334', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.74         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.51/0.74          | ~ (r2_hidden @ X2 @ (k2_pre_topc @ X1 @ X0))
% 0.51/0.74          | ~ (v1_xboole_0 @ (sk_D @ X2 @ X0 @ X1))
% 0.51/0.74          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.51/0.74          | ~ (l1_pre_topc @ X1)
% 0.51/0.74          | ~ (v2_pre_topc @ X1)
% 0.51/0.74          | (v2_struct_0 @ X1))),
% 0.51/0.74      inference('cnf', [status(esa)], [t27_yellow19])).
% 0.51/0.74  thf('335', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((v2_struct_0 @ sk_A)
% 0.51/0.74          | ~ (v2_pre_topc @ sk_A)
% 0.51/0.74          | ~ (l1_pre_topc @ sk_A)
% 0.51/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74          | ~ (v1_xboole_0 @ (sk_D @ X0 @ sk_B @ sk_A))
% 0.51/0.74          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['333', '334'])).
% 0.51/0.74  thf('336', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('337', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('338', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((v2_struct_0 @ sk_A)
% 0.51/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.74          | ~ (v1_xboole_0 @ (sk_D @ X0 @ sk_B @ sk_A))
% 0.51/0.74          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.51/0.74      inference('demod', [status(thm)], ['335', '336', '337'])).
% 0.51/0.74  thf('339', plain,
% 0.51/0.74      ((((v2_struct_0 @ sk_A)
% 0.51/0.74         | (r2_hidden @ sk_D_3 @ sk_B)
% 0.51/0.74         | (v1_xboole_0 @ sk_C_1)
% 0.51/0.74         | ~ (r2_hidden @ sk_D_3 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.51/0.74         | ~ (m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))
% 0.51/0.74         | (v2_struct_0 @ sk_A)))
% 0.51/0.74         <= (((v4_pre_topc @ sk_B @ sk_A)) & 
% 0.51/0.74             ((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['332', '338'])).
% 0.51/0.74  thf('340', plain,
% 0.51/0.74      (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A)))
% 0.51/0.74         <= (((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))))),
% 0.51/0.74      inference('split', [status(esa)], ['201'])).
% 0.51/0.74  thf('341', plain,
% 0.51/0.74      ((((v2_struct_0 @ sk_A)
% 0.51/0.74         | (r2_hidden @ sk_D_3 @ sk_B)
% 0.51/0.74         | (v1_xboole_0 @ sk_C_1)
% 0.51/0.74         | ~ (r2_hidden @ sk_D_3 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.51/0.74         | (v2_struct_0 @ sk_A)))
% 0.51/0.74         <= (((v4_pre_topc @ sk_B @ sk_A)) & 
% 0.51/0.74             ((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('demod', [status(thm)], ['339', '340'])).
% 0.51/0.74  thf('342', plain,
% 0.51/0.74      (((~ (r2_hidden @ sk_D_3 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.51/0.74         | (v1_xboole_0 @ sk_C_1)
% 0.51/0.74         | (r2_hidden @ sk_D_3 @ sk_B)
% 0.51/0.74         | (v2_struct_0 @ sk_A)))
% 0.51/0.74         <= (((v4_pre_topc @ sk_B @ sk_A)) & 
% 0.51/0.74             ((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('simplify', [status(thm)], ['341'])).
% 0.51/0.74  thf('343', plain,
% 0.51/0.74      ((((v1_xboole_0 @ sk_C_1)
% 0.51/0.74         | (v2_struct_0 @ sk_A)
% 0.51/0.74         | (r2_hidden @ sk_D_3 @ sk_B)
% 0.51/0.74         | (v1_xboole_0 @ sk_C_1)))
% 0.51/0.74         <= (((v4_pre_topc @ sk_B @ sk_A)) & 
% 0.51/0.74             ((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['239', '342'])).
% 0.51/0.74  thf('344', plain,
% 0.51/0.74      ((((r2_hidden @ sk_D_3 @ sk_B)
% 0.51/0.74         | (v2_struct_0 @ sk_A)
% 0.51/0.74         | (v1_xboole_0 @ sk_C_1)))
% 0.51/0.74         <= (((v4_pre_topc @ sk_B @ sk_A)) & 
% 0.51/0.74             ((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('simplify', [status(thm)], ['343'])).
% 0.51/0.74  thf('345', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('346', plain,
% 0.51/0.74      ((((v1_xboole_0 @ sk_C_1) | (r2_hidden @ sk_D_3 @ sk_B)))
% 0.51/0.74         <= (((v4_pre_topc @ sk_B @ sk_A)) & 
% 0.51/0.74             ((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('clc', [status(thm)], ['344', '345'])).
% 0.51/0.74  thf('347', plain,
% 0.51/0.74      ((~ (r2_hidden @ sk_D_3 @ sk_B)) <= (~ ((r2_hidden @ sk_D_3 @ sk_B)))),
% 0.51/0.74      inference('split', [status(esa)], ['204'])).
% 0.51/0.74  thf('348', plain,
% 0.51/0.74      (((v1_xboole_0 @ sk_C_1))
% 0.51/0.74         <= (~ ((r2_hidden @ sk_D_3 @ sk_B)) & 
% 0.51/0.74             ((v4_pre_topc @ sk_B @ sk_A)) & 
% 0.51/0.74             ((r2_hidden @ sk_B @ sk_C_1)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.74             ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) & 
% 0.51/0.74             ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74               (k1_zfmisc_1 @ 
% 0.51/0.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) & 
% 0.51/0.74             ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) & 
% 0.51/0.74             ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['346', '347'])).
% 0.51/0.74  thf('349', plain,
% 0.51/0.74      ((~ (v1_xboole_0 @ sk_C_1)) <= (~ ((v1_xboole_0 @ sk_C_1)))),
% 0.51/0.74      inference('split', [status(esa)], ['216'])).
% 0.51/0.74  thf('350', plain,
% 0.51/0.74      (~ ((v13_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) | 
% 0.51/0.74       ~ ((v2_waybel_0 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) | 
% 0.51/0.74       ~ ((v3_waybel_7 @ sk_C_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))) | 
% 0.51/0.74       ~
% 0.51/0.74       ((m1_subset_1 @ sk_C_1 @ 
% 0.51/0.74         (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))) | 
% 0.51/0.74       ~ ((r2_waybel_7 @ sk_A @ sk_C_1 @ sk_D_3)) | 
% 0.51/0.74       ~ ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))) | 
% 0.51/0.74       ~ ((r2_hidden @ sk_B @ sk_C_1)) | ~ ((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.51/0.74       ((r2_hidden @ sk_D_3 @ sk_B)) | ((v1_xboole_0 @ sk_C_1))),
% 0.51/0.74      inference('sup-', [status(thm)], ['348', '349'])).
% 0.51/0.74  thf('351', plain, ($false),
% 0.51/0.74      inference('sat_resolution*', [status(thm)],
% 0.51/0.74                ['1', '200', '202', '203', '205', '207', '209', '211', '213', 
% 0.51/0.74                 '215', '217', '350'])).
% 0.51/0.74  
% 0.51/0.74  % SZS output end Refutation
% 0.51/0.74  
% 0.51/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
