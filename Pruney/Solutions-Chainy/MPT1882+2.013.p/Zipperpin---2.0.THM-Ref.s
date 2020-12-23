%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1B300GgxHP

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:21 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 378 expanded)
%              Number of leaves         :   26 ( 113 expanded)
%              Depth                    :   27
%              Number of atoms          : 1063 (4852 expanded)
%              Number of equality atoms :   30 (  40 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t50_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v2_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v3_tex_2 @ B @ A )
          <=> ( v1_zfmisc_1 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v2_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( ( v3_tex_2 @ B @ A )
            <=> ( v1_zfmisc_1 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_tex_2])).

thf('0',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B )
    | ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B )
    | ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v1_zfmisc_1 @ sk_B )
    | ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tex_2 @ B @ A )
          <=> ( ( v2_tex_2 @ B @ A )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( v2_tex_2 @ C @ A )
                      & ( r1_tarski @ B @ C ) )
                   => ( B = C ) ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v3_tex_2 @ X11 @ X12 )
      | ( v2_tex_2 @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A )
    | ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v2_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v2_tex_2 @ B @ A )
          <=> ( v1_zfmisc_1 @ B ) ) ) ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v2_tex_2 @ X16 @ X17 )
      | ( v1_zfmisc_1 @ X16 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_tdlat_3 @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t44_tex_2])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v2_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_zfmisc_1 @ sk_B )
    | ~ ( v2_tex_2 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_zfmisc_1 @ sk_B )
    | ~ ( v2_tex_2 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['12','13','14','15'])).

thf('17',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v1_zfmisc_1 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_zfmisc_1 @ sk_B ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v1_zfmisc_1 @ sk_B )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B )
   <= ~ ( v1_zfmisc_1 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('23',plain,
    ( ( v1_zfmisc_1 @ sk_B )
    | ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( v1_zfmisc_1 @ sk_B )
    | ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('25',plain,
    ( ( v1_zfmisc_1 @ sk_B )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v1_zfmisc_1 @ X16 )
      | ( v2_tex_2 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_tdlat_3 @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t44_tex_2])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v2_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf('33',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_tex_2 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['25','32'])).

thf('34',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v2_tex_2 @ X11 @ X12 )
      | ( v2_tex_2 @ ( sk_C @ X11 @ X12 ) @ X12 )
      | ( v3_tex_2 @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('40',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B @ sk_A )
    | ( v2_tex_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( v2_tex_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( v2_tex_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v2_tex_2 @ X11 @ X12 )
      | ( m1_subset_1 @ ( sk_C @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v3_tex_2 @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('47',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v2_tex_2 @ X16 @ X17 )
      | ( v1_zfmisc_1 @ X16 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_tdlat_3 @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t44_tex_2])).

thf('52',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v2_tdlat_3 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( v2_tex_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( v2_tex_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['52','53','54','55'])).

thf('57',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v1_zfmisc_1 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['43','56'])).

thf('58',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['57'])).

thf(cc1_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_zfmisc_1 @ A ) ) )).

thf('59',plain,(
    ! [X9: $i] :
      ( ( v1_zfmisc_1 @ X9 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_zfmisc_1])).

thf('60',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C @ sk_B @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C @ sk_B @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('65',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v2_tex_2 @ X11 @ X12 )
      | ( r1_tarski @ X11 @ ( sk_C @ X11 @ X12 ) )
      | ( v3_tex_2 @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('67',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['64','69'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('71',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ~ ( v1_zfmisc_1 @ X14 )
      | ( X15 = X14 )
      | ~ ( r1_tarski @ X15 @ X14 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('72',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( sk_B
        = ( sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_zfmisc_1 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( sk_B
        = ( sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['63','72'])).

thf('74',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( sk_B
        = ( sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['73'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('75',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('76',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( sk_B
        = ( sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( ( sk_C @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('78',plain,
    ( ( ( ( sk_C @ sk_B @ sk_A )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_B )
      | ( sk_B
        = ( sk_C @ sk_B @ sk_A ) ) )
   <= ( ~ ( v3_tex_2 @ sk_B @ sk_A )
      & ( v1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( ( sk_B
        = ( sk_C @ sk_B @ sk_A ) )
      | ( ( sk_C @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ( ~ ( v3_tex_2 @ sk_B @ sk_A )
      & ( v1_zfmisc_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('82',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v2_tex_2 @ X11 @ X12 )
      | ( X11
       != ( sk_C @ X11 @ X12 ) )
      | ( v3_tex_2 @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('84',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B @ sk_A )
    | ( sk_B
     != ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( sk_B
     != ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( sk_B
       != ( sk_C @ sk_B @ sk_A ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['81','86'])).

thf('88',plain,
    ( ( ( sk_B != sk_B )
      | ( ( sk_C @ sk_B @ sk_A )
        = k1_xboole_0 )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( ~ ( v3_tex_2 @ sk_B @ sk_A )
      & ( v1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['80','87'])).

thf('89',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( ( sk_C @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ( ~ ( v3_tex_2 @ sk_B @ sk_A )
      & ( v1_zfmisc_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('91',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ~ ( v3_tex_2 @ sk_B @ sk_A )
      & ( v1_zfmisc_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( ( r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['64','69'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('93',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('94',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ~ ( r1_tarski @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_C @ sk_B @ sk_A )
        = sk_B ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( ( sk_B
       != ( sk_C @ sk_B @ sk_A ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['81','86'])).

thf('96',plain,
    ( ( ~ ( r1_tarski @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_B )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( ~ ( v3_tex_2 @ sk_B @ sk_A )
      & ( v1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['91','96'])).

thf('98',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('99',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['98'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('100',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('102',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
   <= ( ~ ( v3_tex_2 @ sk_B @ sk_A )
      & ( v1_zfmisc_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['97','103'])).

thf('105',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('106',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B )
    | ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','23','24','106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1B300GgxHP
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:22:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.61/0.83  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.61/0.83  % Solved by: fo/fo7.sh
% 0.61/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.83  % done 1107 iterations in 0.374s
% 0.61/0.83  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.61/0.83  % SZS output start Refutation
% 0.61/0.83  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.61/0.83  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.61/0.83  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.61/0.83  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.61/0.83  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.61/0.83  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.61/0.83  thf(sk_B_type, type, sk_B: $i).
% 0.61/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.83  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.61/0.83  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.61/0.83  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.61/0.83  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.61/0.83  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.61/0.83  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.61/0.83  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.61/0.83  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.61/0.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.61/0.83  thf(t50_tex_2, conjecture,
% 0.61/0.83    (![A:$i]:
% 0.61/0.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.61/0.83         ( l1_pre_topc @ A ) ) =>
% 0.61/0.83       ( ![B:$i]:
% 0.61/0.83         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.61/0.83             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.61/0.83           ( ( v3_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.61/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.83    (~( ![A:$i]:
% 0.61/0.83        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.61/0.83            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.61/0.83          ( ![B:$i]:
% 0.61/0.83            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.61/0.83                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.61/0.83              ( ( v3_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.61/0.83    inference('cnf.neg', [status(esa)], [t50_tex_2])).
% 0.61/0.83  thf('0', plain, ((~ (v1_zfmisc_1 @ sk_B) | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('1', plain, (~ ((v1_zfmisc_1 @ sk_B)) | ~ ((v3_tex_2 @ sk_B @ sk_A))),
% 0.61/0.83      inference('split', [status(esa)], ['0'])).
% 0.61/0.83  thf('2', plain, (((v1_zfmisc_1 @ sk_B) | (v3_tex_2 @ sk_B @ sk_A))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('3', plain, (((v3_tex_2 @ sk_B @ sk_A)) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.61/0.83      inference('split', [status(esa)], ['2'])).
% 0.61/0.83  thf('4', plain,
% 0.61/0.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf(d7_tex_2, axiom,
% 0.61/0.83    (![A:$i]:
% 0.61/0.83     ( ( l1_pre_topc @ A ) =>
% 0.61/0.83       ( ![B:$i]:
% 0.61/0.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.61/0.83           ( ( v3_tex_2 @ B @ A ) <=>
% 0.61/0.83             ( ( v2_tex_2 @ B @ A ) & 
% 0.61/0.83               ( ![C:$i]:
% 0.61/0.83                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.61/0.83                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.61/0.83                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.61/0.83  thf('5', plain,
% 0.61/0.83      (![X11 : $i, X12 : $i]:
% 0.61/0.83         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.61/0.83          | ~ (v3_tex_2 @ X11 @ X12)
% 0.61/0.83          | (v2_tex_2 @ X11 @ X12)
% 0.61/0.83          | ~ (l1_pre_topc @ X12))),
% 0.61/0.83      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.61/0.83  thf('6', plain,
% 0.61/0.83      ((~ (l1_pre_topc @ sk_A)
% 0.61/0.83        | (v2_tex_2 @ sk_B @ sk_A)
% 0.61/0.83        | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.61/0.83      inference('sup-', [status(thm)], ['4', '5'])).
% 0.61/0.83  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('8', plain, (((v2_tex_2 @ sk_B @ sk_A) | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.61/0.83      inference('demod', [status(thm)], ['6', '7'])).
% 0.61/0.83  thf('9', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['3', '8'])).
% 0.61/0.83  thf('10', plain,
% 0.61/0.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf(t44_tex_2, axiom,
% 0.61/0.83    (![A:$i]:
% 0.61/0.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.61/0.83         ( l1_pre_topc @ A ) ) =>
% 0.61/0.83       ( ![B:$i]:
% 0.61/0.83         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.61/0.83             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.61/0.83           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.61/0.83  thf('11', plain,
% 0.61/0.83      (![X16 : $i, X17 : $i]:
% 0.61/0.83         ((v1_xboole_0 @ X16)
% 0.61/0.83          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.61/0.83          | ~ (v2_tex_2 @ X16 @ X17)
% 0.61/0.83          | (v1_zfmisc_1 @ X16)
% 0.61/0.83          | ~ (l1_pre_topc @ X17)
% 0.61/0.83          | ~ (v2_tdlat_3 @ X17)
% 0.61/0.83          | ~ (v2_pre_topc @ X17)
% 0.61/0.83          | (v2_struct_0 @ X17))),
% 0.61/0.83      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.61/0.83  thf('12', plain,
% 0.61/0.83      (((v2_struct_0 @ sk_A)
% 0.61/0.83        | ~ (v2_pre_topc @ sk_A)
% 0.61/0.83        | ~ (v2_tdlat_3 @ sk_A)
% 0.61/0.83        | ~ (l1_pre_topc @ sk_A)
% 0.61/0.83        | (v1_zfmisc_1 @ sk_B)
% 0.61/0.83        | ~ (v2_tex_2 @ sk_B @ sk_A)
% 0.61/0.83        | (v1_xboole_0 @ sk_B))),
% 0.61/0.83      inference('sup-', [status(thm)], ['10', '11'])).
% 0.61/0.83  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('14', plain, ((v2_tdlat_3 @ sk_A)),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('16', plain,
% 0.61/0.83      (((v2_struct_0 @ sk_A)
% 0.61/0.83        | (v1_zfmisc_1 @ sk_B)
% 0.61/0.83        | ~ (v2_tex_2 @ sk_B @ sk_A)
% 0.61/0.83        | (v1_xboole_0 @ sk_B))),
% 0.61/0.83      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.61/0.83  thf('17', plain,
% 0.61/0.83      ((((v1_xboole_0 @ sk_B) | (v1_zfmisc_1 @ sk_B) | (v2_struct_0 @ sk_A)))
% 0.61/0.83         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['9', '16'])).
% 0.61/0.83  thf('18', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('19', plain,
% 0.61/0.83      ((((v2_struct_0 @ sk_A) | (v1_zfmisc_1 @ sk_B)))
% 0.61/0.83         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.61/0.83      inference('clc', [status(thm)], ['17', '18'])).
% 0.61/0.83  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('21', plain, (((v1_zfmisc_1 @ sk_B)) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.61/0.83      inference('clc', [status(thm)], ['19', '20'])).
% 0.61/0.83  thf('22', plain, ((~ (v1_zfmisc_1 @ sk_B)) <= (~ ((v1_zfmisc_1 @ sk_B)))),
% 0.61/0.83      inference('split', [status(esa)], ['0'])).
% 0.61/0.83  thf('23', plain, (((v1_zfmisc_1 @ sk_B)) | ~ ((v3_tex_2 @ sk_B @ sk_A))),
% 0.61/0.83      inference('sup-', [status(thm)], ['21', '22'])).
% 0.61/0.83  thf('24', plain, (((v1_zfmisc_1 @ sk_B)) | ((v3_tex_2 @ sk_B @ sk_A))),
% 0.61/0.83      inference('split', [status(esa)], ['2'])).
% 0.61/0.83  thf('25', plain, (((v1_zfmisc_1 @ sk_B)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.61/0.83      inference('split', [status(esa)], ['2'])).
% 0.61/0.83  thf('26', plain,
% 0.61/0.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('27', plain,
% 0.61/0.83      (![X16 : $i, X17 : $i]:
% 0.61/0.83         ((v1_xboole_0 @ X16)
% 0.61/0.83          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.61/0.83          | ~ (v1_zfmisc_1 @ X16)
% 0.61/0.83          | (v2_tex_2 @ X16 @ X17)
% 0.61/0.83          | ~ (l1_pre_topc @ X17)
% 0.61/0.83          | ~ (v2_tdlat_3 @ X17)
% 0.61/0.83          | ~ (v2_pre_topc @ X17)
% 0.61/0.83          | (v2_struct_0 @ X17))),
% 0.61/0.83      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.61/0.83  thf('28', plain,
% 0.61/0.83      (((v2_struct_0 @ sk_A)
% 0.61/0.83        | ~ (v2_pre_topc @ sk_A)
% 0.61/0.83        | ~ (v2_tdlat_3 @ sk_A)
% 0.61/0.83        | ~ (l1_pre_topc @ sk_A)
% 0.61/0.83        | (v2_tex_2 @ sk_B @ sk_A)
% 0.61/0.83        | ~ (v1_zfmisc_1 @ sk_B)
% 0.61/0.83        | (v1_xboole_0 @ sk_B))),
% 0.61/0.83      inference('sup-', [status(thm)], ['26', '27'])).
% 0.61/0.83  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('30', plain, ((v2_tdlat_3 @ sk_A)),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('32', plain,
% 0.61/0.83      (((v2_struct_0 @ sk_A)
% 0.61/0.83        | (v2_tex_2 @ sk_B @ sk_A)
% 0.61/0.83        | ~ (v1_zfmisc_1 @ sk_B)
% 0.61/0.83        | (v1_xboole_0 @ sk_B))),
% 0.61/0.83      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 0.61/0.83  thf('33', plain,
% 0.61/0.83      ((((v1_xboole_0 @ sk_B) | (v2_tex_2 @ sk_B @ sk_A) | (v2_struct_0 @ sk_A)))
% 0.61/0.83         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['25', '32'])).
% 0.61/0.83  thf('34', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('35', plain,
% 0.61/0.83      ((((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B @ sk_A)))
% 0.61/0.83         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.61/0.83      inference('clc', [status(thm)], ['33', '34'])).
% 0.61/0.83  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('37', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.61/0.83      inference('clc', [status(thm)], ['35', '36'])).
% 0.61/0.83  thf('38', plain,
% 0.61/0.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('39', plain,
% 0.61/0.83      (![X11 : $i, X12 : $i]:
% 0.61/0.83         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.61/0.83          | ~ (v2_tex_2 @ X11 @ X12)
% 0.61/0.83          | (v2_tex_2 @ (sk_C @ X11 @ X12) @ X12)
% 0.61/0.83          | (v3_tex_2 @ X11 @ X12)
% 0.61/0.83          | ~ (l1_pre_topc @ X12))),
% 0.61/0.83      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.61/0.83  thf('40', plain,
% 0.61/0.83      ((~ (l1_pre_topc @ sk_A)
% 0.61/0.83        | (v3_tex_2 @ sk_B @ sk_A)
% 0.61/0.83        | (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.61/0.83        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.61/0.83      inference('sup-', [status(thm)], ['38', '39'])).
% 0.61/0.83  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('42', plain,
% 0.61/0.83      (((v3_tex_2 @ sk_B @ sk_A)
% 0.61/0.83        | (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.61/0.83        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.61/0.83      inference('demod', [status(thm)], ['40', '41'])).
% 0.61/0.83  thf('43', plain,
% 0.61/0.83      ((((v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A) | (v3_tex_2 @ sk_B @ sk_A)))
% 0.61/0.83         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['37', '42'])).
% 0.61/0.83  thf('44', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.61/0.83      inference('clc', [status(thm)], ['35', '36'])).
% 0.61/0.83  thf('45', plain,
% 0.61/0.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('46', plain,
% 0.61/0.83      (![X11 : $i, X12 : $i]:
% 0.61/0.83         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.61/0.83          | ~ (v2_tex_2 @ X11 @ X12)
% 0.61/0.83          | (m1_subset_1 @ (sk_C @ X11 @ X12) @ 
% 0.61/0.83             (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.61/0.83          | (v3_tex_2 @ X11 @ X12)
% 0.61/0.83          | ~ (l1_pre_topc @ X12))),
% 0.61/0.83      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.61/0.83  thf('47', plain,
% 0.61/0.83      ((~ (l1_pre_topc @ sk_A)
% 0.61/0.83        | (v3_tex_2 @ sk_B @ sk_A)
% 0.61/0.83        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.61/0.83           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.83        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.61/0.83      inference('sup-', [status(thm)], ['45', '46'])).
% 0.61/0.83  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('49', plain,
% 0.61/0.83      (((v3_tex_2 @ sk_B @ sk_A)
% 0.61/0.83        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.61/0.83           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.83        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.61/0.83      inference('demod', [status(thm)], ['47', '48'])).
% 0.61/0.83  thf('50', plain,
% 0.61/0.83      ((((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.61/0.83          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.83         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['44', '49'])).
% 0.61/0.83  thf('51', plain,
% 0.61/0.83      (![X16 : $i, X17 : $i]:
% 0.61/0.83         ((v1_xboole_0 @ X16)
% 0.61/0.83          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.61/0.83          | ~ (v2_tex_2 @ X16 @ X17)
% 0.61/0.83          | (v1_zfmisc_1 @ X16)
% 0.61/0.83          | ~ (l1_pre_topc @ X17)
% 0.61/0.83          | ~ (v2_tdlat_3 @ X17)
% 0.61/0.83          | ~ (v2_pre_topc @ X17)
% 0.61/0.83          | (v2_struct_0 @ X17))),
% 0.61/0.83      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.61/0.83  thf('52', plain,
% 0.61/0.83      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.61/0.83         | (v2_struct_0 @ sk_A)
% 0.61/0.83         | ~ (v2_pre_topc @ sk_A)
% 0.61/0.83         | ~ (v2_tdlat_3 @ sk_A)
% 0.61/0.83         | ~ (l1_pre_topc @ sk_A)
% 0.61/0.83         | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.61/0.83         | ~ (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.61/0.83         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['50', '51'])).
% 0.61/0.83  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('54', plain, ((v2_tdlat_3 @ sk_A)),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('56', plain,
% 0.61/0.83      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.61/0.83         | (v2_struct_0 @ sk_A)
% 0.61/0.83         | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.61/0.83         | ~ (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.61/0.83         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.61/0.83      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 0.61/0.83  thf('57', plain,
% 0.61/0.83      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.61/0.83         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.61/0.83         | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.61/0.83         | (v2_struct_0 @ sk_A)
% 0.61/0.83         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['43', '56'])).
% 0.61/0.83  thf('58', plain,
% 0.61/0.83      ((((v2_struct_0 @ sk_A)
% 0.61/0.83         | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.61/0.83         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.61/0.83         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.61/0.83      inference('simplify', [status(thm)], ['57'])).
% 0.61/0.83  thf(cc1_zfmisc_1, axiom,
% 0.61/0.83    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_zfmisc_1 @ A ) ))).
% 0.61/0.83  thf('59', plain, (![X9 : $i]: ((v1_zfmisc_1 @ X9) | ~ (v1_xboole_0 @ X9))),
% 0.61/0.83      inference('cnf', [status(esa)], [cc1_zfmisc_1])).
% 0.61/0.83  thf('60', plain,
% 0.61/0.83      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.61/0.83         | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.61/0.83         | (v2_struct_0 @ sk_A)
% 0.61/0.83         | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['58', '59'])).
% 0.61/0.83  thf('61', plain,
% 0.61/0.83      ((((v2_struct_0 @ sk_A)
% 0.61/0.83         | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.61/0.83         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.61/0.83      inference('simplify', [status(thm)], ['60'])).
% 0.61/0.83  thf('62', plain, (~ (v2_struct_0 @ sk_A)),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('63', plain,
% 0.61/0.83      ((((v3_tex_2 @ sk_B @ sk_A) | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))))
% 0.61/0.83         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.61/0.83      inference('clc', [status(thm)], ['61', '62'])).
% 0.61/0.83  thf('64', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.61/0.83      inference('clc', [status(thm)], ['35', '36'])).
% 0.61/0.83  thf('65', plain,
% 0.61/0.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('66', plain,
% 0.61/0.83      (![X11 : $i, X12 : $i]:
% 0.61/0.83         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.61/0.83          | ~ (v2_tex_2 @ X11 @ X12)
% 0.61/0.83          | (r1_tarski @ X11 @ (sk_C @ X11 @ X12))
% 0.61/0.83          | (v3_tex_2 @ X11 @ X12)
% 0.61/0.83          | ~ (l1_pre_topc @ X12))),
% 0.61/0.83      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.61/0.83  thf('67', plain,
% 0.61/0.83      ((~ (l1_pre_topc @ sk_A)
% 0.61/0.83        | (v3_tex_2 @ sk_B @ sk_A)
% 0.61/0.83        | (r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.61/0.83        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.61/0.83      inference('sup-', [status(thm)], ['65', '66'])).
% 0.61/0.83  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('69', plain,
% 0.61/0.83      (((v3_tex_2 @ sk_B @ sk_A)
% 0.61/0.83        | (r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.61/0.83        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.61/0.83      inference('demod', [status(thm)], ['67', '68'])).
% 0.61/0.83  thf('70', plain,
% 0.61/0.83      ((((r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A)) | (v3_tex_2 @ sk_B @ sk_A)))
% 0.61/0.83         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['64', '69'])).
% 0.61/0.83  thf(t1_tex_2, axiom,
% 0.61/0.83    (![A:$i]:
% 0.61/0.83     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.61/0.83       ( ![B:$i]:
% 0.61/0.83         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.61/0.83           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.61/0.83  thf('71', plain,
% 0.61/0.83      (![X14 : $i, X15 : $i]:
% 0.61/0.83         ((v1_xboole_0 @ X14)
% 0.61/0.83          | ~ (v1_zfmisc_1 @ X14)
% 0.61/0.83          | ((X15) = (X14))
% 0.61/0.83          | ~ (r1_tarski @ X15 @ X14)
% 0.61/0.83          | (v1_xboole_0 @ X15))),
% 0.61/0.83      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.61/0.83  thf('72', plain,
% 0.61/0.83      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.61/0.83         | (v1_xboole_0 @ sk_B)
% 0.61/0.83         | ((sk_B) = (sk_C @ sk_B @ sk_A))
% 0.61/0.83         | ~ (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.61/0.83         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['70', '71'])).
% 0.61/0.83  thf('73', plain,
% 0.61/0.83      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.61/0.83         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.61/0.83         | ((sk_B) = (sk_C @ sk_B @ sk_A))
% 0.61/0.83         | (v1_xboole_0 @ sk_B)
% 0.61/0.83         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['63', '72'])).
% 0.61/0.83  thf('74', plain,
% 0.61/0.83      ((((v1_xboole_0 @ sk_B)
% 0.61/0.83         | ((sk_B) = (sk_C @ sk_B @ sk_A))
% 0.61/0.83         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.61/0.83         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.61/0.83      inference('simplify', [status(thm)], ['73'])).
% 0.61/0.83  thf(l13_xboole_0, axiom,
% 0.61/0.83    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.61/0.83  thf('75', plain,
% 0.61/0.83      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.61/0.83      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.61/0.83  thf('76', plain,
% 0.61/0.83      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.61/0.83         | ((sk_B) = (sk_C @ sk_B @ sk_A))
% 0.61/0.83         | (v1_xboole_0 @ sk_B)
% 0.61/0.83         | ((sk_C @ sk_B @ sk_A) = (k1_xboole_0)))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['74', '75'])).
% 0.61/0.83  thf('77', plain,
% 0.61/0.83      ((~ (v3_tex_2 @ sk_B @ sk_A)) <= (~ ((v3_tex_2 @ sk_B @ sk_A)))),
% 0.61/0.83      inference('split', [status(esa)], ['0'])).
% 0.61/0.83  thf('78', plain,
% 0.61/0.83      (((((sk_C @ sk_B @ sk_A) = (k1_xboole_0))
% 0.61/0.83         | (v1_xboole_0 @ sk_B)
% 0.61/0.83         | ((sk_B) = (sk_C @ sk_B @ sk_A))))
% 0.61/0.83         <= (~ ((v3_tex_2 @ sk_B @ sk_A)) & ((v1_zfmisc_1 @ sk_B)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['76', '77'])).
% 0.61/0.83  thf('79', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('80', plain,
% 0.61/0.83      (((((sk_B) = (sk_C @ sk_B @ sk_A))
% 0.61/0.83         | ((sk_C @ sk_B @ sk_A) = (k1_xboole_0))))
% 0.61/0.83         <= (~ ((v3_tex_2 @ sk_B @ sk_A)) & ((v1_zfmisc_1 @ sk_B)))),
% 0.61/0.83      inference('clc', [status(thm)], ['78', '79'])).
% 0.61/0.83  thf('81', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.61/0.83      inference('clc', [status(thm)], ['35', '36'])).
% 0.61/0.83  thf('82', plain,
% 0.61/0.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('83', plain,
% 0.61/0.83      (![X11 : $i, X12 : $i]:
% 0.61/0.83         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.61/0.83          | ~ (v2_tex_2 @ X11 @ X12)
% 0.61/0.83          | ((X11) != (sk_C @ X11 @ X12))
% 0.61/0.83          | (v3_tex_2 @ X11 @ X12)
% 0.61/0.83          | ~ (l1_pre_topc @ X12))),
% 0.61/0.83      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.61/0.83  thf('84', plain,
% 0.61/0.83      ((~ (l1_pre_topc @ sk_A)
% 0.61/0.83        | (v3_tex_2 @ sk_B @ sk_A)
% 0.61/0.83        | ((sk_B) != (sk_C @ sk_B @ sk_A))
% 0.61/0.83        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.61/0.83      inference('sup-', [status(thm)], ['82', '83'])).
% 0.61/0.83  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('86', plain,
% 0.61/0.83      (((v3_tex_2 @ sk_B @ sk_A)
% 0.61/0.83        | ((sk_B) != (sk_C @ sk_B @ sk_A))
% 0.61/0.83        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.61/0.83      inference('demod', [status(thm)], ['84', '85'])).
% 0.61/0.83  thf('87', plain,
% 0.61/0.83      (((((sk_B) != (sk_C @ sk_B @ sk_A)) | (v3_tex_2 @ sk_B @ sk_A)))
% 0.61/0.83         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['81', '86'])).
% 0.61/0.83  thf('88', plain,
% 0.61/0.83      (((((sk_B) != (sk_B))
% 0.61/0.83         | ((sk_C @ sk_B @ sk_A) = (k1_xboole_0))
% 0.61/0.83         | (v3_tex_2 @ sk_B @ sk_A)))
% 0.61/0.83         <= (~ ((v3_tex_2 @ sk_B @ sk_A)) & ((v1_zfmisc_1 @ sk_B)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['80', '87'])).
% 0.61/0.83  thf('89', plain,
% 0.61/0.83      ((((v3_tex_2 @ sk_B @ sk_A) | ((sk_C @ sk_B @ sk_A) = (k1_xboole_0))))
% 0.61/0.83         <= (~ ((v3_tex_2 @ sk_B @ sk_A)) & ((v1_zfmisc_1 @ sk_B)))),
% 0.61/0.83      inference('simplify', [status(thm)], ['88'])).
% 0.61/0.83  thf('90', plain,
% 0.61/0.83      ((~ (v3_tex_2 @ sk_B @ sk_A)) <= (~ ((v3_tex_2 @ sk_B @ sk_A)))),
% 0.61/0.83      inference('split', [status(esa)], ['0'])).
% 0.61/0.83  thf('91', plain,
% 0.61/0.83      ((((sk_C @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.61/0.83         <= (~ ((v3_tex_2 @ sk_B @ sk_A)) & ((v1_zfmisc_1 @ sk_B)))),
% 0.61/0.83      inference('clc', [status(thm)], ['89', '90'])).
% 0.61/0.83  thf('92', plain,
% 0.61/0.83      ((((r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A)) | (v3_tex_2 @ sk_B @ sk_A)))
% 0.61/0.83         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['64', '69'])).
% 0.61/0.83  thf(d10_xboole_0, axiom,
% 0.61/0.83    (![A:$i,B:$i]:
% 0.61/0.83     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.61/0.83  thf('93', plain,
% 0.61/0.83      (![X1 : $i, X3 : $i]:
% 0.61/0.83         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.61/0.83      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.61/0.83  thf('94', plain,
% 0.61/0.83      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.61/0.83         | ~ (r1_tarski @ (sk_C @ sk_B @ sk_A) @ sk_B)
% 0.61/0.83         | ((sk_C @ sk_B @ sk_A) = (sk_B)))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['92', '93'])).
% 0.61/0.83  thf('95', plain,
% 0.61/0.83      (((((sk_B) != (sk_C @ sk_B @ sk_A)) | (v3_tex_2 @ sk_B @ sk_A)))
% 0.61/0.83         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['81', '86'])).
% 0.61/0.83  thf('96', plain,
% 0.61/0.83      (((~ (r1_tarski @ (sk_C @ sk_B @ sk_A) @ sk_B) | (v3_tex_2 @ sk_B @ sk_A)))
% 0.61/0.83         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.61/0.83      inference('clc', [status(thm)], ['94', '95'])).
% 0.61/0.83  thf('97', plain,
% 0.61/0.83      (((~ (r1_tarski @ k1_xboole_0 @ sk_B) | (v3_tex_2 @ sk_B @ sk_A)))
% 0.61/0.83         <= (~ ((v3_tex_2 @ sk_B @ sk_A)) & ((v1_zfmisc_1 @ sk_B)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['91', '96'])).
% 0.61/0.83  thf('98', plain,
% 0.61/0.83      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.61/0.83      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.61/0.83  thf('99', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.61/0.83      inference('simplify', [status(thm)], ['98'])).
% 0.61/0.83  thf(l32_xboole_1, axiom,
% 0.61/0.83    (![A:$i,B:$i]:
% 0.61/0.83     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.61/0.83  thf('100', plain,
% 0.61/0.83      (![X4 : $i, X6 : $i]:
% 0.61/0.83         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.61/0.83      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.61/0.83  thf('101', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.61/0.83      inference('sup-', [status(thm)], ['99', '100'])).
% 0.61/0.83  thf(t36_xboole_1, axiom,
% 0.61/0.83    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.61/0.83  thf('102', plain,
% 0.61/0.83      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 0.61/0.83      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.61/0.83  thf('103', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.61/0.83      inference('sup+', [status(thm)], ['101', '102'])).
% 0.61/0.83  thf('104', plain,
% 0.61/0.83      (((v3_tex_2 @ sk_B @ sk_A))
% 0.61/0.83         <= (~ ((v3_tex_2 @ sk_B @ sk_A)) & ((v1_zfmisc_1 @ sk_B)))),
% 0.61/0.83      inference('demod', [status(thm)], ['97', '103'])).
% 0.61/0.83  thf('105', plain,
% 0.61/0.83      ((~ (v3_tex_2 @ sk_B @ sk_A)) <= (~ ((v3_tex_2 @ sk_B @ sk_A)))),
% 0.61/0.83      inference('split', [status(esa)], ['0'])).
% 0.61/0.83  thf('106', plain, (~ ((v1_zfmisc_1 @ sk_B)) | ((v3_tex_2 @ sk_B @ sk_A))),
% 0.61/0.83      inference('sup-', [status(thm)], ['104', '105'])).
% 0.61/0.83  thf('107', plain, ($false),
% 0.61/0.83      inference('sat_resolution*', [status(thm)], ['1', '23', '24', '106'])).
% 0.61/0.83  
% 0.61/0.83  % SZS output end Refutation
% 0.61/0.83  
% 0.61/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
