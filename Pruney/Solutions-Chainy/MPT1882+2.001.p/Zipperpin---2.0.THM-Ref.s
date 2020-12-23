%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gPHOuqsfZU

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 370 expanded)
%              Number of leaves         :   24 ( 111 expanded)
%              Depth                    :   21
%              Number of atoms          :  995 (4773 expanded)
%              Number of equality atoms :    8 (  14 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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
    ! [X0: $i] :
      ( ( v1_zfmisc_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
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

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('71',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('72',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( sk_C @ sk_B @ sk_A ) ) ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('73',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X10 = X9 )
      | ( v1_subset_1 @ X10 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('74',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( v1_subset_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
      | ( sk_B
        = ( sk_C @ sk_B @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('76',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v2_tex_2 @ X11 @ X12 )
      | ( X11
       != ( sk_C @ X11 @ X12 ) )
      | ( v3_tex_2 @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('78',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B @ sk_A )
    | ( sk_B
     != ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( sk_B
     != ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( sk_B
       != ( sk_C @ sk_B @ sk_A ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['75','80'])).

thf('82',plain,
    ( ( ( v1_subset_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['74','81'])).

thf('83',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( sk_C @ sk_B @ sk_A ) ) ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf(cc1_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( ( v1_subset_1 @ B @ A )
           => ( v1_xboole_0 @ B ) ) ) ) )).

thf('84',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_xboole_0 @ X6 )
      | ~ ( v1_subset_1 @ X6 @ X7 )
      | ~ ( v1_zfmisc_1 @ X7 )
      | ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_tex_2])).

thf('85',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_zfmisc_1 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_subset_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_zfmisc_1 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,
    ( ( ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_zfmisc_1 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( v3_tex_2 @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['63','87'])).

thf('89',plain,
    ( ( ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( sk_C @ sk_B @ sk_A ) ) ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('91',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('92',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ~ ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( ~ ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['89','94'])).

thf('96',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('99',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B )
    | ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','23','24','99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gPHOuqsfZU
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:03:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 76 iterations in 0.038s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.50  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.21/0.50  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.21/0.50  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.50  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.21/0.50  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.21/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.50  thf(t50_tex_2, conjecture,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.21/0.50         ( l1_pre_topc @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.50             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.50           ( ( v3_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]:
% 0.21/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.50            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.50          ( ![B:$i]:
% 0.21/0.50            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.50                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.50              ( ( v3_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t50_tex_2])).
% 0.21/0.50  thf('0', plain, ((~ (v1_zfmisc_1 @ sk_B) | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain, (~ ((v1_zfmisc_1 @ sk_B)) | ~ ((v3_tex_2 @ sk_B @ sk_A))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('2', plain, (((v1_zfmisc_1 @ sk_B) | (v3_tex_2 @ sk_B @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('3', plain, (((v3_tex_2 @ sk_B @ sk_A)) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.50      inference('split', [status(esa)], ['2'])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(d7_tex_2, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_pre_topc @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50           ( ( v3_tex_2 @ B @ A ) <=>
% 0.21/0.50             ( ( v2_tex_2 @ B @ A ) & 
% 0.21/0.50               ( ![C:$i]:
% 0.21/0.50                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.50                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.50          | ~ (v3_tex_2 @ X11 @ X12)
% 0.21/0.50          | (v2_tex_2 @ X11 @ X12)
% 0.21/0.50          | ~ (l1_pre_topc @ X12))),
% 0.21/0.50      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.50        | (v2_tex_2 @ sk_B @ sk_A)
% 0.21/0.50        | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.50  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('8', plain, (((v2_tex_2 @ sk_B @ sk_A) | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.50  thf('9', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['3', '8'])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t44_tex_2, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.21/0.50         ( l1_pre_topc @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.50             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.50           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X16 : $i, X17 : $i]:
% 0.21/0.50         ((v1_xboole_0 @ X16)
% 0.21/0.50          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.50          | ~ (v2_tex_2 @ X16 @ X17)
% 0.21/0.50          | (v1_zfmisc_1 @ X16)
% 0.21/0.50          | ~ (l1_pre_topc @ X17)
% 0.21/0.50          | ~ (v2_tdlat_3 @ X17)
% 0.21/0.50          | ~ (v2_pre_topc @ X17)
% 0.21/0.50          | (v2_struct_0 @ X17))),
% 0.21/0.50      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_A)
% 0.21/0.50        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.50        | ~ (v2_tdlat_3 @ sk_A)
% 0.21/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.50        | (v1_zfmisc_1 @ sk_B)
% 0.21/0.50        | ~ (v2_tex_2 @ sk_B @ sk_A)
% 0.21/0.50        | (v1_xboole_0 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('14', plain, ((v2_tdlat_3 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_A)
% 0.21/0.50        | (v1_zfmisc_1 @ sk_B)
% 0.21/0.50        | ~ (v2_tex_2 @ sk_B @ sk_A)
% 0.21/0.50        | (v1_xboole_0 @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      ((((v1_xboole_0 @ sk_B) | (v1_zfmisc_1 @ sk_B) | (v2_struct_0 @ sk_A)))
% 0.21/0.50         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['9', '16'])).
% 0.21/0.50  thf('18', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      ((((v2_struct_0 @ sk_A) | (v1_zfmisc_1 @ sk_B)))
% 0.21/0.50         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.50      inference('clc', [status(thm)], ['17', '18'])).
% 0.21/0.50  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('21', plain, (((v1_zfmisc_1 @ sk_B)) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.50      inference('clc', [status(thm)], ['19', '20'])).
% 0.21/0.50  thf('22', plain, ((~ (v1_zfmisc_1 @ sk_B)) <= (~ ((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('23', plain, (((v1_zfmisc_1 @ sk_B)) | ~ ((v3_tex_2 @ sk_B @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.50  thf('24', plain, (((v1_zfmisc_1 @ sk_B)) | ((v3_tex_2 @ sk_B @ sk_A))),
% 0.21/0.50      inference('split', [status(esa)], ['2'])).
% 0.21/0.50  thf('25', plain, (((v1_zfmisc_1 @ sk_B)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('split', [status(esa)], ['2'])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      (![X16 : $i, X17 : $i]:
% 0.21/0.50         ((v1_xboole_0 @ X16)
% 0.21/0.50          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.50          | ~ (v1_zfmisc_1 @ X16)
% 0.21/0.50          | (v2_tex_2 @ X16 @ X17)
% 0.21/0.50          | ~ (l1_pre_topc @ X17)
% 0.21/0.50          | ~ (v2_tdlat_3 @ X17)
% 0.21/0.50          | ~ (v2_pre_topc @ X17)
% 0.21/0.50          | (v2_struct_0 @ X17))),
% 0.21/0.50      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_A)
% 0.21/0.50        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.50        | ~ (v2_tdlat_3 @ sk_A)
% 0.21/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.50        | (v2_tex_2 @ sk_B @ sk_A)
% 0.21/0.50        | ~ (v1_zfmisc_1 @ sk_B)
% 0.21/0.50        | (v1_xboole_0 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.50  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('30', plain, ((v2_tdlat_3 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_A)
% 0.21/0.50        | (v2_tex_2 @ sk_B @ sk_A)
% 0.21/0.50        | ~ (v1_zfmisc_1 @ sk_B)
% 0.21/0.50        | (v1_xboole_0 @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      ((((v1_xboole_0 @ sk_B) | (v2_tex_2 @ sk_B @ sk_A) | (v2_struct_0 @ sk_A)))
% 0.21/0.50         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['25', '32'])).
% 0.21/0.50  thf('34', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      ((((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B @ sk_A)))
% 0.21/0.50         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('clc', [status(thm)], ['33', '34'])).
% 0.21/0.50  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('37', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('clc', [status(thm)], ['35', '36'])).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('39', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.50          | ~ (v2_tex_2 @ X11 @ X12)
% 0.21/0.50          | (v2_tex_2 @ (sk_C @ X11 @ X12) @ X12)
% 0.21/0.50          | (v3_tex_2 @ X11 @ X12)
% 0.21/0.50          | ~ (l1_pre_topc @ X12))),
% 0.21/0.50      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.21/0.50  thf('40', plain,
% 0.21/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.50        | (v3_tex_2 @ sk_B @ sk_A)
% 0.21/0.50        | (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.21/0.50        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.50  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('42', plain,
% 0.21/0.50      (((v3_tex_2 @ sk_B @ sk_A)
% 0.21/0.50        | (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.21/0.50        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.50  thf('43', plain,
% 0.21/0.50      ((((v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A) | (v3_tex_2 @ sk_B @ sk_A)))
% 0.21/0.50         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['37', '42'])).
% 0.21/0.50  thf('44', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('clc', [status(thm)], ['35', '36'])).
% 0.21/0.50  thf('45', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('46', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.50          | ~ (v2_tex_2 @ X11 @ X12)
% 0.21/0.50          | (m1_subset_1 @ (sk_C @ X11 @ X12) @ 
% 0.21/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.50          | (v3_tex_2 @ X11 @ X12)
% 0.21/0.50          | ~ (l1_pre_topc @ X12))),
% 0.21/0.50      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.21/0.50  thf('47', plain,
% 0.21/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.50        | (v3_tex_2 @ sk_B @ sk_A)
% 0.21/0.50        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.21/0.50           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.50  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('49', plain,
% 0.21/0.50      (((v3_tex_2 @ sk_B @ sk_A)
% 0.21/0.50        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.21/0.50           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['47', '48'])).
% 0.21/0.50  thf('50', plain,
% 0.21/0.50      ((((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.21/0.50          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['44', '49'])).
% 0.21/0.50  thf('51', plain,
% 0.21/0.50      (![X16 : $i, X17 : $i]:
% 0.21/0.50         ((v1_xboole_0 @ X16)
% 0.21/0.50          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.50          | ~ (v2_tex_2 @ X16 @ X17)
% 0.21/0.50          | (v1_zfmisc_1 @ X16)
% 0.21/0.50          | ~ (l1_pre_topc @ X17)
% 0.21/0.50          | ~ (v2_tdlat_3 @ X17)
% 0.21/0.50          | ~ (v2_pre_topc @ X17)
% 0.21/0.50          | (v2_struct_0 @ X17))),
% 0.21/0.50      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.21/0.50  thf('52', plain,
% 0.21/0.50      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.21/0.50         | (v2_struct_0 @ sk_A)
% 0.21/0.50         | ~ (v2_pre_topc @ sk_A)
% 0.21/0.50         | ~ (v2_tdlat_3 @ sk_A)
% 0.21/0.50         | ~ (l1_pre_topc @ sk_A)
% 0.21/0.50         | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.50         | ~ (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.21/0.50         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.50  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('54', plain, ((v2_tdlat_3 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('56', plain,
% 0.21/0.50      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.21/0.50         | (v2_struct_0 @ sk_A)
% 0.21/0.50         | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.50         | ~ (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.21/0.50         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 0.21/0.50  thf('57', plain,
% 0.21/0.50      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.21/0.50         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.50         | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.50         | (v2_struct_0 @ sk_A)
% 0.21/0.50         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['43', '56'])).
% 0.21/0.50  thf('58', plain,
% 0.21/0.50      ((((v2_struct_0 @ sk_A)
% 0.21/0.50         | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.50         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.50         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['57'])).
% 0.21/0.50  thf(cc1_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_zfmisc_1 @ A ) ))).
% 0.21/0.50  thf('59', plain, (![X0 : $i]: ((v1_zfmisc_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc1_zfmisc_1])).
% 0.21/0.50  thf('60', plain,
% 0.21/0.50      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.21/0.50         | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.50         | (v2_struct_0 @ sk_A)
% 0.21/0.50         | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['58', '59'])).
% 0.21/0.50  thf('61', plain,
% 0.21/0.50      ((((v2_struct_0 @ sk_A)
% 0.21/0.50         | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.50         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['60'])).
% 0.21/0.50  thf('62', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('63', plain,
% 0.21/0.50      ((((v3_tex_2 @ sk_B @ sk_A) | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))))
% 0.21/0.50         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('clc', [status(thm)], ['61', '62'])).
% 0.21/0.50  thf('64', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('clc', [status(thm)], ['35', '36'])).
% 0.21/0.50  thf('65', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('66', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.50          | ~ (v2_tex_2 @ X11 @ X12)
% 0.21/0.50          | (r1_tarski @ X11 @ (sk_C @ X11 @ X12))
% 0.21/0.50          | (v3_tex_2 @ X11 @ X12)
% 0.21/0.50          | ~ (l1_pre_topc @ X12))),
% 0.21/0.50      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.21/0.50  thf('67', plain,
% 0.21/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.50        | (v3_tex_2 @ sk_B @ sk_A)
% 0.21/0.50        | (r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.21/0.50        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['65', '66'])).
% 0.21/0.50  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('69', plain,
% 0.21/0.50      (((v3_tex_2 @ sk_B @ sk_A)
% 0.21/0.50        | (r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.21/0.50        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['67', '68'])).
% 0.21/0.50  thf('70', plain,
% 0.21/0.50      ((((r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A)) | (v3_tex_2 @ sk_B @ sk_A)))
% 0.21/0.50         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['64', '69'])).
% 0.21/0.50  thf(t3_subset, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.50  thf('71', plain,
% 0.21/0.50      (![X3 : $i, X5 : $i]:
% 0.21/0.50         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.21/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.50  thf('72', plain,
% 0.21/0.50      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.21/0.50         | (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (sk_C @ sk_B @ sk_A)))))
% 0.21/0.50         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['70', '71'])).
% 0.21/0.50  thf(d7_subset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.50       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.21/0.50  thf('73', plain,
% 0.21/0.50      (![X9 : $i, X10 : $i]:
% 0.21/0.50         (((X10) = (X9))
% 0.21/0.50          | (v1_subset_1 @ X10 @ X9)
% 0.21/0.50          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.21/0.50      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.21/0.50  thf('74', plain,
% 0.21/0.50      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.21/0.50         | (v1_subset_1 @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.21/0.50         | ((sk_B) = (sk_C @ sk_B @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['72', '73'])).
% 0.21/0.50  thf('75', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('clc', [status(thm)], ['35', '36'])).
% 0.21/0.50  thf('76', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('77', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.50          | ~ (v2_tex_2 @ X11 @ X12)
% 0.21/0.50          | ((X11) != (sk_C @ X11 @ X12))
% 0.21/0.50          | (v3_tex_2 @ X11 @ X12)
% 0.21/0.50          | ~ (l1_pre_topc @ X12))),
% 0.21/0.50      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.21/0.50  thf('78', plain,
% 0.21/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.50        | (v3_tex_2 @ sk_B @ sk_A)
% 0.21/0.50        | ((sk_B) != (sk_C @ sk_B @ sk_A))
% 0.21/0.50        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['76', '77'])).
% 0.21/0.50  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('80', plain,
% 0.21/0.50      (((v3_tex_2 @ sk_B @ sk_A)
% 0.21/0.50        | ((sk_B) != (sk_C @ sk_B @ sk_A))
% 0.21/0.50        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['78', '79'])).
% 0.21/0.50  thf('81', plain,
% 0.21/0.50      (((((sk_B) != (sk_C @ sk_B @ sk_A)) | (v3_tex_2 @ sk_B @ sk_A)))
% 0.21/0.50         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['75', '80'])).
% 0.21/0.50  thf('82', plain,
% 0.21/0.50      ((((v1_subset_1 @ sk_B @ (sk_C @ sk_B @ sk_A)) | (v3_tex_2 @ sk_B @ sk_A)))
% 0.21/0.50         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('clc', [status(thm)], ['74', '81'])).
% 0.21/0.50  thf('83', plain,
% 0.21/0.50      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.21/0.50         | (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (sk_C @ sk_B @ sk_A)))))
% 0.21/0.50         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['70', '71'])).
% 0.21/0.50  thf(cc1_tex_2, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.50           ( ( v1_subset_1 @ B @ A ) => ( v1_xboole_0 @ B ) ) ) ) ))).
% 0.21/0.50  thf('84', plain,
% 0.21/0.50      (![X6 : $i, X7 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.21/0.50          | (v1_xboole_0 @ X6)
% 0.21/0.50          | ~ (v1_subset_1 @ X6 @ X7)
% 0.21/0.50          | ~ (v1_zfmisc_1 @ X7)
% 0.21/0.50          | (v1_xboole_0 @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc1_tex_2])).
% 0.21/0.50  thf('85', plain,
% 0.21/0.50      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.21/0.50         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.50         | ~ (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.50         | ~ (v1_subset_1 @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.21/0.50         | (v1_xboole_0 @ sk_B))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['83', '84'])).
% 0.21/0.50  thf('86', plain,
% 0.21/0.50      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.21/0.50         | (v1_xboole_0 @ sk_B)
% 0.21/0.50         | ~ (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.50         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.50         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['82', '85'])).
% 0.21/0.50  thf('87', plain,
% 0.21/0.50      ((((v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.50         | ~ (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.50         | (v1_xboole_0 @ sk_B)
% 0.21/0.50         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['86'])).
% 0.21/0.50  thf('88', plain,
% 0.21/0.50      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.21/0.50         | (v3_tex_2 @ sk_B @ sk_A)
% 0.21/0.50         | (v1_xboole_0 @ sk_B)
% 0.21/0.50         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['63', '87'])).
% 0.21/0.50  thf('89', plain,
% 0.21/0.50      ((((v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.50         | (v1_xboole_0 @ sk_B)
% 0.21/0.50         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['88'])).
% 0.21/0.50  thf('90', plain,
% 0.21/0.50      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.21/0.50         | (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (sk_C @ sk_B @ sk_A)))))
% 0.21/0.50         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['70', '71'])).
% 0.21/0.50  thf(cc1_subset_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v1_xboole_0 @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.21/0.50  thf('91', plain,
% 0.21/0.50      (![X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.21/0.50          | (v1_xboole_0 @ X1)
% 0.21/0.50          | ~ (v1_xboole_0 @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.21/0.50  thf('92', plain,
% 0.21/0.50      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.21/0.50         | ~ (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.50         | (v1_xboole_0 @ sk_B))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['90', '91'])).
% 0.21/0.50  thf('93', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('94', plain,
% 0.21/0.50      (((~ (v1_xboole_0 @ (sk_C @ sk_B @ sk_A)) | (v3_tex_2 @ sk_B @ sk_A)))
% 0.21/0.50         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('clc', [status(thm)], ['92', '93'])).
% 0.21/0.50  thf('95', plain,
% 0.21/0.50      ((((v3_tex_2 @ sk_B @ sk_A) | (v1_xboole_0 @ sk_B)))
% 0.21/0.50         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('clc', [status(thm)], ['89', '94'])).
% 0.21/0.50  thf('96', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('97', plain, (((v3_tex_2 @ sk_B @ sk_A)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('clc', [status(thm)], ['95', '96'])).
% 0.21/0.50  thf('98', plain,
% 0.21/0.50      ((~ (v3_tex_2 @ sk_B @ sk_A)) <= (~ ((v3_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('99', plain, (~ ((v1_zfmisc_1 @ sk_B)) | ((v3_tex_2 @ sk_B @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['97', '98'])).
% 0.21/0.50  thf('100', plain, ($false),
% 0.21/0.50      inference('sat_resolution*', [status(thm)], ['1', '23', '24', '99'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
