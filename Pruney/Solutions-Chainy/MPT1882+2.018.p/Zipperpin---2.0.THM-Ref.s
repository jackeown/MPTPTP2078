%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Vt0g3bbFYd

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 368 expanded)
%              Number of leaves         :   29 ( 113 expanded)
%              Depth                    :   23
%              Number of atoms          : 1014 (4704 expanded)
%              Number of equality atoms :   25 (  34 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

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
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v3_tex_2 @ X8 @ X9 )
      | ( v2_tex_2 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v2_tex_2 @ X15 @ X16 )
      | ( v1_zfmisc_1 @ X15 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_tdlat_3 @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t44_tex_2])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v2_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
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
    | ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['12','13','14','15'])).

thf('17',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_zfmisc_1 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_zfmisc_1 @ sk_B_1 ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
   <= ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('23',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('25',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('26',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v1_zfmisc_1 @ X15 )
      | ( v2_tex_2 @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_tdlat_3 @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t44_tex_2])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v2_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
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
    | ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf('33',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['25','32'])).

thf('34',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v2_tex_2 @ X8 @ X9 )
      | ( v2_tex_2 @ ( sk_C @ X8 @ X9 ) @ X9 )
      | ( v3_tex_2 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('40',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v2_tex_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v2_tex_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( v2_tex_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('45',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v2_tex_2 @ X8 @ X9 )
      | ( m1_subset_1 @ ( sk_C @ X8 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v3_tex_2 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('47',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v2_tex_2 @ X15 @ X16 )
      | ( v1_zfmisc_1 @ X15 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_tdlat_3 @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t44_tex_2])).

thf('52',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v2_tdlat_3 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( v2_tex_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
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
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( v2_tex_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['52','53','54','55'])).

thf('57',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v1_zfmisc_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['43','56'])).

thf('58',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
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
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('65',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v2_tex_2 @ X8 @ X9 )
      | ( r1_tarski @ X8 @ ( sk_C @ X8 @ X9 ) )
      | ( v3_tex_2 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('67',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( r1_tarski @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( r1_tarski @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( r1_tarski @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
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
    ! [X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X13 )
      | ~ ( v1_zfmisc_1 @ X13 )
      | ( X14 = X13 )
      | ~ ( r1_tarski @ X14 @ X13 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('72',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( sk_B_1
        = ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( v1_zfmisc_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( sk_B_1
        = ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['63','72'])).

thf('74',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( sk_B_1
        = ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ( ( r1_tarski @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['64','69'])).

thf(t1_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('76',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_mcart_1])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('77',plain,(
    ! [X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X1 @ X2 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('78',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_subset_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf(l48_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_tarski @ A @ B )
        & ( A != B )
        & ( ( k6_subset_1 @ B @ A )
          = k1_xboole_0 ) ) )).

thf('81',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ( X11 = X12 )
      | ( ( k6_subset_1 @ X12 @ X11 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l48_tex_2])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ~ ( v1_xboole_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( sk_B_1
        = ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['75','83'])).

thf('85',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('86',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v2_tex_2 @ X8 @ X9 )
      | ( X8
       != ( sk_C @ X8 @ X9 ) )
      | ( v3_tex_2 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('88',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( sk_B_1
     != ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( sk_B_1
     != ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( sk_B_1
       != ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['85','90'])).

thf('92',plain,
    ( ( ~ ( v1_xboole_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['84','91'])).

thf('93',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( sk_B_1
        = ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['74','92'])).

thf('94',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( sk_B_1
        = ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( sk_B_1
        = ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ( sk_B_1
       != ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['85','90'])).

thf('98',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('100',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','23','24','100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Vt0g3bbFYd
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:41:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 102 iterations in 0.054s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.20/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.20/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.50  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.20/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.20/0.50  thf(t50_tex_2, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.20/0.50         ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.50             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.50           ( ( v3_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.50            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50          ( ![B:$i]:
% 0.20/0.50            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.50                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.50              ( ( v3_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t50_tex_2])).
% 0.20/0.50  thf('0', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (~ ((v1_zfmisc_1 @ sk_B_1)) | ~ ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('2', plain, (((v1_zfmisc_1 @ sk_B_1) | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (((v3_tex_2 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.20/0.50      inference('split', [status(esa)], ['2'])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(d7_tex_2, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50           ( ( v3_tex_2 @ B @ A ) <=>
% 0.20/0.50             ( ( v2_tex_2 @ B @ A ) & 
% 0.20/0.50               ( ![C:$i]:
% 0.20/0.50                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.20/0.50                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.50          | ~ (v3_tex_2 @ X8 @ X9)
% 0.20/0.50          | (v2_tex_2 @ X8 @ X9)
% 0.20/0.50          | ~ (l1_pre_topc @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.50        | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.50  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (((v2_tex_2 @ sk_B_1 @ sk_A) | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['3', '8'])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t44_tex_2, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.20/0.50         ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.50             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.50           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X15 : $i, X16 : $i]:
% 0.20/0.50         ((v1_xboole_0 @ X15)
% 0.20/0.50          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.50          | ~ (v2_tex_2 @ X15 @ X16)
% 0.20/0.50          | (v1_zfmisc_1 @ X15)
% 0.20/0.50          | ~ (l1_pre_topc @ X16)
% 0.20/0.50          | ~ (v2_tdlat_3 @ X16)
% 0.20/0.50          | ~ (v2_pre_topc @ X16)
% 0.20/0.50          | (v2_struct_0 @ X16))),
% 0.20/0.50      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.50        | ~ (v2_tdlat_3 @ sk_A)
% 0.20/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | (v1_zfmisc_1 @ sk_B_1)
% 0.20/0.50        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.50        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.50  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('14', plain, ((v2_tdlat_3 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | (v1_zfmisc_1 @ sk_B_1)
% 0.20/0.50        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.50        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.50      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      ((((v1_xboole_0 @ sk_B_1) | (v1_zfmisc_1 @ sk_B_1) | (v2_struct_0 @ sk_A)))
% 0.20/0.50         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['9', '16'])).
% 0.20/0.50  thf('18', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      ((((v2_struct_0 @ sk_A) | (v1_zfmisc_1 @ sk_B_1)))
% 0.20/0.50         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.20/0.50      inference('clc', [status(thm)], ['17', '18'])).
% 0.20/0.50  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (((v1_zfmisc_1 @ sk_B_1)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.20/0.50      inference('clc', [status(thm)], ['19', '20'])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      ((~ (v1_zfmisc_1 @ sk_B_1)) <= (~ ((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('23', plain, (((v1_zfmisc_1 @ sk_B_1)) | ~ ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.50  thf('24', plain, (((v1_zfmisc_1 @ sk_B_1)) | ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.50      inference('split', [status(esa)], ['2'])).
% 0.20/0.50  thf('25', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.50      inference('split', [status(esa)], ['2'])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (![X15 : $i, X16 : $i]:
% 0.20/0.50         ((v1_xboole_0 @ X15)
% 0.20/0.50          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.50          | ~ (v1_zfmisc_1 @ X15)
% 0.20/0.50          | (v2_tex_2 @ X15 @ X16)
% 0.20/0.50          | ~ (l1_pre_topc @ X16)
% 0.20/0.50          | ~ (v2_tdlat_3 @ X16)
% 0.20/0.50          | ~ (v2_pre_topc @ X16)
% 0.20/0.50          | (v2_struct_0 @ X16))),
% 0.20/0.50      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.50        | ~ (v2_tdlat_3 @ sk_A)
% 0.20/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.50        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.20/0.50        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.50  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('30', plain, ((v2_tdlat_3 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.50        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.20/0.50        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.50      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      ((((v1_xboole_0 @ sk_B_1)
% 0.20/0.50         | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.50         | (v2_struct_0 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['25', '32'])).
% 0.20/0.50  thf('34', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      ((((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B_1 @ sk_A)))
% 0.20/0.50         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.50      inference('clc', [status(thm)], ['33', '34'])).
% 0.20/0.50  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.50      inference('clc', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.50          | ~ (v2_tex_2 @ X8 @ X9)
% 0.20/0.50          | (v2_tex_2 @ (sk_C @ X8 @ X9) @ X9)
% 0.20/0.50          | (v3_tex_2 @ X8 @ X9)
% 0.20/0.50          | ~ (l1_pre_topc @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.20/0.50  thf('40', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.50        | (v2_tex_2 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.20/0.50        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.50  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      (((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.50        | (v2_tex_2 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.20/0.50        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      ((((v2_tex_2 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.20/0.50         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['37', '42'])).
% 0.20/0.50  thf('44', plain,
% 0.20/0.50      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.50      inference('clc', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('46', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.50          | ~ (v2_tex_2 @ X8 @ X9)
% 0.20/0.50          | (m1_subset_1 @ (sk_C @ X8 @ X9) @ 
% 0.20/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.50          | (v3_tex_2 @ X8 @ X9)
% 0.20/0.50          | ~ (l1_pre_topc @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.20/0.50  thf('47', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.50        | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ 
% 0.20/0.50           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.50  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('49', plain,
% 0.20/0.50      (((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.50        | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ 
% 0.20/0.50           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.50  thf('50', plain,
% 0.20/0.50      ((((m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ 
% 0.20/0.50          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['44', '49'])).
% 0.20/0.50  thf('51', plain,
% 0.20/0.50      (![X15 : $i, X16 : $i]:
% 0.20/0.50         ((v1_xboole_0 @ X15)
% 0.20/0.50          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.50          | ~ (v2_tex_2 @ X15 @ X16)
% 0.20/0.50          | (v1_zfmisc_1 @ X15)
% 0.20/0.50          | ~ (l1_pre_topc @ X16)
% 0.20/0.50          | ~ (v2_tdlat_3 @ X16)
% 0.20/0.50          | ~ (v2_pre_topc @ X16)
% 0.20/0.50          | (v2_struct_0 @ X16))),
% 0.20/0.50      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.20/0.50  thf('52', plain,
% 0.20/0.50      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.50         | (v2_struct_0 @ sk_A)
% 0.20/0.50         | ~ (v2_pre_topc @ sk_A)
% 0.20/0.50         | ~ (v2_tdlat_3 @ sk_A)
% 0.20/0.50         | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50         | (v1_zfmisc_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.50         | ~ (v2_tex_2 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.20/0.50         | (v1_xboole_0 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.20/0.50         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.50  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('54', plain, ((v2_tdlat_3 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('56', plain,
% 0.20/0.50      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.50         | (v2_struct_0 @ sk_A)
% 0.20/0.50         | (v1_zfmisc_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.50         | ~ (v2_tex_2 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.20/0.50         | (v1_xboole_0 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.20/0.50         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.50      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 0.20/0.50  thf('57', plain,
% 0.20/0.50      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.50         | (v1_xboole_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.50         | (v1_zfmisc_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.50         | (v2_struct_0 @ sk_A)
% 0.20/0.50         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['43', '56'])).
% 0.20/0.50  thf('58', plain,
% 0.20/0.50      ((((v2_struct_0 @ sk_A)
% 0.20/0.50         | (v1_zfmisc_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.50         | (v1_xboole_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.50         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['57'])).
% 0.20/0.50  thf(cc1_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_zfmisc_1 @ A ) ))).
% 0.20/0.50  thf('59', plain, (![X0 : $i]: ((v1_zfmisc_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc1_zfmisc_1])).
% 0.20/0.50  thf('60', plain,
% 0.20/0.50      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.50         | (v1_zfmisc_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.50         | (v2_struct_0 @ sk_A)
% 0.20/0.50         | (v1_zfmisc_1 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.20/0.50         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['58', '59'])).
% 0.20/0.50  thf('61', plain,
% 0.20/0.50      ((((v2_struct_0 @ sk_A)
% 0.20/0.50         | (v1_zfmisc_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.50         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['60'])).
% 0.20/0.50  thf('62', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('63', plain,
% 0.20/0.50      ((((v3_tex_2 @ sk_B_1 @ sk_A) | (v1_zfmisc_1 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.20/0.50         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.50      inference('clc', [status(thm)], ['61', '62'])).
% 0.20/0.50  thf('64', plain,
% 0.20/0.50      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.50      inference('clc', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf('65', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('66', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.50          | ~ (v2_tex_2 @ X8 @ X9)
% 0.20/0.50          | (r1_tarski @ X8 @ (sk_C @ X8 @ X9))
% 0.20/0.50          | (v3_tex_2 @ X8 @ X9)
% 0.20/0.50          | ~ (l1_pre_topc @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.20/0.50  thf('67', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.50        | (r1_tarski @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.50        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['65', '66'])).
% 0.20/0.50  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('69', plain,
% 0.20/0.50      (((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.50        | (r1_tarski @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.50        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['67', '68'])).
% 0.20/0.50  thf('70', plain,
% 0.20/0.50      ((((r1_tarski @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.50         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['64', '69'])).
% 0.20/0.50  thf(t1_tex_2, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.20/0.50           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.20/0.50  thf('71', plain,
% 0.20/0.50      (![X13 : $i, X14 : $i]:
% 0.20/0.50         ((v1_xboole_0 @ X13)
% 0.20/0.50          | ~ (v1_zfmisc_1 @ X13)
% 0.20/0.50          | ((X14) = (X13))
% 0.20/0.50          | ~ (r1_tarski @ X14 @ X13)
% 0.20/0.50          | (v1_xboole_0 @ X14))),
% 0.20/0.50      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.20/0.50  thf('72', plain,
% 0.20/0.50      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.50         | (v1_xboole_0 @ sk_B_1)
% 0.20/0.50         | ((sk_B_1) = (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.50         | ~ (v1_zfmisc_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.50         | (v1_xboole_0 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.20/0.50         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['70', '71'])).
% 0.20/0.50  thf('73', plain,
% 0.20/0.50      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.50         | (v1_xboole_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.50         | ((sk_B_1) = (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.50         | (v1_xboole_0 @ sk_B_1)
% 0.20/0.50         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['63', '72'])).
% 0.20/0.50  thf('74', plain,
% 0.20/0.50      ((((v1_xboole_0 @ sk_B_1)
% 0.20/0.50         | ((sk_B_1) = (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.50         | (v1_xboole_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.50         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['73'])).
% 0.20/0.50  thf('75', plain,
% 0.20/0.50      ((((r1_tarski @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.50         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['64', '69'])).
% 0.20/0.50  thf(t1_mcart_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.50          ( ![B:$i]: ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ))).
% 0.20/0.50  thf('76', plain,
% 0.20/0.50      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.20/0.50      inference('cnf', [status(esa)], [t1_mcart_1])).
% 0.20/0.50  thf(dt_k6_subset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.50  thf('77', plain,
% 0.20/0.50      (![X1 : $i, X2 : $i]:
% 0.20/0.50         (m1_subset_1 @ (k6_subset_1 @ X1 @ X2) @ (k1_zfmisc_1 @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.20/0.50  thf(t5_subset, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.20/0.50          ( v1_xboole_0 @ C ) ) ))).
% 0.20/0.50  thf('78', plain,
% 0.20/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X3 @ X4)
% 0.20/0.50          | ~ (v1_xboole_0 @ X5)
% 0.20/0.50          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t5_subset])).
% 0.20/0.50  thf('79', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X2 @ (k6_subset_1 @ X0 @ X1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['77', '78'])).
% 0.20/0.50  thf('80', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((k6_subset_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['76', '79'])).
% 0.20/0.50  thf(l48_tex_2, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ~( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) & 
% 0.20/0.50          ( ( k6_subset_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.50  thf('81', plain,
% 0.20/0.50      (![X11 : $i, X12 : $i]:
% 0.20/0.50         (~ (r1_tarski @ X11 @ X12)
% 0.20/0.50          | ((X11) = (X12))
% 0.20/0.50          | ((k6_subset_1 @ X12 @ X11) != (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [l48_tex_2])).
% 0.20/0.50  thf('82', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.50          | ~ (v1_xboole_0 @ X1)
% 0.20/0.50          | ((X0) = (X1))
% 0.20/0.50          | ~ (r1_tarski @ X0 @ X1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['80', '81'])).
% 0.20/0.50  thf('83', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.50      inference('simplify', [status(thm)], ['82'])).
% 0.20/0.50  thf('84', plain,
% 0.20/0.50      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.50         | ~ (v1_xboole_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.50         | ((sk_B_1) = (sk_C @ sk_B_1 @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['75', '83'])).
% 0.20/0.50  thf('85', plain,
% 0.20/0.50      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.50      inference('clc', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf('86', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('87', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.50          | ~ (v2_tex_2 @ X8 @ X9)
% 0.20/0.50          | ((X8) != (sk_C @ X8 @ X9))
% 0.20/0.50          | (v3_tex_2 @ X8 @ X9)
% 0.20/0.50          | ~ (l1_pre_topc @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.20/0.50  thf('88', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.50        | ((sk_B_1) != (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.50        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['86', '87'])).
% 0.20/0.50  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('90', plain,
% 0.20/0.50      (((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.50        | ((sk_B_1) != (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.50        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['88', '89'])).
% 0.20/0.50  thf('91', plain,
% 0.20/0.50      (((((sk_B_1) != (sk_C @ sk_B_1 @ sk_A)) | (v3_tex_2 @ sk_B_1 @ sk_A)))
% 0.20/0.50         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['85', '90'])).
% 0.20/0.50  thf('92', plain,
% 0.20/0.50      (((~ (v1_xboole_0 @ (sk_C @ sk_B_1 @ sk_A)) | (v3_tex_2 @ sk_B_1 @ sk_A)))
% 0.20/0.50         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.50      inference('clc', [status(thm)], ['84', '91'])).
% 0.20/0.50  thf('93', plain,
% 0.20/0.50      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.50         | ((sk_B_1) = (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.50         | (v1_xboole_0 @ sk_B_1)
% 0.20/0.50         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['74', '92'])).
% 0.20/0.50  thf('94', plain,
% 0.20/0.50      ((((v1_xboole_0 @ sk_B_1)
% 0.20/0.50         | ((sk_B_1) = (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.50         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['93'])).
% 0.20/0.50  thf('95', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('96', plain,
% 0.20/0.50      ((((v3_tex_2 @ sk_B_1 @ sk_A) | ((sk_B_1) = (sk_C @ sk_B_1 @ sk_A))))
% 0.20/0.50         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.50      inference('clc', [status(thm)], ['94', '95'])).
% 0.20/0.50  thf('97', plain,
% 0.20/0.50      (((((sk_B_1) != (sk_C @ sk_B_1 @ sk_A)) | (v3_tex_2 @ sk_B_1 @ sk_A)))
% 0.20/0.50         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['85', '90'])).
% 0.20/0.50  thf('98', plain,
% 0.20/0.50      (((v3_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.50      inference('clc', [status(thm)], ['96', '97'])).
% 0.20/0.50  thf('99', plain,
% 0.20/0.50      ((~ (v3_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('100', plain,
% 0.20/0.50      (~ ((v1_zfmisc_1 @ sk_B_1)) | ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['98', '99'])).
% 0.20/0.50  thf('101', plain, ($false),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['1', '23', '24', '100'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
