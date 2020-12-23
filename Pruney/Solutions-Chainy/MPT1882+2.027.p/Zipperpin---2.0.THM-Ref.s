%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.I7jWc81QaT

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:23 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 325 expanded)
%              Number of leaves         :   26 ( 100 expanded)
%              Depth                    :   23
%              Number of atoms          :  966 (4151 expanded)
%              Number of equality atoms :   13 (  18 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v3_tex_2 @ X10 @ X11 )
      | ( v2_tex_2 @ X10 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v2_tex_2 @ X10 @ X11 )
      | ( v2_tex_2 @ ( sk_C_1 @ X10 @ X11 ) @ X11 )
      | ( v3_tex_2 @ X10 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('40',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B @ sk_A )
    | ( v2_tex_2 @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( v2_tex_2 @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( v2_tex_2 @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A )
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
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v2_tex_2 @ X10 @ X11 )
      | ( m1_subset_1 @ ( sk_C_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v3_tex_2 @ X10 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('47',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
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
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v2_tdlat_3 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ~ ( v2_tex_2 @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) )
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
      | ( v1_zfmisc_1 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ~ ( v2_tex_2 @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['52','53','54','55'])).

thf('57',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( v1_xboole_0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( v1_zfmisc_1 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['43','56'])).

thf('58',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['57'])).

thf(cc1_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_zfmisc_1 @ A ) ) )).

thf('59',plain,(
    ! [X8: $i] :
      ( ( v1_zfmisc_1 @ X8 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_zfmisc_1])).

thf('60',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C_1 @ sk_B @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C_1 @ sk_B @ sk_A ) ) )
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
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v2_tex_2 @ X10 @ X11 )
      | ( r1_tarski @ X10 @ ( sk_C_1 @ X10 @ X11 ) )
      | ( v3_tex_2 @ X10 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('67',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( r1_tarski @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) )
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
    ! [X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X13 )
      | ~ ( v1_zfmisc_1 @ X13 )
      | ( X14 = X13 )
      | ~ ( r1_tarski @ X14 @ X13 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('72',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( sk_B
        = ( sk_C_1 @ sk_B @ sk_A ) )
      | ~ ( v1_zfmisc_1 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( v1_xboole_0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( sk_B
        = ( sk_C_1 @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['63','72'])).

thf('74',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( sk_B
        = ( sk_C_1 @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ( ( r1_tarski @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['64','69'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('77',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('79',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_xboole_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['75','80'])).

thf('82',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( ~ ( v1_xboole_0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( sk_B
        = ( sk_C_1 @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['74','83'])).

thf('85',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( sk_B
        = ( sk_C_1 @ sk_B @ sk_A ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( sk_B
        = ( sk_C_1 @ sk_B @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('89',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v2_tex_2 @ X10 @ X11 )
      | ( X10
       != ( sk_C_1 @ X10 @ X11 ) )
      | ( v3_tex_2 @ X10 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('91',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B @ sk_A )
    | ( sk_B
     != ( sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( sk_B
     != ( sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( sk_B
       != ( sk_C_1 @ sk_B @ sk_A ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['88','93'])).

thf('95',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['87','94'])).

thf('96',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('97',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B )
    | ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','23','24','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.I7jWc81QaT
% 0.14/0.37  % Computer   : n021.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 13:28:19 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.23/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.52  % Solved by: fo/fo7.sh
% 0.23/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.52  % done 75 iterations in 0.038s
% 0.23/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.52  % SZS output start Refutation
% 0.23/0.52  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.23/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.23/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.23/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.52  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.23/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.52  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.23/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.52  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.23/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.23/0.52  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.23/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.23/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.23/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.23/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.52  thf(t50_tex_2, conjecture,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.23/0.52         ( l1_pre_topc @ A ) ) =>
% 0.23/0.52       ( ![B:$i]:
% 0.23/0.52         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.23/0.52             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.23/0.52           ( ( v3_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.23/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.52    (~( ![A:$i]:
% 0.23/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.23/0.52            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.52          ( ![B:$i]:
% 0.23/0.52            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.23/0.52                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.23/0.52              ( ( v3_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.23/0.52    inference('cnf.neg', [status(esa)], [t50_tex_2])).
% 0.23/0.52  thf('0', plain, ((~ (v1_zfmisc_1 @ sk_B) | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('1', plain, (~ ((v1_zfmisc_1 @ sk_B)) | ~ ((v3_tex_2 @ sk_B @ sk_A))),
% 0.23/0.52      inference('split', [status(esa)], ['0'])).
% 0.23/0.52  thf('2', plain, (((v1_zfmisc_1 @ sk_B) | (v3_tex_2 @ sk_B @ sk_A))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('3', plain, (((v3_tex_2 @ sk_B @ sk_A)) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.23/0.52      inference('split', [status(esa)], ['2'])).
% 0.23/0.52  thf('4', plain,
% 0.23/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf(d7_tex_2, axiom,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( l1_pre_topc @ A ) =>
% 0.23/0.52       ( ![B:$i]:
% 0.23/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.52           ( ( v3_tex_2 @ B @ A ) <=>
% 0.23/0.52             ( ( v2_tex_2 @ B @ A ) & 
% 0.23/0.52               ( ![C:$i]:
% 0.23/0.52                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.52                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.23/0.52                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.23/0.52  thf('5', plain,
% 0.23/0.52      (![X10 : $i, X11 : $i]:
% 0.23/0.52         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.23/0.52          | ~ (v3_tex_2 @ X10 @ X11)
% 0.23/0.52          | (v2_tex_2 @ X10 @ X11)
% 0.23/0.52          | ~ (l1_pre_topc @ X11))),
% 0.23/0.52      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.23/0.52  thf('6', plain,
% 0.23/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.23/0.52        | (v2_tex_2 @ sk_B @ sk_A)
% 0.23/0.52        | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.23/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.23/0.52  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('8', plain, (((v2_tex_2 @ sk_B @ sk_A) | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.23/0.52      inference('demod', [status(thm)], ['6', '7'])).
% 0.23/0.52  thf('9', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['3', '8'])).
% 0.23/0.52  thf('10', plain,
% 0.23/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf(t44_tex_2, axiom,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.23/0.52         ( l1_pre_topc @ A ) ) =>
% 0.23/0.52       ( ![B:$i]:
% 0.23/0.52         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.23/0.52             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.23/0.52           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.23/0.52  thf('11', plain,
% 0.23/0.52      (![X15 : $i, X16 : $i]:
% 0.23/0.52         ((v1_xboole_0 @ X15)
% 0.23/0.52          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.23/0.52          | ~ (v2_tex_2 @ X15 @ X16)
% 0.23/0.52          | (v1_zfmisc_1 @ X15)
% 0.23/0.52          | ~ (l1_pre_topc @ X16)
% 0.23/0.52          | ~ (v2_tdlat_3 @ X16)
% 0.23/0.52          | ~ (v2_pre_topc @ X16)
% 0.23/0.52          | (v2_struct_0 @ X16))),
% 0.23/0.52      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.23/0.52  thf('12', plain,
% 0.23/0.52      (((v2_struct_0 @ sk_A)
% 0.23/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.23/0.52        | ~ (v2_tdlat_3 @ sk_A)
% 0.23/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.23/0.52        | (v1_zfmisc_1 @ sk_B)
% 0.23/0.52        | ~ (v2_tex_2 @ sk_B @ sk_A)
% 0.23/0.52        | (v1_xboole_0 @ sk_B))),
% 0.23/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.23/0.52  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('14', plain, ((v2_tdlat_3 @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('16', plain,
% 0.23/0.52      (((v2_struct_0 @ sk_A)
% 0.23/0.52        | (v1_zfmisc_1 @ sk_B)
% 0.23/0.52        | ~ (v2_tex_2 @ sk_B @ sk_A)
% 0.23/0.52        | (v1_xboole_0 @ sk_B))),
% 0.23/0.52      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.23/0.52  thf('17', plain,
% 0.23/0.52      ((((v1_xboole_0 @ sk_B) | (v1_zfmisc_1 @ sk_B) | (v2_struct_0 @ sk_A)))
% 0.23/0.52         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['9', '16'])).
% 0.23/0.52  thf('18', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('19', plain,
% 0.23/0.52      ((((v2_struct_0 @ sk_A) | (v1_zfmisc_1 @ sk_B)))
% 0.23/0.52         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.23/0.52      inference('clc', [status(thm)], ['17', '18'])).
% 0.23/0.52  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('21', plain, (((v1_zfmisc_1 @ sk_B)) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.23/0.52      inference('clc', [status(thm)], ['19', '20'])).
% 0.23/0.52  thf('22', plain, ((~ (v1_zfmisc_1 @ sk_B)) <= (~ ((v1_zfmisc_1 @ sk_B)))),
% 0.23/0.52      inference('split', [status(esa)], ['0'])).
% 0.23/0.52  thf('23', plain, (((v1_zfmisc_1 @ sk_B)) | ~ ((v3_tex_2 @ sk_B @ sk_A))),
% 0.23/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.23/0.52  thf('24', plain, (((v1_zfmisc_1 @ sk_B)) | ((v3_tex_2 @ sk_B @ sk_A))),
% 0.23/0.52      inference('split', [status(esa)], ['2'])).
% 0.23/0.52  thf('25', plain, (((v1_zfmisc_1 @ sk_B)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.23/0.52      inference('split', [status(esa)], ['2'])).
% 0.23/0.52  thf('26', plain,
% 0.23/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('27', plain,
% 0.23/0.52      (![X15 : $i, X16 : $i]:
% 0.23/0.52         ((v1_xboole_0 @ X15)
% 0.23/0.52          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.23/0.52          | ~ (v1_zfmisc_1 @ X15)
% 0.23/0.52          | (v2_tex_2 @ X15 @ X16)
% 0.23/0.52          | ~ (l1_pre_topc @ X16)
% 0.23/0.52          | ~ (v2_tdlat_3 @ X16)
% 0.23/0.52          | ~ (v2_pre_topc @ X16)
% 0.23/0.52          | (v2_struct_0 @ X16))),
% 0.23/0.52      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.23/0.52  thf('28', plain,
% 0.23/0.52      (((v2_struct_0 @ sk_A)
% 0.23/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.23/0.52        | ~ (v2_tdlat_3 @ sk_A)
% 0.23/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.23/0.52        | (v2_tex_2 @ sk_B @ sk_A)
% 0.23/0.52        | ~ (v1_zfmisc_1 @ sk_B)
% 0.23/0.52        | (v1_xboole_0 @ sk_B))),
% 0.23/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.23/0.52  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('30', plain, ((v2_tdlat_3 @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('32', plain,
% 0.23/0.52      (((v2_struct_0 @ sk_A)
% 0.23/0.52        | (v2_tex_2 @ sk_B @ sk_A)
% 0.23/0.52        | ~ (v1_zfmisc_1 @ sk_B)
% 0.23/0.52        | (v1_xboole_0 @ sk_B))),
% 0.23/0.52      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 0.23/0.52  thf('33', plain,
% 0.23/0.52      ((((v1_xboole_0 @ sk_B) | (v2_tex_2 @ sk_B @ sk_A) | (v2_struct_0 @ sk_A)))
% 0.23/0.52         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['25', '32'])).
% 0.23/0.52  thf('34', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('35', plain,
% 0.23/0.52      ((((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B @ sk_A)))
% 0.23/0.52         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.23/0.52      inference('clc', [status(thm)], ['33', '34'])).
% 0.23/0.52  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('37', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.23/0.52      inference('clc', [status(thm)], ['35', '36'])).
% 0.23/0.52  thf('38', plain,
% 0.23/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('39', plain,
% 0.23/0.52      (![X10 : $i, X11 : $i]:
% 0.23/0.52         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.23/0.52          | ~ (v2_tex_2 @ X10 @ X11)
% 0.23/0.52          | (v2_tex_2 @ (sk_C_1 @ X10 @ X11) @ X11)
% 0.23/0.52          | (v3_tex_2 @ X10 @ X11)
% 0.23/0.52          | ~ (l1_pre_topc @ X11))),
% 0.23/0.52      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.23/0.52  thf('40', plain,
% 0.23/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.23/0.52        | (v3_tex_2 @ sk_B @ sk_A)
% 0.23/0.52        | (v2_tex_2 @ (sk_C_1 @ sk_B @ sk_A) @ sk_A)
% 0.23/0.52        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.23/0.52      inference('sup-', [status(thm)], ['38', '39'])).
% 0.23/0.52  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('42', plain,
% 0.23/0.52      (((v3_tex_2 @ sk_B @ sk_A)
% 0.23/0.52        | (v2_tex_2 @ (sk_C_1 @ sk_B @ sk_A) @ sk_A)
% 0.23/0.52        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.23/0.52      inference('demod', [status(thm)], ['40', '41'])).
% 0.23/0.52  thf('43', plain,
% 0.23/0.52      ((((v2_tex_2 @ (sk_C_1 @ sk_B @ sk_A) @ sk_A) | (v3_tex_2 @ sk_B @ sk_A)))
% 0.23/0.52         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['37', '42'])).
% 0.23/0.52  thf('44', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.23/0.52      inference('clc', [status(thm)], ['35', '36'])).
% 0.23/0.52  thf('45', plain,
% 0.23/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('46', plain,
% 0.23/0.52      (![X10 : $i, X11 : $i]:
% 0.23/0.52         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.23/0.52          | ~ (v2_tex_2 @ X10 @ X11)
% 0.23/0.52          | (m1_subset_1 @ (sk_C_1 @ X10 @ X11) @ 
% 0.23/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.23/0.52          | (v3_tex_2 @ X10 @ X11)
% 0.23/0.52          | ~ (l1_pre_topc @ X11))),
% 0.23/0.52      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.23/0.52  thf('47', plain,
% 0.23/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.23/0.52        | (v3_tex_2 @ sk_B @ sk_A)
% 0.23/0.52        | (m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ 
% 0.23/0.52           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.52        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.23/0.52      inference('sup-', [status(thm)], ['45', '46'])).
% 0.23/0.52  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('49', plain,
% 0.23/0.52      (((v3_tex_2 @ sk_B @ sk_A)
% 0.23/0.52        | (m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ 
% 0.23/0.52           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.52        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.23/0.52      inference('demod', [status(thm)], ['47', '48'])).
% 0.23/0.52  thf('50', plain,
% 0.23/0.52      ((((m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ 
% 0.23/0.52          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.52         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['44', '49'])).
% 0.23/0.52  thf('51', plain,
% 0.23/0.52      (![X15 : $i, X16 : $i]:
% 0.23/0.52         ((v1_xboole_0 @ X15)
% 0.23/0.52          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.23/0.52          | ~ (v2_tex_2 @ X15 @ X16)
% 0.23/0.52          | (v1_zfmisc_1 @ X15)
% 0.23/0.52          | ~ (l1_pre_topc @ X16)
% 0.23/0.52          | ~ (v2_tdlat_3 @ X16)
% 0.23/0.52          | ~ (v2_pre_topc @ X16)
% 0.23/0.52          | (v2_struct_0 @ X16))),
% 0.23/0.52      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.23/0.52  thf('52', plain,
% 0.23/0.52      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.23/0.52         | (v2_struct_0 @ sk_A)
% 0.23/0.52         | ~ (v2_pre_topc @ sk_A)
% 0.23/0.52         | ~ (v2_tdlat_3 @ sk_A)
% 0.23/0.52         | ~ (l1_pre_topc @ sk_A)
% 0.23/0.52         | (v1_zfmisc_1 @ (sk_C_1 @ sk_B @ sk_A))
% 0.23/0.52         | ~ (v2_tex_2 @ (sk_C_1 @ sk_B @ sk_A) @ sk_A)
% 0.23/0.52         | (v1_xboole_0 @ (sk_C_1 @ sk_B @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['50', '51'])).
% 0.23/0.52  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('54', plain, ((v2_tdlat_3 @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('56', plain,
% 0.23/0.52      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.23/0.52         | (v2_struct_0 @ sk_A)
% 0.23/0.52         | (v1_zfmisc_1 @ (sk_C_1 @ sk_B @ sk_A))
% 0.23/0.52         | ~ (v2_tex_2 @ (sk_C_1 @ sk_B @ sk_A) @ sk_A)
% 0.23/0.52         | (v1_xboole_0 @ (sk_C_1 @ sk_B @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.23/0.52      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 0.23/0.52  thf('57', plain,
% 0.23/0.52      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.23/0.52         | (v1_xboole_0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.23/0.52         | (v1_zfmisc_1 @ (sk_C_1 @ sk_B @ sk_A))
% 0.23/0.52         | (v2_struct_0 @ sk_A)
% 0.23/0.52         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['43', '56'])).
% 0.23/0.52  thf('58', plain,
% 0.23/0.52      ((((v2_struct_0 @ sk_A)
% 0.23/0.52         | (v1_zfmisc_1 @ (sk_C_1 @ sk_B @ sk_A))
% 0.23/0.52         | (v1_xboole_0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.23/0.52         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.23/0.52      inference('simplify', [status(thm)], ['57'])).
% 0.23/0.52  thf(cc1_zfmisc_1, axiom,
% 0.23/0.52    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_zfmisc_1 @ A ) ))).
% 0.23/0.52  thf('59', plain, (![X8 : $i]: ((v1_zfmisc_1 @ X8) | ~ (v1_xboole_0 @ X8))),
% 0.23/0.52      inference('cnf', [status(esa)], [cc1_zfmisc_1])).
% 0.23/0.52  thf('60', plain,
% 0.23/0.52      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.23/0.52         | (v1_zfmisc_1 @ (sk_C_1 @ sk_B @ sk_A))
% 0.23/0.52         | (v2_struct_0 @ sk_A)
% 0.23/0.52         | (v1_zfmisc_1 @ (sk_C_1 @ sk_B @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['58', '59'])).
% 0.23/0.52  thf('61', plain,
% 0.23/0.52      ((((v2_struct_0 @ sk_A)
% 0.23/0.52         | (v1_zfmisc_1 @ (sk_C_1 @ sk_B @ sk_A))
% 0.23/0.52         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.23/0.52      inference('simplify', [status(thm)], ['60'])).
% 0.23/0.52  thf('62', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('63', plain,
% 0.23/0.52      ((((v3_tex_2 @ sk_B @ sk_A) | (v1_zfmisc_1 @ (sk_C_1 @ sk_B @ sk_A))))
% 0.23/0.52         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.23/0.52      inference('clc', [status(thm)], ['61', '62'])).
% 0.23/0.52  thf('64', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.23/0.52      inference('clc', [status(thm)], ['35', '36'])).
% 0.23/0.52  thf('65', plain,
% 0.23/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('66', plain,
% 0.23/0.52      (![X10 : $i, X11 : $i]:
% 0.23/0.52         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.23/0.52          | ~ (v2_tex_2 @ X10 @ X11)
% 0.23/0.52          | (r1_tarski @ X10 @ (sk_C_1 @ X10 @ X11))
% 0.23/0.52          | (v3_tex_2 @ X10 @ X11)
% 0.23/0.52          | ~ (l1_pre_topc @ X11))),
% 0.23/0.52      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.23/0.52  thf('67', plain,
% 0.23/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.23/0.52        | (v3_tex_2 @ sk_B @ sk_A)
% 0.23/0.52        | (r1_tarski @ sk_B @ (sk_C_1 @ sk_B @ sk_A))
% 0.23/0.52        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.23/0.52      inference('sup-', [status(thm)], ['65', '66'])).
% 0.23/0.52  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('69', plain,
% 0.23/0.52      (((v3_tex_2 @ sk_B @ sk_A)
% 0.23/0.52        | (r1_tarski @ sk_B @ (sk_C_1 @ sk_B @ sk_A))
% 0.23/0.52        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.23/0.52      inference('demod', [status(thm)], ['67', '68'])).
% 0.23/0.52  thf('70', plain,
% 0.23/0.52      ((((r1_tarski @ sk_B @ (sk_C_1 @ sk_B @ sk_A)) | (v3_tex_2 @ sk_B @ sk_A)))
% 0.23/0.52         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['64', '69'])).
% 0.23/0.52  thf(t1_tex_2, axiom,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.23/0.52       ( ![B:$i]:
% 0.23/0.52         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.23/0.52           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.23/0.52  thf('71', plain,
% 0.23/0.52      (![X13 : $i, X14 : $i]:
% 0.23/0.52         ((v1_xboole_0 @ X13)
% 0.23/0.52          | ~ (v1_zfmisc_1 @ X13)
% 0.23/0.52          | ((X14) = (X13))
% 0.23/0.52          | ~ (r1_tarski @ X14 @ X13)
% 0.23/0.52          | (v1_xboole_0 @ X14))),
% 0.23/0.52      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.23/0.52  thf('72', plain,
% 0.23/0.52      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.23/0.52         | (v1_xboole_0 @ sk_B)
% 0.23/0.52         | ((sk_B) = (sk_C_1 @ sk_B @ sk_A))
% 0.23/0.52         | ~ (v1_zfmisc_1 @ (sk_C_1 @ sk_B @ sk_A))
% 0.23/0.52         | (v1_xboole_0 @ (sk_C_1 @ sk_B @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['70', '71'])).
% 0.23/0.52  thf('73', plain,
% 0.23/0.52      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.23/0.52         | (v1_xboole_0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.23/0.52         | ((sk_B) = (sk_C_1 @ sk_B @ sk_A))
% 0.23/0.52         | (v1_xboole_0 @ sk_B)
% 0.23/0.52         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['63', '72'])).
% 0.23/0.52  thf('74', plain,
% 0.23/0.52      ((((v1_xboole_0 @ sk_B)
% 0.23/0.52         | ((sk_B) = (sk_C_1 @ sk_B @ sk_A))
% 0.23/0.52         | (v1_xboole_0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.23/0.52         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.23/0.52      inference('simplify', [status(thm)], ['73'])).
% 0.23/0.52  thf('75', plain,
% 0.23/0.52      ((((r1_tarski @ sk_B @ (sk_C_1 @ sk_B @ sk_A)) | (v3_tex_2 @ sk_B @ sk_A)))
% 0.23/0.52         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['64', '69'])).
% 0.23/0.52  thf(t3_xboole_0, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.23/0.52            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.23/0.52       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.23/0.52            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.23/0.52  thf('76', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]:
% 0.23/0.52         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.23/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.23/0.52  thf(t7_boole, axiom,
% 0.23/0.52    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( v1_xboole_0 @ B ) ) ))).
% 0.23/0.52  thf('77', plain,
% 0.23/0.52      (![X6 : $i, X7 : $i]: (~ (r2_hidden @ X6 @ X7) | ~ (v1_xboole_0 @ X7))),
% 0.23/0.52      inference('cnf', [status(esa)], [t7_boole])).
% 0.23/0.52  thf('78', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.23/0.52      inference('sup-', [status(thm)], ['76', '77'])).
% 0.23/0.52  thf(t69_xboole_1, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.23/0.52       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.23/0.52  thf('79', plain,
% 0.23/0.52      (![X4 : $i, X5 : $i]:
% 0.23/0.52         (~ (r1_xboole_0 @ X4 @ X5)
% 0.23/0.52          | ~ (r1_tarski @ X4 @ X5)
% 0.23/0.52          | (v1_xboole_0 @ X4))),
% 0.23/0.52      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.23/0.52  thf('80', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]:
% 0.23/0.52         (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ X1) | ~ (r1_tarski @ X1 @ X0))),
% 0.23/0.52      inference('sup-', [status(thm)], ['78', '79'])).
% 0.23/0.52  thf('81', plain,
% 0.23/0.52      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.23/0.52         | (v1_xboole_0 @ sk_B)
% 0.23/0.52         | ~ (v1_xboole_0 @ (sk_C_1 @ sk_B @ sk_A))))
% 0.23/0.52         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['75', '80'])).
% 0.23/0.52  thf('82', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('83', plain,
% 0.23/0.52      (((~ (v1_xboole_0 @ (sk_C_1 @ sk_B @ sk_A)) | (v3_tex_2 @ sk_B @ sk_A)))
% 0.23/0.52         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.23/0.52      inference('clc', [status(thm)], ['81', '82'])).
% 0.23/0.52  thf('84', plain,
% 0.23/0.52      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.23/0.52         | ((sk_B) = (sk_C_1 @ sk_B @ sk_A))
% 0.23/0.52         | (v1_xboole_0 @ sk_B)
% 0.23/0.52         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['74', '83'])).
% 0.23/0.52  thf('85', plain,
% 0.23/0.52      ((((v1_xboole_0 @ sk_B)
% 0.23/0.52         | ((sk_B) = (sk_C_1 @ sk_B @ sk_A))
% 0.23/0.52         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.23/0.52      inference('simplify', [status(thm)], ['84'])).
% 0.23/0.52  thf('86', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('87', plain,
% 0.23/0.52      ((((v3_tex_2 @ sk_B @ sk_A) | ((sk_B) = (sk_C_1 @ sk_B @ sk_A))))
% 0.23/0.52         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.23/0.52      inference('clc', [status(thm)], ['85', '86'])).
% 0.23/0.52  thf('88', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.23/0.52      inference('clc', [status(thm)], ['35', '36'])).
% 0.23/0.52  thf('89', plain,
% 0.23/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('90', plain,
% 0.23/0.52      (![X10 : $i, X11 : $i]:
% 0.23/0.52         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.23/0.52          | ~ (v2_tex_2 @ X10 @ X11)
% 0.23/0.52          | ((X10) != (sk_C_1 @ X10 @ X11))
% 0.23/0.52          | (v3_tex_2 @ X10 @ X11)
% 0.23/0.52          | ~ (l1_pre_topc @ X11))),
% 0.23/0.52      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.23/0.52  thf('91', plain,
% 0.23/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.23/0.52        | (v3_tex_2 @ sk_B @ sk_A)
% 0.23/0.52        | ((sk_B) != (sk_C_1 @ sk_B @ sk_A))
% 0.23/0.52        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.23/0.52      inference('sup-', [status(thm)], ['89', '90'])).
% 0.23/0.52  thf('92', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('93', plain,
% 0.23/0.52      (((v3_tex_2 @ sk_B @ sk_A)
% 0.23/0.52        | ((sk_B) != (sk_C_1 @ sk_B @ sk_A))
% 0.23/0.52        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.23/0.52      inference('demod', [status(thm)], ['91', '92'])).
% 0.23/0.52  thf('94', plain,
% 0.23/0.52      (((((sk_B) != (sk_C_1 @ sk_B @ sk_A)) | (v3_tex_2 @ sk_B @ sk_A)))
% 0.23/0.52         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['88', '93'])).
% 0.23/0.52  thf('95', plain, (((v3_tex_2 @ sk_B @ sk_A)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.23/0.52      inference('clc', [status(thm)], ['87', '94'])).
% 0.23/0.52  thf('96', plain,
% 0.23/0.52      ((~ (v3_tex_2 @ sk_B @ sk_A)) <= (~ ((v3_tex_2 @ sk_B @ sk_A)))),
% 0.23/0.52      inference('split', [status(esa)], ['0'])).
% 0.23/0.52  thf('97', plain, (~ ((v1_zfmisc_1 @ sk_B)) | ((v3_tex_2 @ sk_B @ sk_A))),
% 0.23/0.52      inference('sup-', [status(thm)], ['95', '96'])).
% 0.23/0.52  thf('98', plain, ($false),
% 0.23/0.52      inference('sat_resolution*', [status(thm)], ['1', '23', '24', '97'])).
% 0.23/0.52  
% 0.23/0.52  % SZS output end Refutation
% 0.23/0.52  
% 0.23/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
