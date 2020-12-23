%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0TloVfzOR2

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:23 EST 2020

% Result     : Theorem 0.26s
% Output     : Refutation 0.26s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 420 expanded)
%              Number of leaves         :   25 ( 126 expanded)
%              Depth                    :   23
%              Number of atoms          : 1075 (5203 expanded)
%              Number of equality atoms :   19 (  33 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

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
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v3_tex_2 @ X10 @ X11 )
      | ( v2_tex_2 @ X10 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v2_tex_2 @ X10 @ X11 )
      | ( v2_tex_2 @ ( sk_C @ X10 @ X11 ) @ X11 )
      | ( v3_tex_2 @ X10 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v2_tex_2 @ X10 @ X11 )
      | ( m1_subset_1 @ ( sk_C @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v3_tex_2 @ X10 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
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

thf('59',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('60',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v2_tex_2 @ X10 @ X11 )
      | ( r1_tarski @ X10 @ ( sk_C @ X10 @ X11 ) )
      | ( v3_tex_2 @ X10 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('62',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( r1_tarski @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( r1_tarski @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( r1_tarski @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['59','64'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('66',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('67',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X6 ) @ X8 )
      | ~ ( r2_hidden @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('69',plain,(
    ! [X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X13 )
      | ~ ( v1_zfmisc_1 @ X13 )
      | ( X14 = X13 )
      | ~ ( r1_tarski @ X14 @ X13 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('72',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('73',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_tarski @ ( k1_tarski @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('77',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','77'])).

thf('79',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_tarski @ ( k1_tarski @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_zfmisc_1 @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['65','80'])).

thf('82',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('83',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('87',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ~ ( v1_xboole_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['58','87'])).

thf('89',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( ( r1_tarski @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['59','64'])).

thf('93',plain,(
    ! [X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X13 )
      | ~ ( v1_zfmisc_1 @ X13 )
      | ( X14 = X13 )
      | ~ ( r1_tarski @ X14 @ X13 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('94',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( sk_B_1
        = ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( v1_zfmisc_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( sk_B_1
        = ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['91','94'])).

thf('96',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( sk_B_1
        = ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ~ ( v1_xboole_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('98',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( sk_B_1
        = ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( sk_B_1
        = ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( sk_B_1
        = ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('103',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v2_tex_2 @ X10 @ X11 )
      | ( X10
       != ( sk_C @ X10 @ X11 ) )
      | ( v3_tex_2 @ X10 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('105',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( sk_B_1
     != ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( sk_B_1
     != ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( ( sk_B_1
       != ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['102','107'])).

thf('109',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['101','108'])).

thf('110',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('111',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','23','24','111'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0TloVfzOR2
% 0.15/0.39  % Computer   : n022.cluster.edu
% 0.15/0.39  % Model      : x86_64 x86_64
% 0.15/0.39  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.39  % Memory     : 8042.1875MB
% 0.15/0.39  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.39  % CPULimit   : 60
% 0.15/0.39  % DateTime   : Tue Dec  1 14:23:41 EST 2020
% 0.15/0.39  % CPUTime    : 
% 0.15/0.39  % Running portfolio for 600 s
% 0.15/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.39  % Number of cores: 8
% 0.15/0.39  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 0.26/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.26/0.56  % Solved by: fo/fo7.sh
% 0.26/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.26/0.56  % done 101 iterations in 0.054s
% 0.26/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.26/0.56  % SZS output start Refutation
% 0.26/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.26/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.26/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.26/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.26/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.26/0.56  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.26/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.26/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.26/0.56  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.26/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.26/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.26/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.26/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.26/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.26/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.26/0.56  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.26/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.26/0.56  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.26/0.56  thf(t50_tex_2, conjecture,
% 0.26/0.56    (![A:$i]:
% 0.26/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.26/0.56         ( l1_pre_topc @ A ) ) =>
% 0.26/0.56       ( ![B:$i]:
% 0.26/0.56         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.26/0.56             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.26/0.56           ( ( v3_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.26/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.26/0.56    (~( ![A:$i]:
% 0.26/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.26/0.56            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.26/0.56          ( ![B:$i]:
% 0.26/0.56            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.26/0.56                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.26/0.56              ( ( v3_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.26/0.56    inference('cnf.neg', [status(esa)], [t50_tex_2])).
% 0.26/0.56  thf('0', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.26/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.56  thf('1', plain,
% 0.26/0.56      (~ ((v1_zfmisc_1 @ sk_B_1)) | ~ ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.26/0.56      inference('split', [status(esa)], ['0'])).
% 0.26/0.56  thf('2', plain, (((v1_zfmisc_1 @ sk_B_1) | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.26/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.56  thf('3', plain,
% 0.26/0.56      (((v3_tex_2 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.26/0.56      inference('split', [status(esa)], ['2'])).
% 0.26/0.56  thf('4', plain,
% 0.26/0.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.26/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.56  thf(d7_tex_2, axiom,
% 0.26/0.56    (![A:$i]:
% 0.26/0.56     ( ( l1_pre_topc @ A ) =>
% 0.26/0.56       ( ![B:$i]:
% 0.26/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.26/0.56           ( ( v3_tex_2 @ B @ A ) <=>
% 0.26/0.56             ( ( v2_tex_2 @ B @ A ) & 
% 0.26/0.56               ( ![C:$i]:
% 0.26/0.56                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.26/0.56                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.26/0.56                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.26/0.56  thf('5', plain,
% 0.26/0.56      (![X10 : $i, X11 : $i]:
% 0.26/0.56         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.26/0.56          | ~ (v3_tex_2 @ X10 @ X11)
% 0.26/0.56          | (v2_tex_2 @ X10 @ X11)
% 0.26/0.56          | ~ (l1_pre_topc @ X11))),
% 0.26/0.56      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.26/0.56  thf('6', plain,
% 0.26/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.26/0.56        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.26/0.56        | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.26/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.26/0.56  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.26/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.56  thf('8', plain,
% 0.26/0.56      (((v2_tex_2 @ sk_B_1 @ sk_A) | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.26/0.56      inference('demod', [status(thm)], ['6', '7'])).
% 0.26/0.56  thf('9', plain,
% 0.26/0.56      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.26/0.56      inference('sup-', [status(thm)], ['3', '8'])).
% 0.26/0.56  thf('10', plain,
% 0.26/0.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.26/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.56  thf(t44_tex_2, axiom,
% 0.26/0.56    (![A:$i]:
% 0.26/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.26/0.56         ( l1_pre_topc @ A ) ) =>
% 0.26/0.56       ( ![B:$i]:
% 0.26/0.56         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.26/0.56             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.26/0.56           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.26/0.56  thf('11', plain,
% 0.26/0.56      (![X15 : $i, X16 : $i]:
% 0.26/0.56         ((v1_xboole_0 @ X15)
% 0.26/0.56          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.26/0.56          | ~ (v2_tex_2 @ X15 @ X16)
% 0.26/0.56          | (v1_zfmisc_1 @ X15)
% 0.26/0.56          | ~ (l1_pre_topc @ X16)
% 0.26/0.56          | ~ (v2_tdlat_3 @ X16)
% 0.26/0.56          | ~ (v2_pre_topc @ X16)
% 0.26/0.56          | (v2_struct_0 @ X16))),
% 0.26/0.56      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.26/0.56  thf('12', plain,
% 0.26/0.56      (((v2_struct_0 @ sk_A)
% 0.26/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.26/0.56        | ~ (v2_tdlat_3 @ sk_A)
% 0.26/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.26/0.56        | (v1_zfmisc_1 @ sk_B_1)
% 0.26/0.56        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.26/0.56        | (v1_xboole_0 @ sk_B_1))),
% 0.26/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.26/0.56  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.26/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.56  thf('14', plain, ((v2_tdlat_3 @ sk_A)),
% 0.26/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.56  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.26/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.56  thf('16', plain,
% 0.26/0.56      (((v2_struct_0 @ sk_A)
% 0.26/0.56        | (v1_zfmisc_1 @ sk_B_1)
% 0.26/0.56        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.26/0.56        | (v1_xboole_0 @ sk_B_1))),
% 0.26/0.56      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.26/0.56  thf('17', plain,
% 0.26/0.56      ((((v1_xboole_0 @ sk_B_1) | (v1_zfmisc_1 @ sk_B_1) | (v2_struct_0 @ sk_A)))
% 0.26/0.56         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.26/0.56      inference('sup-', [status(thm)], ['9', '16'])).
% 0.26/0.56  thf('18', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.26/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.56  thf('19', plain,
% 0.26/0.56      ((((v2_struct_0 @ sk_A) | (v1_zfmisc_1 @ sk_B_1)))
% 0.26/0.56         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.26/0.56      inference('clc', [status(thm)], ['17', '18'])).
% 0.26/0.56  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.26/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.56  thf('21', plain,
% 0.26/0.56      (((v1_zfmisc_1 @ sk_B_1)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.26/0.56      inference('clc', [status(thm)], ['19', '20'])).
% 0.26/0.56  thf('22', plain,
% 0.26/0.56      ((~ (v1_zfmisc_1 @ sk_B_1)) <= (~ ((v1_zfmisc_1 @ sk_B_1)))),
% 0.26/0.56      inference('split', [status(esa)], ['0'])).
% 0.26/0.56  thf('23', plain, (((v1_zfmisc_1 @ sk_B_1)) | ~ ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.26/0.56      inference('sup-', [status(thm)], ['21', '22'])).
% 0.26/0.56  thf('24', plain, (((v1_zfmisc_1 @ sk_B_1)) | ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.26/0.56      inference('split', [status(esa)], ['2'])).
% 0.26/0.56  thf('25', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.26/0.56      inference('split', [status(esa)], ['2'])).
% 0.26/0.56  thf('26', plain,
% 0.26/0.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.26/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.56  thf('27', plain,
% 0.26/0.56      (![X15 : $i, X16 : $i]:
% 0.26/0.56         ((v1_xboole_0 @ X15)
% 0.26/0.56          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.26/0.56          | ~ (v1_zfmisc_1 @ X15)
% 0.26/0.56          | (v2_tex_2 @ X15 @ X16)
% 0.26/0.56          | ~ (l1_pre_topc @ X16)
% 0.26/0.56          | ~ (v2_tdlat_3 @ X16)
% 0.26/0.56          | ~ (v2_pre_topc @ X16)
% 0.26/0.56          | (v2_struct_0 @ X16))),
% 0.26/0.56      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.26/0.56  thf('28', plain,
% 0.26/0.56      (((v2_struct_0 @ sk_A)
% 0.26/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.26/0.56        | ~ (v2_tdlat_3 @ sk_A)
% 0.26/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.26/0.56        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.26/0.56        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.26/0.56        | (v1_xboole_0 @ sk_B_1))),
% 0.26/0.56      inference('sup-', [status(thm)], ['26', '27'])).
% 0.26/0.56  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.26/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.56  thf('30', plain, ((v2_tdlat_3 @ sk_A)),
% 0.26/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.56  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.26/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.56  thf('32', plain,
% 0.26/0.56      (((v2_struct_0 @ sk_A)
% 0.26/0.56        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.26/0.56        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.26/0.56        | (v1_xboole_0 @ sk_B_1))),
% 0.26/0.56      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 0.26/0.56  thf('33', plain,
% 0.26/0.56      ((((v1_xboole_0 @ sk_B_1)
% 0.26/0.56         | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.26/0.56         | (v2_struct_0 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.26/0.56      inference('sup-', [status(thm)], ['25', '32'])).
% 0.26/0.56  thf('34', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.26/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.56  thf('35', plain,
% 0.26/0.56      ((((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B_1 @ sk_A)))
% 0.26/0.56         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.26/0.56      inference('clc', [status(thm)], ['33', '34'])).
% 0.26/0.56  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.26/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.56  thf('37', plain,
% 0.26/0.56      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.26/0.56      inference('clc', [status(thm)], ['35', '36'])).
% 0.26/0.56  thf('38', plain,
% 0.26/0.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.26/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.56  thf('39', plain,
% 0.26/0.56      (![X10 : $i, X11 : $i]:
% 0.26/0.56         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.26/0.56          | ~ (v2_tex_2 @ X10 @ X11)
% 0.26/0.56          | (v2_tex_2 @ (sk_C @ X10 @ X11) @ X11)
% 0.26/0.56          | (v3_tex_2 @ X10 @ X11)
% 0.26/0.56          | ~ (l1_pre_topc @ X11))),
% 0.26/0.56      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.26/0.56  thf('40', plain,
% 0.26/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.26/0.56        | (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.26/0.56        | (v2_tex_2 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.26/0.56        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.26/0.56      inference('sup-', [status(thm)], ['38', '39'])).
% 0.26/0.56  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.26/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.56  thf('42', plain,
% 0.26/0.56      (((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.26/0.56        | (v2_tex_2 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.26/0.56        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.26/0.56      inference('demod', [status(thm)], ['40', '41'])).
% 0.26/0.56  thf('43', plain,
% 0.26/0.56      ((((v2_tex_2 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.26/0.56         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.26/0.56      inference('sup-', [status(thm)], ['37', '42'])).
% 0.26/0.56  thf('44', plain,
% 0.26/0.56      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.26/0.56      inference('clc', [status(thm)], ['35', '36'])).
% 0.26/0.56  thf('45', plain,
% 0.26/0.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.26/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.56  thf('46', plain,
% 0.26/0.56      (![X10 : $i, X11 : $i]:
% 0.26/0.56         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.26/0.56          | ~ (v2_tex_2 @ X10 @ X11)
% 0.26/0.56          | (m1_subset_1 @ (sk_C @ X10 @ X11) @ 
% 0.26/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.26/0.56          | (v3_tex_2 @ X10 @ X11)
% 0.26/0.56          | ~ (l1_pre_topc @ X11))),
% 0.26/0.56      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.26/0.56  thf('47', plain,
% 0.26/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.26/0.56        | (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.26/0.56        | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ 
% 0.26/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.26/0.56        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.26/0.56      inference('sup-', [status(thm)], ['45', '46'])).
% 0.26/0.56  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.26/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.56  thf('49', plain,
% 0.26/0.56      (((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.26/0.56        | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ 
% 0.26/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.26/0.56        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.26/0.56      inference('demod', [status(thm)], ['47', '48'])).
% 0.26/0.56  thf('50', plain,
% 0.26/0.56      ((((m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ 
% 0.26/0.56          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.26/0.56         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.26/0.56      inference('sup-', [status(thm)], ['44', '49'])).
% 0.26/0.56  thf('51', plain,
% 0.26/0.56      (![X15 : $i, X16 : $i]:
% 0.26/0.56         ((v1_xboole_0 @ X15)
% 0.26/0.56          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.26/0.56          | ~ (v2_tex_2 @ X15 @ X16)
% 0.26/0.56          | (v1_zfmisc_1 @ X15)
% 0.26/0.56          | ~ (l1_pre_topc @ X16)
% 0.26/0.56          | ~ (v2_tdlat_3 @ X16)
% 0.26/0.56          | ~ (v2_pre_topc @ X16)
% 0.26/0.56          | (v2_struct_0 @ X16))),
% 0.26/0.56      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.26/0.56  thf('52', plain,
% 0.26/0.56      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.26/0.56         | (v2_struct_0 @ sk_A)
% 0.26/0.56         | ~ (v2_pre_topc @ sk_A)
% 0.26/0.56         | ~ (v2_tdlat_3 @ sk_A)
% 0.26/0.56         | ~ (l1_pre_topc @ sk_A)
% 0.26/0.56         | (v1_zfmisc_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.26/0.56         | ~ (v2_tex_2 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.26/0.56         | (v1_xboole_0 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.26/0.56         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.26/0.56      inference('sup-', [status(thm)], ['50', '51'])).
% 0.26/0.56  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.26/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.56  thf('54', plain, ((v2_tdlat_3 @ sk_A)),
% 0.26/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.56  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.26/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.56  thf('56', plain,
% 0.26/0.56      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.26/0.56         | (v2_struct_0 @ sk_A)
% 0.26/0.56         | (v1_zfmisc_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.26/0.56         | ~ (v2_tex_2 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.26/0.56         | (v1_xboole_0 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.26/0.56         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.26/0.56      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 0.26/0.56  thf('57', plain,
% 0.26/0.56      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.26/0.56         | (v1_xboole_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.26/0.56         | (v1_zfmisc_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.26/0.56         | (v2_struct_0 @ sk_A)
% 0.26/0.56         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.26/0.56      inference('sup-', [status(thm)], ['43', '56'])).
% 0.26/0.56  thf('58', plain,
% 0.26/0.56      ((((v2_struct_0 @ sk_A)
% 0.26/0.56         | (v1_zfmisc_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.26/0.56         | (v1_xboole_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.26/0.56         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.26/0.56      inference('simplify', [status(thm)], ['57'])).
% 0.26/0.56  thf('59', plain,
% 0.26/0.56      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.26/0.56      inference('clc', [status(thm)], ['35', '36'])).
% 0.26/0.56  thf('60', plain,
% 0.26/0.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.26/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.56  thf('61', plain,
% 0.26/0.56      (![X10 : $i, X11 : $i]:
% 0.26/0.56         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.26/0.56          | ~ (v2_tex_2 @ X10 @ X11)
% 0.26/0.56          | (r1_tarski @ X10 @ (sk_C @ X10 @ X11))
% 0.26/0.56          | (v3_tex_2 @ X10 @ X11)
% 0.26/0.56          | ~ (l1_pre_topc @ X11))),
% 0.26/0.56      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.26/0.56  thf('62', plain,
% 0.26/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.26/0.56        | (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.26/0.56        | (r1_tarski @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.26/0.56        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.26/0.56      inference('sup-', [status(thm)], ['60', '61'])).
% 0.26/0.56  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.26/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.56  thf('64', plain,
% 0.26/0.56      (((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.26/0.56        | (r1_tarski @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.26/0.56        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.26/0.56      inference('demod', [status(thm)], ['62', '63'])).
% 0.26/0.56  thf('65', plain,
% 0.26/0.56      ((((r1_tarski @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.26/0.56         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.26/0.56      inference('sup-', [status(thm)], ['59', '64'])).
% 0.26/0.56  thf(d1_xboole_0, axiom,
% 0.26/0.56    (![A:$i]:
% 0.26/0.56     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.26/0.56  thf('66', plain,
% 0.26/0.56      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.26/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.26/0.56  thf(l1_zfmisc_1, axiom,
% 0.26/0.56    (![A:$i,B:$i]:
% 0.26/0.56     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.26/0.56  thf('67', plain,
% 0.26/0.56      (![X6 : $i, X8 : $i]:
% 0.26/0.56         ((r1_tarski @ (k1_tarski @ X6) @ X8) | ~ (r2_hidden @ X6 @ X8))),
% 0.26/0.56      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.26/0.56  thf('68', plain,
% 0.26/0.56      (![X0 : $i]:
% 0.26/0.56         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.26/0.56      inference('sup-', [status(thm)], ['66', '67'])).
% 0.26/0.56  thf(t1_tex_2, axiom,
% 0.26/0.56    (![A:$i]:
% 0.26/0.56     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.26/0.56       ( ![B:$i]:
% 0.26/0.56         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.26/0.56           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.26/0.56  thf('69', plain,
% 0.26/0.56      (![X13 : $i, X14 : $i]:
% 0.26/0.56         ((v1_xboole_0 @ X13)
% 0.26/0.56          | ~ (v1_zfmisc_1 @ X13)
% 0.26/0.56          | ((X14) = (X13))
% 0.26/0.56          | ~ (r1_tarski @ X14 @ X13)
% 0.26/0.56          | (v1_xboole_0 @ X14))),
% 0.26/0.56      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.26/0.56  thf('70', plain,
% 0.26/0.56      (![X0 : $i]:
% 0.26/0.56         ((v1_xboole_0 @ X0)
% 0.26/0.56          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.26/0.56          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.26/0.56          | ~ (v1_zfmisc_1 @ X0)
% 0.26/0.56          | (v1_xboole_0 @ X0))),
% 0.26/0.56      inference('sup-', [status(thm)], ['68', '69'])).
% 0.26/0.56  thf('71', plain,
% 0.26/0.56      (![X0 : $i]:
% 0.26/0.56         (~ (v1_zfmisc_1 @ X0)
% 0.26/0.56          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.26/0.56          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.26/0.56          | (v1_xboole_0 @ X0))),
% 0.26/0.56      inference('simplify', [status(thm)], ['70'])).
% 0.26/0.56  thf(d10_xboole_0, axiom,
% 0.26/0.56    (![A:$i,B:$i]:
% 0.26/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.26/0.56  thf('72', plain,
% 0.26/0.56      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 0.26/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.26/0.56  thf('73', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.26/0.56      inference('simplify', [status(thm)], ['72'])).
% 0.26/0.56  thf('74', plain,
% 0.26/0.56      (![X6 : $i, X7 : $i]:
% 0.26/0.56         ((r2_hidden @ X6 @ X7) | ~ (r1_tarski @ (k1_tarski @ X6) @ X7))),
% 0.26/0.56      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.26/0.56  thf('75', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.26/0.56      inference('sup-', [status(thm)], ['73', '74'])).
% 0.26/0.56  thf('76', plain,
% 0.26/0.56      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.26/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.26/0.56  thf('77', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.26/0.56      inference('sup-', [status(thm)], ['75', '76'])).
% 0.26/0.56  thf('78', plain,
% 0.26/0.56      (![X0 : $i]:
% 0.26/0.56         ((v1_xboole_0 @ X0)
% 0.26/0.56          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.26/0.56          | ~ (v1_zfmisc_1 @ X0))),
% 0.26/0.56      inference('sup-', [status(thm)], ['71', '77'])).
% 0.26/0.56  thf('79', plain,
% 0.26/0.56      (![X6 : $i, X7 : $i]:
% 0.26/0.56         ((r2_hidden @ X6 @ X7) | ~ (r1_tarski @ (k1_tarski @ X6) @ X7))),
% 0.26/0.56      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.26/0.56  thf('80', plain,
% 0.26/0.56      (![X0 : $i, X1 : $i]:
% 0.26/0.56         (~ (r1_tarski @ X0 @ X1)
% 0.26/0.56          | ~ (v1_zfmisc_1 @ X0)
% 0.26/0.56          | (v1_xboole_0 @ X0)
% 0.26/0.56          | (r2_hidden @ (sk_B @ X0) @ X1))),
% 0.26/0.56      inference('sup-', [status(thm)], ['78', '79'])).
% 0.26/0.56  thf('81', plain,
% 0.26/0.56      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.26/0.56         | (r2_hidden @ (sk_B @ sk_B_1) @ (sk_C @ sk_B_1 @ sk_A))
% 0.26/0.56         | (v1_xboole_0 @ sk_B_1)
% 0.26/0.56         | ~ (v1_zfmisc_1 @ sk_B_1))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.26/0.56      inference('sup-', [status(thm)], ['65', '80'])).
% 0.26/0.56  thf('82', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.26/0.56      inference('split', [status(esa)], ['2'])).
% 0.26/0.56  thf('83', plain,
% 0.26/0.56      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.26/0.56         | (r2_hidden @ (sk_B @ sk_B_1) @ (sk_C @ sk_B_1 @ sk_A))
% 0.26/0.56         | (v1_xboole_0 @ sk_B_1))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.26/0.56      inference('demod', [status(thm)], ['81', '82'])).
% 0.26/0.56  thf('84', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.26/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.56  thf('85', plain,
% 0.26/0.56      ((((r2_hidden @ (sk_B @ sk_B_1) @ (sk_C @ sk_B_1 @ sk_A))
% 0.26/0.56         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.26/0.56      inference('clc', [status(thm)], ['83', '84'])).
% 0.26/0.56  thf('86', plain,
% 0.26/0.56      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.26/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.26/0.56  thf('87', plain,
% 0.26/0.56      ((((v3_tex_2 @ sk_B_1 @ sk_A) | ~ (v1_xboole_0 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.26/0.56         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.26/0.56      inference('sup-', [status(thm)], ['85', '86'])).
% 0.26/0.56  thf('88', plain,
% 0.26/0.56      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.26/0.56         | (v1_zfmisc_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.26/0.56         | (v2_struct_0 @ sk_A)
% 0.26/0.56         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.26/0.56      inference('sup-', [status(thm)], ['58', '87'])).
% 0.26/0.56  thf('89', plain,
% 0.26/0.56      ((((v2_struct_0 @ sk_A)
% 0.26/0.56         | (v1_zfmisc_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.26/0.56         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.26/0.56      inference('simplify', [status(thm)], ['88'])).
% 0.26/0.56  thf('90', plain, (~ (v2_struct_0 @ sk_A)),
% 0.26/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.56  thf('91', plain,
% 0.26/0.56      ((((v3_tex_2 @ sk_B_1 @ sk_A) | (v1_zfmisc_1 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.26/0.56         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.26/0.56      inference('clc', [status(thm)], ['89', '90'])).
% 0.26/0.56  thf('92', plain,
% 0.26/0.56      ((((r1_tarski @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.26/0.56         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.26/0.56      inference('sup-', [status(thm)], ['59', '64'])).
% 0.26/0.56  thf('93', plain,
% 0.26/0.56      (![X13 : $i, X14 : $i]:
% 0.26/0.56         ((v1_xboole_0 @ X13)
% 0.26/0.56          | ~ (v1_zfmisc_1 @ X13)
% 0.26/0.56          | ((X14) = (X13))
% 0.26/0.56          | ~ (r1_tarski @ X14 @ X13)
% 0.26/0.56          | (v1_xboole_0 @ X14))),
% 0.26/0.56      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.26/0.56  thf('94', plain,
% 0.26/0.56      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.26/0.56         | (v1_xboole_0 @ sk_B_1)
% 0.26/0.56         | ((sk_B_1) = (sk_C @ sk_B_1 @ sk_A))
% 0.26/0.56         | ~ (v1_zfmisc_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.26/0.56         | (v1_xboole_0 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.26/0.56         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.26/0.56      inference('sup-', [status(thm)], ['92', '93'])).
% 0.26/0.56  thf('95', plain,
% 0.26/0.56      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.26/0.56         | (v1_xboole_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.26/0.56         | ((sk_B_1) = (sk_C @ sk_B_1 @ sk_A))
% 0.26/0.56         | (v1_xboole_0 @ sk_B_1)
% 0.26/0.56         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.26/0.56      inference('sup-', [status(thm)], ['91', '94'])).
% 0.26/0.56  thf('96', plain,
% 0.26/0.56      ((((v1_xboole_0 @ sk_B_1)
% 0.26/0.56         | ((sk_B_1) = (sk_C @ sk_B_1 @ sk_A))
% 0.26/0.56         | (v1_xboole_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.26/0.56         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.26/0.56      inference('simplify', [status(thm)], ['95'])).
% 0.26/0.56  thf('97', plain,
% 0.26/0.56      ((((v3_tex_2 @ sk_B_1 @ sk_A) | ~ (v1_xboole_0 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.26/0.56         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.26/0.56      inference('sup-', [status(thm)], ['85', '86'])).
% 0.26/0.56  thf('98', plain,
% 0.26/0.56      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.26/0.56         | ((sk_B_1) = (sk_C @ sk_B_1 @ sk_A))
% 0.26/0.56         | (v1_xboole_0 @ sk_B_1)
% 0.26/0.56         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.26/0.56      inference('sup-', [status(thm)], ['96', '97'])).
% 0.26/0.56  thf('99', plain,
% 0.26/0.56      ((((v1_xboole_0 @ sk_B_1)
% 0.26/0.56         | ((sk_B_1) = (sk_C @ sk_B_1 @ sk_A))
% 0.26/0.56         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.26/0.56      inference('simplify', [status(thm)], ['98'])).
% 0.26/0.56  thf('100', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.26/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.56  thf('101', plain,
% 0.26/0.56      ((((v3_tex_2 @ sk_B_1 @ sk_A) | ((sk_B_1) = (sk_C @ sk_B_1 @ sk_A))))
% 0.26/0.56         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.26/0.56      inference('clc', [status(thm)], ['99', '100'])).
% 0.26/0.56  thf('102', plain,
% 0.26/0.56      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.26/0.56      inference('clc', [status(thm)], ['35', '36'])).
% 0.26/0.56  thf('103', plain,
% 0.26/0.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.26/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.56  thf('104', plain,
% 0.26/0.56      (![X10 : $i, X11 : $i]:
% 0.26/0.56         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.26/0.56          | ~ (v2_tex_2 @ X10 @ X11)
% 0.26/0.56          | ((X10) != (sk_C @ X10 @ X11))
% 0.26/0.56          | (v3_tex_2 @ X10 @ X11)
% 0.26/0.56          | ~ (l1_pre_topc @ X11))),
% 0.26/0.56      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.26/0.56  thf('105', plain,
% 0.26/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.26/0.56        | (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.26/0.56        | ((sk_B_1) != (sk_C @ sk_B_1 @ sk_A))
% 0.26/0.56        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.26/0.56      inference('sup-', [status(thm)], ['103', '104'])).
% 0.26/0.56  thf('106', plain, ((l1_pre_topc @ sk_A)),
% 0.26/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.56  thf('107', plain,
% 0.26/0.56      (((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.26/0.56        | ((sk_B_1) != (sk_C @ sk_B_1 @ sk_A))
% 0.26/0.56        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.26/0.56      inference('demod', [status(thm)], ['105', '106'])).
% 0.26/0.56  thf('108', plain,
% 0.26/0.56      (((((sk_B_1) != (sk_C @ sk_B_1 @ sk_A)) | (v3_tex_2 @ sk_B_1 @ sk_A)))
% 0.26/0.56         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.26/0.56      inference('sup-', [status(thm)], ['102', '107'])).
% 0.26/0.56  thf('109', plain,
% 0.26/0.56      (((v3_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.26/0.56      inference('clc', [status(thm)], ['101', '108'])).
% 0.26/0.56  thf('110', plain,
% 0.26/0.56      ((~ (v3_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.26/0.56      inference('split', [status(esa)], ['0'])).
% 0.26/0.56  thf('111', plain,
% 0.26/0.56      (~ ((v1_zfmisc_1 @ sk_B_1)) | ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.26/0.56      inference('sup-', [status(thm)], ['109', '110'])).
% 0.26/0.56  thf('112', plain, ($false),
% 0.26/0.56      inference('sat_resolution*', [status(thm)], ['1', '23', '24', '111'])).
% 0.26/0.56  
% 0.26/0.56  % SZS output end Refutation
% 0.26/0.56  
% 0.42/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
