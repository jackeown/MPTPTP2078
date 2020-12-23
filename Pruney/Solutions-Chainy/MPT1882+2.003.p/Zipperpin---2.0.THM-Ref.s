%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dsibRwdRHZ

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:19 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 382 expanded)
%              Number of leaves         :   24 ( 114 expanded)
%              Depth                    :   23
%              Number of atoms          : 1006 (4903 expanded)
%              Number of equality atoms :   15 (  23 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v3_tex_2 @ X14 @ X15 )
      | ( v2_tex_2 @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v2_tex_2 @ X19 @ X20 )
      | ( v1_zfmisc_1 @ X19 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_tdlat_3 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v1_zfmisc_1 @ X19 )
      | ( v2_tex_2 @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_tdlat_3 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v2_tex_2 @ X14 @ X15 )
      | ( v2_tex_2 @ ( sk_C_1 @ X14 @ X15 ) @ X15 )
      | ( v3_tex_2 @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('40',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v2_tex_2 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v2_tex_2 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( v2_tex_2 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
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
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v2_tex_2 @ X14 @ X15 )
      | ( m1_subset_1 @ ( sk_C_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v3_tex_2 @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('47',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( m1_subset_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v2_tex_2 @ X19 @ X20 )
      | ( v1_zfmisc_1 @ X19 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_tdlat_3 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t44_tex_2])).

thf('52',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v2_tdlat_3 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v2_tex_2 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
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
      | ( v1_zfmisc_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v2_tex_2 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['52','53','54','55'])).

thf('57',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v1_zfmisc_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['43','56'])).

thf('58',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
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
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v2_tex_2 @ X14 @ X15 )
      | ( r1_tarski @ X14 @ ( sk_C_1 @ X14 @ X15 ) )
      | ( v3_tex_2 @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('62',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( r1_tarski @ sk_B_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( r1_tarski @ sk_B_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( r1_tarski @ sk_B_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['59','64'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('66',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ( X5
       != ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('67',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['65','67'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('69',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( m1_subset_1 @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('71',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('73',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_xboole_0 @ X11 )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('74',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ~ ( v1_xboole_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( ~ ( v1_xboole_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['58','76'])).

thf('78',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( r1_tarski @ sk_B_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['59','64'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('82',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( v1_zfmisc_1 @ X17 )
      | ( X18 = X17 )
      | ~ ( r1_tarski @ X18 @ X17 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('83',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( sk_B_1
        = ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_zfmisc_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( sk_B_1
        = ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( sk_B_1
        = ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,
    ( ( ~ ( v1_xboole_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('87',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( sk_B_1
        = ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( sk_B_1
        = ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( sk_B_1
        = ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('92',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v2_tex_2 @ X14 @ X15 )
      | ( X14
       != ( sk_C_1 @ X14 @ X15 ) )
      | ( v3_tex_2 @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('94',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( sk_B_1
     != ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( sk_B_1
     != ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ( sk_B_1
       != ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['91','96'])).

thf('98',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['90','97'])).

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
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dsibRwdRHZ
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:29:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.55  % Solved by: fo/fo7.sh
% 0.35/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.55  % done 121 iterations in 0.086s
% 0.35/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.55  % SZS output start Refutation
% 0.35/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.55  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.35/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.55  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.35/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.35/0.55  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.35/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.35/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.35/0.55  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.35/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.35/0.55  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.35/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.35/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.35/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.55  thf(t50_tex_2, conjecture,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.35/0.55         ( l1_pre_topc @ A ) ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.35/0.55             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.35/0.55           ( ( v3_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.35/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.55    (~( ![A:$i]:
% 0.35/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.35/0.55            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.55          ( ![B:$i]:
% 0.35/0.55            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.35/0.55                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.35/0.55              ( ( v3_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.35/0.55    inference('cnf.neg', [status(esa)], [t50_tex_2])).
% 0.35/0.55  thf('0', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('1', plain,
% 0.35/0.55      (~ ((v1_zfmisc_1 @ sk_B_1)) | ~ ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.35/0.55      inference('split', [status(esa)], ['0'])).
% 0.35/0.55  thf('2', plain, (((v1_zfmisc_1 @ sk_B_1) | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('3', plain,
% 0.35/0.55      (((v3_tex_2 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.35/0.55      inference('split', [status(esa)], ['2'])).
% 0.35/0.55  thf('4', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(d7_tex_2, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( l1_pre_topc @ A ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.55           ( ( v3_tex_2 @ B @ A ) <=>
% 0.35/0.55             ( ( v2_tex_2 @ B @ A ) & 
% 0.35/0.55               ( ![C:$i]:
% 0.35/0.55                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.55                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.35/0.55                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.35/0.55  thf('5', plain,
% 0.35/0.55      (![X14 : $i, X15 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.35/0.55          | ~ (v3_tex_2 @ X14 @ X15)
% 0.35/0.55          | (v2_tex_2 @ X14 @ X15)
% 0.35/0.55          | ~ (l1_pre_topc @ X15))),
% 0.35/0.55      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.35/0.55  thf('6', plain,
% 0.35/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.35/0.55        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.35/0.55        | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.35/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.35/0.55  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('8', plain,
% 0.35/0.55      (((v2_tex_2 @ sk_B_1 @ sk_A) | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.35/0.55      inference('demod', [status(thm)], ['6', '7'])).
% 0.35/0.55  thf('9', plain,
% 0.35/0.55      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['3', '8'])).
% 0.35/0.55  thf('10', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(t44_tex_2, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.35/0.55         ( l1_pre_topc @ A ) ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.35/0.55             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.35/0.55           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.35/0.55  thf('11', plain,
% 0.35/0.55      (![X19 : $i, X20 : $i]:
% 0.35/0.55         ((v1_xboole_0 @ X19)
% 0.35/0.55          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.35/0.55          | ~ (v2_tex_2 @ X19 @ X20)
% 0.35/0.55          | (v1_zfmisc_1 @ X19)
% 0.35/0.55          | ~ (l1_pre_topc @ X20)
% 0.35/0.55          | ~ (v2_tdlat_3 @ X20)
% 0.35/0.55          | ~ (v2_pre_topc @ X20)
% 0.35/0.55          | (v2_struct_0 @ X20))),
% 0.35/0.55      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.35/0.55  thf('12', plain,
% 0.35/0.55      (((v2_struct_0 @ sk_A)
% 0.35/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.35/0.55        | ~ (v2_tdlat_3 @ sk_A)
% 0.35/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.35/0.55        | (v1_zfmisc_1 @ sk_B_1)
% 0.35/0.55        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.35/0.55        | (v1_xboole_0 @ sk_B_1))),
% 0.35/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.35/0.55  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('14', plain, ((v2_tdlat_3 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('16', plain,
% 0.35/0.55      (((v2_struct_0 @ sk_A)
% 0.35/0.55        | (v1_zfmisc_1 @ sk_B_1)
% 0.35/0.55        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.35/0.55        | (v1_xboole_0 @ sk_B_1))),
% 0.35/0.55      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.35/0.55  thf('17', plain,
% 0.35/0.55      ((((v1_xboole_0 @ sk_B_1) | (v1_zfmisc_1 @ sk_B_1) | (v2_struct_0 @ sk_A)))
% 0.35/0.55         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['9', '16'])).
% 0.35/0.55  thf('18', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('19', plain,
% 0.35/0.55      ((((v2_struct_0 @ sk_A) | (v1_zfmisc_1 @ sk_B_1)))
% 0.35/0.55         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.35/0.55      inference('clc', [status(thm)], ['17', '18'])).
% 0.35/0.55  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('21', plain,
% 0.35/0.55      (((v1_zfmisc_1 @ sk_B_1)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.35/0.55      inference('clc', [status(thm)], ['19', '20'])).
% 0.35/0.55  thf('22', plain,
% 0.35/0.55      ((~ (v1_zfmisc_1 @ sk_B_1)) <= (~ ((v1_zfmisc_1 @ sk_B_1)))),
% 0.35/0.55      inference('split', [status(esa)], ['0'])).
% 0.35/0.55  thf('23', plain, (((v1_zfmisc_1 @ sk_B_1)) | ~ ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.35/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.35/0.55  thf('24', plain, (((v1_zfmisc_1 @ sk_B_1)) | ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.35/0.55      inference('split', [status(esa)], ['2'])).
% 0.35/0.55  thf('25', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.35/0.55      inference('split', [status(esa)], ['2'])).
% 0.35/0.55  thf('26', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('27', plain,
% 0.35/0.55      (![X19 : $i, X20 : $i]:
% 0.35/0.55         ((v1_xboole_0 @ X19)
% 0.35/0.55          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.35/0.55          | ~ (v1_zfmisc_1 @ X19)
% 0.35/0.55          | (v2_tex_2 @ X19 @ X20)
% 0.35/0.55          | ~ (l1_pre_topc @ X20)
% 0.35/0.55          | ~ (v2_tdlat_3 @ X20)
% 0.35/0.55          | ~ (v2_pre_topc @ X20)
% 0.35/0.55          | (v2_struct_0 @ X20))),
% 0.35/0.55      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.35/0.55  thf('28', plain,
% 0.35/0.55      (((v2_struct_0 @ sk_A)
% 0.35/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.35/0.55        | ~ (v2_tdlat_3 @ sk_A)
% 0.35/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.35/0.55        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.35/0.55        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.35/0.55        | (v1_xboole_0 @ sk_B_1))),
% 0.35/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.35/0.55  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('30', plain, ((v2_tdlat_3 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('32', plain,
% 0.35/0.55      (((v2_struct_0 @ sk_A)
% 0.35/0.55        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.35/0.55        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.35/0.55        | (v1_xboole_0 @ sk_B_1))),
% 0.35/0.55      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 0.35/0.55  thf('33', plain,
% 0.35/0.55      ((((v1_xboole_0 @ sk_B_1)
% 0.35/0.55         | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.35/0.55         | (v2_struct_0 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['25', '32'])).
% 0.35/0.55  thf('34', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('35', plain,
% 0.35/0.55      ((((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B_1 @ sk_A)))
% 0.35/0.55         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.35/0.55      inference('clc', [status(thm)], ['33', '34'])).
% 0.35/0.55  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('37', plain,
% 0.35/0.55      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.35/0.55      inference('clc', [status(thm)], ['35', '36'])).
% 0.35/0.55  thf('38', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('39', plain,
% 0.35/0.55      (![X14 : $i, X15 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.35/0.55          | ~ (v2_tex_2 @ X14 @ X15)
% 0.35/0.55          | (v2_tex_2 @ (sk_C_1 @ X14 @ X15) @ X15)
% 0.35/0.55          | (v3_tex_2 @ X14 @ X15)
% 0.35/0.55          | ~ (l1_pre_topc @ X15))),
% 0.35/0.55      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.35/0.55  thf('40', plain,
% 0.35/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.35/0.55        | (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.35/0.55        | (v2_tex_2 @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.35/0.55        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.35/0.55      inference('sup-', [status(thm)], ['38', '39'])).
% 0.35/0.55  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('42', plain,
% 0.35/0.55      (((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.35/0.55        | (v2_tex_2 @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.35/0.55        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.35/0.55      inference('demod', [status(thm)], ['40', '41'])).
% 0.35/0.55  thf('43', plain,
% 0.35/0.55      ((((v2_tex_2 @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.35/0.55         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['37', '42'])).
% 0.35/0.55  thf('44', plain,
% 0.35/0.55      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.35/0.55      inference('clc', [status(thm)], ['35', '36'])).
% 0.35/0.55  thf('45', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('46', plain,
% 0.35/0.55      (![X14 : $i, X15 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.35/0.55          | ~ (v2_tex_2 @ X14 @ X15)
% 0.35/0.55          | (m1_subset_1 @ (sk_C_1 @ X14 @ X15) @ 
% 0.35/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.35/0.55          | (v3_tex_2 @ X14 @ X15)
% 0.35/0.55          | ~ (l1_pre_topc @ X15))),
% 0.35/0.55      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.35/0.55  thf('47', plain,
% 0.35/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.35/0.55        | (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.35/0.55        | (m1_subset_1 @ (sk_C_1 @ sk_B_1 @ sk_A) @ 
% 0.35/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.55        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.35/0.55      inference('sup-', [status(thm)], ['45', '46'])).
% 0.35/0.55  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('49', plain,
% 0.35/0.55      (((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.35/0.55        | (m1_subset_1 @ (sk_C_1 @ sk_B_1 @ sk_A) @ 
% 0.35/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.55        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.35/0.55      inference('demod', [status(thm)], ['47', '48'])).
% 0.35/0.55  thf('50', plain,
% 0.35/0.55      ((((m1_subset_1 @ (sk_C_1 @ sk_B_1 @ sk_A) @ 
% 0.35/0.55          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.55         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['44', '49'])).
% 0.35/0.55  thf('51', plain,
% 0.35/0.55      (![X19 : $i, X20 : $i]:
% 0.35/0.55         ((v1_xboole_0 @ X19)
% 0.35/0.55          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.35/0.55          | ~ (v2_tex_2 @ X19 @ X20)
% 0.35/0.55          | (v1_zfmisc_1 @ X19)
% 0.35/0.55          | ~ (l1_pre_topc @ X20)
% 0.35/0.55          | ~ (v2_tdlat_3 @ X20)
% 0.35/0.55          | ~ (v2_pre_topc @ X20)
% 0.35/0.55          | (v2_struct_0 @ X20))),
% 0.35/0.55      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.35/0.55  thf('52', plain,
% 0.35/0.55      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.35/0.55         | (v2_struct_0 @ sk_A)
% 0.35/0.55         | ~ (v2_pre_topc @ sk_A)
% 0.35/0.55         | ~ (v2_tdlat_3 @ sk_A)
% 0.35/0.55         | ~ (l1_pre_topc @ sk_A)
% 0.35/0.55         | (v1_zfmisc_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.35/0.55         | ~ (v2_tex_2 @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.35/0.55         | (v1_xboole_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.35/0.55         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['50', '51'])).
% 0.35/0.55  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('54', plain, ((v2_tdlat_3 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('56', plain,
% 0.35/0.55      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.35/0.55         | (v2_struct_0 @ sk_A)
% 0.35/0.55         | (v1_zfmisc_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.35/0.55         | ~ (v2_tex_2 @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.35/0.55         | (v1_xboole_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.35/0.55         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.35/0.55      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 0.35/0.55  thf('57', plain,
% 0.35/0.55      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.35/0.55         | (v1_xboole_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.35/0.55         | (v1_zfmisc_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.35/0.55         | (v2_struct_0 @ sk_A)
% 0.35/0.55         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['43', '56'])).
% 0.35/0.55  thf('58', plain,
% 0.35/0.55      ((((v2_struct_0 @ sk_A)
% 0.35/0.55         | (v1_zfmisc_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.35/0.55         | (v1_xboole_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.35/0.55         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.35/0.55      inference('simplify', [status(thm)], ['57'])).
% 0.35/0.55  thf('59', plain,
% 0.35/0.55      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.35/0.55      inference('clc', [status(thm)], ['35', '36'])).
% 0.35/0.55  thf('60', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('61', plain,
% 0.35/0.55      (![X14 : $i, X15 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.35/0.55          | ~ (v2_tex_2 @ X14 @ X15)
% 0.35/0.55          | (r1_tarski @ X14 @ (sk_C_1 @ X14 @ X15))
% 0.35/0.55          | (v3_tex_2 @ X14 @ X15)
% 0.35/0.55          | ~ (l1_pre_topc @ X15))),
% 0.35/0.55      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.35/0.55  thf('62', plain,
% 0.35/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.35/0.55        | (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.35/0.55        | (r1_tarski @ sk_B_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.35/0.55        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.35/0.55      inference('sup-', [status(thm)], ['60', '61'])).
% 0.35/0.55  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('64', plain,
% 0.35/0.55      (((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.35/0.55        | (r1_tarski @ sk_B_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.35/0.55        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.35/0.55      inference('demod', [status(thm)], ['62', '63'])).
% 0.35/0.55  thf('65', plain,
% 0.35/0.55      ((((r1_tarski @ sk_B_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.35/0.55         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['59', '64'])).
% 0.35/0.55  thf(d1_zfmisc_1, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.35/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.35/0.55  thf('66', plain,
% 0.35/0.55      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.35/0.55         (~ (r1_tarski @ X3 @ X4)
% 0.35/0.55          | (r2_hidden @ X3 @ X5)
% 0.35/0.55          | ((X5) != (k1_zfmisc_1 @ X4)))),
% 0.35/0.55      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.35/0.55  thf('67', plain,
% 0.35/0.55      (![X3 : $i, X4 : $i]:
% 0.35/0.55         ((r2_hidden @ X3 @ (k1_zfmisc_1 @ X4)) | ~ (r1_tarski @ X3 @ X4))),
% 0.35/0.55      inference('simplify', [status(thm)], ['66'])).
% 0.35/0.55  thf('68', plain,
% 0.35/0.55      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.35/0.55         | (r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ (sk_C_1 @ sk_B_1 @ sk_A)))))
% 0.35/0.55         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['65', '67'])).
% 0.35/0.55  thf(d2_subset_1, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( ( v1_xboole_0 @ A ) =>
% 0.35/0.55         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.35/0.55       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.35/0.55         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.35/0.55  thf('69', plain,
% 0.35/0.55      (![X8 : $i, X9 : $i]:
% 0.35/0.55         (~ (r2_hidden @ X8 @ X9)
% 0.35/0.55          | (m1_subset_1 @ X8 @ X9)
% 0.35/0.55          | (v1_xboole_0 @ X9))),
% 0.35/0.55      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.35/0.55  thf(d1_xboole_0, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.35/0.55  thf('70', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.35/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.35/0.55  thf('71', plain,
% 0.35/0.55      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 0.35/0.55      inference('clc', [status(thm)], ['69', '70'])).
% 0.35/0.55  thf('72', plain,
% 0.35/0.55      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.35/0.55         | (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (sk_C_1 @ sk_B_1 @ sk_A)))))
% 0.35/0.55         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['68', '71'])).
% 0.35/0.55  thf(cc1_subset_1, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( v1_xboole_0 @ A ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.35/0.55  thf('73', plain,
% 0.35/0.55      (![X11 : $i, X12 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.35/0.55          | (v1_xboole_0 @ X11)
% 0.35/0.55          | ~ (v1_xboole_0 @ X12))),
% 0.35/0.55      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.35/0.55  thf('74', plain,
% 0.35/0.55      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.35/0.55         | ~ (v1_xboole_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.35/0.55         | (v1_xboole_0 @ sk_B_1))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['72', '73'])).
% 0.35/0.55  thf('75', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('76', plain,
% 0.35/0.55      (((~ (v1_xboole_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.35/0.55         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.35/0.55      inference('clc', [status(thm)], ['74', '75'])).
% 0.35/0.55  thf('77', plain,
% 0.35/0.55      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.35/0.55         | (v1_zfmisc_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.35/0.55         | (v2_struct_0 @ sk_A)
% 0.35/0.55         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['58', '76'])).
% 0.35/0.55  thf('78', plain,
% 0.35/0.55      ((((v2_struct_0 @ sk_A)
% 0.35/0.55         | (v1_zfmisc_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.35/0.55         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.35/0.55      inference('simplify', [status(thm)], ['77'])).
% 0.35/0.55  thf('79', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('80', plain,
% 0.35/0.55      ((((v3_tex_2 @ sk_B_1 @ sk_A) | (v1_zfmisc_1 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.35/0.55         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.35/0.55      inference('clc', [status(thm)], ['78', '79'])).
% 0.35/0.55  thf('81', plain,
% 0.35/0.55      ((((r1_tarski @ sk_B_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.35/0.55         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['59', '64'])).
% 0.35/0.55  thf(t1_tex_2, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.35/0.55           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.35/0.55  thf('82', plain,
% 0.35/0.55      (![X17 : $i, X18 : $i]:
% 0.35/0.55         ((v1_xboole_0 @ X17)
% 0.35/0.55          | ~ (v1_zfmisc_1 @ X17)
% 0.35/0.55          | ((X18) = (X17))
% 0.35/0.55          | ~ (r1_tarski @ X18 @ X17)
% 0.35/0.55          | (v1_xboole_0 @ X18))),
% 0.35/0.55      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.35/0.55  thf('83', plain,
% 0.35/0.55      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.35/0.55         | (v1_xboole_0 @ sk_B_1)
% 0.35/0.55         | ((sk_B_1) = (sk_C_1 @ sk_B_1 @ sk_A))
% 0.35/0.55         | ~ (v1_zfmisc_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.35/0.55         | (v1_xboole_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.35/0.55         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['81', '82'])).
% 0.35/0.55  thf('84', plain,
% 0.35/0.55      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.35/0.55         | (v1_xboole_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.35/0.55         | ((sk_B_1) = (sk_C_1 @ sk_B_1 @ sk_A))
% 0.35/0.55         | (v1_xboole_0 @ sk_B_1)
% 0.35/0.55         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['80', '83'])).
% 0.35/0.55  thf('85', plain,
% 0.35/0.55      ((((v1_xboole_0 @ sk_B_1)
% 0.35/0.55         | ((sk_B_1) = (sk_C_1 @ sk_B_1 @ sk_A))
% 0.35/0.55         | (v1_xboole_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.35/0.55         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.35/0.55      inference('simplify', [status(thm)], ['84'])).
% 0.35/0.55  thf('86', plain,
% 0.35/0.55      (((~ (v1_xboole_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.35/0.55         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.35/0.55      inference('clc', [status(thm)], ['74', '75'])).
% 0.35/0.55  thf('87', plain,
% 0.35/0.55      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.35/0.55         | ((sk_B_1) = (sk_C_1 @ sk_B_1 @ sk_A))
% 0.35/0.55         | (v1_xboole_0 @ sk_B_1)
% 0.35/0.55         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['85', '86'])).
% 0.35/0.55  thf('88', plain,
% 0.35/0.55      ((((v1_xboole_0 @ sk_B_1)
% 0.35/0.55         | ((sk_B_1) = (sk_C_1 @ sk_B_1 @ sk_A))
% 0.35/0.55         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.35/0.55      inference('simplify', [status(thm)], ['87'])).
% 0.35/0.55  thf('89', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('90', plain,
% 0.35/0.55      ((((v3_tex_2 @ sk_B_1 @ sk_A) | ((sk_B_1) = (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.35/0.55         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.35/0.55      inference('clc', [status(thm)], ['88', '89'])).
% 0.35/0.55  thf('91', plain,
% 0.35/0.55      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.35/0.55      inference('clc', [status(thm)], ['35', '36'])).
% 0.35/0.55  thf('92', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('93', plain,
% 0.35/0.55      (![X14 : $i, X15 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.35/0.55          | ~ (v2_tex_2 @ X14 @ X15)
% 0.35/0.55          | ((X14) != (sk_C_1 @ X14 @ X15))
% 0.35/0.55          | (v3_tex_2 @ X14 @ X15)
% 0.35/0.55          | ~ (l1_pre_topc @ X15))),
% 0.35/0.55      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.35/0.55  thf('94', plain,
% 0.35/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.35/0.55        | (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.35/0.55        | ((sk_B_1) != (sk_C_1 @ sk_B_1 @ sk_A))
% 0.35/0.55        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.35/0.55      inference('sup-', [status(thm)], ['92', '93'])).
% 0.35/0.55  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('96', plain,
% 0.35/0.55      (((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.35/0.55        | ((sk_B_1) != (sk_C_1 @ sk_B_1 @ sk_A))
% 0.35/0.55        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.35/0.55      inference('demod', [status(thm)], ['94', '95'])).
% 0.35/0.55  thf('97', plain,
% 0.35/0.55      (((((sk_B_1) != (sk_C_1 @ sk_B_1 @ sk_A)) | (v3_tex_2 @ sk_B_1 @ sk_A)))
% 0.35/0.55         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['91', '96'])).
% 0.35/0.55  thf('98', plain,
% 0.35/0.55      (((v3_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.35/0.55      inference('clc', [status(thm)], ['90', '97'])).
% 0.35/0.55  thf('99', plain,
% 0.35/0.55      ((~ (v3_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.35/0.55      inference('split', [status(esa)], ['0'])).
% 0.35/0.55  thf('100', plain,
% 0.35/0.55      (~ ((v1_zfmisc_1 @ sk_B_1)) | ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.35/0.55      inference('sup-', [status(thm)], ['98', '99'])).
% 0.35/0.55  thf('101', plain, ($false),
% 0.35/0.55      inference('sat_resolution*', [status(thm)], ['1', '23', '24', '100'])).
% 0.35/0.55  
% 0.35/0.55  % SZS output end Refutation
% 0.35/0.55  
% 0.38/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
