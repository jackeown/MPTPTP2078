%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kavLuZ9Qnf

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 375 expanded)
%              Number of leaves         :   23 ( 113 expanded)
%              Depth                    :   23
%              Number of atoms          :  962 (4825 expanded)
%              Number of equality atoms :   13 (  19 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

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
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v3_tex_2 @ X7 @ X8 )
      | ( v2_tex_2 @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v2_tex_2 @ X12 @ X13 )
      | ( v1_zfmisc_1 @ X12 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_tdlat_3 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v1_zfmisc_1 @ X12 )
      | ( v2_tex_2 @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_tdlat_3 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v2_tex_2 @ X7 @ X8 )
      | ( v2_tex_2 @ ( sk_C_1 @ X7 @ X8 ) @ X8 )
      | ( v3_tex_2 @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v2_tex_2 @ X7 @ X8 )
      | ( m1_subset_1 @ ( sk_C_1 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v3_tex_2 @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v2_tex_2 @ X12 @ X13 )
      | ( v1_zfmisc_1 @ X12 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_tdlat_3 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
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

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('59',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('60',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('61',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v2_tex_2 @ X7 @ X8 )
      | ( r1_tarski @ X7 @ ( sk_C_1 @ X7 @ X8 ) )
      | ( v3_tex_2 @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('63',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( r1_tarski @ sk_B_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( r1_tarski @ sk_B_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( r1_tarski @ sk_B_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('67',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('68',plain,
    ( ! [X0: $i] :
        ( ( v3_tex_2 @ sk_B_1 @ sk_A )
        | ( r2_hidden @ X0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['59','68'])).

thf('70',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('73',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ~ ( v1_xboole_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['58','73'])).

thf('75',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( r1_tarski @ sk_B_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('79',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v1_xboole_0 @ X10 )
      | ~ ( v1_zfmisc_1 @ X10 )
      | ( X11 = X10 )
      | ~ ( r1_tarski @ X11 @ X10 )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('80',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( sk_B_1
        = ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_zfmisc_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( sk_B_1
        = ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( sk_B_1
        = ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ~ ( v1_xboole_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('84',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( sk_B_1
        = ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( sk_B_1
        = ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( sk_B_1
        = ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('89',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v2_tex_2 @ X7 @ X8 )
      | ( X7
       != ( sk_C_1 @ X7 @ X8 ) )
      | ( v3_tex_2 @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('91',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( sk_B_1
     != ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( sk_B_1
     != ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( sk_B_1
       != ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['88','93'])).

thf('95',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['87','94'])).

thf('96',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('97',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','23','24','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kavLuZ9Qnf
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:04:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 61 iterations in 0.032s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.48  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.21/0.48  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.48  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.21/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.48  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.21/0.48  thf(t50_tex_2, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.21/0.48         ( l1_pre_topc @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.48             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.48           ( ( v3_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.48            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.48          ( ![B:$i]:
% 0.21/0.48            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.48                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.48              ( ( v3_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t50_tex_2])).
% 0.21/0.48  thf('0', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (~ ((v1_zfmisc_1 @ sk_B_1)) | ~ ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('2', plain, (((v1_zfmisc_1 @ sk_B_1) | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (((v3_tex_2 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.48      inference('split', [status(esa)], ['2'])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(d7_tex_2, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_pre_topc @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48           ( ( v3_tex_2 @ B @ A ) <=>
% 0.21/0.48             ( ( v2_tex_2 @ B @ A ) & 
% 0.21/0.48               ( ![C:$i]:
% 0.21/0.48                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.48                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.48          | ~ (v3_tex_2 @ X7 @ X8)
% 0.21/0.48          | (v2_tex_2 @ X7 @ X8)
% 0.21/0.48          | ~ (l1_pre_topc @ X8))),
% 0.21/0.48      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.48        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.48        | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.48  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (((v2_tex_2 @ sk_B_1 @ sk_A) | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['3', '8'])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t44_tex_2, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.21/0.48         ( l1_pre_topc @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.48             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.48           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (![X12 : $i, X13 : $i]:
% 0.21/0.48         ((v1_xboole_0 @ X12)
% 0.21/0.48          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.48          | ~ (v2_tex_2 @ X12 @ X13)
% 0.21/0.48          | (v1_zfmisc_1 @ X12)
% 0.21/0.48          | ~ (l1_pre_topc @ X13)
% 0.21/0.48          | ~ (v2_tdlat_3 @ X13)
% 0.21/0.48          | ~ (v2_pre_topc @ X13)
% 0.21/0.48          | (v2_struct_0 @ X13))),
% 0.21/0.48      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_A)
% 0.21/0.48        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.48        | ~ (v2_tdlat_3 @ sk_A)
% 0.21/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.48        | (v1_zfmisc_1 @ sk_B_1)
% 0.21/0.48        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.48        | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.48  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('14', plain, ((v2_tdlat_3 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_A)
% 0.21/0.48        | (v1_zfmisc_1 @ sk_B_1)
% 0.21/0.48        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.48        | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.48      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      ((((v1_xboole_0 @ sk_B_1) | (v1_zfmisc_1 @ sk_B_1) | (v2_struct_0 @ sk_A)))
% 0.21/0.48         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['9', '16'])).
% 0.21/0.48  thf('18', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      ((((v2_struct_0 @ sk_A) | (v1_zfmisc_1 @ sk_B_1)))
% 0.21/0.48         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.48      inference('clc', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (((v1_zfmisc_1 @ sk_B_1)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.48      inference('clc', [status(thm)], ['19', '20'])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      ((~ (v1_zfmisc_1 @ sk_B_1)) <= (~ ((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('23', plain, (((v1_zfmisc_1 @ sk_B_1)) | ~ ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.48  thf('24', plain, (((v1_zfmisc_1 @ sk_B_1)) | ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.48      inference('split', [status(esa)], ['2'])).
% 0.21/0.48  thf('25', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.48      inference('split', [status(esa)], ['2'])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (![X12 : $i, X13 : $i]:
% 0.21/0.48         ((v1_xboole_0 @ X12)
% 0.21/0.48          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.48          | ~ (v1_zfmisc_1 @ X12)
% 0.21/0.48          | (v2_tex_2 @ X12 @ X13)
% 0.21/0.48          | ~ (l1_pre_topc @ X13)
% 0.21/0.48          | ~ (v2_tdlat_3 @ X13)
% 0.21/0.48          | ~ (v2_pre_topc @ X13)
% 0.21/0.48          | (v2_struct_0 @ X13))),
% 0.21/0.48      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_A)
% 0.21/0.48        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.48        | ~ (v2_tdlat_3 @ sk_A)
% 0.21/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.48        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.48        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.21/0.48        | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.48  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('30', plain, ((v2_tdlat_3 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('32', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_A)
% 0.21/0.48        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.48        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.21/0.48        | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.48      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 0.21/0.48  thf('33', plain,
% 0.21/0.48      ((((v1_xboole_0 @ sk_B_1)
% 0.21/0.48         | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.48         | (v2_struct_0 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['25', '32'])).
% 0.21/0.48  thf('34', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('35', plain,
% 0.21/0.48      ((((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B_1 @ sk_A)))
% 0.21/0.48         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.48      inference('clc', [status(thm)], ['33', '34'])).
% 0.21/0.48  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('37', plain,
% 0.21/0.48      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.48      inference('clc', [status(thm)], ['35', '36'])).
% 0.21/0.48  thf('38', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('39', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.48          | ~ (v2_tex_2 @ X7 @ X8)
% 0.21/0.48          | (v2_tex_2 @ (sk_C_1 @ X7 @ X8) @ X8)
% 0.21/0.48          | (v3_tex_2 @ X7 @ X8)
% 0.21/0.48          | ~ (l1_pre_topc @ X8))),
% 0.21/0.48      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.21/0.48  thf('40', plain,
% 0.21/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.48        | (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.48        | (v2_tex_2 @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.21/0.48        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.48  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('42', plain,
% 0.21/0.48      (((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.48        | (v2_tex_2 @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.21/0.48        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.48  thf('43', plain,
% 0.21/0.48      ((((v2_tex_2 @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.21/0.48         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['37', '42'])).
% 0.21/0.48  thf('44', plain,
% 0.21/0.48      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.48      inference('clc', [status(thm)], ['35', '36'])).
% 0.21/0.48  thf('45', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('46', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.48          | ~ (v2_tex_2 @ X7 @ X8)
% 0.21/0.48          | (m1_subset_1 @ (sk_C_1 @ X7 @ X8) @ 
% 0.21/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.48          | (v3_tex_2 @ X7 @ X8)
% 0.21/0.48          | ~ (l1_pre_topc @ X8))),
% 0.21/0.48      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.21/0.48  thf('47', plain,
% 0.21/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.48        | (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.48        | (m1_subset_1 @ (sk_C_1 @ sk_B_1 @ sk_A) @ 
% 0.21/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.48        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.48  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('49', plain,
% 0.21/0.48      (((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.48        | (m1_subset_1 @ (sk_C_1 @ sk_B_1 @ sk_A) @ 
% 0.21/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.48        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['47', '48'])).
% 0.21/0.48  thf('50', plain,
% 0.21/0.48      ((((m1_subset_1 @ (sk_C_1 @ sk_B_1 @ sk_A) @ 
% 0.21/0.48          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.48         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['44', '49'])).
% 0.21/0.48  thf('51', plain,
% 0.21/0.48      (![X12 : $i, X13 : $i]:
% 0.21/0.48         ((v1_xboole_0 @ X12)
% 0.21/0.48          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.48          | ~ (v2_tex_2 @ X12 @ X13)
% 0.21/0.48          | (v1_zfmisc_1 @ X12)
% 0.21/0.48          | ~ (l1_pre_topc @ X13)
% 0.21/0.48          | ~ (v2_tdlat_3 @ X13)
% 0.21/0.48          | ~ (v2_pre_topc @ X13)
% 0.21/0.48          | (v2_struct_0 @ X13))),
% 0.21/0.48      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.21/0.48  thf('52', plain,
% 0.21/0.48      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.48         | (v2_struct_0 @ sk_A)
% 0.21/0.48         | ~ (v2_pre_topc @ sk_A)
% 0.21/0.48         | ~ (v2_tdlat_3 @ sk_A)
% 0.21/0.48         | ~ (l1_pre_topc @ sk_A)
% 0.21/0.48         | (v1_zfmisc_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.48         | ~ (v2_tex_2 @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.21/0.48         | (v1_xboole_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.21/0.48         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.48  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('54', plain, ((v2_tdlat_3 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('56', plain,
% 0.21/0.48      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.48         | (v2_struct_0 @ sk_A)
% 0.21/0.48         | (v1_zfmisc_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.48         | ~ (v2_tex_2 @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.21/0.48         | (v1_xboole_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.21/0.48         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.48      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 0.21/0.48  thf('57', plain,
% 0.21/0.48      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.48         | (v1_xboole_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.48         | (v1_zfmisc_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.48         | (v2_struct_0 @ sk_A)
% 0.21/0.48         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['43', '56'])).
% 0.21/0.48  thf('58', plain,
% 0.21/0.48      ((((v2_struct_0 @ sk_A)
% 0.21/0.48         | (v1_zfmisc_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.48         | (v1_xboole_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.48         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['57'])).
% 0.21/0.48  thf(d1_xboole_0, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.48  thf('59', plain,
% 0.21/0.48      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.48      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.48  thf('60', plain,
% 0.21/0.48      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.48      inference('clc', [status(thm)], ['35', '36'])).
% 0.21/0.48  thf('61', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('62', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.48          | ~ (v2_tex_2 @ X7 @ X8)
% 0.21/0.48          | (r1_tarski @ X7 @ (sk_C_1 @ X7 @ X8))
% 0.21/0.48          | (v3_tex_2 @ X7 @ X8)
% 0.21/0.48          | ~ (l1_pre_topc @ X8))),
% 0.21/0.48      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.21/0.48  thf('63', plain,
% 0.21/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.48        | (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.48        | (r1_tarski @ sk_B_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.48        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['61', '62'])).
% 0.21/0.48  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('65', plain,
% 0.21/0.48      (((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.48        | (r1_tarski @ sk_B_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.48        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['63', '64'])).
% 0.21/0.48  thf('66', plain,
% 0.21/0.48      ((((r1_tarski @ sk_B_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.48         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['60', '65'])).
% 0.21/0.48  thf(d3_tarski, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.48  thf('67', plain,
% 0.21/0.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X3 @ X4)
% 0.21/0.48          | (r2_hidden @ X3 @ X5)
% 0.21/0.48          | ~ (r1_tarski @ X4 @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.48  thf('68', plain,
% 0.21/0.48      ((![X0 : $i]:
% 0.21/0.48          ((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.48           | (r2_hidden @ X0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.48           | ~ (r2_hidden @ X0 @ sk_B_1)))
% 0.21/0.48         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['66', '67'])).
% 0.21/0.48  thf('69', plain,
% 0.21/0.48      ((((v1_xboole_0 @ sk_B_1)
% 0.21/0.48         | (r2_hidden @ (sk_B @ sk_B_1) @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.48         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['59', '68'])).
% 0.21/0.48  thf('70', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('71', plain,
% 0.21/0.48      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.48         | (r2_hidden @ (sk_B @ sk_B_1) @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.21/0.48         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.48      inference('clc', [status(thm)], ['69', '70'])).
% 0.21/0.48  thf('72', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.48      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.48  thf('73', plain,
% 0.21/0.48      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.48         | ~ (v1_xboole_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.21/0.48         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['71', '72'])).
% 0.21/0.48  thf('74', plain,
% 0.21/0.48      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.48         | (v1_zfmisc_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.48         | (v2_struct_0 @ sk_A)
% 0.21/0.48         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['58', '73'])).
% 0.21/0.48  thf('75', plain,
% 0.21/0.48      ((((v2_struct_0 @ sk_A)
% 0.21/0.48         | (v1_zfmisc_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.48         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['74'])).
% 0.21/0.48  thf('76', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('77', plain,
% 0.21/0.48      ((((v3_tex_2 @ sk_B_1 @ sk_A) | (v1_zfmisc_1 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.21/0.48         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.48      inference('clc', [status(thm)], ['75', '76'])).
% 0.21/0.48  thf('78', plain,
% 0.21/0.48      ((((r1_tarski @ sk_B_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.48         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['60', '65'])).
% 0.21/0.48  thf(t1_tex_2, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.21/0.48           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.21/0.48  thf('79', plain,
% 0.21/0.48      (![X10 : $i, X11 : $i]:
% 0.21/0.48         ((v1_xboole_0 @ X10)
% 0.21/0.48          | ~ (v1_zfmisc_1 @ X10)
% 0.21/0.48          | ((X11) = (X10))
% 0.21/0.48          | ~ (r1_tarski @ X11 @ X10)
% 0.21/0.48          | (v1_xboole_0 @ X11))),
% 0.21/0.48      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.21/0.48  thf('80', plain,
% 0.21/0.48      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.48         | (v1_xboole_0 @ sk_B_1)
% 0.21/0.48         | ((sk_B_1) = (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.48         | ~ (v1_zfmisc_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.48         | (v1_xboole_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.21/0.48         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['78', '79'])).
% 0.21/0.48  thf('81', plain,
% 0.21/0.48      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.48         | (v1_xboole_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.48         | ((sk_B_1) = (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.48         | (v1_xboole_0 @ sk_B_1)
% 0.21/0.48         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['77', '80'])).
% 0.21/0.48  thf('82', plain,
% 0.21/0.48      ((((v1_xboole_0 @ sk_B_1)
% 0.21/0.48         | ((sk_B_1) = (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.48         | (v1_xboole_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.48         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['81'])).
% 0.21/0.48  thf('83', plain,
% 0.21/0.48      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.48         | ~ (v1_xboole_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.21/0.48         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['71', '72'])).
% 0.21/0.48  thf('84', plain,
% 0.21/0.48      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.48         | ((sk_B_1) = (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.48         | (v1_xboole_0 @ sk_B_1)
% 0.21/0.48         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['82', '83'])).
% 0.21/0.48  thf('85', plain,
% 0.21/0.48      ((((v1_xboole_0 @ sk_B_1)
% 0.21/0.48         | ((sk_B_1) = (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.48         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['84'])).
% 0.21/0.48  thf('86', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('87', plain,
% 0.21/0.48      ((((v3_tex_2 @ sk_B_1 @ sk_A) | ((sk_B_1) = (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.21/0.48         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.48      inference('clc', [status(thm)], ['85', '86'])).
% 0.21/0.48  thf('88', plain,
% 0.21/0.48      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.48      inference('clc', [status(thm)], ['35', '36'])).
% 0.21/0.48  thf('89', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('90', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.48          | ~ (v2_tex_2 @ X7 @ X8)
% 0.21/0.48          | ((X7) != (sk_C_1 @ X7 @ X8))
% 0.21/0.48          | (v3_tex_2 @ X7 @ X8)
% 0.21/0.48          | ~ (l1_pre_topc @ X8))),
% 0.21/0.48      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.21/0.48  thf('91', plain,
% 0.21/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.48        | (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.48        | ((sk_B_1) != (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.48        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['89', '90'])).
% 0.21/0.48  thf('92', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('93', plain,
% 0.21/0.48      (((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.48        | ((sk_B_1) != (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.48        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['91', '92'])).
% 0.21/0.48  thf('94', plain,
% 0.21/0.48      (((((sk_B_1) != (sk_C_1 @ sk_B_1 @ sk_A)) | (v3_tex_2 @ sk_B_1 @ sk_A)))
% 0.21/0.48         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['88', '93'])).
% 0.21/0.48  thf('95', plain,
% 0.21/0.48      (((v3_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.48      inference('clc', [status(thm)], ['87', '94'])).
% 0.21/0.48  thf('96', plain,
% 0.21/0.48      ((~ (v3_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('97', plain, (~ ((v1_zfmisc_1 @ sk_B_1)) | ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['95', '96'])).
% 0.21/0.48  thf('98', plain, ($false),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['1', '23', '24', '97'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
