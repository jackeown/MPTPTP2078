%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.377xH75Hx6

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:20 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 409 expanded)
%              Number of leaves         :   27 ( 122 expanded)
%              Depth                    :   28
%              Number of atoms          : 1361 (5022 expanded)
%              Number of equality atoms :   78 ( 107 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

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
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v3_tex_2 @ X12 @ X13 )
      | ( v2_tex_2 @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v2_tex_2 @ X17 @ X18 )
      | ( v1_zfmisc_1 @ X17 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_tdlat_3 @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v1_zfmisc_1 @ X17 )
      | ( v2_tex_2 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_tdlat_3 @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v2_tex_2 @ X12 @ X13 )
      | ( v2_tex_2 @ ( sk_C @ X12 @ X13 ) @ X13 )
      | ( v3_tex_2 @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v2_tex_2 @ X12 @ X13 )
      | ( m1_subset_1 @ ( sk_C @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v3_tex_2 @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v2_tex_2 @ X17 @ X18 )
      | ( v1_zfmisc_1 @ X17 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_tdlat_3 @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
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
    ! [X10: $i] :
      ( ( v1_zfmisc_1 @ X10 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v2_tex_2 @ X12 @ X13 )
      | ( r1_tarski @ X12 @ ( sk_C @ X12 @ X13 ) )
      | ( v3_tex_2 @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
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

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('71',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('72',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( ( k4_xboole_0 @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
        = k1_xboole_0 ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( v1_zfmisc_1 @ sk_B )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('74',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('75',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( v1_zfmisc_1 @ X15 )
      | ( X16 = X15 )
      | ~ ( r1_tarski @ X16 @ X15 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( ( k4_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('77',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('78',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ~ ( v1_xboole_0 @ X9 )
      | ( X8 = X9 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ~ ( v1_zfmisc_1 @ X1 )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = X1 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_zfmisc_1 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_zfmisc_1 @ X1 )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( v1_zfmisc_1 @ X15 )
      | ( X16 = X15 )
      | ~ ( r1_tarski @ X16 @ X15 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_zfmisc_1 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( X1 = X0 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_zfmisc_1 @ X1 )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_zfmisc_1 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( sk_B = X0 )
      | ~ ( v1_zfmisc_1 @ sk_B )
      | ( ( k4_xboole_0 @ sk_B @ X0 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ sk_B @ X0 )
          = sk_B )
        | ( sk_B = X0 )
        | ~ ( v1_zfmisc_1 @ X0 )
        | ( k1_xboole_0 = X0 ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['73','90'])).

thf('92',plain,
    ( ( ( k1_xboole_0 = sk_B )
      | ( v3_tex_2 @ sk_B @ sk_A )
      | ( k1_xboole_0
        = ( sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_zfmisc_1 @ ( sk_C @ sk_B @ sk_A ) )
      | ( sk_B
        = ( sk_C @ sk_B @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['72','91'])).

thf('93',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( sk_B
        = ( sk_C @ sk_B @ sk_A ) )
      | ( k1_xboole_0
        = ( sk_C @ sk_B @ sk_A ) )
      | ( v3_tex_2 @ sk_B @ sk_A )
      | ( k1_xboole_0 = sk_B ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['63','92'])).

thf('94',plain,
    ( ( ( k1_xboole_0 = sk_B )
      | ( k1_xboole_0
        = ( sk_C @ sk_B @ sk_A ) )
      | ( sk_B
        = ( sk_C @ sk_B @ sk_A ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('96',plain,
    ( ( ( sk_B
        = ( sk_C @ sk_B @ sk_A ) )
      | ( k1_xboole_0
        = ( sk_C @ sk_B @ sk_A ) )
      | ( k1_xboole_0 = sk_B ) )
   <= ( ~ ( v3_tex_2 @ sk_B @ sk_A )
      & ( v1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('98',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v2_tex_2 @ X12 @ X13 )
      | ( X12
       != ( sk_C @ X12 @ X13 ) )
      | ( v3_tex_2 @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('100',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B @ sk_A )
    | ( sk_B
     != ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( sk_B
     != ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( ( sk_B
       != ( sk_C @ sk_B @ sk_A ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['97','102'])).

thf('104',plain,
    ( ( ( sk_B != sk_B )
      | ( k1_xboole_0 = sk_B )
      | ( k1_xboole_0
        = ( sk_C @ sk_B @ sk_A ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( ~ ( v3_tex_2 @ sk_B @ sk_A )
      & ( v1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['96','103'])).

thf('105',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( k1_xboole_0
        = ( sk_C @ sk_B @ sk_A ) )
      | ( k1_xboole_0 = sk_B ) )
   <= ( ~ ( v3_tex_2 @ sk_B @ sk_A )
      & ( v1_zfmisc_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('107',plain,
    ( ( ( k1_xboole_0 = sk_B )
      | ( k1_xboole_0
        = ( sk_C @ sk_B @ sk_A ) ) )
   <= ( ~ ( v3_tex_2 @ sk_B @ sk_A )
      & ( v1_zfmisc_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( ( k4_xboole_0 @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
        = k1_xboole_0 ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('109',plain,
    ( ( ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( k1_xboole_0 = sk_B )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( ~ ( v3_tex_2 @ sk_B @ sk_A )
      & ( v1_zfmisc_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( v1_zfmisc_1 @ sk_B )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_zfmisc_1 @ X1 )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ~ ( v1_zfmisc_1 @ X1 )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = X1 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('113',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('114',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ k1_xboole_0 )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_zfmisc_1 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['112','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ~ ( v1_zfmisc_1 @ X1 )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = X1 )
      | ~ ( r1_tarski @ X1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['111','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X1 )
        = X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
        = sk_B )
      | ~ ( v1_zfmisc_1 @ sk_B )
      | ( ( k4_xboole_0 @ sk_B @ X0 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
      = sk_B )
    | ~ ( v1_zfmisc_1 @ sk_B ) ),
    inference(condensation,[status(thm)],['121'])).

thf('123',plain,
    ( ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
      = sk_B )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['110','122'])).

thf('124',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( k1_xboole_0 = sk_B )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( ~ ( v3_tex_2 @ sk_B @ sk_A )
      & ( v1_zfmisc_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['109','123'])).

thf('125',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ~ ( v3_tex_2 @ sk_B @ sk_A )
      & ( v1_zfmisc_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('127',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ~ ( v3_tex_2 @ sk_B @ sk_A )
      & ( v1_zfmisc_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ~ ( v3_tex_2 @ sk_B @ sk_A )
      & ( v1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('131',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B )
    | ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','23','24','131'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.377xH75Hx6
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:43:22 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.35  % Running portfolio for 600 s
% 0.21/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.59/0.82  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.82  % Solved by: fo/fo7.sh
% 0.59/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.82  % done 323 iterations in 0.364s
% 0.59/0.82  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.82  % SZS output start Refutation
% 0.59/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.82  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.59/0.82  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.59/0.82  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.59/0.82  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.82  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.82  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.59/0.82  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.59/0.82  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.59/0.82  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.82  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.82  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.59/0.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.82  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.59/0.82  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.59/0.82  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.59/0.82  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.59/0.82  thf(t50_tex_2, conjecture,
% 0.59/0.82    (![A:$i]:
% 0.59/0.82     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.59/0.82         ( l1_pre_topc @ A ) ) =>
% 0.59/0.82       ( ![B:$i]:
% 0.59/0.82         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.59/0.82             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.59/0.82           ( ( v3_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.59/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.82    (~( ![A:$i]:
% 0.59/0.82        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.59/0.82            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.82          ( ![B:$i]:
% 0.59/0.82            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.59/0.82                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.59/0.82              ( ( v3_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.59/0.82    inference('cnf.neg', [status(esa)], [t50_tex_2])).
% 0.59/0.82  thf('0', plain, ((~ (v1_zfmisc_1 @ sk_B) | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('1', plain, (~ ((v1_zfmisc_1 @ sk_B)) | ~ ((v3_tex_2 @ sk_B @ sk_A))),
% 0.59/0.82      inference('split', [status(esa)], ['0'])).
% 0.59/0.82  thf('2', plain, (((v1_zfmisc_1 @ sk_B) | (v3_tex_2 @ sk_B @ sk_A))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('3', plain, (((v3_tex_2 @ sk_B @ sk_A)) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.59/0.82      inference('split', [status(esa)], ['2'])).
% 0.59/0.82  thf('4', plain,
% 0.59/0.82      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf(d7_tex_2, axiom,
% 0.59/0.82    (![A:$i]:
% 0.59/0.82     ( ( l1_pre_topc @ A ) =>
% 0.59/0.82       ( ![B:$i]:
% 0.59/0.82         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.82           ( ( v3_tex_2 @ B @ A ) <=>
% 0.59/0.82             ( ( v2_tex_2 @ B @ A ) & 
% 0.59/0.82               ( ![C:$i]:
% 0.59/0.82                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.82                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.59/0.82                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.59/0.82  thf('5', plain,
% 0.59/0.82      (![X12 : $i, X13 : $i]:
% 0.59/0.82         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.59/0.82          | ~ (v3_tex_2 @ X12 @ X13)
% 0.59/0.82          | (v2_tex_2 @ X12 @ X13)
% 0.59/0.82          | ~ (l1_pre_topc @ X13))),
% 0.59/0.82      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.59/0.82  thf('6', plain,
% 0.59/0.82      ((~ (l1_pre_topc @ sk_A)
% 0.59/0.82        | (v2_tex_2 @ sk_B @ sk_A)
% 0.59/0.82        | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.59/0.82      inference('sup-', [status(thm)], ['4', '5'])).
% 0.59/0.82  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('8', plain, (((v2_tex_2 @ sk_B @ sk_A) | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.59/0.82      inference('demod', [status(thm)], ['6', '7'])).
% 0.59/0.82  thf('9', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['3', '8'])).
% 0.59/0.82  thf('10', plain,
% 0.59/0.82      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf(t44_tex_2, axiom,
% 0.59/0.82    (![A:$i]:
% 0.59/0.82     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.59/0.82         ( l1_pre_topc @ A ) ) =>
% 0.59/0.82       ( ![B:$i]:
% 0.59/0.82         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.59/0.82             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.59/0.82           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.59/0.82  thf('11', plain,
% 0.59/0.82      (![X17 : $i, X18 : $i]:
% 0.59/0.82         ((v1_xboole_0 @ X17)
% 0.59/0.82          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.59/0.82          | ~ (v2_tex_2 @ X17 @ X18)
% 0.59/0.82          | (v1_zfmisc_1 @ X17)
% 0.59/0.82          | ~ (l1_pre_topc @ X18)
% 0.59/0.82          | ~ (v2_tdlat_3 @ X18)
% 0.59/0.82          | ~ (v2_pre_topc @ X18)
% 0.59/0.82          | (v2_struct_0 @ X18))),
% 0.59/0.82      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.59/0.82  thf('12', plain,
% 0.59/0.82      (((v2_struct_0 @ sk_A)
% 0.59/0.82        | ~ (v2_pre_topc @ sk_A)
% 0.59/0.82        | ~ (v2_tdlat_3 @ sk_A)
% 0.59/0.82        | ~ (l1_pre_topc @ sk_A)
% 0.59/0.82        | (v1_zfmisc_1 @ sk_B)
% 0.59/0.82        | ~ (v2_tex_2 @ sk_B @ sk_A)
% 0.59/0.82        | (v1_xboole_0 @ sk_B))),
% 0.59/0.82      inference('sup-', [status(thm)], ['10', '11'])).
% 0.59/0.82  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('14', plain, ((v2_tdlat_3 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('16', plain,
% 0.59/0.82      (((v2_struct_0 @ sk_A)
% 0.59/0.82        | (v1_zfmisc_1 @ sk_B)
% 0.59/0.82        | ~ (v2_tex_2 @ sk_B @ sk_A)
% 0.59/0.82        | (v1_xboole_0 @ sk_B))),
% 0.59/0.82      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.59/0.82  thf('17', plain,
% 0.59/0.82      ((((v1_xboole_0 @ sk_B) | (v1_zfmisc_1 @ sk_B) | (v2_struct_0 @ sk_A)))
% 0.59/0.82         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['9', '16'])).
% 0.59/0.82  thf('18', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('19', plain,
% 0.59/0.82      ((((v2_struct_0 @ sk_A) | (v1_zfmisc_1 @ sk_B)))
% 0.59/0.82         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.59/0.82      inference('clc', [status(thm)], ['17', '18'])).
% 0.59/0.82  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('21', plain, (((v1_zfmisc_1 @ sk_B)) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.59/0.82      inference('clc', [status(thm)], ['19', '20'])).
% 0.59/0.82  thf('22', plain, ((~ (v1_zfmisc_1 @ sk_B)) <= (~ ((v1_zfmisc_1 @ sk_B)))),
% 0.59/0.82      inference('split', [status(esa)], ['0'])).
% 0.59/0.82  thf('23', plain, (((v1_zfmisc_1 @ sk_B)) | ~ ((v3_tex_2 @ sk_B @ sk_A))),
% 0.59/0.82      inference('sup-', [status(thm)], ['21', '22'])).
% 0.59/0.82  thf('24', plain, (((v1_zfmisc_1 @ sk_B)) | ((v3_tex_2 @ sk_B @ sk_A))),
% 0.59/0.82      inference('split', [status(esa)], ['2'])).
% 0.59/0.82  thf('25', plain, (((v1_zfmisc_1 @ sk_B)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.59/0.82      inference('split', [status(esa)], ['2'])).
% 0.59/0.82  thf('26', plain,
% 0.59/0.82      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('27', plain,
% 0.59/0.82      (![X17 : $i, X18 : $i]:
% 0.59/0.82         ((v1_xboole_0 @ X17)
% 0.59/0.82          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.59/0.82          | ~ (v1_zfmisc_1 @ X17)
% 0.59/0.82          | (v2_tex_2 @ X17 @ X18)
% 0.59/0.82          | ~ (l1_pre_topc @ X18)
% 0.59/0.82          | ~ (v2_tdlat_3 @ X18)
% 0.59/0.82          | ~ (v2_pre_topc @ X18)
% 0.59/0.82          | (v2_struct_0 @ X18))),
% 0.59/0.82      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.59/0.82  thf('28', plain,
% 0.59/0.82      (((v2_struct_0 @ sk_A)
% 0.59/0.82        | ~ (v2_pre_topc @ sk_A)
% 0.59/0.82        | ~ (v2_tdlat_3 @ sk_A)
% 0.59/0.82        | ~ (l1_pre_topc @ sk_A)
% 0.59/0.82        | (v2_tex_2 @ sk_B @ sk_A)
% 0.59/0.82        | ~ (v1_zfmisc_1 @ sk_B)
% 0.59/0.82        | (v1_xboole_0 @ sk_B))),
% 0.59/0.82      inference('sup-', [status(thm)], ['26', '27'])).
% 0.59/0.82  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('30', plain, ((v2_tdlat_3 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('32', plain,
% 0.59/0.82      (((v2_struct_0 @ sk_A)
% 0.59/0.82        | (v2_tex_2 @ sk_B @ sk_A)
% 0.59/0.82        | ~ (v1_zfmisc_1 @ sk_B)
% 0.59/0.82        | (v1_xboole_0 @ sk_B))),
% 0.59/0.82      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 0.59/0.82  thf('33', plain,
% 0.59/0.82      ((((v1_xboole_0 @ sk_B) | (v2_tex_2 @ sk_B @ sk_A) | (v2_struct_0 @ sk_A)))
% 0.59/0.82         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['25', '32'])).
% 0.59/0.82  thf('34', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('35', plain,
% 0.59/0.82      ((((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B @ sk_A)))
% 0.59/0.82         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.59/0.82      inference('clc', [status(thm)], ['33', '34'])).
% 0.59/0.82  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('37', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.59/0.82      inference('clc', [status(thm)], ['35', '36'])).
% 0.59/0.82  thf('38', plain,
% 0.59/0.82      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('39', plain,
% 0.59/0.82      (![X12 : $i, X13 : $i]:
% 0.59/0.82         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.59/0.82          | ~ (v2_tex_2 @ X12 @ X13)
% 0.59/0.82          | (v2_tex_2 @ (sk_C @ X12 @ X13) @ X13)
% 0.59/0.82          | (v3_tex_2 @ X12 @ X13)
% 0.59/0.82          | ~ (l1_pre_topc @ X13))),
% 0.59/0.82      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.59/0.82  thf('40', plain,
% 0.59/0.82      ((~ (l1_pre_topc @ sk_A)
% 0.59/0.82        | (v3_tex_2 @ sk_B @ sk_A)
% 0.59/0.82        | (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.59/0.82        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.59/0.82      inference('sup-', [status(thm)], ['38', '39'])).
% 0.59/0.82  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('42', plain,
% 0.59/0.82      (((v3_tex_2 @ sk_B @ sk_A)
% 0.59/0.82        | (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.59/0.82        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.59/0.82      inference('demod', [status(thm)], ['40', '41'])).
% 0.59/0.82  thf('43', plain,
% 0.59/0.82      ((((v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A) | (v3_tex_2 @ sk_B @ sk_A)))
% 0.59/0.82         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['37', '42'])).
% 0.59/0.82  thf('44', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.59/0.82      inference('clc', [status(thm)], ['35', '36'])).
% 0.59/0.82  thf('45', plain,
% 0.59/0.82      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('46', plain,
% 0.59/0.82      (![X12 : $i, X13 : $i]:
% 0.59/0.82         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.59/0.82          | ~ (v2_tex_2 @ X12 @ X13)
% 0.59/0.82          | (m1_subset_1 @ (sk_C @ X12 @ X13) @ 
% 0.59/0.82             (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.59/0.82          | (v3_tex_2 @ X12 @ X13)
% 0.59/0.82          | ~ (l1_pre_topc @ X13))),
% 0.59/0.82      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.59/0.83  thf('47', plain,
% 0.59/0.83      ((~ (l1_pre_topc @ sk_A)
% 0.59/0.83        | (v3_tex_2 @ sk_B @ sk_A)
% 0.59/0.83        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.59/0.83           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.83        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.59/0.83      inference('sup-', [status(thm)], ['45', '46'])).
% 0.59/0.83  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('49', plain,
% 0.59/0.83      (((v3_tex_2 @ sk_B @ sk_A)
% 0.59/0.83        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.59/0.83           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.83        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.59/0.83      inference('demod', [status(thm)], ['47', '48'])).
% 0.59/0.83  thf('50', plain,
% 0.59/0.83      ((((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.59/0.83          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.83         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['44', '49'])).
% 0.59/0.83  thf('51', plain,
% 0.59/0.83      (![X17 : $i, X18 : $i]:
% 0.59/0.83         ((v1_xboole_0 @ X17)
% 0.59/0.83          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.59/0.83          | ~ (v2_tex_2 @ X17 @ X18)
% 0.59/0.83          | (v1_zfmisc_1 @ X17)
% 0.59/0.83          | ~ (l1_pre_topc @ X18)
% 0.59/0.83          | ~ (v2_tdlat_3 @ X18)
% 0.59/0.83          | ~ (v2_pre_topc @ X18)
% 0.59/0.83          | (v2_struct_0 @ X18))),
% 0.59/0.83      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.59/0.83  thf('52', plain,
% 0.59/0.83      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.59/0.83         | (v2_struct_0 @ sk_A)
% 0.59/0.83         | ~ (v2_pre_topc @ sk_A)
% 0.59/0.83         | ~ (v2_tdlat_3 @ sk_A)
% 0.59/0.83         | ~ (l1_pre_topc @ sk_A)
% 0.59/0.83         | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.59/0.83         | ~ (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.59/0.83         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['50', '51'])).
% 0.59/0.83  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('54', plain, ((v2_tdlat_3 @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('56', plain,
% 0.59/0.83      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.59/0.83         | (v2_struct_0 @ sk_A)
% 0.59/0.83         | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.59/0.83         | ~ (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.59/0.83         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.59/0.83      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 0.59/0.83  thf('57', plain,
% 0.59/0.83      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.59/0.83         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.59/0.83         | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.59/0.83         | (v2_struct_0 @ sk_A)
% 0.59/0.83         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['43', '56'])).
% 0.59/0.83  thf('58', plain,
% 0.59/0.83      ((((v2_struct_0 @ sk_A)
% 0.59/0.83         | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.59/0.83         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.59/0.83         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.59/0.83      inference('simplify', [status(thm)], ['57'])).
% 0.59/0.83  thf(cc1_zfmisc_1, axiom,
% 0.59/0.83    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_zfmisc_1 @ A ) ))).
% 0.59/0.83  thf('59', plain,
% 0.59/0.83      (![X10 : $i]: ((v1_zfmisc_1 @ X10) | ~ (v1_xboole_0 @ X10))),
% 0.59/0.83      inference('cnf', [status(esa)], [cc1_zfmisc_1])).
% 0.59/0.83  thf('60', plain,
% 0.59/0.83      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.59/0.83         | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.59/0.83         | (v2_struct_0 @ sk_A)
% 0.59/0.83         | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['58', '59'])).
% 0.59/0.83  thf('61', plain,
% 0.59/0.83      ((((v2_struct_0 @ sk_A)
% 0.59/0.83         | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.59/0.83         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.59/0.83      inference('simplify', [status(thm)], ['60'])).
% 0.59/0.83  thf('62', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('63', plain,
% 0.59/0.83      ((((v3_tex_2 @ sk_B @ sk_A) | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))))
% 0.59/0.83         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.59/0.83      inference('clc', [status(thm)], ['61', '62'])).
% 0.59/0.83  thf('64', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.59/0.83      inference('clc', [status(thm)], ['35', '36'])).
% 0.59/0.83  thf('65', plain,
% 0.59/0.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('66', plain,
% 0.59/0.83      (![X12 : $i, X13 : $i]:
% 0.59/0.83         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.59/0.83          | ~ (v2_tex_2 @ X12 @ X13)
% 0.59/0.83          | (r1_tarski @ X12 @ (sk_C @ X12 @ X13))
% 0.59/0.83          | (v3_tex_2 @ X12 @ X13)
% 0.59/0.83          | ~ (l1_pre_topc @ X13))),
% 0.59/0.83      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.59/0.83  thf('67', plain,
% 0.59/0.83      ((~ (l1_pre_topc @ sk_A)
% 0.59/0.83        | (v3_tex_2 @ sk_B @ sk_A)
% 0.59/0.83        | (r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.59/0.83        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.59/0.83      inference('sup-', [status(thm)], ['65', '66'])).
% 0.59/0.83  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('69', plain,
% 0.59/0.83      (((v3_tex_2 @ sk_B @ sk_A)
% 0.59/0.83        | (r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.59/0.83        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.59/0.83      inference('demod', [status(thm)], ['67', '68'])).
% 0.59/0.83  thf('70', plain,
% 0.59/0.83      ((((r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A)) | (v3_tex_2 @ sk_B @ sk_A)))
% 0.59/0.83         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['64', '69'])).
% 0.59/0.83  thf(l32_xboole_1, axiom,
% 0.59/0.83    (![A:$i,B:$i]:
% 0.59/0.83     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.59/0.83  thf('71', plain,
% 0.59/0.83      (![X3 : $i, X5 : $i]:
% 0.59/0.83         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.59/0.83      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.59/0.83  thf('72', plain,
% 0.59/0.83      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.59/0.83         | ((k4_xboole_0 @ sk_B @ (sk_C @ sk_B @ sk_A)) = (k1_xboole_0))))
% 0.59/0.83         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['70', '71'])).
% 0.59/0.83  thf('73', plain, (((v1_zfmisc_1 @ sk_B)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.59/0.83      inference('split', [status(esa)], ['2'])).
% 0.59/0.83  thf(t36_xboole_1, axiom,
% 0.59/0.83    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.59/0.83  thf('74', plain,
% 0.59/0.83      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 0.59/0.83      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.59/0.83  thf(t1_tex_2, axiom,
% 0.59/0.83    (![A:$i]:
% 0.59/0.83     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.59/0.83       ( ![B:$i]:
% 0.59/0.83         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.59/0.83           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.59/0.83  thf('75', plain,
% 0.59/0.83      (![X15 : $i, X16 : $i]:
% 0.59/0.83         ((v1_xboole_0 @ X15)
% 0.59/0.83          | ~ (v1_zfmisc_1 @ X15)
% 0.59/0.83          | ((X16) = (X15))
% 0.59/0.83          | ~ (r1_tarski @ X16 @ X15)
% 0.59/0.83          | (v1_xboole_0 @ X16))),
% 0.59/0.83      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.59/0.83  thf('76', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((v1_xboole_0 @ (k4_xboole_0 @ X0 @ X1))
% 0.59/0.83          | ((k4_xboole_0 @ X0 @ X1) = (X0))
% 0.59/0.83          | ~ (v1_zfmisc_1 @ X0)
% 0.59/0.83          | (v1_xboole_0 @ X0))),
% 0.59/0.83      inference('sup-', [status(thm)], ['74', '75'])).
% 0.59/0.83  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.59/0.83  thf('77', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.59/0.83      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.59/0.83  thf(t8_boole, axiom,
% 0.59/0.83    (![A:$i,B:$i]:
% 0.59/0.83     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.59/0.83  thf('78', plain,
% 0.59/0.83      (![X8 : $i, X9 : $i]:
% 0.59/0.83         (~ (v1_xboole_0 @ X8) | ~ (v1_xboole_0 @ X9) | ((X8) = (X9)))),
% 0.59/0.83      inference('cnf', [status(esa)], [t8_boole])).
% 0.59/0.83  thf('79', plain,
% 0.59/0.83      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.83      inference('sup-', [status(thm)], ['77', '78'])).
% 0.59/0.83  thf('80', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((v1_xboole_0 @ X1)
% 0.59/0.83          | ~ (v1_zfmisc_1 @ X1)
% 0.59/0.83          | ((k4_xboole_0 @ X1 @ X0) = (X1))
% 0.59/0.83          | ((k1_xboole_0) = (k4_xboole_0 @ X1 @ X0)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['76', '79'])).
% 0.59/0.83  thf('81', plain,
% 0.59/0.83      (![X3 : $i, X4 : $i]:
% 0.59/0.83         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.59/0.83      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.59/0.83  thf('82', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         (((k1_xboole_0) != (k1_xboole_0))
% 0.59/0.83          | ((k4_xboole_0 @ X1 @ X0) = (X1))
% 0.59/0.83          | ~ (v1_zfmisc_1 @ X1)
% 0.59/0.83          | (v1_xboole_0 @ X1)
% 0.59/0.83          | (r1_tarski @ X1 @ X0))),
% 0.59/0.83      inference('sup-', [status(thm)], ['80', '81'])).
% 0.59/0.83  thf('83', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((r1_tarski @ X1 @ X0)
% 0.59/0.83          | (v1_xboole_0 @ X1)
% 0.59/0.83          | ~ (v1_zfmisc_1 @ X1)
% 0.59/0.83          | ((k4_xboole_0 @ X1 @ X0) = (X1)))),
% 0.59/0.83      inference('simplify', [status(thm)], ['82'])).
% 0.59/0.83  thf('84', plain,
% 0.59/0.83      (![X15 : $i, X16 : $i]:
% 0.59/0.83         ((v1_xboole_0 @ X15)
% 0.59/0.83          | ~ (v1_zfmisc_1 @ X15)
% 0.59/0.83          | ((X16) = (X15))
% 0.59/0.83          | ~ (r1_tarski @ X16 @ X15)
% 0.59/0.83          | (v1_xboole_0 @ X16))),
% 0.59/0.83      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.59/0.83  thf('85', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         (((k4_xboole_0 @ X1 @ X0) = (X1))
% 0.59/0.83          | ~ (v1_zfmisc_1 @ X1)
% 0.59/0.83          | (v1_xboole_0 @ X1)
% 0.59/0.83          | (v1_xboole_0 @ X1)
% 0.59/0.83          | ((X1) = (X0))
% 0.59/0.83          | ~ (v1_zfmisc_1 @ X0)
% 0.59/0.83          | (v1_xboole_0 @ X0))),
% 0.59/0.83      inference('sup-', [status(thm)], ['83', '84'])).
% 0.59/0.83  thf('86', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((v1_xboole_0 @ X0)
% 0.59/0.83          | ~ (v1_zfmisc_1 @ X0)
% 0.59/0.83          | ((X1) = (X0))
% 0.59/0.83          | (v1_xboole_0 @ X1)
% 0.59/0.83          | ~ (v1_zfmisc_1 @ X1)
% 0.59/0.83          | ((k4_xboole_0 @ X1 @ X0) = (X1)))),
% 0.59/0.83      inference('simplify', [status(thm)], ['85'])).
% 0.59/0.83  thf('87', plain,
% 0.59/0.83      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.83      inference('sup-', [status(thm)], ['77', '78'])).
% 0.59/0.83  thf('88', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         (((k4_xboole_0 @ X1 @ X0) = (X1))
% 0.59/0.83          | ~ (v1_zfmisc_1 @ X1)
% 0.59/0.83          | (v1_xboole_0 @ X1)
% 0.59/0.83          | ((X1) = (X0))
% 0.59/0.83          | ~ (v1_zfmisc_1 @ X0)
% 0.59/0.83          | ((k1_xboole_0) = (X0)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['86', '87'])).
% 0.59/0.83  thf('89', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('90', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (((k1_xboole_0) = (X0))
% 0.59/0.83          | ~ (v1_zfmisc_1 @ X0)
% 0.59/0.83          | ((sk_B) = (X0))
% 0.59/0.83          | ~ (v1_zfmisc_1 @ sk_B)
% 0.59/0.83          | ((k4_xboole_0 @ sk_B @ X0) = (sk_B)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['88', '89'])).
% 0.59/0.83  thf('91', plain,
% 0.59/0.83      ((![X0 : $i]:
% 0.59/0.83          (((k4_xboole_0 @ sk_B @ X0) = (sk_B))
% 0.59/0.83           | ((sk_B) = (X0))
% 0.59/0.83           | ~ (v1_zfmisc_1 @ X0)
% 0.59/0.83           | ((k1_xboole_0) = (X0))))
% 0.59/0.83         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['73', '90'])).
% 0.59/0.83  thf('92', plain,
% 0.59/0.83      (((((k1_xboole_0) = (sk_B))
% 0.59/0.83         | (v3_tex_2 @ sk_B @ sk_A)
% 0.59/0.83         | ((k1_xboole_0) = (sk_C @ sk_B @ sk_A))
% 0.59/0.83         | ~ (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.59/0.83         | ((sk_B) = (sk_C @ sk_B @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.59/0.83      inference('sup+', [status(thm)], ['72', '91'])).
% 0.59/0.83  thf('93', plain,
% 0.59/0.83      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.59/0.83         | ((sk_B) = (sk_C @ sk_B @ sk_A))
% 0.59/0.83         | ((k1_xboole_0) = (sk_C @ sk_B @ sk_A))
% 0.59/0.83         | (v3_tex_2 @ sk_B @ sk_A)
% 0.59/0.83         | ((k1_xboole_0) = (sk_B)))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['63', '92'])).
% 0.59/0.83  thf('94', plain,
% 0.59/0.83      (((((k1_xboole_0) = (sk_B))
% 0.59/0.83         | ((k1_xboole_0) = (sk_C @ sk_B @ sk_A))
% 0.59/0.83         | ((sk_B) = (sk_C @ sk_B @ sk_A))
% 0.59/0.83         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.59/0.83      inference('simplify', [status(thm)], ['93'])).
% 0.59/0.83  thf('95', plain,
% 0.59/0.83      ((~ (v3_tex_2 @ sk_B @ sk_A)) <= (~ ((v3_tex_2 @ sk_B @ sk_A)))),
% 0.59/0.83      inference('split', [status(esa)], ['0'])).
% 0.59/0.83  thf('96', plain,
% 0.59/0.83      (((((sk_B) = (sk_C @ sk_B @ sk_A))
% 0.59/0.83         | ((k1_xboole_0) = (sk_C @ sk_B @ sk_A))
% 0.59/0.83         | ((k1_xboole_0) = (sk_B))))
% 0.59/0.83         <= (~ ((v3_tex_2 @ sk_B @ sk_A)) & ((v1_zfmisc_1 @ sk_B)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['94', '95'])).
% 0.59/0.83  thf('97', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.59/0.83      inference('clc', [status(thm)], ['35', '36'])).
% 0.59/0.83  thf('98', plain,
% 0.59/0.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('99', plain,
% 0.59/0.83      (![X12 : $i, X13 : $i]:
% 0.59/0.83         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.59/0.83          | ~ (v2_tex_2 @ X12 @ X13)
% 0.59/0.83          | ((X12) != (sk_C @ X12 @ X13))
% 0.59/0.83          | (v3_tex_2 @ X12 @ X13)
% 0.59/0.83          | ~ (l1_pre_topc @ X13))),
% 0.59/0.83      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.59/0.83  thf('100', plain,
% 0.59/0.83      ((~ (l1_pre_topc @ sk_A)
% 0.59/0.83        | (v3_tex_2 @ sk_B @ sk_A)
% 0.59/0.83        | ((sk_B) != (sk_C @ sk_B @ sk_A))
% 0.59/0.83        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.59/0.83      inference('sup-', [status(thm)], ['98', '99'])).
% 0.59/0.83  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('102', plain,
% 0.59/0.83      (((v3_tex_2 @ sk_B @ sk_A)
% 0.59/0.83        | ((sk_B) != (sk_C @ sk_B @ sk_A))
% 0.59/0.83        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.59/0.83      inference('demod', [status(thm)], ['100', '101'])).
% 0.59/0.83  thf('103', plain,
% 0.59/0.83      (((((sk_B) != (sk_C @ sk_B @ sk_A)) | (v3_tex_2 @ sk_B @ sk_A)))
% 0.59/0.83         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['97', '102'])).
% 0.59/0.83  thf('104', plain,
% 0.59/0.83      (((((sk_B) != (sk_B))
% 0.59/0.83         | ((k1_xboole_0) = (sk_B))
% 0.59/0.83         | ((k1_xboole_0) = (sk_C @ sk_B @ sk_A))
% 0.59/0.83         | (v3_tex_2 @ sk_B @ sk_A)))
% 0.59/0.83         <= (~ ((v3_tex_2 @ sk_B @ sk_A)) & ((v1_zfmisc_1 @ sk_B)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['96', '103'])).
% 0.59/0.83  thf('105', plain,
% 0.59/0.83      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.59/0.83         | ((k1_xboole_0) = (sk_C @ sk_B @ sk_A))
% 0.59/0.83         | ((k1_xboole_0) = (sk_B))))
% 0.59/0.83         <= (~ ((v3_tex_2 @ sk_B @ sk_A)) & ((v1_zfmisc_1 @ sk_B)))),
% 0.59/0.83      inference('simplify', [status(thm)], ['104'])).
% 0.59/0.83  thf('106', plain,
% 0.59/0.83      ((~ (v3_tex_2 @ sk_B @ sk_A)) <= (~ ((v3_tex_2 @ sk_B @ sk_A)))),
% 0.59/0.83      inference('split', [status(esa)], ['0'])).
% 0.59/0.83  thf('107', plain,
% 0.59/0.83      (((((k1_xboole_0) = (sk_B)) | ((k1_xboole_0) = (sk_C @ sk_B @ sk_A))))
% 0.59/0.83         <= (~ ((v3_tex_2 @ sk_B @ sk_A)) & ((v1_zfmisc_1 @ sk_B)))),
% 0.59/0.83      inference('clc', [status(thm)], ['105', '106'])).
% 0.59/0.83  thf('108', plain,
% 0.59/0.83      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.59/0.83         | ((k4_xboole_0 @ sk_B @ (sk_C @ sk_B @ sk_A)) = (k1_xboole_0))))
% 0.59/0.83         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['70', '71'])).
% 0.59/0.83  thf('109', plain,
% 0.59/0.83      (((((k4_xboole_0 @ sk_B @ k1_xboole_0) = (k1_xboole_0))
% 0.59/0.83         | ((k1_xboole_0) = (sk_B))
% 0.59/0.83         | (v3_tex_2 @ sk_B @ sk_A)))
% 0.59/0.83         <= (~ ((v3_tex_2 @ sk_B @ sk_A)) & ((v1_zfmisc_1 @ sk_B)))),
% 0.59/0.83      inference('sup+', [status(thm)], ['107', '108'])).
% 0.59/0.83  thf('110', plain, (((v1_zfmisc_1 @ sk_B)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.59/0.83      inference('split', [status(esa)], ['2'])).
% 0.59/0.83  thf('111', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((r1_tarski @ X1 @ X0)
% 0.59/0.83          | (v1_xboole_0 @ X1)
% 0.59/0.83          | ~ (v1_zfmisc_1 @ X1)
% 0.59/0.83          | ((k4_xboole_0 @ X1 @ X0) = (X1)))),
% 0.59/0.83      inference('simplify', [status(thm)], ['82'])).
% 0.59/0.83  thf('112', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((v1_xboole_0 @ X1)
% 0.59/0.83          | ~ (v1_zfmisc_1 @ X1)
% 0.59/0.83          | ((k4_xboole_0 @ X1 @ X0) = (X1))
% 0.59/0.83          | ((k1_xboole_0) = (k4_xboole_0 @ X1 @ X0)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['76', '79'])).
% 0.59/0.83  thf('113', plain,
% 0.59/0.83      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 0.59/0.83      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.59/0.83  thf(d10_xboole_0, axiom,
% 0.59/0.83    (![A:$i,B:$i]:
% 0.59/0.83     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.59/0.83  thf('114', plain,
% 0.59/0.83      (![X0 : $i, X2 : $i]:
% 0.59/0.83         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.59/0.83      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.83  thf('115', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.59/0.83          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['113', '114'])).
% 0.59/0.83  thf('116', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         (~ (r1_tarski @ X1 @ k1_xboole_0)
% 0.59/0.83          | ((k4_xboole_0 @ X1 @ X0) = (X1))
% 0.59/0.83          | ~ (v1_zfmisc_1 @ X1)
% 0.59/0.83          | (v1_xboole_0 @ X1)
% 0.59/0.83          | ((X1) = (k4_xboole_0 @ X1 @ X0)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['112', '115'])).
% 0.59/0.83  thf('117', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((v1_xboole_0 @ X1)
% 0.59/0.83          | ~ (v1_zfmisc_1 @ X1)
% 0.59/0.83          | ((k4_xboole_0 @ X1 @ X0) = (X1))
% 0.59/0.83          | ~ (r1_tarski @ X1 @ k1_xboole_0))),
% 0.59/0.83      inference('simplify', [status(thm)], ['116'])).
% 0.59/0.83  thf('118', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         (((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))
% 0.59/0.83          | ~ (v1_zfmisc_1 @ X0)
% 0.59/0.83          | (v1_xboole_0 @ X0)
% 0.59/0.83          | ((k4_xboole_0 @ X0 @ X1) = (X0))
% 0.59/0.83          | ~ (v1_zfmisc_1 @ X0)
% 0.59/0.83          | (v1_xboole_0 @ X0))),
% 0.59/0.83      inference('sup-', [status(thm)], ['111', '117'])).
% 0.59/0.83  thf('119', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         (((k4_xboole_0 @ X0 @ X1) = (X0))
% 0.59/0.83          | (v1_xboole_0 @ X0)
% 0.59/0.83          | ~ (v1_zfmisc_1 @ X0)
% 0.59/0.83          | ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0)))),
% 0.59/0.83      inference('simplify', [status(thm)], ['118'])).
% 0.59/0.83  thf('120', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('121', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (((k4_xboole_0 @ sk_B @ k1_xboole_0) = (sk_B))
% 0.59/0.83          | ~ (v1_zfmisc_1 @ sk_B)
% 0.59/0.83          | ((k4_xboole_0 @ sk_B @ X0) = (sk_B)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['119', '120'])).
% 0.59/0.83  thf('122', plain,
% 0.59/0.83      ((((k4_xboole_0 @ sk_B @ k1_xboole_0) = (sk_B)) | ~ (v1_zfmisc_1 @ sk_B))),
% 0.59/0.83      inference('condensation', [status(thm)], ['121'])).
% 0.59/0.83  thf('123', plain,
% 0.59/0.83      ((((k4_xboole_0 @ sk_B @ k1_xboole_0) = (sk_B)))
% 0.59/0.83         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['110', '122'])).
% 0.59/0.83  thf('124', plain,
% 0.59/0.83      (((((sk_B) = (k1_xboole_0))
% 0.59/0.83         | ((k1_xboole_0) = (sk_B))
% 0.59/0.83         | (v3_tex_2 @ sk_B @ sk_A)))
% 0.59/0.83         <= (~ ((v3_tex_2 @ sk_B @ sk_A)) & ((v1_zfmisc_1 @ sk_B)))),
% 0.59/0.83      inference('demod', [status(thm)], ['109', '123'])).
% 0.59/0.83  thf('125', plain,
% 0.59/0.83      ((((v3_tex_2 @ sk_B @ sk_A) | ((sk_B) = (k1_xboole_0))))
% 0.59/0.83         <= (~ ((v3_tex_2 @ sk_B @ sk_A)) & ((v1_zfmisc_1 @ sk_B)))),
% 0.59/0.83      inference('simplify', [status(thm)], ['124'])).
% 0.59/0.83  thf('126', plain,
% 0.59/0.83      ((~ (v3_tex_2 @ sk_B @ sk_A)) <= (~ ((v3_tex_2 @ sk_B @ sk_A)))),
% 0.59/0.83      inference('split', [status(esa)], ['0'])).
% 0.59/0.83  thf('127', plain,
% 0.59/0.83      ((((sk_B) = (k1_xboole_0)))
% 0.59/0.83         <= (~ ((v3_tex_2 @ sk_B @ sk_A)) & ((v1_zfmisc_1 @ sk_B)))),
% 0.59/0.83      inference('clc', [status(thm)], ['125', '126'])).
% 0.59/0.83  thf('128', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('129', plain,
% 0.59/0.83      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.59/0.83         <= (~ ((v3_tex_2 @ sk_B @ sk_A)) & ((v1_zfmisc_1 @ sk_B)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['127', '128'])).
% 0.59/0.83  thf('130', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.59/0.83      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.59/0.83  thf('131', plain, (~ ((v1_zfmisc_1 @ sk_B)) | ((v3_tex_2 @ sk_B @ sk_A))),
% 0.59/0.83      inference('demod', [status(thm)], ['129', '130'])).
% 0.59/0.83  thf('132', plain, ($false),
% 0.59/0.83      inference('sat_resolution*', [status(thm)], ['1', '23', '24', '131'])).
% 0.59/0.83  
% 0.59/0.83  % SZS output end Refutation
% 0.59/0.83  
% 0.59/0.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
