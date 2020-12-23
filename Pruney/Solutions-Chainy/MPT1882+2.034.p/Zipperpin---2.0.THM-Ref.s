%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ocxxTMv0Lw

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:24 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 460 expanded)
%              Number of leaves         :   25 ( 136 expanded)
%              Depth                    :   23
%              Number of atoms          :  992 (5885 expanded)
%              Number of equality atoms :   21 (  43 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v3_tex_2 @ X13 @ X14 )
      | ( v2_tex_2 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v2_tex_2 @ X18 @ X19 )
      | ( v1_zfmisc_1 @ X18 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_tdlat_3 @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v1_zfmisc_1 @ X18 )
      | ( v2_tex_2 @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_tdlat_3 @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v2_tex_2 @ X13 @ X14 )
      | ( v2_tex_2 @ ( sk_C @ X13 @ X14 ) @ X14 )
      | ( v3_tex_2 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v2_tex_2 @ X13 @ X14 )
      | ( m1_subset_1 @ ( sk_C @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v3_tex_2 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v2_tex_2 @ X18 @ X19 )
      | ( v1_zfmisc_1 @ X18 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_tdlat_3 @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
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

thf('59',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v2_tex_2 @ X13 @ X14 )
      | ( r1_tarski @ X13 @ ( sk_C @ X13 @ X14 ) )
      | ( v3_tex_2 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('62',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['59','64'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('66',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('67',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('69',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('70',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('71',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['68','71'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('73',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( sk_B
        = ( sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['65','74'])).

thf('76',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('77',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v2_tex_2 @ X13 @ X14 )
      | ( X13
       != ( sk_C @ X13 @ X14 ) )
      | ( v3_tex_2 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('79',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B @ sk_A )
    | ( sk_B
     != ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( sk_B
     != ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( sk_B
       != ( sk_C @ sk_B @ sk_A ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['76','81'])).

thf('83',plain,
    ( ( ~ ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['75','82'])).

thf('84',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['58','83'])).

thf('85',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C @ sk_B @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['59','64'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('89',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ~ ( v1_zfmisc_1 @ X16 )
      | ( X17 = X16 )
      | ~ ( r1_tarski @ X17 @ X16 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('90',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( sk_B
        = ( sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_zfmisc_1 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( sk_B
        = ( sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['87','90'])).

thf('92',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( sk_B
        = ( sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ( ~ ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['75','82'])).

thf('94',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( sk_B
        = ( sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( sk_B
        = ( sk_C @ sk_B @ sk_A ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( sk_B
        = ( sk_C @ sk_B @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( ( sk_B
       != ( sk_C @ sk_B @ sk_A ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['76','81'])).

thf('99',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('101',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B )
    | ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','23','24','101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ocxxTMv0Lw
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:44:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.38/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.61  % Solved by: fo/fo7.sh
% 0.38/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.61  % done 271 iterations in 0.156s
% 0.38/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.61  % SZS output start Refutation
% 0.38/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.61  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.38/0.61  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.61  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.38/0.61  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.38/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.61  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.38/0.61  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.38/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.61  thf(t50_tex_2, conjecture,
% 0.38/0.61    (![A:$i]:
% 0.38/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.38/0.61         ( l1_pre_topc @ A ) ) =>
% 0.38/0.61       ( ![B:$i]:
% 0.38/0.61         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.38/0.61             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.61           ( ( v3_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.38/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.61    (~( ![A:$i]:
% 0.38/0.61        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.61            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.61          ( ![B:$i]:
% 0.38/0.61            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.38/0.61                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.61              ( ( v3_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.38/0.61    inference('cnf.neg', [status(esa)], [t50_tex_2])).
% 0.38/0.61  thf('0', plain, ((~ (v1_zfmisc_1 @ sk_B) | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('1', plain, (~ ((v1_zfmisc_1 @ sk_B)) | ~ ((v3_tex_2 @ sk_B @ sk_A))),
% 0.38/0.61      inference('split', [status(esa)], ['0'])).
% 0.38/0.61  thf('2', plain, (((v1_zfmisc_1 @ sk_B) | (v3_tex_2 @ sk_B @ sk_A))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('3', plain, (((v3_tex_2 @ sk_B @ sk_A)) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.38/0.61      inference('split', [status(esa)], ['2'])).
% 0.38/0.61  thf('4', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(d7_tex_2, axiom,
% 0.38/0.61    (![A:$i]:
% 0.38/0.61     ( ( l1_pre_topc @ A ) =>
% 0.38/0.61       ( ![B:$i]:
% 0.38/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.61           ( ( v3_tex_2 @ B @ A ) <=>
% 0.38/0.61             ( ( v2_tex_2 @ B @ A ) & 
% 0.38/0.61               ( ![C:$i]:
% 0.38/0.61                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.61                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.38/0.61                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.61  thf('5', plain,
% 0.38/0.61      (![X13 : $i, X14 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.38/0.61          | ~ (v3_tex_2 @ X13 @ X14)
% 0.38/0.61          | (v2_tex_2 @ X13 @ X14)
% 0.38/0.61          | ~ (l1_pre_topc @ X14))),
% 0.38/0.61      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.38/0.61  thf('6', plain,
% 0.38/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.61        | (v2_tex_2 @ sk_B @ sk_A)
% 0.38/0.61        | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.38/0.61      inference('sup-', [status(thm)], ['4', '5'])).
% 0.38/0.61  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('8', plain, (((v2_tex_2 @ sk_B @ sk_A) | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.38/0.61      inference('demod', [status(thm)], ['6', '7'])).
% 0.38/0.61  thf('9', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['3', '8'])).
% 0.38/0.61  thf('10', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(t44_tex_2, axiom,
% 0.38/0.61    (![A:$i]:
% 0.38/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.38/0.61         ( l1_pre_topc @ A ) ) =>
% 0.38/0.61       ( ![B:$i]:
% 0.38/0.61         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.38/0.61             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.61           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.38/0.61  thf('11', plain,
% 0.38/0.61      (![X18 : $i, X19 : $i]:
% 0.38/0.61         ((v1_xboole_0 @ X18)
% 0.38/0.61          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.38/0.61          | ~ (v2_tex_2 @ X18 @ X19)
% 0.38/0.61          | (v1_zfmisc_1 @ X18)
% 0.38/0.61          | ~ (l1_pre_topc @ X19)
% 0.38/0.61          | ~ (v2_tdlat_3 @ X19)
% 0.38/0.61          | ~ (v2_pre_topc @ X19)
% 0.38/0.61          | (v2_struct_0 @ X19))),
% 0.38/0.61      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.38/0.61  thf('12', plain,
% 0.38/0.61      (((v2_struct_0 @ sk_A)
% 0.38/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.61        | ~ (v2_tdlat_3 @ sk_A)
% 0.38/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.61        | (v1_zfmisc_1 @ sk_B)
% 0.38/0.61        | ~ (v2_tex_2 @ sk_B @ sk_A)
% 0.38/0.61        | (v1_xboole_0 @ sk_B))),
% 0.38/0.61      inference('sup-', [status(thm)], ['10', '11'])).
% 0.38/0.61  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('14', plain, ((v2_tdlat_3 @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('16', plain,
% 0.38/0.61      (((v2_struct_0 @ sk_A)
% 0.38/0.61        | (v1_zfmisc_1 @ sk_B)
% 0.38/0.61        | ~ (v2_tex_2 @ sk_B @ sk_A)
% 0.38/0.61        | (v1_xboole_0 @ sk_B))),
% 0.38/0.61      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.38/0.61  thf('17', plain,
% 0.38/0.61      ((((v1_xboole_0 @ sk_B) | (v1_zfmisc_1 @ sk_B) | (v2_struct_0 @ sk_A)))
% 0.38/0.61         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['9', '16'])).
% 0.38/0.61  thf('18', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('19', plain,
% 0.38/0.61      ((((v2_struct_0 @ sk_A) | (v1_zfmisc_1 @ sk_B)))
% 0.38/0.61         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.38/0.61      inference('clc', [status(thm)], ['17', '18'])).
% 0.38/0.61  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('21', plain, (((v1_zfmisc_1 @ sk_B)) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.38/0.61      inference('clc', [status(thm)], ['19', '20'])).
% 0.38/0.61  thf('22', plain, ((~ (v1_zfmisc_1 @ sk_B)) <= (~ ((v1_zfmisc_1 @ sk_B)))),
% 0.38/0.61      inference('split', [status(esa)], ['0'])).
% 0.38/0.61  thf('23', plain, (((v1_zfmisc_1 @ sk_B)) | ~ ((v3_tex_2 @ sk_B @ sk_A))),
% 0.38/0.61      inference('sup-', [status(thm)], ['21', '22'])).
% 0.38/0.61  thf('24', plain, (((v1_zfmisc_1 @ sk_B)) | ((v3_tex_2 @ sk_B @ sk_A))),
% 0.38/0.61      inference('split', [status(esa)], ['2'])).
% 0.38/0.61  thf('25', plain, (((v1_zfmisc_1 @ sk_B)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.38/0.61      inference('split', [status(esa)], ['2'])).
% 0.38/0.61  thf('26', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('27', plain,
% 0.38/0.61      (![X18 : $i, X19 : $i]:
% 0.38/0.61         ((v1_xboole_0 @ X18)
% 0.38/0.61          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.38/0.61          | ~ (v1_zfmisc_1 @ X18)
% 0.38/0.61          | (v2_tex_2 @ X18 @ X19)
% 0.38/0.61          | ~ (l1_pre_topc @ X19)
% 0.38/0.61          | ~ (v2_tdlat_3 @ X19)
% 0.38/0.61          | ~ (v2_pre_topc @ X19)
% 0.38/0.61          | (v2_struct_0 @ X19))),
% 0.38/0.61      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.38/0.61  thf('28', plain,
% 0.38/0.61      (((v2_struct_0 @ sk_A)
% 0.38/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.61        | ~ (v2_tdlat_3 @ sk_A)
% 0.38/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.61        | (v2_tex_2 @ sk_B @ sk_A)
% 0.38/0.61        | ~ (v1_zfmisc_1 @ sk_B)
% 0.38/0.61        | (v1_xboole_0 @ sk_B))),
% 0.38/0.61      inference('sup-', [status(thm)], ['26', '27'])).
% 0.38/0.61  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('30', plain, ((v2_tdlat_3 @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('32', plain,
% 0.38/0.61      (((v2_struct_0 @ sk_A)
% 0.38/0.61        | (v2_tex_2 @ sk_B @ sk_A)
% 0.38/0.61        | ~ (v1_zfmisc_1 @ sk_B)
% 0.38/0.61        | (v1_xboole_0 @ sk_B))),
% 0.38/0.61      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 0.38/0.61  thf('33', plain,
% 0.38/0.61      ((((v1_xboole_0 @ sk_B) | (v2_tex_2 @ sk_B @ sk_A) | (v2_struct_0 @ sk_A)))
% 0.38/0.61         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['25', '32'])).
% 0.38/0.61  thf('34', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('35', plain,
% 0.38/0.61      ((((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B @ sk_A)))
% 0.38/0.61         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.38/0.61      inference('clc', [status(thm)], ['33', '34'])).
% 0.38/0.61  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('37', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.38/0.61      inference('clc', [status(thm)], ['35', '36'])).
% 0.38/0.61  thf('38', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('39', plain,
% 0.38/0.61      (![X13 : $i, X14 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.38/0.61          | ~ (v2_tex_2 @ X13 @ X14)
% 0.38/0.61          | (v2_tex_2 @ (sk_C @ X13 @ X14) @ X14)
% 0.38/0.61          | (v3_tex_2 @ X13 @ X14)
% 0.38/0.61          | ~ (l1_pre_topc @ X14))),
% 0.38/0.61      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.38/0.61  thf('40', plain,
% 0.38/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.61        | (v3_tex_2 @ sk_B @ sk_A)
% 0.38/0.61        | (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.38/0.61        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.38/0.61      inference('sup-', [status(thm)], ['38', '39'])).
% 0.38/0.61  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('42', plain,
% 0.38/0.61      (((v3_tex_2 @ sk_B @ sk_A)
% 0.38/0.61        | (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.38/0.61        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.38/0.61      inference('demod', [status(thm)], ['40', '41'])).
% 0.38/0.61  thf('43', plain,
% 0.38/0.61      ((((v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A) | (v3_tex_2 @ sk_B @ sk_A)))
% 0.38/0.61         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['37', '42'])).
% 0.38/0.61  thf('44', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.38/0.61      inference('clc', [status(thm)], ['35', '36'])).
% 0.38/0.61  thf('45', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('46', plain,
% 0.38/0.61      (![X13 : $i, X14 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.38/0.61          | ~ (v2_tex_2 @ X13 @ X14)
% 0.38/0.61          | (m1_subset_1 @ (sk_C @ X13 @ X14) @ 
% 0.38/0.61             (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.38/0.61          | (v3_tex_2 @ X13 @ X14)
% 0.38/0.61          | ~ (l1_pre_topc @ X14))),
% 0.38/0.61      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.38/0.61  thf('47', plain,
% 0.38/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.61        | (v3_tex_2 @ sk_B @ sk_A)
% 0.38/0.61        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.38/0.61           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.61        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.38/0.61      inference('sup-', [status(thm)], ['45', '46'])).
% 0.38/0.61  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('49', plain,
% 0.38/0.61      (((v3_tex_2 @ sk_B @ sk_A)
% 0.38/0.61        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.38/0.61           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.61        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.38/0.61      inference('demod', [status(thm)], ['47', '48'])).
% 0.38/0.61  thf('50', plain,
% 0.38/0.61      ((((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.38/0.61          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.61         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['44', '49'])).
% 0.38/0.61  thf('51', plain,
% 0.38/0.61      (![X18 : $i, X19 : $i]:
% 0.38/0.61         ((v1_xboole_0 @ X18)
% 0.38/0.61          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.38/0.61          | ~ (v2_tex_2 @ X18 @ X19)
% 0.38/0.61          | (v1_zfmisc_1 @ X18)
% 0.38/0.61          | ~ (l1_pre_topc @ X19)
% 0.38/0.61          | ~ (v2_tdlat_3 @ X19)
% 0.38/0.61          | ~ (v2_pre_topc @ X19)
% 0.38/0.61          | (v2_struct_0 @ X19))),
% 0.38/0.61      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.38/0.61  thf('52', plain,
% 0.38/0.61      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.38/0.61         | (v2_struct_0 @ sk_A)
% 0.38/0.61         | ~ (v2_pre_topc @ sk_A)
% 0.38/0.61         | ~ (v2_tdlat_3 @ sk_A)
% 0.38/0.61         | ~ (l1_pre_topc @ sk_A)
% 0.38/0.61         | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.61         | ~ (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.38/0.61         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['50', '51'])).
% 0.38/0.61  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('54', plain, ((v2_tdlat_3 @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('56', plain,
% 0.38/0.61      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.38/0.61         | (v2_struct_0 @ sk_A)
% 0.38/0.61         | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.61         | ~ (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.38/0.61         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.38/0.61      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 0.38/0.61  thf('57', plain,
% 0.38/0.61      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.38/0.61         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.61         | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.61         | (v2_struct_0 @ sk_A)
% 0.38/0.61         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['43', '56'])).
% 0.38/0.61  thf('58', plain,
% 0.38/0.61      ((((v2_struct_0 @ sk_A)
% 0.38/0.61         | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.61         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.61         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.38/0.61      inference('simplify', [status(thm)], ['57'])).
% 0.38/0.61  thf('59', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.38/0.61      inference('clc', [status(thm)], ['35', '36'])).
% 0.38/0.61  thf('60', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('61', plain,
% 0.38/0.61      (![X13 : $i, X14 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.38/0.61          | ~ (v2_tex_2 @ X13 @ X14)
% 0.38/0.61          | (r1_tarski @ X13 @ (sk_C @ X13 @ X14))
% 0.38/0.61          | (v3_tex_2 @ X13 @ X14)
% 0.38/0.61          | ~ (l1_pre_topc @ X14))),
% 0.38/0.61      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.38/0.61  thf('62', plain,
% 0.38/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.61        | (v3_tex_2 @ sk_B @ sk_A)
% 0.38/0.61        | (r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.38/0.61        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.38/0.61      inference('sup-', [status(thm)], ['60', '61'])).
% 0.38/0.61  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('64', plain,
% 0.38/0.61      (((v3_tex_2 @ sk_B @ sk_A)
% 0.38/0.61        | (r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.38/0.61        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.38/0.61      inference('demod', [status(thm)], ['62', '63'])).
% 0.38/0.61  thf('65', plain,
% 0.38/0.61      ((((r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A)) | (v3_tex_2 @ sk_B @ sk_A)))
% 0.38/0.61         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['59', '64'])).
% 0.38/0.61  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.38/0.61  thf('66', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.38/0.61  thf(t8_boole, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.38/0.61  thf('67', plain,
% 0.38/0.61      (![X3 : $i, X4 : $i]:
% 0.38/0.61         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 0.38/0.61      inference('cnf', [status(esa)], [t8_boole])).
% 0.38/0.61  thf('68', plain,
% 0.38/0.61      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['66', '67'])).
% 0.38/0.61  thf(t4_subset_1, axiom,
% 0.38/0.61    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.38/0.61  thf('69', plain,
% 0.38/0.61      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.38/0.61      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.38/0.61  thf(t3_subset, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.61  thf('70', plain,
% 0.38/0.61      (![X6 : $i, X7 : $i]:
% 0.38/0.61         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.38/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.61  thf('71', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.38/0.61      inference('sup-', [status(thm)], ['69', '70'])).
% 0.38/0.61  thf('72', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['68', '71'])).
% 0.38/0.61  thf(d10_xboole_0, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.61  thf('73', plain,
% 0.38/0.61      (![X0 : $i, X2 : $i]:
% 0.38/0.61         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.38/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.61  thf('74', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['72', '73'])).
% 0.38/0.61  thf('75', plain,
% 0.38/0.61      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.38/0.61         | ((sk_B) = (sk_C @ sk_B @ sk_A))
% 0.38/0.61         | ~ (v1_xboole_0 @ (sk_C @ sk_B @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['65', '74'])).
% 0.38/0.61  thf('76', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.38/0.61      inference('clc', [status(thm)], ['35', '36'])).
% 0.38/0.61  thf('77', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('78', plain,
% 0.38/0.61      (![X13 : $i, X14 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.38/0.61          | ~ (v2_tex_2 @ X13 @ X14)
% 0.38/0.61          | ((X13) != (sk_C @ X13 @ X14))
% 0.38/0.61          | (v3_tex_2 @ X13 @ X14)
% 0.38/0.61          | ~ (l1_pre_topc @ X14))),
% 0.38/0.61      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.38/0.61  thf('79', plain,
% 0.38/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.61        | (v3_tex_2 @ sk_B @ sk_A)
% 0.38/0.61        | ((sk_B) != (sk_C @ sk_B @ sk_A))
% 0.38/0.61        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.38/0.61      inference('sup-', [status(thm)], ['77', '78'])).
% 0.38/0.61  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('81', plain,
% 0.38/0.61      (((v3_tex_2 @ sk_B @ sk_A)
% 0.38/0.61        | ((sk_B) != (sk_C @ sk_B @ sk_A))
% 0.38/0.61        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.38/0.61      inference('demod', [status(thm)], ['79', '80'])).
% 0.38/0.61  thf('82', plain,
% 0.38/0.61      (((((sk_B) != (sk_C @ sk_B @ sk_A)) | (v3_tex_2 @ sk_B @ sk_A)))
% 0.38/0.61         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['76', '81'])).
% 0.38/0.61  thf('83', plain,
% 0.38/0.61      (((~ (v1_xboole_0 @ (sk_C @ sk_B @ sk_A)) | (v3_tex_2 @ sk_B @ sk_A)))
% 0.38/0.61         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.38/0.61      inference('clc', [status(thm)], ['75', '82'])).
% 0.38/0.61  thf('84', plain,
% 0.38/0.61      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.38/0.61         | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.61         | (v2_struct_0 @ sk_A)
% 0.38/0.61         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['58', '83'])).
% 0.38/0.61  thf('85', plain,
% 0.38/0.61      ((((v2_struct_0 @ sk_A)
% 0.38/0.61         | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.61         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.38/0.61      inference('simplify', [status(thm)], ['84'])).
% 0.38/0.61  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('87', plain,
% 0.38/0.61      ((((v3_tex_2 @ sk_B @ sk_A) | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))))
% 0.38/0.61         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.38/0.61      inference('clc', [status(thm)], ['85', '86'])).
% 0.38/0.61  thf('88', plain,
% 0.38/0.61      ((((r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A)) | (v3_tex_2 @ sk_B @ sk_A)))
% 0.38/0.61         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['59', '64'])).
% 0.38/0.61  thf(t1_tex_2, axiom,
% 0.38/0.61    (![A:$i]:
% 0.38/0.61     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.38/0.61       ( ![B:$i]:
% 0.38/0.61         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.38/0.61           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.38/0.61  thf('89', plain,
% 0.38/0.61      (![X16 : $i, X17 : $i]:
% 0.38/0.61         ((v1_xboole_0 @ X16)
% 0.38/0.61          | ~ (v1_zfmisc_1 @ X16)
% 0.38/0.61          | ((X17) = (X16))
% 0.38/0.61          | ~ (r1_tarski @ X17 @ X16)
% 0.38/0.61          | (v1_xboole_0 @ X17))),
% 0.38/0.61      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.38/0.61  thf('90', plain,
% 0.38/0.61      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.38/0.61         | (v1_xboole_0 @ sk_B)
% 0.38/0.61         | ((sk_B) = (sk_C @ sk_B @ sk_A))
% 0.38/0.61         | ~ (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.61         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['88', '89'])).
% 0.38/0.61  thf('91', plain,
% 0.38/0.61      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.38/0.61         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.61         | ((sk_B) = (sk_C @ sk_B @ sk_A))
% 0.38/0.61         | (v1_xboole_0 @ sk_B)
% 0.38/0.61         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['87', '90'])).
% 0.38/0.61  thf('92', plain,
% 0.38/0.61      ((((v1_xboole_0 @ sk_B)
% 0.38/0.61         | ((sk_B) = (sk_C @ sk_B @ sk_A))
% 0.38/0.61         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.61         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.38/0.61      inference('simplify', [status(thm)], ['91'])).
% 0.38/0.61  thf('93', plain,
% 0.38/0.61      (((~ (v1_xboole_0 @ (sk_C @ sk_B @ sk_A)) | (v3_tex_2 @ sk_B @ sk_A)))
% 0.38/0.61         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.38/0.61      inference('clc', [status(thm)], ['75', '82'])).
% 0.38/0.61  thf('94', plain,
% 0.38/0.61      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.38/0.61         | ((sk_B) = (sk_C @ sk_B @ sk_A))
% 0.38/0.61         | (v1_xboole_0 @ sk_B)
% 0.38/0.61         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['92', '93'])).
% 0.38/0.61  thf('95', plain,
% 0.38/0.61      ((((v1_xboole_0 @ sk_B)
% 0.38/0.61         | ((sk_B) = (sk_C @ sk_B @ sk_A))
% 0.38/0.61         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.38/0.61      inference('simplify', [status(thm)], ['94'])).
% 0.38/0.61  thf('96', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('97', plain,
% 0.38/0.61      ((((v3_tex_2 @ sk_B @ sk_A) | ((sk_B) = (sk_C @ sk_B @ sk_A))))
% 0.38/0.61         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.38/0.61      inference('clc', [status(thm)], ['95', '96'])).
% 0.38/0.61  thf('98', plain,
% 0.38/0.61      (((((sk_B) != (sk_C @ sk_B @ sk_A)) | (v3_tex_2 @ sk_B @ sk_A)))
% 0.38/0.61         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['76', '81'])).
% 0.38/0.61  thf('99', plain, (((v3_tex_2 @ sk_B @ sk_A)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.38/0.61      inference('clc', [status(thm)], ['97', '98'])).
% 0.38/0.61  thf('100', plain,
% 0.38/0.61      ((~ (v3_tex_2 @ sk_B @ sk_A)) <= (~ ((v3_tex_2 @ sk_B @ sk_A)))),
% 0.38/0.61      inference('split', [status(esa)], ['0'])).
% 0.38/0.61  thf('101', plain, (~ ((v1_zfmisc_1 @ sk_B)) | ((v3_tex_2 @ sk_B @ sk_A))),
% 0.38/0.61      inference('sup-', [status(thm)], ['99', '100'])).
% 0.38/0.61  thf('102', plain, ($false),
% 0.38/0.61      inference('sat_resolution*', [status(thm)], ['1', '23', '24', '101'])).
% 0.38/0.61  
% 0.38/0.61  % SZS output end Refutation
% 0.38/0.61  
% 0.38/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
