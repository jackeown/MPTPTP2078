%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6XeooswOuM

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:20 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 384 expanded)
%              Number of leaves         :   30 ( 116 expanded)
%              Depth                    :   27
%              Number of atoms          : 1096 (4876 expanded)
%              Number of equality atoms :   35 (  44 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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

thf(cc1_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_zfmisc_1 @ A ) ) )).

thf('59',plain,(
    ! [X11: $i] :
      ( ( v1_zfmisc_1 @ X11 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v2_tex_2 @ X13 @ X14 )
      | ( r1_tarski @ X13 @ ( sk_C @ X13 @ X14 ) )
      | ( v3_tex_2 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ~ ( v1_zfmisc_1 @ X16 )
      | ( X17 = X16 )
      | ~ ( r1_tarski @ X17 @ X16 )
      | ( v1_xboole_0 @ X17 ) ) ),
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

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('75',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('76',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_xboole_0 @ X9 )
      | ~ ( v1_xboole_0 @ X10 )
      | ( X9 = X10 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( sk_B
        = ( sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( k1_xboole_0
        = ( sk_C @ sk_B @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('80',plain,
    ( ( ( k1_xboole_0
        = ( sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( sk_B
        = ( sk_C @ sk_B @ sk_A ) ) )
   <= ( ~ ( v3_tex_2 @ sk_B @ sk_A )
      & ( v1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( ( sk_B
        = ( sk_C @ sk_B @ sk_A ) )
      | ( k1_xboole_0
        = ( sk_C @ sk_B @ sk_A ) ) )
   <= ( ~ ( v3_tex_2 @ sk_B @ sk_A )
      & ( v1_zfmisc_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('84',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v2_tex_2 @ X13 @ X14 )
      | ( X13
       != ( sk_C @ X13 @ X14 ) )
      | ( v3_tex_2 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('86',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B @ sk_A )
    | ( sk_B
     != ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( sk_B
     != ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ( sk_B
       != ( sk_C @ sk_B @ sk_A ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['83','88'])).

thf('90',plain,
    ( ( ( sk_B != sk_B )
      | ( k1_xboole_0
        = ( sk_C @ sk_B @ sk_A ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( ~ ( v3_tex_2 @ sk_B @ sk_A )
      & ( v1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['82','89'])).

thf('91',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( k1_xboole_0
        = ( sk_C @ sk_B @ sk_A ) ) )
   <= ( ~ ( v3_tex_2 @ sk_B @ sk_A )
      & ( v1_zfmisc_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('93',plain,
    ( ( k1_xboole_0
      = ( sk_C @ sk_B @ sk_A ) )
   <= ( ~ ( v3_tex_2 @ sk_B @ sk_A )
      & ( v1_zfmisc_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['64','69'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('95',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('96',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ~ ( r1_tarski @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_C @ sk_B @ sk_A )
        = sk_B ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ( sk_B
       != ( sk_C @ sk_B @ sk_A ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['83','88'])).

thf('98',plain,
    ( ( ~ ( r1_tarski @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_B )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( ~ ( v3_tex_2 @ sk_B @ sk_A )
      & ( v1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['93','98'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('100',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('101',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('103',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['102','103'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('105',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
   <= ( ~ ( v3_tex_2 @ sk_B @ sk_A )
      & ( v1_zfmisc_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['99','106'])).

thf('108',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('109',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B )
    | ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','23','24','109'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6XeooswOuM
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:28:18 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.69/0.86  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.69/0.86  % Solved by: fo/fo7.sh
% 0.69/0.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.86  % done 409 iterations in 0.416s
% 0.69/0.86  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.69/0.86  % SZS output start Refutation
% 0.69/0.86  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.69/0.86  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.69/0.86  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.69/0.86  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.69/0.86  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.69/0.86  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.69/0.86  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.69/0.86  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.69/0.86  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.69/0.86  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.86  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.69/0.86  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.69/0.86  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.69/0.86  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.69/0.86  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.69/0.86  thf(sk_B_type, type, sk_B: $i).
% 0.69/0.86  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.69/0.86  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.69/0.86  thf(t50_tex_2, conjecture,
% 0.69/0.86    (![A:$i]:
% 0.69/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.69/0.86         ( l1_pre_topc @ A ) ) =>
% 0.69/0.86       ( ![B:$i]:
% 0.69/0.86         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.69/0.86             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.69/0.86           ( ( v3_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.69/0.86  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.86    (~( ![A:$i]:
% 0.69/0.86        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.69/0.86            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.69/0.86          ( ![B:$i]:
% 0.69/0.86            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.69/0.86                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.69/0.86              ( ( v3_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.69/0.86    inference('cnf.neg', [status(esa)], [t50_tex_2])).
% 0.69/0.86  thf('0', plain, ((~ (v1_zfmisc_1 @ sk_B) | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('1', plain, (~ ((v1_zfmisc_1 @ sk_B)) | ~ ((v3_tex_2 @ sk_B @ sk_A))),
% 0.69/0.86      inference('split', [status(esa)], ['0'])).
% 0.69/0.86  thf('2', plain, (((v1_zfmisc_1 @ sk_B) | (v3_tex_2 @ sk_B @ sk_A))),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('3', plain, (((v3_tex_2 @ sk_B @ sk_A)) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.69/0.86      inference('split', [status(esa)], ['2'])).
% 0.69/0.86  thf('4', plain,
% 0.69/0.86      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf(d7_tex_2, axiom,
% 0.69/0.86    (![A:$i]:
% 0.69/0.86     ( ( l1_pre_topc @ A ) =>
% 0.69/0.86       ( ![B:$i]:
% 0.69/0.86         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.86           ( ( v3_tex_2 @ B @ A ) <=>
% 0.69/0.86             ( ( v2_tex_2 @ B @ A ) & 
% 0.69/0.86               ( ![C:$i]:
% 0.69/0.86                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.86                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.69/0.86                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.69/0.86  thf('5', plain,
% 0.69/0.86      (![X13 : $i, X14 : $i]:
% 0.69/0.86         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.69/0.86          | ~ (v3_tex_2 @ X13 @ X14)
% 0.69/0.86          | (v2_tex_2 @ X13 @ X14)
% 0.69/0.86          | ~ (l1_pre_topc @ X14))),
% 0.69/0.86      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.69/0.86  thf('6', plain,
% 0.69/0.86      ((~ (l1_pre_topc @ sk_A)
% 0.69/0.86        | (v2_tex_2 @ sk_B @ sk_A)
% 0.69/0.86        | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.69/0.86      inference('sup-', [status(thm)], ['4', '5'])).
% 0.69/0.86  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('8', plain, (((v2_tex_2 @ sk_B @ sk_A) | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.69/0.86      inference('demod', [status(thm)], ['6', '7'])).
% 0.69/0.86  thf('9', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.69/0.86      inference('sup-', [status(thm)], ['3', '8'])).
% 0.69/0.86  thf('10', plain,
% 0.69/0.86      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf(t44_tex_2, axiom,
% 0.69/0.86    (![A:$i]:
% 0.69/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.69/0.86         ( l1_pre_topc @ A ) ) =>
% 0.69/0.87       ( ![B:$i]:
% 0.69/0.87         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.69/0.87             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.69/0.87           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.69/0.87  thf('11', plain,
% 0.69/0.87      (![X18 : $i, X19 : $i]:
% 0.69/0.87         ((v1_xboole_0 @ X18)
% 0.69/0.87          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.69/0.87          | ~ (v2_tex_2 @ X18 @ X19)
% 0.69/0.87          | (v1_zfmisc_1 @ X18)
% 0.69/0.87          | ~ (l1_pre_topc @ X19)
% 0.69/0.87          | ~ (v2_tdlat_3 @ X19)
% 0.69/0.87          | ~ (v2_pre_topc @ X19)
% 0.69/0.87          | (v2_struct_0 @ X19))),
% 0.69/0.87      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.69/0.87  thf('12', plain,
% 0.69/0.87      (((v2_struct_0 @ sk_A)
% 0.69/0.87        | ~ (v2_pre_topc @ sk_A)
% 0.69/0.87        | ~ (v2_tdlat_3 @ sk_A)
% 0.69/0.87        | ~ (l1_pre_topc @ sk_A)
% 0.69/0.87        | (v1_zfmisc_1 @ sk_B)
% 0.69/0.87        | ~ (v2_tex_2 @ sk_B @ sk_A)
% 0.69/0.87        | (v1_xboole_0 @ sk_B))),
% 0.69/0.87      inference('sup-', [status(thm)], ['10', '11'])).
% 0.69/0.87  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('14', plain, ((v2_tdlat_3 @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('16', plain,
% 0.69/0.87      (((v2_struct_0 @ sk_A)
% 0.69/0.87        | (v1_zfmisc_1 @ sk_B)
% 0.69/0.87        | ~ (v2_tex_2 @ sk_B @ sk_A)
% 0.69/0.87        | (v1_xboole_0 @ sk_B))),
% 0.69/0.87      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.69/0.87  thf('17', plain,
% 0.69/0.87      ((((v1_xboole_0 @ sk_B) | (v1_zfmisc_1 @ sk_B) | (v2_struct_0 @ sk_A)))
% 0.69/0.87         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['9', '16'])).
% 0.69/0.87  thf('18', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('19', plain,
% 0.69/0.87      ((((v2_struct_0 @ sk_A) | (v1_zfmisc_1 @ sk_B)))
% 0.69/0.87         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.69/0.87      inference('clc', [status(thm)], ['17', '18'])).
% 0.69/0.87  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('21', plain, (((v1_zfmisc_1 @ sk_B)) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.69/0.87      inference('clc', [status(thm)], ['19', '20'])).
% 0.69/0.87  thf('22', plain, ((~ (v1_zfmisc_1 @ sk_B)) <= (~ ((v1_zfmisc_1 @ sk_B)))),
% 0.69/0.87      inference('split', [status(esa)], ['0'])).
% 0.69/0.87  thf('23', plain, (((v1_zfmisc_1 @ sk_B)) | ~ ((v3_tex_2 @ sk_B @ sk_A))),
% 0.69/0.87      inference('sup-', [status(thm)], ['21', '22'])).
% 0.69/0.87  thf('24', plain, (((v1_zfmisc_1 @ sk_B)) | ((v3_tex_2 @ sk_B @ sk_A))),
% 0.69/0.87      inference('split', [status(esa)], ['2'])).
% 0.69/0.87  thf('25', plain, (((v1_zfmisc_1 @ sk_B)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.69/0.87      inference('split', [status(esa)], ['2'])).
% 0.69/0.87  thf('26', plain,
% 0.69/0.87      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('27', plain,
% 0.69/0.87      (![X18 : $i, X19 : $i]:
% 0.69/0.87         ((v1_xboole_0 @ X18)
% 0.69/0.87          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.69/0.87          | ~ (v1_zfmisc_1 @ X18)
% 0.69/0.87          | (v2_tex_2 @ X18 @ X19)
% 0.69/0.87          | ~ (l1_pre_topc @ X19)
% 0.69/0.87          | ~ (v2_tdlat_3 @ X19)
% 0.69/0.87          | ~ (v2_pre_topc @ X19)
% 0.69/0.87          | (v2_struct_0 @ X19))),
% 0.69/0.87      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.69/0.87  thf('28', plain,
% 0.69/0.87      (((v2_struct_0 @ sk_A)
% 0.69/0.87        | ~ (v2_pre_topc @ sk_A)
% 0.69/0.87        | ~ (v2_tdlat_3 @ sk_A)
% 0.69/0.87        | ~ (l1_pre_topc @ sk_A)
% 0.69/0.87        | (v2_tex_2 @ sk_B @ sk_A)
% 0.69/0.87        | ~ (v1_zfmisc_1 @ sk_B)
% 0.69/0.87        | (v1_xboole_0 @ sk_B))),
% 0.69/0.87      inference('sup-', [status(thm)], ['26', '27'])).
% 0.69/0.87  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('30', plain, ((v2_tdlat_3 @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('32', plain,
% 0.69/0.87      (((v2_struct_0 @ sk_A)
% 0.69/0.87        | (v2_tex_2 @ sk_B @ sk_A)
% 0.69/0.87        | ~ (v1_zfmisc_1 @ sk_B)
% 0.69/0.87        | (v1_xboole_0 @ sk_B))),
% 0.69/0.87      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 0.69/0.87  thf('33', plain,
% 0.69/0.87      ((((v1_xboole_0 @ sk_B) | (v2_tex_2 @ sk_B @ sk_A) | (v2_struct_0 @ sk_A)))
% 0.69/0.87         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['25', '32'])).
% 0.69/0.87  thf('34', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('35', plain,
% 0.69/0.87      ((((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B @ sk_A)))
% 0.69/0.87         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.69/0.87      inference('clc', [status(thm)], ['33', '34'])).
% 0.69/0.87  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('37', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.69/0.87      inference('clc', [status(thm)], ['35', '36'])).
% 0.69/0.87  thf('38', plain,
% 0.69/0.87      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('39', plain,
% 0.69/0.87      (![X13 : $i, X14 : $i]:
% 0.69/0.87         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.69/0.87          | ~ (v2_tex_2 @ X13 @ X14)
% 0.69/0.87          | (v2_tex_2 @ (sk_C @ X13 @ X14) @ X14)
% 0.69/0.87          | (v3_tex_2 @ X13 @ X14)
% 0.69/0.87          | ~ (l1_pre_topc @ X14))),
% 0.69/0.87      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.69/0.87  thf('40', plain,
% 0.69/0.87      ((~ (l1_pre_topc @ sk_A)
% 0.69/0.87        | (v3_tex_2 @ sk_B @ sk_A)
% 0.69/0.87        | (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.69/0.87        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.69/0.87      inference('sup-', [status(thm)], ['38', '39'])).
% 0.69/0.87  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('42', plain,
% 0.69/0.87      (((v3_tex_2 @ sk_B @ sk_A)
% 0.69/0.87        | (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.69/0.87        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.69/0.87      inference('demod', [status(thm)], ['40', '41'])).
% 0.69/0.87  thf('43', plain,
% 0.69/0.87      ((((v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A) | (v3_tex_2 @ sk_B @ sk_A)))
% 0.69/0.87         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['37', '42'])).
% 0.69/0.87  thf('44', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.69/0.87      inference('clc', [status(thm)], ['35', '36'])).
% 0.69/0.87  thf('45', plain,
% 0.69/0.87      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('46', plain,
% 0.69/0.87      (![X13 : $i, X14 : $i]:
% 0.69/0.87         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.69/0.87          | ~ (v2_tex_2 @ X13 @ X14)
% 0.69/0.87          | (m1_subset_1 @ (sk_C @ X13 @ X14) @ 
% 0.69/0.87             (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.69/0.87          | (v3_tex_2 @ X13 @ X14)
% 0.69/0.87          | ~ (l1_pre_topc @ X14))),
% 0.69/0.87      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.69/0.87  thf('47', plain,
% 0.69/0.87      ((~ (l1_pre_topc @ sk_A)
% 0.69/0.87        | (v3_tex_2 @ sk_B @ sk_A)
% 0.69/0.87        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.69/0.87           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.69/0.87        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.69/0.87      inference('sup-', [status(thm)], ['45', '46'])).
% 0.69/0.87  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('49', plain,
% 0.69/0.87      (((v3_tex_2 @ sk_B @ sk_A)
% 0.69/0.87        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.69/0.87           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.69/0.87        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.69/0.87      inference('demod', [status(thm)], ['47', '48'])).
% 0.69/0.87  thf('50', plain,
% 0.69/0.87      ((((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.69/0.87          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.69/0.87         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['44', '49'])).
% 0.69/0.87  thf('51', plain,
% 0.69/0.87      (![X18 : $i, X19 : $i]:
% 0.69/0.87         ((v1_xboole_0 @ X18)
% 0.69/0.87          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.69/0.87          | ~ (v2_tex_2 @ X18 @ X19)
% 0.69/0.87          | (v1_zfmisc_1 @ X18)
% 0.69/0.87          | ~ (l1_pre_topc @ X19)
% 0.69/0.87          | ~ (v2_tdlat_3 @ X19)
% 0.69/0.87          | ~ (v2_pre_topc @ X19)
% 0.69/0.87          | (v2_struct_0 @ X19))),
% 0.69/0.87      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.69/0.87  thf('52', plain,
% 0.69/0.87      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.69/0.87         | (v2_struct_0 @ sk_A)
% 0.69/0.87         | ~ (v2_pre_topc @ sk_A)
% 0.69/0.87         | ~ (v2_tdlat_3 @ sk_A)
% 0.69/0.87         | ~ (l1_pre_topc @ sk_A)
% 0.69/0.87         | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.69/0.87         | ~ (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.69/0.87         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['50', '51'])).
% 0.69/0.87  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('54', plain, ((v2_tdlat_3 @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('56', plain,
% 0.69/0.87      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.69/0.87         | (v2_struct_0 @ sk_A)
% 0.69/0.87         | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.69/0.87         | ~ (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.69/0.87         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.69/0.87      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 0.69/0.87  thf('57', plain,
% 0.69/0.87      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.69/0.87         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.69/0.87         | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.69/0.87         | (v2_struct_0 @ sk_A)
% 0.69/0.87         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['43', '56'])).
% 0.69/0.87  thf('58', plain,
% 0.69/0.87      ((((v2_struct_0 @ sk_A)
% 0.69/0.87         | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.69/0.87         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.69/0.87         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.69/0.87      inference('simplify', [status(thm)], ['57'])).
% 0.69/0.87  thf(cc1_zfmisc_1, axiom,
% 0.69/0.87    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_zfmisc_1 @ A ) ))).
% 0.69/0.87  thf('59', plain,
% 0.69/0.87      (![X11 : $i]: ((v1_zfmisc_1 @ X11) | ~ (v1_xboole_0 @ X11))),
% 0.69/0.87      inference('cnf', [status(esa)], [cc1_zfmisc_1])).
% 0.69/0.87  thf('60', plain,
% 0.69/0.87      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.69/0.87         | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.69/0.87         | (v2_struct_0 @ sk_A)
% 0.69/0.87         | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['58', '59'])).
% 0.69/0.87  thf('61', plain,
% 0.69/0.87      ((((v2_struct_0 @ sk_A)
% 0.69/0.87         | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.69/0.87         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.69/0.87      inference('simplify', [status(thm)], ['60'])).
% 0.69/0.87  thf('62', plain, (~ (v2_struct_0 @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('63', plain,
% 0.69/0.87      ((((v3_tex_2 @ sk_B @ sk_A) | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))))
% 0.69/0.87         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.69/0.87      inference('clc', [status(thm)], ['61', '62'])).
% 0.69/0.87  thf('64', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.69/0.87      inference('clc', [status(thm)], ['35', '36'])).
% 0.69/0.87  thf('65', plain,
% 0.69/0.87      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('66', plain,
% 0.69/0.87      (![X13 : $i, X14 : $i]:
% 0.69/0.87         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.69/0.87          | ~ (v2_tex_2 @ X13 @ X14)
% 0.69/0.87          | (r1_tarski @ X13 @ (sk_C @ X13 @ X14))
% 0.69/0.87          | (v3_tex_2 @ X13 @ X14)
% 0.69/0.87          | ~ (l1_pre_topc @ X14))),
% 0.69/0.87      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.69/0.87  thf('67', plain,
% 0.69/0.87      ((~ (l1_pre_topc @ sk_A)
% 0.69/0.87        | (v3_tex_2 @ sk_B @ sk_A)
% 0.69/0.87        | (r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.69/0.87        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.69/0.87      inference('sup-', [status(thm)], ['65', '66'])).
% 0.69/0.87  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('69', plain,
% 0.69/0.87      (((v3_tex_2 @ sk_B @ sk_A)
% 0.69/0.87        | (r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.69/0.87        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.69/0.87      inference('demod', [status(thm)], ['67', '68'])).
% 0.69/0.87  thf('70', plain,
% 0.69/0.87      ((((r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A)) | (v3_tex_2 @ sk_B @ sk_A)))
% 0.69/0.87         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['64', '69'])).
% 0.69/0.87  thf(t1_tex_2, axiom,
% 0.69/0.87    (![A:$i]:
% 0.69/0.87     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.69/0.87       ( ![B:$i]:
% 0.69/0.87         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.69/0.87           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.69/0.87  thf('71', plain,
% 0.69/0.87      (![X16 : $i, X17 : $i]:
% 0.69/0.87         ((v1_xboole_0 @ X16)
% 0.69/0.87          | ~ (v1_zfmisc_1 @ X16)
% 0.69/0.87          | ((X17) = (X16))
% 0.69/0.87          | ~ (r1_tarski @ X17 @ X16)
% 0.69/0.87          | (v1_xboole_0 @ X17))),
% 0.69/0.87      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.69/0.87  thf('72', plain,
% 0.69/0.87      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.69/0.87         | (v1_xboole_0 @ sk_B)
% 0.69/0.87         | ((sk_B) = (sk_C @ sk_B @ sk_A))
% 0.69/0.87         | ~ (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.69/0.87         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['70', '71'])).
% 0.69/0.87  thf('73', plain,
% 0.69/0.87      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.69/0.87         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.69/0.87         | ((sk_B) = (sk_C @ sk_B @ sk_A))
% 0.69/0.87         | (v1_xboole_0 @ sk_B)
% 0.69/0.87         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['63', '72'])).
% 0.69/0.87  thf('74', plain,
% 0.69/0.87      ((((v1_xboole_0 @ sk_B)
% 0.69/0.87         | ((sk_B) = (sk_C @ sk_B @ sk_A))
% 0.69/0.87         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.69/0.87         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.69/0.87      inference('simplify', [status(thm)], ['73'])).
% 0.69/0.87  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.69/0.87  thf('75', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.69/0.87      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.69/0.87  thf(t8_boole, axiom,
% 0.69/0.87    (![A:$i,B:$i]:
% 0.69/0.87     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.69/0.87  thf('76', plain,
% 0.69/0.87      (![X9 : $i, X10 : $i]:
% 0.69/0.87         (~ (v1_xboole_0 @ X9) | ~ (v1_xboole_0 @ X10) | ((X9) = (X10)))),
% 0.69/0.87      inference('cnf', [status(esa)], [t8_boole])).
% 0.69/0.87  thf('77', plain,
% 0.69/0.87      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.69/0.87      inference('sup-', [status(thm)], ['75', '76'])).
% 0.69/0.87  thf('78', plain,
% 0.69/0.87      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.69/0.87         | ((sk_B) = (sk_C @ sk_B @ sk_A))
% 0.69/0.87         | (v1_xboole_0 @ sk_B)
% 0.69/0.87         | ((k1_xboole_0) = (sk_C @ sk_B @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['74', '77'])).
% 0.69/0.87  thf('79', plain,
% 0.69/0.87      ((~ (v3_tex_2 @ sk_B @ sk_A)) <= (~ ((v3_tex_2 @ sk_B @ sk_A)))),
% 0.69/0.87      inference('split', [status(esa)], ['0'])).
% 0.69/0.87  thf('80', plain,
% 0.69/0.87      (((((k1_xboole_0) = (sk_C @ sk_B @ sk_A))
% 0.69/0.87         | (v1_xboole_0 @ sk_B)
% 0.69/0.87         | ((sk_B) = (sk_C @ sk_B @ sk_A))))
% 0.69/0.87         <= (~ ((v3_tex_2 @ sk_B @ sk_A)) & ((v1_zfmisc_1 @ sk_B)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['78', '79'])).
% 0.69/0.87  thf('81', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('82', plain,
% 0.69/0.87      (((((sk_B) = (sk_C @ sk_B @ sk_A))
% 0.69/0.87         | ((k1_xboole_0) = (sk_C @ sk_B @ sk_A))))
% 0.69/0.87         <= (~ ((v3_tex_2 @ sk_B @ sk_A)) & ((v1_zfmisc_1 @ sk_B)))),
% 0.69/0.87      inference('clc', [status(thm)], ['80', '81'])).
% 0.69/0.87  thf('83', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.69/0.87      inference('clc', [status(thm)], ['35', '36'])).
% 0.69/0.87  thf('84', plain,
% 0.69/0.87      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('85', plain,
% 0.69/0.87      (![X13 : $i, X14 : $i]:
% 0.69/0.87         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.69/0.87          | ~ (v2_tex_2 @ X13 @ X14)
% 0.69/0.87          | ((X13) != (sk_C @ X13 @ X14))
% 0.69/0.87          | (v3_tex_2 @ X13 @ X14)
% 0.69/0.87          | ~ (l1_pre_topc @ X14))),
% 0.69/0.87      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.69/0.87  thf('86', plain,
% 0.69/0.87      ((~ (l1_pre_topc @ sk_A)
% 0.69/0.87        | (v3_tex_2 @ sk_B @ sk_A)
% 0.69/0.87        | ((sk_B) != (sk_C @ sk_B @ sk_A))
% 0.69/0.87        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.69/0.87      inference('sup-', [status(thm)], ['84', '85'])).
% 0.69/0.87  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('88', plain,
% 0.69/0.87      (((v3_tex_2 @ sk_B @ sk_A)
% 0.69/0.87        | ((sk_B) != (sk_C @ sk_B @ sk_A))
% 0.69/0.87        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.69/0.87      inference('demod', [status(thm)], ['86', '87'])).
% 0.69/0.87  thf('89', plain,
% 0.69/0.87      (((((sk_B) != (sk_C @ sk_B @ sk_A)) | (v3_tex_2 @ sk_B @ sk_A)))
% 0.69/0.87         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['83', '88'])).
% 0.69/0.87  thf('90', plain,
% 0.69/0.87      (((((sk_B) != (sk_B))
% 0.69/0.87         | ((k1_xboole_0) = (sk_C @ sk_B @ sk_A))
% 0.69/0.87         | (v3_tex_2 @ sk_B @ sk_A)))
% 0.69/0.87         <= (~ ((v3_tex_2 @ sk_B @ sk_A)) & ((v1_zfmisc_1 @ sk_B)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['82', '89'])).
% 0.69/0.87  thf('91', plain,
% 0.69/0.87      ((((v3_tex_2 @ sk_B @ sk_A) | ((k1_xboole_0) = (sk_C @ sk_B @ sk_A))))
% 0.69/0.87         <= (~ ((v3_tex_2 @ sk_B @ sk_A)) & ((v1_zfmisc_1 @ sk_B)))),
% 0.69/0.87      inference('simplify', [status(thm)], ['90'])).
% 0.69/0.87  thf('92', plain,
% 0.69/0.87      ((~ (v3_tex_2 @ sk_B @ sk_A)) <= (~ ((v3_tex_2 @ sk_B @ sk_A)))),
% 0.69/0.87      inference('split', [status(esa)], ['0'])).
% 0.69/0.87  thf('93', plain,
% 0.69/0.87      ((((k1_xboole_0) = (sk_C @ sk_B @ sk_A)))
% 0.69/0.87         <= (~ ((v3_tex_2 @ sk_B @ sk_A)) & ((v1_zfmisc_1 @ sk_B)))),
% 0.69/0.87      inference('clc', [status(thm)], ['91', '92'])).
% 0.69/0.87  thf('94', plain,
% 0.69/0.87      ((((r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A)) | (v3_tex_2 @ sk_B @ sk_A)))
% 0.69/0.87         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['64', '69'])).
% 0.69/0.87  thf(d10_xboole_0, axiom,
% 0.69/0.87    (![A:$i,B:$i]:
% 0.69/0.87     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.69/0.87  thf('95', plain,
% 0.69/0.87      (![X0 : $i, X2 : $i]:
% 0.69/0.87         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.69/0.87      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.69/0.87  thf('96', plain,
% 0.69/0.87      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.69/0.87         | ~ (r1_tarski @ (sk_C @ sk_B @ sk_A) @ sk_B)
% 0.69/0.87         | ((sk_C @ sk_B @ sk_A) = (sk_B)))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['94', '95'])).
% 0.69/0.87  thf('97', plain,
% 0.69/0.87      (((((sk_B) != (sk_C @ sk_B @ sk_A)) | (v3_tex_2 @ sk_B @ sk_A)))
% 0.69/0.87         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['83', '88'])).
% 0.69/0.87  thf('98', plain,
% 0.69/0.87      (((~ (r1_tarski @ (sk_C @ sk_B @ sk_A) @ sk_B) | (v3_tex_2 @ sk_B @ sk_A)))
% 0.69/0.87         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.69/0.87      inference('clc', [status(thm)], ['96', '97'])).
% 0.69/0.87  thf('99', plain,
% 0.69/0.87      (((~ (r1_tarski @ k1_xboole_0 @ sk_B) | (v3_tex_2 @ sk_B @ sk_A)))
% 0.69/0.87         <= (~ ((v3_tex_2 @ sk_B @ sk_A)) & ((v1_zfmisc_1 @ sk_B)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['93', '98'])).
% 0.69/0.87  thf(t3_boole, axiom,
% 0.69/0.87    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.69/0.87  thf('100', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.69/0.87      inference('cnf', [status(esa)], [t3_boole])).
% 0.69/0.87  thf(t48_xboole_1, axiom,
% 0.69/0.87    (![A:$i,B:$i]:
% 0.69/0.87     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.69/0.87  thf('101', plain,
% 0.69/0.87      (![X7 : $i, X8 : $i]:
% 0.69/0.87         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.69/0.87           = (k3_xboole_0 @ X7 @ X8))),
% 0.69/0.87      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.69/0.87  thf('102', plain,
% 0.69/0.87      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.69/0.87      inference('sup+', [status(thm)], ['100', '101'])).
% 0.69/0.87  thf(t2_boole, axiom,
% 0.69/0.87    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.69/0.87  thf('103', plain,
% 0.69/0.87      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.69/0.87      inference('cnf', [status(esa)], [t2_boole])).
% 0.69/0.87  thf('104', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.69/0.87      inference('demod', [status(thm)], ['102', '103'])).
% 0.69/0.87  thf(t36_xboole_1, axiom,
% 0.69/0.87    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.69/0.87  thf('105', plain,
% 0.69/0.87      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 0.69/0.87      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.69/0.87  thf('106', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.69/0.87      inference('sup+', [status(thm)], ['104', '105'])).
% 0.69/0.87  thf('107', plain,
% 0.69/0.87      (((v3_tex_2 @ sk_B @ sk_A))
% 0.69/0.87         <= (~ ((v3_tex_2 @ sk_B @ sk_A)) & ((v1_zfmisc_1 @ sk_B)))),
% 0.69/0.87      inference('demod', [status(thm)], ['99', '106'])).
% 0.69/0.87  thf('108', plain,
% 0.69/0.87      ((~ (v3_tex_2 @ sk_B @ sk_A)) <= (~ ((v3_tex_2 @ sk_B @ sk_A)))),
% 0.69/0.87      inference('split', [status(esa)], ['0'])).
% 0.69/0.87  thf('109', plain, (~ ((v1_zfmisc_1 @ sk_B)) | ((v3_tex_2 @ sk_B @ sk_A))),
% 0.69/0.87      inference('sup-', [status(thm)], ['107', '108'])).
% 0.69/0.87  thf('110', plain, ($false),
% 0.69/0.87      inference('sat_resolution*', [status(thm)], ['1', '23', '24', '109'])).
% 0.69/0.87  
% 0.69/0.87  % SZS output end Refutation
% 0.69/0.87  
% 0.69/0.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
