%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IRJxKIJUDl

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 586 expanded)
%              Number of leaves         :   24 ( 167 expanded)
%              Depth                    :   28
%              Number of atoms          : 1045 (7752 expanded)
%              Number of equality atoms :   30 (  64 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v3_tex_2 @ X23 @ X24 )
      | ( v2_tex_2 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
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
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v2_tex_2 @ X28 @ X29 )
      | ( v1_zfmisc_1 @ X28 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_tdlat_3 @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
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
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v1_zfmisc_1 @ X28 )
      | ( v2_tex_2 @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_tdlat_3 @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v2_tex_2 @ X23 @ X24 )
      | ( v2_tex_2 @ ( sk_C_1 @ X23 @ X24 ) @ X24 )
      | ( v3_tex_2 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v2_tex_2 @ X23 @ X24 )
      | ( m1_subset_1 @ ( sk_C_1 @ X23 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v3_tex_2 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
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
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v2_tex_2 @ X28 @ X29 )
      | ( v1_zfmisc_1 @ X28 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_tdlat_3 @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
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

thf(cc1_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_zfmisc_1 @ A ) ) )).

thf('59',plain,(
    ! [X18: $i] :
      ( ( v1_zfmisc_1 @ X18 )
      | ~ ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc1_zfmisc_1])).

thf('60',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
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
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v2_tex_2 @ X23 @ X24 )
      | ( r1_tarski @ X23 @ ( sk_C_1 @ X23 @ X24 ) )
      | ( v3_tex_2 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('67',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( r1_tarski @ sk_B_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( r1_tarski @ sk_B_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( r1_tarski @ sk_B_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
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
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( v1_zfmisc_1 @ X26 )
      | ( X27 = X26 )
      | ~ ( r1_tarski @ X27 @ X26 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('72',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( sk_B_1
        = ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_zfmisc_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( sk_B_1
        = ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['63','72'])).

thf('74',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( sk_B_1
        = ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
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
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_xboole_0 @ X16 )
      | ~ ( v1_xboole_0 @ X17 )
      | ( X16 = X17 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( sk_B_1
        = ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( k1_xboole_0
        = ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('80',plain,
    ( ( ( k1_xboole_0
        = ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( sk_B_1
        = ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_zfmisc_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( ( sk_B_1
        = ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( k1_xboole_0
        = ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_zfmisc_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('84',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v2_tex_2 @ X23 @ X24 )
      | ( X23
       != ( sk_C_1 @ X23 @ X24 ) )
      | ( v3_tex_2 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('86',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( sk_B_1
     != ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( sk_B_1
     != ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ( sk_B_1
       != ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['83','88'])).

thf('90',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( k1_xboole_0
        = ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_zfmisc_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['82','89'])).

thf('91',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( k1_xboole_0
        = ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_zfmisc_1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('93',plain,
    ( ( k1_xboole_0
      = ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_zfmisc_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( r1_tarski @ sk_B_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['64','69'])).

thf('95',plain,
    ( ( ( r1_tarski @ sk_B_1 @ k1_xboole_0 )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_zfmisc_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('97',plain,
    ( ( r1_tarski @ sk_B_1 @ k1_xboole_0 )
   <= ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_zfmisc_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('98',plain,(
    ! [X11: $i] :
      ( ( X11 = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('99',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_zfmisc_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k1_xboole_0
      = ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_zfmisc_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('101',plain,
    ( ( ( sk_B_1
       != ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['83','88'])).

thf('102',plain,
    ( ( ( sk_B_1 != k1_xboole_0 )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_zfmisc_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('104',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_zfmisc_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['99','104'])).

thf('106',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','23','24','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IRJxKIJUDl
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:12:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 213 iterations in 0.087s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.21/0.55  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.21/0.55  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.55  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.21/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.55  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.21/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.55  thf(t50_tex_2, conjecture,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.21/0.55         ( l1_pre_topc @ A ) ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.55             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.55           ( ( v3_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i]:
% 0.21/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.55            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.55          ( ![B:$i]:
% 0.21/0.55            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.55                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.55              ( ( v3_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t50_tex_2])).
% 0.21/0.55  thf('0', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      (~ ((v1_zfmisc_1 @ sk_B_1)) | ~ ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf('2', plain, (((v1_zfmisc_1 @ sk_B_1) | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      (((v3_tex_2 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.55      inference('split', [status(esa)], ['2'])).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(d7_tex_2, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( l1_pre_topc @ A ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55           ( ( v3_tex_2 @ B @ A ) <=>
% 0.21/0.55             ( ( v2_tex_2 @ B @ A ) & 
% 0.21/0.55               ( ![C:$i]:
% 0.21/0.55                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.55                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (![X23 : $i, X24 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.21/0.55          | ~ (v3_tex_2 @ X23 @ X24)
% 0.21/0.55          | (v2_tex_2 @ X23 @ X24)
% 0.21/0.55          | ~ (l1_pre_topc @ X24))),
% 0.21/0.55      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.55        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.55        | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.55  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      (((v2_tex_2 @ sk_B_1 @ sk_A) | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['3', '8'])).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(t44_tex_2, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.21/0.55         ( l1_pre_topc @ A ) ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.55             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.55           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      (![X28 : $i, X29 : $i]:
% 0.21/0.55         ((v1_xboole_0 @ X28)
% 0.21/0.55          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.21/0.55          | ~ (v2_tex_2 @ X28 @ X29)
% 0.21/0.55          | (v1_zfmisc_1 @ X28)
% 0.21/0.55          | ~ (l1_pre_topc @ X29)
% 0.21/0.55          | ~ (v2_tdlat_3 @ X29)
% 0.21/0.55          | ~ (v2_pre_topc @ X29)
% 0.21/0.55          | (v2_struct_0 @ X29))),
% 0.21/0.55      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_A)
% 0.21/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.55        | ~ (v2_tdlat_3 @ sk_A)
% 0.21/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.55        | (v1_zfmisc_1 @ sk_B_1)
% 0.21/0.55        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.55        | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.55  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('14', plain, ((v2_tdlat_3 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('16', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_A)
% 0.21/0.55        | (v1_zfmisc_1 @ sk_B_1)
% 0.21/0.55        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.55        | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.55      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.21/0.55  thf('17', plain,
% 0.21/0.55      ((((v1_xboole_0 @ sk_B_1) | (v1_zfmisc_1 @ sk_B_1) | (v2_struct_0 @ sk_A)))
% 0.21/0.55         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['9', '16'])).
% 0.21/0.55  thf('18', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      ((((v2_struct_0 @ sk_A) | (v1_zfmisc_1 @ sk_B_1)))
% 0.21/0.55         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.55      inference('clc', [status(thm)], ['17', '18'])).
% 0.21/0.55  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('21', plain,
% 0.21/0.55      (((v1_zfmisc_1 @ sk_B_1)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.55      inference('clc', [status(thm)], ['19', '20'])).
% 0.21/0.55  thf('22', plain,
% 0.21/0.55      ((~ (v1_zfmisc_1 @ sk_B_1)) <= (~ ((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf('23', plain, (((v1_zfmisc_1 @ sk_B_1)) | ~ ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.55  thf('24', plain, (((v1_zfmisc_1 @ sk_B_1)) | ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.55      inference('split', [status(esa)], ['2'])).
% 0.21/0.55  thf('25', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.55      inference('split', [status(esa)], ['2'])).
% 0.21/0.55  thf('26', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('27', plain,
% 0.21/0.55      (![X28 : $i, X29 : $i]:
% 0.21/0.55         ((v1_xboole_0 @ X28)
% 0.21/0.55          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.21/0.55          | ~ (v1_zfmisc_1 @ X28)
% 0.21/0.55          | (v2_tex_2 @ X28 @ X29)
% 0.21/0.55          | ~ (l1_pre_topc @ X29)
% 0.21/0.55          | ~ (v2_tdlat_3 @ X29)
% 0.21/0.55          | ~ (v2_pre_topc @ X29)
% 0.21/0.55          | (v2_struct_0 @ X29))),
% 0.21/0.55      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.21/0.55  thf('28', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_A)
% 0.21/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.55        | ~ (v2_tdlat_3 @ sk_A)
% 0.21/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.55        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.55        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.21/0.55        | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.55  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('30', plain, ((v2_tdlat_3 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('32', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_A)
% 0.21/0.55        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.55        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.21/0.55        | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.55      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 0.21/0.55  thf('33', plain,
% 0.21/0.55      ((((v1_xboole_0 @ sk_B_1)
% 0.21/0.55         | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.55         | (v2_struct_0 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['25', '32'])).
% 0.21/0.55  thf('34', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('35', plain,
% 0.21/0.55      ((((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B_1 @ sk_A)))
% 0.21/0.55         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.55      inference('clc', [status(thm)], ['33', '34'])).
% 0.21/0.55  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('37', plain,
% 0.21/0.55      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.55      inference('clc', [status(thm)], ['35', '36'])).
% 0.21/0.55  thf('38', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('39', plain,
% 0.21/0.55      (![X23 : $i, X24 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.21/0.55          | ~ (v2_tex_2 @ X23 @ X24)
% 0.21/0.55          | (v2_tex_2 @ (sk_C_1 @ X23 @ X24) @ X24)
% 0.21/0.55          | (v3_tex_2 @ X23 @ X24)
% 0.21/0.55          | ~ (l1_pre_topc @ X24))),
% 0.21/0.55      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.21/0.55  thf('40', plain,
% 0.21/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.55        | (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.55        | (v2_tex_2 @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.21/0.55        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.55  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('42', plain,
% 0.21/0.55      (((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.55        | (v2_tex_2 @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.21/0.55        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.55  thf('43', plain,
% 0.21/0.55      ((((v2_tex_2 @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.21/0.55         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['37', '42'])).
% 0.21/0.55  thf('44', plain,
% 0.21/0.55      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.55      inference('clc', [status(thm)], ['35', '36'])).
% 0.21/0.55  thf('45', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('46', plain,
% 0.21/0.55      (![X23 : $i, X24 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.21/0.55          | ~ (v2_tex_2 @ X23 @ X24)
% 0.21/0.55          | (m1_subset_1 @ (sk_C_1 @ X23 @ X24) @ 
% 0.21/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.21/0.55          | (v3_tex_2 @ X23 @ X24)
% 0.21/0.55          | ~ (l1_pre_topc @ X24))),
% 0.21/0.55      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.21/0.55  thf('47', plain,
% 0.21/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.55        | (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.55        | (m1_subset_1 @ (sk_C_1 @ sk_B_1 @ sk_A) @ 
% 0.21/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.55        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.55  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('49', plain,
% 0.21/0.55      (((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.55        | (m1_subset_1 @ (sk_C_1 @ sk_B_1 @ sk_A) @ 
% 0.21/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.55        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['47', '48'])).
% 0.21/0.55  thf('50', plain,
% 0.21/0.55      ((((m1_subset_1 @ (sk_C_1 @ sk_B_1 @ sk_A) @ 
% 0.21/0.55          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.55         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['44', '49'])).
% 0.21/0.55  thf('51', plain,
% 0.21/0.55      (![X28 : $i, X29 : $i]:
% 0.21/0.55         ((v1_xboole_0 @ X28)
% 0.21/0.55          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.21/0.55          | ~ (v2_tex_2 @ X28 @ X29)
% 0.21/0.55          | (v1_zfmisc_1 @ X28)
% 0.21/0.55          | ~ (l1_pre_topc @ X29)
% 0.21/0.55          | ~ (v2_tdlat_3 @ X29)
% 0.21/0.55          | ~ (v2_pre_topc @ X29)
% 0.21/0.55          | (v2_struct_0 @ X29))),
% 0.21/0.55      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.21/0.55  thf('52', plain,
% 0.21/0.55      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.55         | (v2_struct_0 @ sk_A)
% 0.21/0.55         | ~ (v2_pre_topc @ sk_A)
% 0.21/0.55         | ~ (v2_tdlat_3 @ sk_A)
% 0.21/0.55         | ~ (l1_pre_topc @ sk_A)
% 0.21/0.55         | (v1_zfmisc_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.55         | ~ (v2_tex_2 @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.21/0.55         | (v1_xboole_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.21/0.55         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.55  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('54', plain, ((v2_tdlat_3 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('56', plain,
% 0.21/0.55      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.55         | (v2_struct_0 @ sk_A)
% 0.21/0.55         | (v1_zfmisc_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.55         | ~ (v2_tex_2 @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.21/0.55         | (v1_xboole_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.21/0.55         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.55      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 0.21/0.55  thf('57', plain,
% 0.21/0.55      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.55         | (v1_xboole_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.55         | (v1_zfmisc_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.55         | (v2_struct_0 @ sk_A)
% 0.21/0.55         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['43', '56'])).
% 0.21/0.55  thf('58', plain,
% 0.21/0.55      ((((v2_struct_0 @ sk_A)
% 0.21/0.55         | (v1_zfmisc_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.55         | (v1_xboole_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.55         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['57'])).
% 0.21/0.55  thf(cc1_zfmisc_1, axiom,
% 0.21/0.55    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_zfmisc_1 @ A ) ))).
% 0.21/0.55  thf('59', plain,
% 0.21/0.55      (![X18 : $i]: ((v1_zfmisc_1 @ X18) | ~ (v1_xboole_0 @ X18))),
% 0.21/0.55      inference('cnf', [status(esa)], [cc1_zfmisc_1])).
% 0.21/0.55  thf('60', plain,
% 0.21/0.55      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.55         | (v1_zfmisc_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.55         | (v2_struct_0 @ sk_A)
% 0.21/0.55         | (v1_zfmisc_1 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.21/0.55         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['58', '59'])).
% 0.21/0.55  thf('61', plain,
% 0.21/0.55      ((((v2_struct_0 @ sk_A)
% 0.21/0.55         | (v1_zfmisc_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.55         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['60'])).
% 0.21/0.55  thf('62', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('63', plain,
% 0.21/0.55      ((((v3_tex_2 @ sk_B_1 @ sk_A) | (v1_zfmisc_1 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.21/0.55         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.55      inference('clc', [status(thm)], ['61', '62'])).
% 0.21/0.55  thf('64', plain,
% 0.21/0.55      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.55      inference('clc', [status(thm)], ['35', '36'])).
% 0.21/0.55  thf('65', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('66', plain,
% 0.21/0.55      (![X23 : $i, X24 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.21/0.55          | ~ (v2_tex_2 @ X23 @ X24)
% 0.21/0.55          | (r1_tarski @ X23 @ (sk_C_1 @ X23 @ X24))
% 0.21/0.55          | (v3_tex_2 @ X23 @ X24)
% 0.21/0.55          | ~ (l1_pre_topc @ X24))),
% 0.21/0.55      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.21/0.55  thf('67', plain,
% 0.21/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.55        | (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.55        | (r1_tarski @ sk_B_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.55        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['65', '66'])).
% 0.21/0.55  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('69', plain,
% 0.21/0.55      (((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.55        | (r1_tarski @ sk_B_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.55        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['67', '68'])).
% 0.21/0.55  thf('70', plain,
% 0.21/0.55      ((((r1_tarski @ sk_B_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.55         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['64', '69'])).
% 0.21/0.55  thf(t1_tex_2, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.21/0.55           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.21/0.55  thf('71', plain,
% 0.21/0.55      (![X26 : $i, X27 : $i]:
% 0.21/0.55         ((v1_xboole_0 @ X26)
% 0.21/0.55          | ~ (v1_zfmisc_1 @ X26)
% 0.21/0.55          | ((X27) = (X26))
% 0.21/0.55          | ~ (r1_tarski @ X27 @ X26)
% 0.21/0.55          | (v1_xboole_0 @ X27))),
% 0.21/0.55      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.21/0.55  thf('72', plain,
% 0.21/0.55      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.55         | (v1_xboole_0 @ sk_B_1)
% 0.21/0.55         | ((sk_B_1) = (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.55         | ~ (v1_zfmisc_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.55         | (v1_xboole_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.21/0.55         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['70', '71'])).
% 0.21/0.55  thf('73', plain,
% 0.21/0.55      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.55         | (v1_xboole_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.55         | ((sk_B_1) = (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.55         | (v1_xboole_0 @ sk_B_1)
% 0.21/0.55         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['63', '72'])).
% 0.21/0.55  thf('74', plain,
% 0.21/0.55      ((((v1_xboole_0 @ sk_B_1)
% 0.21/0.55         | ((sk_B_1) = (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.55         | (v1_xboole_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.55         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['73'])).
% 0.21/0.55  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.55  thf('75', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.55  thf(t8_boole, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.21/0.55  thf('76', plain,
% 0.21/0.55      (![X16 : $i, X17 : $i]:
% 0.21/0.55         (~ (v1_xboole_0 @ X16) | ~ (v1_xboole_0 @ X17) | ((X16) = (X17)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t8_boole])).
% 0.21/0.55  thf('77', plain,
% 0.21/0.55      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['75', '76'])).
% 0.21/0.55  thf('78', plain,
% 0.21/0.55      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.55         | ((sk_B_1) = (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.55         | (v1_xboole_0 @ sk_B_1)
% 0.21/0.55         | ((k1_xboole_0) = (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.21/0.55         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['74', '77'])).
% 0.21/0.55  thf('79', plain,
% 0.21/0.55      ((~ (v3_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf('80', plain,
% 0.21/0.55      (((((k1_xboole_0) = (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.55         | (v1_xboole_0 @ sk_B_1)
% 0.21/0.55         | ((sk_B_1) = (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.21/0.55         <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) & ((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['78', '79'])).
% 0.21/0.55  thf('81', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('82', plain,
% 0.21/0.55      (((((sk_B_1) = (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.55         | ((k1_xboole_0) = (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.21/0.55         <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) & ((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.55      inference('clc', [status(thm)], ['80', '81'])).
% 0.21/0.55  thf('83', plain,
% 0.21/0.55      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.55      inference('clc', [status(thm)], ['35', '36'])).
% 0.21/0.55  thf('84', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('85', plain,
% 0.21/0.55      (![X23 : $i, X24 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.21/0.55          | ~ (v2_tex_2 @ X23 @ X24)
% 0.21/0.55          | ((X23) != (sk_C_1 @ X23 @ X24))
% 0.21/0.55          | (v3_tex_2 @ X23 @ X24)
% 0.21/0.55          | ~ (l1_pre_topc @ X24))),
% 0.21/0.55      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.21/0.55  thf('86', plain,
% 0.21/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.55        | (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.55        | ((sk_B_1) != (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.55        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['84', '85'])).
% 0.21/0.55  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('88', plain,
% 0.21/0.55      (((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.55        | ((sk_B_1) != (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.55        | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['86', '87'])).
% 0.21/0.55  thf('89', plain,
% 0.21/0.55      (((((sk_B_1) != (sk_C_1 @ sk_B_1 @ sk_A)) | (v3_tex_2 @ sk_B_1 @ sk_A)))
% 0.21/0.55         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['83', '88'])).
% 0.21/0.55  thf('90', plain,
% 0.21/0.55      (((((sk_B_1) != (sk_B_1))
% 0.21/0.55         | ((k1_xboole_0) = (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.55         | (v3_tex_2 @ sk_B_1 @ sk_A)))
% 0.21/0.55         <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) & ((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['82', '89'])).
% 0.21/0.55  thf('91', plain,
% 0.21/0.55      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.55         | ((k1_xboole_0) = (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.21/0.55         <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) & ((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['90'])).
% 0.21/0.55  thf('92', plain,
% 0.21/0.55      ((~ (v3_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf('93', plain,
% 0.21/0.55      ((((k1_xboole_0) = (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.21/0.55         <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) & ((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.55      inference('clc', [status(thm)], ['91', '92'])).
% 0.21/0.55  thf('94', plain,
% 0.21/0.55      ((((r1_tarski @ sk_B_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.21/0.55         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['64', '69'])).
% 0.21/0.55  thf('95', plain,
% 0.21/0.55      ((((r1_tarski @ sk_B_1 @ k1_xboole_0) | (v3_tex_2 @ sk_B_1 @ sk_A)))
% 0.21/0.55         <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) & ((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['93', '94'])).
% 0.21/0.55  thf('96', plain,
% 0.21/0.55      ((~ (v3_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf('97', plain,
% 0.21/0.55      (((r1_tarski @ sk_B_1 @ k1_xboole_0))
% 0.21/0.55         <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) & ((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.55      inference('clc', [status(thm)], ['95', '96'])).
% 0.21/0.55  thf(t3_xboole_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.55  thf('98', plain,
% 0.21/0.55      (![X11 : $i]:
% 0.21/0.55         (((X11) = (k1_xboole_0)) | ~ (r1_tarski @ X11 @ k1_xboole_0))),
% 0.21/0.55      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.21/0.55  thf('99', plain,
% 0.21/0.55      ((((sk_B_1) = (k1_xboole_0)))
% 0.21/0.55         <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) & ((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['97', '98'])).
% 0.21/0.55  thf('100', plain,
% 0.21/0.55      ((((k1_xboole_0) = (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.21/0.55         <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) & ((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.55      inference('clc', [status(thm)], ['91', '92'])).
% 0.21/0.55  thf('101', plain,
% 0.21/0.55      (((((sk_B_1) != (sk_C_1 @ sk_B_1 @ sk_A)) | (v3_tex_2 @ sk_B_1 @ sk_A)))
% 0.21/0.55         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['83', '88'])).
% 0.21/0.55  thf('102', plain,
% 0.21/0.55      (((((sk_B_1) != (k1_xboole_0)) | (v3_tex_2 @ sk_B_1 @ sk_A)))
% 0.21/0.55         <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) & ((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['100', '101'])).
% 0.21/0.55  thf('103', plain,
% 0.21/0.55      ((~ (v3_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf('104', plain,
% 0.21/0.55      ((((sk_B_1) != (k1_xboole_0)))
% 0.21/0.55         <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) & ((v1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.55      inference('clc', [status(thm)], ['102', '103'])).
% 0.21/0.55  thf('105', plain,
% 0.21/0.55      (~ ((v1_zfmisc_1 @ sk_B_1)) | ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.55      inference('simplify_reflect-', [status(thm)], ['99', '104'])).
% 0.21/0.55  thf('106', plain, ($false),
% 0.21/0.55      inference('sat_resolution*', [status(thm)], ['1', '23', '24', '105'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
