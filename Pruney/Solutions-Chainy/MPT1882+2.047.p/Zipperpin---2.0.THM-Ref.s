%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KxcjSTkYSM

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:26 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 262 expanded)
%              Number of leaves         :   27 (  85 expanded)
%              Depth                    :   20
%              Number of atoms          :  945 (3316 expanded)
%              Number of equality atoms :   22 (  25 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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

thf(t80_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ~ ( ( C != k1_xboole_0 )
                    & ( v3_pre_topc @ C @ A )
                    & ( r1_xboole_0 @ B @ C ) ) ) ) ) ) )).

thf('39',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( v3_pre_topc @ ( sk_C @ X5 @ X6 ) @ X6 )
      | ( v1_tops_1 @ X5 @ X6 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t80_tops_1])).

thf('40',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ( v3_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ( v3_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( m1_subset_1 @ ( sk_C @ X5 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( v1_tops_1 @ X5 @ X6 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t80_tops_1])).

thf('46',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf(t20_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v2_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ~ ( ( v3_pre_topc @ B @ A )
                & ( B != k1_xboole_0 )
                & ( B
                 != ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('50',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v2_tdlat_3 @ X11 )
      | ( X12
        = ( u1_struct_0 @ X11 ) )
      | ( X12 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X12 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t20_tdlat_3])).

thf('51',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ( ( sk_C @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ( ( sk_C @ sk_B_1 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ( ( sk_C @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ( ( sk_C @ sk_B_1 @ sk_A )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('56',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ( ( sk_C @ sk_B_1 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( ( sk_C @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','55'])).

thf('57',plain,
    ( ( ( sk_C @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ( ( sk_C @ sk_B_1 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( ( sk_C @ X5 @ X6 )
       != k1_xboole_0 )
      | ( v1_tops_1 @ X5 @ X6 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t80_tops_1])).

thf('60',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ( ( sk_C @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ( ( sk_C @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ( ( sk_C @ sk_B_1 @ sk_A )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['57','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v1_tops_1 @ B @ A )
              & ( v2_tex_2 @ B @ A ) )
           => ( v3_tex_2 @ B @ A ) ) ) ) )).

thf('66',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v3_tex_2 @ X17 @ X18 )
      | ~ ( v2_tex_2 @ X17 @ X18 )
      | ~ ( v1_tops_1 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_tex_2])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ( ( sk_C @ sk_B_1 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','70'])).

thf('72',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( ( sk_C @ sk_B_1 @ sk_A )
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['37','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ( ( sk_C @ sk_B_1 @ sk_A )
        = ( u1_struct_0 @ sk_A ) )
      | ( v3_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('76',plain,
    ( ( ( sk_C @ sk_B_1 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_zfmisc_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( r1_xboole_0 @ X5 @ ( sk_C @ X5 @ X6 ) )
      | ( v1_tops_1 @ X5 @ X6 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t80_tops_1])).

thf('79',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ( r1_xboole_0 @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ( r1_xboole_0 @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('84',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ~ ( r1_tarski @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ~ ( r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ sk_B_1 @ sk_A ) )
   <= ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_zfmisc_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['76','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('89',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('90',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
   <= ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_zfmisc_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['87','90'])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('93',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_zfmisc_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('95',plain,
    ( ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_zfmisc_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_zfmisc_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','23','24','99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KxcjSTkYSM
% 0.15/0.36  % Computer   : n006.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 18:43:08 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.41/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.60  % Solved by: fo/fo7.sh
% 0.41/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.60  % done 174 iterations in 0.130s
% 0.41/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.60  % SZS output start Refutation
% 0.41/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.60  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.41/0.60  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.41/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.60  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.41/0.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.41/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.41/0.60  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.41/0.60  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.41/0.60  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.41/0.60  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.41/0.60  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.41/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.60  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.41/0.60  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.41/0.60  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.41/0.60  thf(t50_tex_2, conjecture,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.41/0.60         ( l1_pre_topc @ A ) ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.41/0.60             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.41/0.60           ( ( v3_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.41/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.60    (~( ![A:$i]:
% 0.41/0.60        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.41/0.60            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.60          ( ![B:$i]:
% 0.41/0.60            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.41/0.60                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.41/0.60              ( ( v3_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.41/0.60    inference('cnf.neg', [status(esa)], [t50_tex_2])).
% 0.41/0.60  thf('0', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('1', plain,
% 0.41/0.60      (~ ((v1_zfmisc_1 @ sk_B_1)) | ~ ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.41/0.60      inference('split', [status(esa)], ['0'])).
% 0.41/0.60  thf('2', plain, (((v1_zfmisc_1 @ sk_B_1) | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('3', plain,
% 0.41/0.60      (((v3_tex_2 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.60      inference('split', [status(esa)], ['2'])).
% 0.41/0.60  thf('4', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(d7_tex_2, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( l1_pre_topc @ A ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.60           ( ( v3_tex_2 @ B @ A ) <=>
% 0.41/0.60             ( ( v2_tex_2 @ B @ A ) & 
% 0.41/0.60               ( ![C:$i]:
% 0.41/0.60                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.60                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.41/0.60                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.60  thf('5', plain,
% 0.41/0.60      (![X8 : $i, X9 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.41/0.60          | ~ (v3_tex_2 @ X8 @ X9)
% 0.41/0.60          | (v2_tex_2 @ X8 @ X9)
% 0.41/0.60          | ~ (l1_pre_topc @ X9))),
% 0.41/0.60      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.41/0.60  thf('6', plain,
% 0.41/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.60        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.41/0.60        | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['4', '5'])).
% 0.41/0.60  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('8', plain,
% 0.41/0.60      (((v2_tex_2 @ sk_B_1 @ sk_A) | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.41/0.60      inference('demod', [status(thm)], ['6', '7'])).
% 0.41/0.60  thf('9', plain,
% 0.41/0.60      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['3', '8'])).
% 0.41/0.60  thf('10', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(t44_tex_2, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.41/0.60         ( l1_pre_topc @ A ) ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.41/0.60             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.41/0.60           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.41/0.60  thf('11', plain,
% 0.41/0.60      (![X15 : $i, X16 : $i]:
% 0.41/0.60         ((v1_xboole_0 @ X15)
% 0.41/0.60          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.41/0.60          | ~ (v2_tex_2 @ X15 @ X16)
% 0.41/0.60          | (v1_zfmisc_1 @ X15)
% 0.41/0.60          | ~ (l1_pre_topc @ X16)
% 0.41/0.60          | ~ (v2_tdlat_3 @ X16)
% 0.41/0.60          | ~ (v2_pre_topc @ X16)
% 0.41/0.60          | (v2_struct_0 @ X16))),
% 0.41/0.60      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.41/0.60  thf('12', plain,
% 0.41/0.60      (((v2_struct_0 @ sk_A)
% 0.41/0.60        | ~ (v2_pre_topc @ sk_A)
% 0.41/0.60        | ~ (v2_tdlat_3 @ sk_A)
% 0.41/0.60        | ~ (l1_pre_topc @ sk_A)
% 0.41/0.60        | (v1_zfmisc_1 @ sk_B_1)
% 0.41/0.60        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.41/0.60        | (v1_xboole_0 @ sk_B_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['10', '11'])).
% 0.41/0.60  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('14', plain, ((v2_tdlat_3 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('16', plain,
% 0.41/0.60      (((v2_struct_0 @ sk_A)
% 0.41/0.60        | (v1_zfmisc_1 @ sk_B_1)
% 0.41/0.60        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.41/0.60        | (v1_xboole_0 @ sk_B_1))),
% 0.41/0.60      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.41/0.60  thf('17', plain,
% 0.41/0.60      ((((v1_xboole_0 @ sk_B_1) | (v1_zfmisc_1 @ sk_B_1) | (v2_struct_0 @ sk_A)))
% 0.41/0.60         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['9', '16'])).
% 0.41/0.60  thf('18', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('19', plain,
% 0.41/0.60      ((((v2_struct_0 @ sk_A) | (v1_zfmisc_1 @ sk_B_1)))
% 0.41/0.60         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.60      inference('clc', [status(thm)], ['17', '18'])).
% 0.41/0.60  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('21', plain,
% 0.41/0.60      (((v1_zfmisc_1 @ sk_B_1)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.60      inference('clc', [status(thm)], ['19', '20'])).
% 0.41/0.60  thf('22', plain,
% 0.41/0.60      ((~ (v1_zfmisc_1 @ sk_B_1)) <= (~ ((v1_zfmisc_1 @ sk_B_1)))),
% 0.41/0.60      inference('split', [status(esa)], ['0'])).
% 0.41/0.60  thf('23', plain, (((v1_zfmisc_1 @ sk_B_1)) | ~ ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['21', '22'])).
% 0.41/0.60  thf('24', plain, (((v1_zfmisc_1 @ sk_B_1)) | ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.41/0.60      inference('split', [status(esa)], ['2'])).
% 0.41/0.60  thf('25', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.41/0.60      inference('split', [status(esa)], ['2'])).
% 0.41/0.60  thf('26', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('27', plain,
% 0.41/0.60      (![X15 : $i, X16 : $i]:
% 0.41/0.60         ((v1_xboole_0 @ X15)
% 0.41/0.60          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.41/0.60          | ~ (v1_zfmisc_1 @ X15)
% 0.41/0.60          | (v2_tex_2 @ X15 @ X16)
% 0.41/0.60          | ~ (l1_pre_topc @ X16)
% 0.41/0.60          | ~ (v2_tdlat_3 @ X16)
% 0.41/0.60          | ~ (v2_pre_topc @ X16)
% 0.41/0.60          | (v2_struct_0 @ X16))),
% 0.41/0.60      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.41/0.60  thf('28', plain,
% 0.41/0.60      (((v2_struct_0 @ sk_A)
% 0.41/0.60        | ~ (v2_pre_topc @ sk_A)
% 0.41/0.60        | ~ (v2_tdlat_3 @ sk_A)
% 0.41/0.60        | ~ (l1_pre_topc @ sk_A)
% 0.41/0.60        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.41/0.60        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.41/0.60        | (v1_xboole_0 @ sk_B_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['26', '27'])).
% 0.41/0.60  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('30', plain, ((v2_tdlat_3 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('32', plain,
% 0.41/0.60      (((v2_struct_0 @ sk_A)
% 0.41/0.60        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.41/0.60        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.41/0.60        | (v1_xboole_0 @ sk_B_1))),
% 0.41/0.60      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 0.41/0.60  thf('33', plain,
% 0.41/0.60      ((((v1_xboole_0 @ sk_B_1)
% 0.41/0.60         | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.41/0.60         | (v2_struct_0 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['25', '32'])).
% 0.41/0.60  thf('34', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('35', plain,
% 0.41/0.60      ((((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B_1 @ sk_A)))
% 0.41/0.60         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.41/0.60      inference('clc', [status(thm)], ['33', '34'])).
% 0.41/0.60  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('37', plain,
% 0.41/0.60      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.41/0.60      inference('clc', [status(thm)], ['35', '36'])).
% 0.41/0.60  thf('38', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(t80_tops_1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.60           ( ( v1_tops_1 @ B @ A ) <=>
% 0.41/0.60             ( ![C:$i]:
% 0.41/0.60               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.60                 ( ~( ( ( C ) != ( k1_xboole_0 ) ) & ( v3_pre_topc @ C @ A ) & 
% 0.41/0.60                      ( r1_xboole_0 @ B @ C ) ) ) ) ) ) ) ) ))).
% 0.41/0.60  thf('39', plain,
% 0.41/0.60      (![X5 : $i, X6 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.41/0.60          | (v3_pre_topc @ (sk_C @ X5 @ X6) @ X6)
% 0.41/0.60          | (v1_tops_1 @ X5 @ X6)
% 0.41/0.60          | ~ (l1_pre_topc @ X6)
% 0.41/0.60          | ~ (v2_pre_topc @ X6))),
% 0.41/0.60      inference('cnf', [status(esa)], [t80_tops_1])).
% 0.41/0.60  thf('40', plain,
% 0.41/0.60      ((~ (v2_pre_topc @ sk_A)
% 0.41/0.60        | ~ (l1_pre_topc @ sk_A)
% 0.41/0.60        | (v1_tops_1 @ sk_B_1 @ sk_A)
% 0.41/0.60        | (v3_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['38', '39'])).
% 0.41/0.60  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('43', plain,
% 0.41/0.60      (((v1_tops_1 @ sk_B_1 @ sk_A)
% 0.41/0.60        | (v3_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A))),
% 0.41/0.60      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.41/0.60  thf('44', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('45', plain,
% 0.41/0.60      (![X5 : $i, X6 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.41/0.60          | (m1_subset_1 @ (sk_C @ X5 @ X6) @ 
% 0.41/0.60             (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.41/0.60          | (v1_tops_1 @ X5 @ X6)
% 0.41/0.60          | ~ (l1_pre_topc @ X6)
% 0.41/0.60          | ~ (v2_pre_topc @ X6))),
% 0.41/0.60      inference('cnf', [status(esa)], [t80_tops_1])).
% 0.41/0.60  thf('46', plain,
% 0.41/0.60      ((~ (v2_pre_topc @ sk_A)
% 0.41/0.60        | ~ (l1_pre_topc @ sk_A)
% 0.41/0.60        | (v1_tops_1 @ sk_B_1 @ sk_A)
% 0.41/0.60        | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ 
% 0.41/0.60           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['44', '45'])).
% 0.41/0.60  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('49', plain,
% 0.41/0.60      (((v1_tops_1 @ sk_B_1 @ sk_A)
% 0.41/0.60        | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ 
% 0.41/0.60           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.60      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.41/0.60  thf(t20_tdlat_3, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.60       ( ( v2_tdlat_3 @ A ) <=>
% 0.41/0.60         ( ![B:$i]:
% 0.41/0.60           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.60             ( ~( ( v3_pre_topc @ B @ A ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.41/0.60                  ( ( B ) != ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.41/0.60  thf('50', plain,
% 0.41/0.60      (![X11 : $i, X12 : $i]:
% 0.41/0.60         (~ (v2_tdlat_3 @ X11)
% 0.41/0.60          | ((X12) = (u1_struct_0 @ X11))
% 0.41/0.60          | ((X12) = (k1_xboole_0))
% 0.41/0.60          | ~ (v3_pre_topc @ X12 @ X11)
% 0.41/0.60          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.41/0.60          | ~ (l1_pre_topc @ X11)
% 0.41/0.60          | ~ (v2_pre_topc @ X11))),
% 0.41/0.60      inference('cnf', [status(esa)], [t20_tdlat_3])).
% 0.41/0.60  thf('51', plain,
% 0.41/0.60      (((v1_tops_1 @ sk_B_1 @ sk_A)
% 0.41/0.60        | ~ (v2_pre_topc @ sk_A)
% 0.41/0.60        | ~ (l1_pre_topc @ sk_A)
% 0.41/0.60        | ~ (v3_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.41/0.60        | ((sk_C @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.41/0.60        | ((sk_C @ sk_B_1 @ sk_A) = (u1_struct_0 @ sk_A))
% 0.41/0.60        | ~ (v2_tdlat_3 @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['49', '50'])).
% 0.41/0.60  thf('52', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('54', plain, ((v2_tdlat_3 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('55', plain,
% 0.41/0.60      (((v1_tops_1 @ sk_B_1 @ sk_A)
% 0.41/0.60        | ~ (v3_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.41/0.60        | ((sk_C @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.41/0.60        | ((sk_C @ sk_B_1 @ sk_A) = (u1_struct_0 @ sk_A)))),
% 0.41/0.60      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 0.41/0.60  thf('56', plain,
% 0.41/0.60      (((v1_tops_1 @ sk_B_1 @ sk_A)
% 0.41/0.60        | ((sk_C @ sk_B_1 @ sk_A) = (u1_struct_0 @ sk_A))
% 0.41/0.60        | ((sk_C @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.41/0.60        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['43', '55'])).
% 0.41/0.60  thf('57', plain,
% 0.41/0.60      ((((sk_C @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.41/0.60        | ((sk_C @ sk_B_1 @ sk_A) = (u1_struct_0 @ sk_A))
% 0.41/0.60        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.41/0.60      inference('simplify', [status(thm)], ['56'])).
% 0.41/0.60  thf('58', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('59', plain,
% 0.41/0.60      (![X5 : $i, X6 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.41/0.60          | ((sk_C @ X5 @ X6) != (k1_xboole_0))
% 0.41/0.60          | (v1_tops_1 @ X5 @ X6)
% 0.41/0.60          | ~ (l1_pre_topc @ X6)
% 0.41/0.60          | ~ (v2_pre_topc @ X6))),
% 0.41/0.60      inference('cnf', [status(esa)], [t80_tops_1])).
% 0.41/0.60  thf('60', plain,
% 0.41/0.60      ((~ (v2_pre_topc @ sk_A)
% 0.41/0.60        | ~ (l1_pre_topc @ sk_A)
% 0.41/0.60        | (v1_tops_1 @ sk_B_1 @ sk_A)
% 0.41/0.60        | ((sk_C @ sk_B_1 @ sk_A) != (k1_xboole_0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['58', '59'])).
% 0.41/0.60  thf('61', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('63', plain,
% 0.41/0.60      (((v1_tops_1 @ sk_B_1 @ sk_A) | ((sk_C @ sk_B_1 @ sk_A) != (k1_xboole_0)))),
% 0.41/0.60      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.41/0.60  thf('64', plain,
% 0.41/0.60      (((v1_tops_1 @ sk_B_1 @ sk_A)
% 0.41/0.60        | ((sk_C @ sk_B_1 @ sk_A) = (u1_struct_0 @ sk_A)))),
% 0.41/0.60      inference('clc', [status(thm)], ['57', '63'])).
% 0.41/0.60  thf('65', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(t48_tex_2, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.60           ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.41/0.60             ( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.41/0.60  thf('66', plain,
% 0.41/0.60      (![X17 : $i, X18 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.41/0.60          | (v3_tex_2 @ X17 @ X18)
% 0.41/0.60          | ~ (v2_tex_2 @ X17 @ X18)
% 0.41/0.60          | ~ (v1_tops_1 @ X17 @ X18)
% 0.41/0.60          | ~ (l1_pre_topc @ X18)
% 0.41/0.60          | ~ (v2_pre_topc @ X18)
% 0.41/0.60          | (v2_struct_0 @ X18))),
% 0.41/0.60      inference('cnf', [status(esa)], [t48_tex_2])).
% 0.41/0.60  thf('67', plain,
% 0.41/0.60      (((v2_struct_0 @ sk_A)
% 0.41/0.60        | ~ (v2_pre_topc @ sk_A)
% 0.41/0.60        | ~ (l1_pre_topc @ sk_A)
% 0.41/0.60        | ~ (v1_tops_1 @ sk_B_1 @ sk_A)
% 0.41/0.60        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.41/0.60        | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['65', '66'])).
% 0.41/0.60  thf('68', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('70', plain,
% 0.41/0.60      (((v2_struct_0 @ sk_A)
% 0.41/0.60        | ~ (v1_tops_1 @ sk_B_1 @ sk_A)
% 0.41/0.60        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.41/0.60        | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.41/0.60      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.41/0.60  thf('71', plain,
% 0.41/0.60      ((((sk_C @ sk_B_1 @ sk_A) = (u1_struct_0 @ sk_A))
% 0.41/0.60        | (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.41/0.60        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.41/0.60        | (v2_struct_0 @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['64', '70'])).
% 0.41/0.60  thf('72', plain,
% 0.41/0.60      ((((v2_struct_0 @ sk_A)
% 0.41/0.60         | (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.41/0.60         | ((sk_C @ sk_B_1 @ sk_A) = (u1_struct_0 @ sk_A))))
% 0.41/0.60         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['37', '71'])).
% 0.41/0.60  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('74', plain,
% 0.41/0.60      (((((sk_C @ sk_B_1 @ sk_A) = (u1_struct_0 @ sk_A))
% 0.41/0.60         | (v3_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.41/0.60      inference('clc', [status(thm)], ['72', '73'])).
% 0.41/0.60  thf('75', plain,
% 0.41/0.60      ((~ (v3_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.60      inference('split', [status(esa)], ['0'])).
% 0.41/0.60  thf('76', plain,
% 0.41/0.60      ((((sk_C @ sk_B_1 @ sk_A) = (u1_struct_0 @ sk_A)))
% 0.41/0.60         <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) & ((v1_zfmisc_1 @ sk_B_1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['74', '75'])).
% 0.41/0.60  thf('77', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('78', plain,
% 0.41/0.60      (![X5 : $i, X6 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.41/0.60          | (r1_xboole_0 @ X5 @ (sk_C @ X5 @ X6))
% 0.41/0.60          | (v1_tops_1 @ X5 @ X6)
% 0.41/0.60          | ~ (l1_pre_topc @ X6)
% 0.41/0.60          | ~ (v2_pre_topc @ X6))),
% 0.41/0.60      inference('cnf', [status(esa)], [t80_tops_1])).
% 0.41/0.60  thf('79', plain,
% 0.41/0.60      ((~ (v2_pre_topc @ sk_A)
% 0.41/0.60        | ~ (l1_pre_topc @ sk_A)
% 0.41/0.60        | (v1_tops_1 @ sk_B_1 @ sk_A)
% 0.41/0.60        | (r1_xboole_0 @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['77', '78'])).
% 0.41/0.60  thf('80', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('82', plain,
% 0.41/0.60      (((v1_tops_1 @ sk_B_1 @ sk_A)
% 0.41/0.60        | (r1_xboole_0 @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.41/0.60      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.41/0.60  thf(t69_xboole_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.41/0.60       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.41/0.60  thf('83', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (~ (r1_xboole_0 @ X0 @ X1)
% 0.41/0.60          | ~ (r1_tarski @ X0 @ X1)
% 0.41/0.60          | (v1_xboole_0 @ X0))),
% 0.41/0.60      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.41/0.60  thf('84', plain,
% 0.41/0.60      (((v1_tops_1 @ sk_B_1 @ sk_A)
% 0.41/0.60        | (v1_xboole_0 @ sk_B_1)
% 0.41/0.60        | ~ (r1_tarski @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['82', '83'])).
% 0.41/0.60  thf('85', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('86', plain,
% 0.41/0.60      ((~ (r1_tarski @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.41/0.60        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.41/0.60      inference('clc', [status(thm)], ['84', '85'])).
% 0.41/0.60  thf('87', plain,
% 0.41/0.60      (((~ (r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.41/0.60         | (v1_tops_1 @ sk_B_1 @ sk_A)))
% 0.41/0.60         <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) & ((v1_zfmisc_1 @ sk_B_1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['76', '86'])).
% 0.41/0.60  thf('88', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(t3_subset, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.41/0.60  thf('89', plain,
% 0.41/0.60      (![X2 : $i, X3 : $i]:
% 0.41/0.60         ((r1_tarski @ X2 @ X3) | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.41/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.41/0.60  thf('90', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['88', '89'])).
% 0.41/0.60  thf('91', plain,
% 0.41/0.60      (((v1_tops_1 @ sk_B_1 @ sk_A))
% 0.41/0.60         <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) & ((v1_zfmisc_1 @ sk_B_1)))),
% 0.41/0.60      inference('demod', [status(thm)], ['87', '90'])).
% 0.41/0.60  thf('92', plain,
% 0.41/0.60      (((v2_struct_0 @ sk_A)
% 0.41/0.60        | ~ (v1_tops_1 @ sk_B_1 @ sk_A)
% 0.41/0.60        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.41/0.60        | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.41/0.60      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.41/0.60  thf('93', plain,
% 0.41/0.60      ((((v3_tex_2 @ sk_B_1 @ sk_A)
% 0.41/0.60         | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.41/0.60         | (v2_struct_0 @ sk_A)))
% 0.41/0.60         <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) & ((v1_zfmisc_1 @ sk_B_1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['91', '92'])).
% 0.41/0.60  thf('94', plain,
% 0.41/0.60      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.41/0.60      inference('clc', [status(thm)], ['35', '36'])).
% 0.41/0.60  thf('95', plain,
% 0.41/0.60      ((((v3_tex_2 @ sk_B_1 @ sk_A) | (v2_struct_0 @ sk_A)))
% 0.41/0.60         <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) & ((v1_zfmisc_1 @ sk_B_1)))),
% 0.41/0.60      inference('demod', [status(thm)], ['93', '94'])).
% 0.41/0.60  thf('96', plain,
% 0.41/0.60      ((~ (v3_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.60      inference('split', [status(esa)], ['0'])).
% 0.41/0.60  thf('97', plain,
% 0.41/0.60      (((v2_struct_0 @ sk_A))
% 0.41/0.60         <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) & ((v1_zfmisc_1 @ sk_B_1)))),
% 0.41/0.60      inference('clc', [status(thm)], ['95', '96'])).
% 0.41/0.60  thf('98', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('99', plain, (~ ((v1_zfmisc_1 @ sk_B_1)) | ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['97', '98'])).
% 0.41/0.60  thf('100', plain, ($false),
% 0.41/0.60      inference('sat_resolution*', [status(thm)], ['1', '23', '24', '99'])).
% 0.41/0.60  
% 0.41/0.60  % SZS output end Refutation
% 0.41/0.60  
% 0.45/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
