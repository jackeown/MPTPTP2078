%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eYASZ46Vo6

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:25 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 370 expanded)
%              Number of leaves         :   23 ( 110 expanded)
%              Depth                    :   27
%              Number of atoms          : 1065 (4850 expanded)
%              Number of equality atoms :   33 (  43 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( v3_tex_2 @ X5 @ X6 )
      | ( v2_tex_2 @ X5 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v2_tex_2 @ X10 @ X11 )
      | ( v1_zfmisc_1 @ X10 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_tdlat_3 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v1_zfmisc_1 @ X10 )
      | ( v2_tex_2 @ X10 @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_tdlat_3 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( v2_tex_2 @ X5 @ X6 )
      | ( v2_tex_2 @ ( sk_C @ X5 @ X6 ) @ X6 )
      | ( v3_tex_2 @ X5 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( v2_tex_2 @ X5 @ X6 )
      | ( m1_subset_1 @ ( sk_C @ X5 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( v3_tex_2 @ X5 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v2_tex_2 @ X10 @ X11 )
      | ( v1_zfmisc_1 @ X10 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_tdlat_3 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
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

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('59',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('60',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_C @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('62',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( v2_tex_2 @ X5 @ X6 )
      | ( r1_tarski @ X5 @ ( sk_C @ X5 @ X6 ) )
      | ( v3_tex_2 @ X5 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('64',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('68',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v1_xboole_0 @ X8 )
      | ~ ( v1_zfmisc_1 @ X8 )
      | ( X9 = X8 )
      | ~ ( r1_tarski @ X9 @ X8 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('69',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( sk_B
        = ( sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_zfmisc_1 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( ( sk_C @ sk_B @ sk_A )
        = k1_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( v3_tex_2 @ sk_B @ sk_A )
      | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( sk_B
        = ( sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['60','69'])).

thf('71',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( sk_B
        = ( sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v3_tex_2 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_C @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('73',plain,
    ( ( ( ( sk_C @ sk_B @ sk_A )
        = k1_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( v3_tex_2 @ sk_B @ sk_A )
      | ( sk_B
        = ( sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( ( sk_C @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( sk_B
        = ( sk_C @ sk_B @ sk_A ) )
      | ( v3_tex_2 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_C @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('76',plain,
    ( ( ( ( sk_C @ sk_B @ sk_A )
        = k1_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( sk_C @ sk_B @ sk_A ) )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( v3_tex_2 @ sk_B @ sk_A )
      & ( v1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('78',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( v2_tex_2 @ X5 @ X6 )
      | ( X5
       != ( sk_C @ X5 @ X6 ) )
      | ( v3_tex_2 @ X5 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('80',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B @ sk_A )
    | ( sk_B
     != ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( sk_B
     != ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( sk_B
       != ( sk_C @ sk_B @ sk_A ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['77','82'])).

thf('84',plain,
    ( ( ( sk_B != sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_C @ sk_B @ sk_A )
        = k1_xboole_0 )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( ~ ( v3_tex_2 @ sk_B @ sk_A )
      & ( v1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['76','83'])).

thf('85',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( ( sk_C @ sk_B @ sk_A )
        = k1_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( v3_tex_2 @ sk_B @ sk_A )
      & ( v1_zfmisc_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('87',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_C @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ( ~ ( v3_tex_2 @ sk_B @ sk_A )
      & ( v1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( ( ( sk_C @ sk_B @ sk_A )
        = k1_xboole_0 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v3_tex_2 @ sk_B @ sk_A )
      & ( v1_zfmisc_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ~ ( v3_tex_2 @ sk_B @ sk_A )
      & ( v1_zfmisc_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( ( r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('93',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('94',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ~ ( r1_tarski @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_C @ sk_B @ sk_A )
        = sk_B ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( ( sk_B
       != ( sk_C @ sk_B @ sk_A ) )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['77','82'])).

thf('96',plain,
    ( ( ~ ( r1_tarski @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_B )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( ~ ( v3_tex_2 @ sk_B @ sk_A )
      & ( v1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['91','96'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('98',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('99',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
   <= ( ~ ( v3_tex_2 @ sk_B @ sk_A )
      & ( v1_zfmisc_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['97','98'])).

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
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eYASZ46Vo6
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:28:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.56  % Solved by: fo/fo7.sh
% 0.20/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.56  % done 187 iterations in 0.101s
% 0.20/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.56  % SZS output start Refutation
% 0.20/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.56  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.20/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.56  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.20/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.56  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.20/0.56  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.20/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.56  thf(t50_tex_2, conjecture,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.20/0.56         ( l1_pre_topc @ A ) ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.56             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.56           ( ( v3_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.20/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.56    (~( ![A:$i]:
% 0.20/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.56            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.56          ( ![B:$i]:
% 0.20/0.56            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.56                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.56              ( ( v3_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.20/0.56    inference('cnf.neg', [status(esa)], [t50_tex_2])).
% 0.20/0.56  thf('0', plain, ((~ (v1_zfmisc_1 @ sk_B) | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('1', plain, (~ ((v1_zfmisc_1 @ sk_B)) | ~ ((v3_tex_2 @ sk_B @ sk_A))),
% 0.20/0.56      inference('split', [status(esa)], ['0'])).
% 0.20/0.56  thf('2', plain, (((v1_zfmisc_1 @ sk_B) | (v3_tex_2 @ sk_B @ sk_A))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('3', plain, (((v3_tex_2 @ sk_B @ sk_A)) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.20/0.56      inference('split', [status(esa)], ['2'])).
% 0.20/0.56  thf('4', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(d7_tex_2, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( l1_pre_topc @ A ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56           ( ( v3_tex_2 @ B @ A ) <=>
% 0.20/0.56             ( ( v2_tex_2 @ B @ A ) & 
% 0.20/0.56               ( ![C:$i]:
% 0.20/0.56                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.20/0.56                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.56  thf('5', plain,
% 0.20/0.56      (![X5 : $i, X6 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.20/0.56          | ~ (v3_tex_2 @ X5 @ X6)
% 0.20/0.56          | (v2_tex_2 @ X5 @ X6)
% 0.20/0.56          | ~ (l1_pre_topc @ X6))),
% 0.20/0.56      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.20/0.56  thf('6', plain,
% 0.20/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.56        | (v2_tex_2 @ sk_B @ sk_A)
% 0.20/0.56        | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.56  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('8', plain, (((v2_tex_2 @ sk_B @ sk_A) | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.56  thf('9', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['3', '8'])).
% 0.20/0.56  thf('10', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(t44_tex_2, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.20/0.56         ( l1_pre_topc @ A ) ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.56             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.56           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.20/0.56  thf('11', plain,
% 0.20/0.56      (![X10 : $i, X11 : $i]:
% 0.20/0.56         ((v1_xboole_0 @ X10)
% 0.20/0.56          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.56          | ~ (v2_tex_2 @ X10 @ X11)
% 0.20/0.56          | (v1_zfmisc_1 @ X10)
% 0.20/0.56          | ~ (l1_pre_topc @ X11)
% 0.20/0.56          | ~ (v2_tdlat_3 @ X11)
% 0.20/0.56          | ~ (v2_pre_topc @ X11)
% 0.20/0.56          | (v2_struct_0 @ X11))),
% 0.20/0.56      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.20/0.56  thf('12', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_A)
% 0.20/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.56        | ~ (v2_tdlat_3 @ sk_A)
% 0.20/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.56        | (v1_zfmisc_1 @ sk_B)
% 0.20/0.56        | ~ (v2_tex_2 @ sk_B @ sk_A)
% 0.20/0.56        | (v1_xboole_0 @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.56  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('14', plain, ((v2_tdlat_3 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('16', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_A)
% 0.20/0.56        | (v1_zfmisc_1 @ sk_B)
% 0.20/0.56        | ~ (v2_tex_2 @ sk_B @ sk_A)
% 0.20/0.56        | (v1_xboole_0 @ sk_B))),
% 0.20/0.56      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.20/0.56  thf('17', plain,
% 0.20/0.56      ((((v1_xboole_0 @ sk_B) | (v1_zfmisc_1 @ sk_B) | (v2_struct_0 @ sk_A)))
% 0.20/0.56         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['9', '16'])).
% 0.20/0.56  thf('18', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('19', plain,
% 0.20/0.56      ((((v2_struct_0 @ sk_A) | (v1_zfmisc_1 @ sk_B)))
% 0.20/0.56         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.20/0.56      inference('clc', [status(thm)], ['17', '18'])).
% 0.20/0.56  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('21', plain, (((v1_zfmisc_1 @ sk_B)) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.20/0.56      inference('clc', [status(thm)], ['19', '20'])).
% 0.20/0.56  thf('22', plain, ((~ (v1_zfmisc_1 @ sk_B)) <= (~ ((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.56      inference('split', [status(esa)], ['0'])).
% 0.20/0.56  thf('23', plain, (((v1_zfmisc_1 @ sk_B)) | ~ ((v3_tex_2 @ sk_B @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.56  thf('24', plain, (((v1_zfmisc_1 @ sk_B)) | ((v3_tex_2 @ sk_B @ sk_A))),
% 0.20/0.56      inference('split', [status(esa)], ['2'])).
% 0.20/0.56  thf('25', plain, (((v1_zfmisc_1 @ sk_B)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.56      inference('split', [status(esa)], ['2'])).
% 0.20/0.56  thf('26', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('27', plain,
% 0.20/0.56      (![X10 : $i, X11 : $i]:
% 0.20/0.56         ((v1_xboole_0 @ X10)
% 0.20/0.56          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.56          | ~ (v1_zfmisc_1 @ X10)
% 0.20/0.56          | (v2_tex_2 @ X10 @ X11)
% 0.20/0.56          | ~ (l1_pre_topc @ X11)
% 0.20/0.56          | ~ (v2_tdlat_3 @ X11)
% 0.20/0.56          | ~ (v2_pre_topc @ X11)
% 0.20/0.56          | (v2_struct_0 @ X11))),
% 0.20/0.56      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.20/0.56  thf('28', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_A)
% 0.20/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.56        | ~ (v2_tdlat_3 @ sk_A)
% 0.20/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.56        | (v2_tex_2 @ sk_B @ sk_A)
% 0.20/0.56        | ~ (v1_zfmisc_1 @ sk_B)
% 0.20/0.56        | (v1_xboole_0 @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.56  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('30', plain, ((v2_tdlat_3 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('32', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_A)
% 0.20/0.56        | (v2_tex_2 @ sk_B @ sk_A)
% 0.20/0.56        | ~ (v1_zfmisc_1 @ sk_B)
% 0.20/0.56        | (v1_xboole_0 @ sk_B))),
% 0.20/0.56      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 0.20/0.56  thf('33', plain,
% 0.20/0.56      ((((v1_xboole_0 @ sk_B) | (v2_tex_2 @ sk_B @ sk_A) | (v2_struct_0 @ sk_A)))
% 0.20/0.56         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['25', '32'])).
% 0.20/0.56  thf('34', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('35', plain,
% 0.20/0.56      ((((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B @ sk_A)))
% 0.20/0.56         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.56      inference('clc', [status(thm)], ['33', '34'])).
% 0.20/0.56  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('37', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.56      inference('clc', [status(thm)], ['35', '36'])).
% 0.20/0.56  thf('38', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('39', plain,
% 0.20/0.56      (![X5 : $i, X6 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.20/0.56          | ~ (v2_tex_2 @ X5 @ X6)
% 0.20/0.56          | (v2_tex_2 @ (sk_C @ X5 @ X6) @ X6)
% 0.20/0.56          | (v3_tex_2 @ X5 @ X6)
% 0.20/0.56          | ~ (l1_pre_topc @ X6))),
% 0.20/0.56      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.20/0.56  thf('40', plain,
% 0.20/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.56        | (v3_tex_2 @ sk_B @ sk_A)
% 0.20/0.56        | (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.20/0.56        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.56  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('42', plain,
% 0.20/0.56      (((v3_tex_2 @ sk_B @ sk_A)
% 0.20/0.56        | (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.20/0.56        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.56  thf('43', plain,
% 0.20/0.56      ((((v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A) | (v3_tex_2 @ sk_B @ sk_A)))
% 0.20/0.56         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['37', '42'])).
% 0.20/0.56  thf('44', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.56      inference('clc', [status(thm)], ['35', '36'])).
% 0.20/0.56  thf('45', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('46', plain,
% 0.20/0.56      (![X5 : $i, X6 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.20/0.56          | ~ (v2_tex_2 @ X5 @ X6)
% 0.20/0.56          | (m1_subset_1 @ (sk_C @ X5 @ X6) @ 
% 0.20/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.20/0.56          | (v3_tex_2 @ X5 @ X6)
% 0.20/0.56          | ~ (l1_pre_topc @ X6))),
% 0.20/0.56      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.20/0.56  thf('47', plain,
% 0.20/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.56        | (v3_tex_2 @ sk_B @ sk_A)
% 0.20/0.56        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.20/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.56  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('49', plain,
% 0.20/0.56      (((v3_tex_2 @ sk_B @ sk_A)
% 0.20/0.56        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.20/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.56  thf('50', plain,
% 0.20/0.56      ((((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.20/0.56          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['44', '49'])).
% 0.20/0.56  thf('51', plain,
% 0.20/0.56      (![X10 : $i, X11 : $i]:
% 0.20/0.56         ((v1_xboole_0 @ X10)
% 0.20/0.56          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.56          | ~ (v2_tex_2 @ X10 @ X11)
% 0.20/0.56          | (v1_zfmisc_1 @ X10)
% 0.20/0.56          | ~ (l1_pre_topc @ X11)
% 0.20/0.56          | ~ (v2_tdlat_3 @ X11)
% 0.20/0.56          | ~ (v2_pre_topc @ X11)
% 0.20/0.56          | (v2_struct_0 @ X11))),
% 0.20/0.56      inference('cnf', [status(esa)], [t44_tex_2])).
% 0.20/0.56  thf('52', plain,
% 0.20/0.56      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.20/0.56         | (v2_struct_0 @ sk_A)
% 0.20/0.56         | ~ (v2_pre_topc @ sk_A)
% 0.20/0.56         | ~ (v2_tdlat_3 @ sk_A)
% 0.20/0.56         | ~ (l1_pre_topc @ sk_A)
% 0.20/0.56         | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.56         | ~ (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.20/0.56         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.56  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('54', plain, ((v2_tdlat_3 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('56', plain,
% 0.20/0.56      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.20/0.56         | (v2_struct_0 @ sk_A)
% 0.20/0.56         | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.56         | ~ (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.20/0.56         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.56      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 0.20/0.56  thf('57', plain,
% 0.20/0.56      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.20/0.56         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.56         | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.56         | (v2_struct_0 @ sk_A)
% 0.20/0.56         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['43', '56'])).
% 0.20/0.56  thf('58', plain,
% 0.20/0.56      ((((v2_struct_0 @ sk_A)
% 0.20/0.56         | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.56         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.56         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['57'])).
% 0.20/0.56  thf(l13_xboole_0, axiom,
% 0.20/0.56    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.56  thf('59', plain,
% 0.20/0.56      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.56      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.56  thf('60', plain,
% 0.20/0.56      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.20/0.56         | (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.56         | (v2_struct_0 @ sk_A)
% 0.20/0.56         | ((sk_C @ sk_B @ sk_A) = (k1_xboole_0)))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['58', '59'])).
% 0.20/0.56  thf('61', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.56      inference('clc', [status(thm)], ['35', '36'])).
% 0.20/0.56  thf('62', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('63', plain,
% 0.20/0.56      (![X5 : $i, X6 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.20/0.56          | ~ (v2_tex_2 @ X5 @ X6)
% 0.20/0.56          | (r1_tarski @ X5 @ (sk_C @ X5 @ X6))
% 0.20/0.56          | (v3_tex_2 @ X5 @ X6)
% 0.20/0.56          | ~ (l1_pre_topc @ X6))),
% 0.20/0.56      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.20/0.56  thf('64', plain,
% 0.20/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.56        | (v3_tex_2 @ sk_B @ sk_A)
% 0.20/0.56        | (r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.20/0.56        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['62', '63'])).
% 0.20/0.56  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('66', plain,
% 0.20/0.56      (((v3_tex_2 @ sk_B @ sk_A)
% 0.20/0.56        | (r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.20/0.56        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['64', '65'])).
% 0.20/0.56  thf('67', plain,
% 0.20/0.56      ((((r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A)) | (v3_tex_2 @ sk_B @ sk_A)))
% 0.20/0.56         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['61', '66'])).
% 0.20/0.56  thf(t1_tex_2, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.20/0.56           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.20/0.56  thf('68', plain,
% 0.20/0.56      (![X8 : $i, X9 : $i]:
% 0.20/0.56         ((v1_xboole_0 @ X8)
% 0.20/0.56          | ~ (v1_zfmisc_1 @ X8)
% 0.20/0.56          | ((X9) = (X8))
% 0.20/0.56          | ~ (r1_tarski @ X9 @ X8)
% 0.20/0.56          | (v1_xboole_0 @ X9))),
% 0.20/0.56      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.20/0.56  thf('69', plain,
% 0.20/0.56      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.20/0.56         | (v1_xboole_0 @ sk_B)
% 0.20/0.56         | ((sk_B) = (sk_C @ sk_B @ sk_A))
% 0.20/0.56         | ~ (v1_zfmisc_1 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.56         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['67', '68'])).
% 0.20/0.56  thf('70', plain,
% 0.20/0.56      (((((sk_C @ sk_B @ sk_A) = (k1_xboole_0))
% 0.20/0.56         | (v2_struct_0 @ sk_A)
% 0.20/0.56         | (v3_tex_2 @ sk_B @ sk_A)
% 0.20/0.56         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.56         | ((sk_B) = (sk_C @ sk_B @ sk_A))
% 0.20/0.56         | (v1_xboole_0 @ sk_B)
% 0.20/0.56         | (v3_tex_2 @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['60', '69'])).
% 0.20/0.56  thf('71', plain,
% 0.20/0.56      ((((v1_xboole_0 @ sk_B)
% 0.20/0.56         | ((sk_B) = (sk_C @ sk_B @ sk_A))
% 0.20/0.56         | (v1_xboole_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.56         | (v3_tex_2 @ sk_B @ sk_A)
% 0.20/0.56         | (v2_struct_0 @ sk_A)
% 0.20/0.56         | ((sk_C @ sk_B @ sk_A) = (k1_xboole_0)))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['70'])).
% 0.20/0.56  thf('72', plain,
% 0.20/0.56      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.56      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.56  thf('73', plain,
% 0.20/0.56      (((((sk_C @ sk_B @ sk_A) = (k1_xboole_0))
% 0.20/0.56         | (v2_struct_0 @ sk_A)
% 0.20/0.56         | (v3_tex_2 @ sk_B @ sk_A)
% 0.20/0.56         | ((sk_B) = (sk_C @ sk_B @ sk_A))
% 0.20/0.56         | (v1_xboole_0 @ sk_B)
% 0.20/0.56         | ((sk_C @ sk_B @ sk_A) = (k1_xboole_0)))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['71', '72'])).
% 0.20/0.56  thf('74', plain,
% 0.20/0.56      ((((v1_xboole_0 @ sk_B)
% 0.20/0.56         | ((sk_B) = (sk_C @ sk_B @ sk_A))
% 0.20/0.56         | (v3_tex_2 @ sk_B @ sk_A)
% 0.20/0.56         | (v2_struct_0 @ sk_A)
% 0.20/0.56         | ((sk_C @ sk_B @ sk_A) = (k1_xboole_0)))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['73'])).
% 0.20/0.56  thf('75', plain,
% 0.20/0.56      ((~ (v3_tex_2 @ sk_B @ sk_A)) <= (~ ((v3_tex_2 @ sk_B @ sk_A)))),
% 0.20/0.56      inference('split', [status(esa)], ['0'])).
% 0.20/0.56  thf('76', plain,
% 0.20/0.56      (((((sk_C @ sk_B @ sk_A) = (k1_xboole_0))
% 0.20/0.56         | (v2_struct_0 @ sk_A)
% 0.20/0.56         | ((sk_B) = (sk_C @ sk_B @ sk_A))
% 0.20/0.56         | (v1_xboole_0 @ sk_B)))
% 0.20/0.56         <= (~ ((v3_tex_2 @ sk_B @ sk_A)) & ((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['74', '75'])).
% 0.20/0.56  thf('77', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.56      inference('clc', [status(thm)], ['35', '36'])).
% 0.20/0.56  thf('78', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('79', plain,
% 0.20/0.56      (![X5 : $i, X6 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.20/0.56          | ~ (v2_tex_2 @ X5 @ X6)
% 0.20/0.56          | ((X5) != (sk_C @ X5 @ X6))
% 0.20/0.56          | (v3_tex_2 @ X5 @ X6)
% 0.20/0.56          | ~ (l1_pre_topc @ X6))),
% 0.20/0.56      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.20/0.56  thf('80', plain,
% 0.20/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.56        | (v3_tex_2 @ sk_B @ sk_A)
% 0.20/0.56        | ((sk_B) != (sk_C @ sk_B @ sk_A))
% 0.20/0.56        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['78', '79'])).
% 0.20/0.56  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('82', plain,
% 0.20/0.56      (((v3_tex_2 @ sk_B @ sk_A)
% 0.20/0.56        | ((sk_B) != (sk_C @ sk_B @ sk_A))
% 0.20/0.56        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['80', '81'])).
% 0.20/0.56  thf('83', plain,
% 0.20/0.56      (((((sk_B) != (sk_C @ sk_B @ sk_A)) | (v3_tex_2 @ sk_B @ sk_A)))
% 0.20/0.56         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['77', '82'])).
% 0.20/0.56  thf('84', plain,
% 0.20/0.56      (((((sk_B) != (sk_B))
% 0.20/0.56         | (v1_xboole_0 @ sk_B)
% 0.20/0.56         | (v2_struct_0 @ sk_A)
% 0.20/0.56         | ((sk_C @ sk_B @ sk_A) = (k1_xboole_0))
% 0.20/0.56         | (v3_tex_2 @ sk_B @ sk_A)))
% 0.20/0.56         <= (~ ((v3_tex_2 @ sk_B @ sk_A)) & ((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['76', '83'])).
% 0.20/0.56  thf('85', plain,
% 0.20/0.56      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.20/0.56         | ((sk_C @ sk_B @ sk_A) = (k1_xboole_0))
% 0.20/0.56         | (v2_struct_0 @ sk_A)
% 0.20/0.56         | (v1_xboole_0 @ sk_B)))
% 0.20/0.56         <= (~ ((v3_tex_2 @ sk_B @ sk_A)) & ((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['84'])).
% 0.20/0.56  thf('86', plain,
% 0.20/0.56      ((~ (v3_tex_2 @ sk_B @ sk_A)) <= (~ ((v3_tex_2 @ sk_B @ sk_A)))),
% 0.20/0.56      inference('split', [status(esa)], ['0'])).
% 0.20/0.56  thf('87', plain,
% 0.20/0.56      ((((v1_xboole_0 @ sk_B)
% 0.20/0.56         | (v2_struct_0 @ sk_A)
% 0.20/0.56         | ((sk_C @ sk_B @ sk_A) = (k1_xboole_0))))
% 0.20/0.56         <= (~ ((v3_tex_2 @ sk_B @ sk_A)) & ((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['85', '86'])).
% 0.20/0.56  thf('88', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('89', plain,
% 0.20/0.56      (((((sk_C @ sk_B @ sk_A) = (k1_xboole_0)) | (v2_struct_0 @ sk_A)))
% 0.20/0.56         <= (~ ((v3_tex_2 @ sk_B @ sk_A)) & ((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.56      inference('clc', [status(thm)], ['87', '88'])).
% 0.20/0.56  thf('90', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('91', plain,
% 0.20/0.56      ((((sk_C @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.20/0.56         <= (~ ((v3_tex_2 @ sk_B @ sk_A)) & ((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.56      inference('clc', [status(thm)], ['89', '90'])).
% 0.20/0.56  thf('92', plain,
% 0.20/0.56      ((((r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A)) | (v3_tex_2 @ sk_B @ sk_A)))
% 0.20/0.56         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['61', '66'])).
% 0.20/0.56  thf(d10_xboole_0, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.56  thf('93', plain,
% 0.20/0.56      (![X1 : $i, X3 : $i]:
% 0.20/0.56         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.20/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.56  thf('94', plain,
% 0.20/0.56      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.20/0.56         | ~ (r1_tarski @ (sk_C @ sk_B @ sk_A) @ sk_B)
% 0.20/0.56         | ((sk_C @ sk_B @ sk_A) = (sk_B)))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['92', '93'])).
% 0.20/0.56  thf('95', plain,
% 0.20/0.56      (((((sk_B) != (sk_C @ sk_B @ sk_A)) | (v3_tex_2 @ sk_B @ sk_A)))
% 0.20/0.56         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['77', '82'])).
% 0.20/0.56  thf('96', plain,
% 0.20/0.56      (((~ (r1_tarski @ (sk_C @ sk_B @ sk_A) @ sk_B) | (v3_tex_2 @ sk_B @ sk_A)))
% 0.20/0.56         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.56      inference('clc', [status(thm)], ['94', '95'])).
% 0.20/0.56  thf('97', plain,
% 0.20/0.56      (((~ (r1_tarski @ k1_xboole_0 @ sk_B) | (v3_tex_2 @ sk_B @ sk_A)))
% 0.20/0.56         <= (~ ((v3_tex_2 @ sk_B @ sk_A)) & ((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['91', '96'])).
% 0.20/0.56  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.56  thf('98', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.20/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.56  thf('99', plain,
% 0.20/0.56      (((v3_tex_2 @ sk_B @ sk_A))
% 0.20/0.56         <= (~ ((v3_tex_2 @ sk_B @ sk_A)) & ((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.56      inference('demod', [status(thm)], ['97', '98'])).
% 0.20/0.56  thf('100', plain,
% 0.20/0.56      ((~ (v3_tex_2 @ sk_B @ sk_A)) <= (~ ((v3_tex_2 @ sk_B @ sk_A)))),
% 0.20/0.56      inference('split', [status(esa)], ['0'])).
% 0.20/0.56  thf('101', plain, (~ ((v1_zfmisc_1 @ sk_B)) | ((v3_tex_2 @ sk_B @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['99', '100'])).
% 0.20/0.56  thf('102', plain, ($false),
% 0.20/0.56      inference('sat_resolution*', [status(thm)], ['1', '23', '24', '101'])).
% 0.20/0.56  
% 0.20/0.56  % SZS output end Refutation
% 0.20/0.56  
% 0.20/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
