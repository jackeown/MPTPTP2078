%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3Qb4rIQJSZ

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:55 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 462 expanded)
%              Number of leaves         :   28 ( 136 expanded)
%              Depth                    :   20
%              Number of atoms          : 1057 (5802 expanded)
%              Number of equality atoms :   14 (  51 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t44_tex_2,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v2_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( ( v2_tex_2 @ B @ A )
            <=> ( v1_zfmisc_1 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_tex_2])).

thf('0',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v1_zfmisc_1 @ sk_B )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ? [C: $i] :
              ( ( B
                = ( u1_struct_0 @ C ) )
              & ( m1_pre_topc @ C @ A )
              & ( v1_pre_topc @ C )
              & ~ ( v2_struct_0 @ C ) ) ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( X11
        = ( u1_struct_0 @ ( sk_C @ X11 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B
      = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( sk_B
    = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf(t26_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( v2_tex_2 @ C @ A )
                <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X14 )
      | ( X15
       != ( u1_struct_0 @ X13 ) )
      | ~ ( v2_tex_2 @ X15 @ X14 )
      | ( v1_tdlat_3 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t26_tex_2])).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v1_tdlat_3 @ X13 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X13 ) @ X14 )
      | ~ ( m1_pre_topc @ X13 @ X14 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) @ X0 )
      | ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,
    ( sk_B
    = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ X0 )
      | ~ ( v2_tex_2 @ sk_B @ X0 )
      | ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_pre_topc @ ( sk_C @ X11 @ X12 ) @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','30'])).

thf('32',plain,
    ( ( ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v2_struct_0 @ ( sk_C @ X11 @ X12 ) )
      | ~ ( l1_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ~ ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['32','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['28','29'])).

thf(cc32_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v2_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( ~ ( v2_struct_0 @ B )
              & ~ ( v7_struct_0 @ B ) )
           => ( ~ ( v2_struct_0 @ B )
              & ~ ( v1_tdlat_3 @ B ) ) ) ) ) )).

thf('46',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ~ ( v1_tdlat_3 @ X9 )
      | ( v7_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_tdlat_3 @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc32_tex_2])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v2_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v7_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v7_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('52',plain,
    ( ( ( v7_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('54',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v7_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v7_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,
    ( sk_B
    = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('58',plain,(
    ! [X6: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 )
      | ~ ( v7_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('59',plain,
    ( ( v1_zfmisc_1 @ sk_B )
    | ~ ( v7_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( l1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['28','29'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('61',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( l1_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('62',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_pre_topc @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('65',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('66',plain,(
    l1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( v1_zfmisc_1 @ sk_B )
    | ~ ( v7_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','66'])).

thf('68',plain,
    ( ( v1_zfmisc_1 @ sk_B )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['56','67'])).

thf('69',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B )
   <= ~ ( v1_zfmisc_1 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('70',plain,
    ( ( v1_zfmisc_1 @ sk_B )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( v1_zfmisc_1 @ sk_B )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('72',plain,(
    m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['28','29'])).

thf('73',plain,
    ( ( v1_zfmisc_1 @ sk_B )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('74',plain,
    ( sk_B
    = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf(fc6_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('75',plain,(
    ! [X5: $i] :
      ( ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 )
      | ( v7_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_struct_0])).

thf('76',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B )
    | ( v7_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( l1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('78',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B )
    | ( v7_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( v7_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['73','78'])).

thf(cc1_tex_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v7_struct_0 @ A )
          & ( v2_pre_topc @ A ) )
       => ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v1_tdlat_3 @ A )
          & ( v2_tdlat_3 @ A ) ) ) ) )).

thf('80',plain,(
    ! [X7: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( v7_struct_0 @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v1_tdlat_3 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_tex_1])).

thf('81',plain,(
    ~ ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('82',plain,
    ( ~ ( l1_pre_topc @ ( sk_C @ sk_B @ sk_A ) )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_pre_topc @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v7_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['28','29'])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('85',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v2_pre_topc @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,
    ( ~ ( l1_pre_topc @ ( sk_C @ sk_B @ sk_A ) )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v7_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','88'])).

thf('90',plain,(
    l1_pre_topc @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('91',plain,
    ( ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v7_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['79','91'])).

thf('93',plain,
    ( sk_B
    = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('94',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X14 )
      | ( X15
       != ( u1_struct_0 @ X13 ) )
      | ~ ( v1_tdlat_3 @ X13 )
      | ( v2_tex_2 @ X15 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t26_tex_2])).

thf('95',plain,(
    ! [X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ X13 ) @ X14 )
      | ~ ( v1_tdlat_3 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X14 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ X0 )
      | ~ ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','95'])).

thf('97',plain,
    ( sk_B
    = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ X0 )
      | ~ ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v2_tex_2 @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_tex_2 @ sk_B @ X0 )
        | ~ ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ X0 )
        | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['92','98'])).

thf('100',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v2_tex_2 @ sk_B @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['72','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v2_tex_2 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,(
    ~ ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('105',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,
    ( ~ ( v2_tex_2 @ sk_B @ sk_A )
   <= ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('109',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','70','71','109'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3Qb4rIQJSZ
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:44:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 73 iterations in 0.037s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.50  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.20/0.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.50  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.20/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.50  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.20/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.50  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.20/0.50  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.20/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.50  thf(t44_tex_2, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.20/0.50         ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.50             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.50           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.50            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50          ( ![B:$i]:
% 0.20/0.50            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.50                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.50              ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t44_tex_2])).
% 0.20/0.50  thf('0', plain, ((~ (v1_zfmisc_1 @ sk_B) | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('1', plain, (~ ((v1_zfmisc_1 @ sk_B)) | ~ ((v2_tex_2 @ sk_B @ sk_A))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('2', plain, (((v1_zfmisc_1 @ sk_B) | (v2_tex_2 @ sk_B @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('3', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('split', [status(esa)], ['2'])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t10_tsep_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.50             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.50           ( ?[C:$i]:
% 0.20/0.50             ( ( ( B ) = ( u1_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) & 
% 0.20/0.50               ( v1_pre_topc @ C ) & ( ~( v2_struct_0 @ C ) ) ) ) ) ) ))).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X11 : $i, X12 : $i]:
% 0.20/0.50         ((v1_xboole_0 @ X11)
% 0.20/0.50          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.20/0.50          | ((X11) = (u1_struct_0 @ (sk_C @ X11 @ X12)))
% 0.20/0.50          | ~ (l1_pre_topc @ X12)
% 0.20/0.50          | (v2_struct_0 @ X12))),
% 0.20/0.50      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | ((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A)))
% 0.20/0.50        | (v1_xboole_0 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.50  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A)))
% 0.20/0.50        | (v1_xboole_0 @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.50  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (((v1_xboole_0 @ sk_B) | ((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A))))),
% 0.20/0.50      inference('clc', [status(thm)], ['9', '10'])).
% 0.20/0.50  thf('12', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('13', plain, (((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.50      inference('clc', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf(t26_tex_2, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.20/0.50                 ( ( v2_tex_2 @ C @ A ) <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X13)
% 0.20/0.50          | ~ (m1_pre_topc @ X13 @ X14)
% 0.20/0.50          | ((X15) != (u1_struct_0 @ X13))
% 0.20/0.50          | ~ (v2_tex_2 @ X15 @ X14)
% 0.20/0.50          | (v1_tdlat_3 @ X13)
% 0.20/0.50          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.50          | ~ (l1_pre_topc @ X14)
% 0.20/0.50          | (v2_struct_0 @ X14))),
% 0.20/0.50      inference('cnf', [status(esa)], [t26_tex_2])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X13 : $i, X14 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X14)
% 0.20/0.50          | ~ (l1_pre_topc @ X14)
% 0.20/0.50          | ~ (m1_subset_1 @ (u1_struct_0 @ X13) @ 
% 0.20/0.50               (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.50          | (v1_tdlat_3 @ X13)
% 0.20/0.50          | ~ (v2_tex_2 @ (u1_struct_0 @ X13) @ X14)
% 0.20/0.50          | ~ (m1_pre_topc @ X13 @ X14)
% 0.20/0.50          | (v2_struct_0 @ X13))),
% 0.20/0.50      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.50          | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.50          | ~ (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ X0)
% 0.20/0.50          | ~ (v2_tex_2 @ (u1_struct_0 @ (sk_C @ sk_B @ sk_A)) @ X0)
% 0.20/0.50          | (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | (v2_struct_0 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['13', '15'])).
% 0.20/0.50  thf('17', plain, (((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.50      inference('clc', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.50          | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.50          | ~ (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ X0)
% 0.20/0.50          | ~ (v2_tex_2 @ sk_B @ X0)
% 0.20/0.50          | (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | (v2_struct_0 @ X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.50        | ~ (v2_tex_2 @ sk_B @ sk_A)
% 0.20/0.50        | ~ (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.20/0.50        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['4', '18'])).
% 0.20/0.50  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.50        | ~ (v2_tex_2 @ sk_B @ sk_A)
% 0.20/0.50        | ~ (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.20/0.50        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (![X11 : $i, X12 : $i]:
% 0.20/0.50         ((v1_xboole_0 @ X11)
% 0.20/0.50          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.20/0.50          | (m1_pre_topc @ (sk_C @ X11 @ X12) @ X12)
% 0.20/0.50          | ~ (l1_pre_topc @ X12)
% 0.20/0.50          | (v2_struct_0 @ X12))),
% 0.20/0.50      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.20/0.50        | (v1_xboole_0 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.50  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.20/0.50        | (v1_xboole_0 @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.50  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (((v1_xboole_0 @ sk_B) | (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.20/0.50      inference('clc', [status(thm)], ['26', '27'])).
% 0.20/0.50  thf('29', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('30', plain, ((m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.20/0.50      inference('clc', [status(thm)], ['28', '29'])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.50        | ~ (v2_tex_2 @ sk_B @ sk_A)
% 0.20/0.50        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['21', '30'])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      ((((v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.50         | (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.50         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['3', '31'])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (![X11 : $i, X12 : $i]:
% 0.20/0.50         ((v1_xboole_0 @ X11)
% 0.20/0.50          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.20/0.50          | ~ (v2_struct_0 @ (sk_C @ X11 @ X12))
% 0.20/0.50          | ~ (l1_pre_topc @ X12)
% 0.20/0.50          | (v2_struct_0 @ X12))),
% 0.20/0.50      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | ~ (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.50        | (v1_xboole_0 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.50  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ~ (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.50        | (v1_xboole_0 @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      (((v1_xboole_0 @ sk_B) | ~ (v2_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.50      inference('clc', [status(thm)], ['37', '38'])).
% 0.20/0.50  thf('40', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('41', plain, (~ (v2_struct_0 @ (sk_C @ sk_B @ sk_A))),
% 0.20/0.50      inference('clc', [status(thm)], ['39', '40'])).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      ((((v2_struct_0 @ sk_A) | (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))))
% 0.20/0.50         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('clc', [status(thm)], ['32', '41'])).
% 0.20/0.50  thf('43', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('44', plain,
% 0.20/0.50      (((v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))) <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('clc', [status(thm)], ['42', '43'])).
% 0.20/0.50  thf('45', plain, ((m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.20/0.50      inference('clc', [status(thm)], ['28', '29'])).
% 0.20/0.50  thf(cc32_tex_2, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.20/0.50         ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.50           ( ( ( ~( v2_struct_0 @ B ) ) & ( ~( v7_struct_0 @ B ) ) ) =>
% 0.20/0.50             ( ( ~( v2_struct_0 @ B ) ) & ( ~( v1_tdlat_3 @ B ) ) ) ) ) ) ))).
% 0.20/0.50  thf('46', plain,
% 0.20/0.50      (![X9 : $i, X10 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X9 @ X10)
% 0.20/0.50          | ~ (v1_tdlat_3 @ X9)
% 0.20/0.50          | (v7_struct_0 @ X9)
% 0.20/0.50          | (v2_struct_0 @ X9)
% 0.20/0.50          | ~ (l1_pre_topc @ X10)
% 0.20/0.50          | ~ (v2_tdlat_3 @ X10)
% 0.20/0.50          | ~ (v2_pre_topc @ X10)
% 0.20/0.50          | (v2_struct_0 @ X10))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc32_tex_2])).
% 0.20/0.50  thf('47', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.50        | ~ (v2_tdlat_3 @ sk_A)
% 0.20/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.50        | (v7_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.50        | ~ (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.50  thf('48', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('49', plain, ((v2_tdlat_3 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('51', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.50        | (v7_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.50        | ~ (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 0.20/0.50  thf('52', plain,
% 0.20/0.50      ((((v7_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.50         | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.50         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['44', '51'])).
% 0.20/0.50  thf('53', plain, (~ (v2_struct_0 @ (sk_C @ sk_B @ sk_A))),
% 0.20/0.50      inference('clc', [status(thm)], ['39', '40'])).
% 0.20/0.50  thf('54', plain,
% 0.20/0.50      ((((v2_struct_0 @ sk_A) | (v7_struct_0 @ (sk_C @ sk_B @ sk_A))))
% 0.20/0.50         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('clc', [status(thm)], ['52', '53'])).
% 0.20/0.50  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('56', plain,
% 0.20/0.50      (((v7_struct_0 @ (sk_C @ sk_B @ sk_A))) <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('clc', [status(thm)], ['54', '55'])).
% 0.20/0.50  thf('57', plain, (((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.50      inference('clc', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf(fc7_struct_0, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.50       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.20/0.50  thf('58', plain,
% 0.20/0.50      (![X6 : $i]:
% 0.20/0.50         ((v1_zfmisc_1 @ (u1_struct_0 @ X6))
% 0.20/0.50          | ~ (l1_struct_0 @ X6)
% 0.20/0.50          | ~ (v7_struct_0 @ X6))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.20/0.50  thf('59', plain,
% 0.20/0.50      (((v1_zfmisc_1 @ sk_B)
% 0.20/0.50        | ~ (v7_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.50        | ~ (l1_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['57', '58'])).
% 0.20/0.50  thf('60', plain, ((m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.20/0.50      inference('clc', [status(thm)], ['28', '29'])).
% 0.20/0.50  thf(dt_m1_pre_topc, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.50  thf('61', plain,
% 0.20/0.50      (![X3 : $i, X4 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X3 @ X4) | (l1_pre_topc @ X3) | ~ (l1_pre_topc @ X4))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.50  thf('62', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.50  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('64', plain, ((l1_pre_topc @ (sk_C @ sk_B @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['62', '63'])).
% 0.20/0.50  thf(dt_l1_pre_topc, axiom,
% 0.20/0.50    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.50  thf('65', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf('66', plain, ((l1_struct_0 @ (sk_C @ sk_B @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['64', '65'])).
% 0.20/0.50  thf('67', plain,
% 0.20/0.50      (((v1_zfmisc_1 @ sk_B) | ~ (v7_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['59', '66'])).
% 0.20/0.50  thf('68', plain, (((v1_zfmisc_1 @ sk_B)) <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['56', '67'])).
% 0.20/0.50  thf('69', plain, ((~ (v1_zfmisc_1 @ sk_B)) <= (~ ((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('70', plain, (((v1_zfmisc_1 @ sk_B)) | ~ ((v2_tex_2 @ sk_B @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['68', '69'])).
% 0.20/0.50  thf('71', plain, (((v1_zfmisc_1 @ sk_B)) | ((v2_tex_2 @ sk_B @ sk_A))),
% 0.20/0.50      inference('split', [status(esa)], ['2'])).
% 0.20/0.50  thf('72', plain, ((m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.20/0.50      inference('clc', [status(thm)], ['28', '29'])).
% 0.20/0.50  thf('73', plain, (((v1_zfmisc_1 @ sk_B)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.50      inference('split', [status(esa)], ['2'])).
% 0.20/0.50  thf('74', plain, (((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.50      inference('clc', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf(fc6_struct_0, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v7_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.50       ( ~( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.50  thf('75', plain,
% 0.20/0.50      (![X5 : $i]:
% 0.20/0.50         (~ (v1_zfmisc_1 @ (u1_struct_0 @ X5))
% 0.20/0.50          | ~ (l1_struct_0 @ X5)
% 0.20/0.50          | (v7_struct_0 @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc6_struct_0])).
% 0.20/0.50  thf('76', plain,
% 0.20/0.50      ((~ (v1_zfmisc_1 @ sk_B)
% 0.20/0.50        | (v7_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.50        | ~ (l1_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['74', '75'])).
% 0.20/0.50  thf('77', plain, ((l1_struct_0 @ (sk_C @ sk_B @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['64', '65'])).
% 0.20/0.50  thf('78', plain,
% 0.20/0.50      ((~ (v1_zfmisc_1 @ sk_B) | (v7_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['76', '77'])).
% 0.20/0.50  thf('79', plain,
% 0.20/0.50      (((v7_struct_0 @ (sk_C @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['73', '78'])).
% 0.20/0.50  thf(cc1_tex_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ( ( ~( v2_struct_0 @ A ) ) & ( v7_struct_0 @ A ) & ( v2_pre_topc @ A ) ) =>
% 0.20/0.50         ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.50           ( v1_tdlat_3 @ A ) & ( v2_tdlat_3 @ A ) ) ) ))).
% 0.20/0.50  thf('80', plain,
% 0.20/0.50      (![X7 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X7)
% 0.20/0.50          | ~ (v7_struct_0 @ X7)
% 0.20/0.50          | ~ (v2_pre_topc @ X7)
% 0.20/0.50          | (v1_tdlat_3 @ X7)
% 0.20/0.50          | ~ (l1_pre_topc @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc1_tex_1])).
% 0.20/0.50  thf('81', plain, (~ (v2_struct_0 @ (sk_C @ sk_B @ sk_A))),
% 0.20/0.50      inference('clc', [status(thm)], ['39', '40'])).
% 0.20/0.50  thf('82', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ (sk_C @ sk_B @ sk_A))
% 0.20/0.50        | (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.50        | ~ (v2_pre_topc @ (sk_C @ sk_B @ sk_A))
% 0.20/0.50        | ~ (v7_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['80', '81'])).
% 0.20/0.50  thf('83', plain, ((m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.20/0.50      inference('clc', [status(thm)], ['28', '29'])).
% 0.20/0.50  thf(cc1_pre_topc, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.20/0.50  thf('84', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.50          | (v2_pre_topc @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ X1)
% 0.20/0.50          | ~ (v2_pre_topc @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.20/0.50  thf('85', plain,
% 0.20/0.50      ((~ (v2_pre_topc @ sk_A)
% 0.20/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | (v2_pre_topc @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['83', '84'])).
% 0.20/0.50  thf('86', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('88', plain, ((v2_pre_topc @ (sk_C @ sk_B @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['85', '86', '87'])).
% 0.20/0.50  thf('89', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ (sk_C @ sk_B @ sk_A))
% 0.20/0.50        | (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.50        | ~ (v7_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['82', '88'])).
% 0.20/0.50  thf('90', plain, ((l1_pre_topc @ (sk_C @ sk_B @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['62', '63'])).
% 0.20/0.50  thf('91', plain,
% 0.20/0.50      (((v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.50        | ~ (v7_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['89', '90'])).
% 0.20/0.50  thf('92', plain,
% 0.20/0.50      (((v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['79', '91'])).
% 0.20/0.50  thf('93', plain, (((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.50      inference('clc', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf('94', plain,
% 0.20/0.50      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X13)
% 0.20/0.50          | ~ (m1_pre_topc @ X13 @ X14)
% 0.20/0.50          | ((X15) != (u1_struct_0 @ X13))
% 0.20/0.50          | ~ (v1_tdlat_3 @ X13)
% 0.20/0.50          | (v2_tex_2 @ X15 @ X14)
% 0.20/0.50          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.50          | ~ (l1_pre_topc @ X14)
% 0.20/0.50          | (v2_struct_0 @ X14))),
% 0.20/0.50      inference('cnf', [status(esa)], [t26_tex_2])).
% 0.20/0.50  thf('95', plain,
% 0.20/0.50      (![X13 : $i, X14 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X14)
% 0.20/0.50          | ~ (l1_pre_topc @ X14)
% 0.20/0.50          | ~ (m1_subset_1 @ (u1_struct_0 @ X13) @ 
% 0.20/0.50               (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.50          | (v2_tex_2 @ (u1_struct_0 @ X13) @ X14)
% 0.20/0.50          | ~ (v1_tdlat_3 @ X13)
% 0.20/0.50          | ~ (m1_pre_topc @ X13 @ X14)
% 0.20/0.50          | (v2_struct_0 @ X13))),
% 0.20/0.50      inference('simplify', [status(thm)], ['94'])).
% 0.20/0.50  thf('96', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.50          | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.50          | ~ (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ X0)
% 0.20/0.50          | ~ (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.50          | (v2_tex_2 @ (u1_struct_0 @ (sk_C @ sk_B @ sk_A)) @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | (v2_struct_0 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['93', '95'])).
% 0.20/0.50  thf('97', plain, (((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.50      inference('clc', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf('98', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.50          | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.50          | ~ (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ X0)
% 0.20/0.50          | ~ (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.50          | (v2_tex_2 @ sk_B @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | (v2_struct_0 @ X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['96', '97'])).
% 0.20/0.50  thf('99', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          ((v2_struct_0 @ X0)
% 0.20/0.50           | ~ (l1_pre_topc @ X0)
% 0.20/0.50           | (v2_tex_2 @ sk_B @ X0)
% 0.20/0.50           | ~ (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ X0)
% 0.20/0.50           | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.50           | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))))
% 0.20/0.50         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['92', '98'])).
% 0.20/0.50  thf('100', plain,
% 0.20/0.50      (((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50         | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.50         | (v2_tex_2 @ sk_B @ sk_A)
% 0.20/0.50         | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50         | (v2_struct_0 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['72', '99'])).
% 0.20/0.50  thf('101', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('103', plain,
% 0.20/0.50      ((((v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.50         | (v2_tex_2 @ sk_B @ sk_A)
% 0.20/0.50         | (v2_struct_0 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.50      inference('demod', [status(thm)], ['100', '101', '102'])).
% 0.20/0.50  thf('104', plain, (~ (v2_struct_0 @ (sk_C @ sk_B @ sk_A))),
% 0.20/0.50      inference('clc', [status(thm)], ['39', '40'])).
% 0.20/0.50  thf('105', plain,
% 0.20/0.50      ((((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B @ sk_A)))
% 0.20/0.50         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.50      inference('clc', [status(thm)], ['103', '104'])).
% 0.20/0.50  thf('106', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('107', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.50      inference('clc', [status(thm)], ['105', '106'])).
% 0.20/0.50  thf('108', plain,
% 0.20/0.50      ((~ (v2_tex_2 @ sk_B @ sk_A)) <= (~ ((v2_tex_2 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('109', plain, (~ ((v1_zfmisc_1 @ sk_B)) | ((v2_tex_2 @ sk_B @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['107', '108'])).
% 0.20/0.50  thf('110', plain, ($false),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['1', '70', '71', '109'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
