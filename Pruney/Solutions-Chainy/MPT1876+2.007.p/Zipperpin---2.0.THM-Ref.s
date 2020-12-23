%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.14eZMqOZHT

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 754 expanded)
%              Number of leaves         :   29 ( 214 expanded)
%              Depth                    :   28
%              Number of atoms          : 1103 (9581 expanded)
%              Number of equality atoms :   14 (  79 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
   <= ~ ( v1_zfmisc_1 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
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

thf('4',plain,(
    ! [X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( m1_pre_topc @ ( sk_C @ X13 @ X14 ) @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('5',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( v1_zfmisc_1 @ sk_B )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( v1_zfmisc_1 @ sk_B )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( X13
        = ( u1_struct_0 @ ( sk_C @ X13 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B
      = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( sk_B
    = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf(fc6_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('23',plain,(
    ! [X5: $i] :
      ( ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 )
      | ( v7_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_struct_0])).

thf('24',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B )
    | ( v7_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( l1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['9','10'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('26',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( l1_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('30',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('31',plain,(
    l1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B )
    | ( v7_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','31'])).

thf('33',plain,
    ( ( v7_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','32'])).

thf('34',plain,(
    m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['9','10'])).

thf(cc25_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( ~ ( v2_struct_0 @ B )
              & ( v7_struct_0 @ B )
              & ( v2_pre_topc @ B ) )
           => ( ~ ( v2_struct_0 @ B )
              & ( v1_tdlat_3 @ B )
              & ( v2_tdlat_3 @ B ) ) ) ) ) )).

thf('35',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v1_tdlat_3 @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ~ ( v7_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc25_tex_2])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v7_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_pre_topc @ ( sk_C @ sk_B @ sk_A ) )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v7_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_pre_topc @ ( sk_C @ sk_B @ sk_A ) )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['9','10'])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('41',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v2_pre_topc @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v7_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','44'])).

thf('46',plain,
    ( ( ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v2_struct_0 @ ( sk_C @ X13 @ X14 ) )
      | ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ~ ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['46','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,
    ( sk_B
    = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['20','21'])).

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

thf('60',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( X17
       != ( u1_struct_0 @ X15 ) )
      | ~ ( v1_tdlat_3 @ X15 )
      | ( v2_tex_2 @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t26_tex_2])).

thf('61',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ X15 ) @ X16 )
      | ~ ( v1_tdlat_3 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ X0 )
      | ~ ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','61'])).

thf('63',plain,
    ( sk_B
    = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ X0 )
      | ~ ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v2_tex_2 @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_tex_2 @ sk_B @ X0 )
        | ~ ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ X0 )
        | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['58','64'])).

thf('66',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v2_tex_2 @ sk_B @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['11','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v2_tex_2 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('71',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( v2_tex_2 @ sk_B @ sk_A )
   <= ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('75',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ~ ( v1_zfmisc_1 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','75'])).

thf('77',plain,(
    ~ ( v1_zfmisc_1 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','76'])).

thf('78',plain,
    ( sk_B
    = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('79',plain,(
    ! [X6: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 )
      | ~ ( v7_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('80',plain,
    ( ( v1_zfmisc_1 @ sk_B )
    | ~ ( v7_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( l1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('82',plain,
    ( ( v1_zfmisc_1 @ sk_B )
    | ~ ( v7_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf(cc2_tex_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v1_tdlat_3 @ A )
          & ( v2_tdlat_3 @ A ) )
       => ( ~ ( v2_struct_0 @ A )
          & ( v7_struct_0 @ A )
          & ( v2_pre_topc @ A ) ) ) ) )).

thf('83',plain,(
    ! [X10: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ~ ( v1_tdlat_3 @ X10 )
      | ~ ( v2_tdlat_3 @ X10 )
      | ( v7_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc2_tex_1])).

thf('84',plain,(
    ~ ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('85',plain,
    ( ~ ( l1_pre_topc @ ( sk_C @ sk_B @ sk_A ) )
    | ( v7_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_pre_topc @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v2_pre_topc @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('87',plain,
    ( ~ ( l1_pre_topc @ ( sk_C @ sk_B @ sk_A ) )
    | ( v7_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    l1_pre_topc @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('89',plain,(
    m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['9','10'])).

thf(cc6_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v2_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_tdlat_3 @ B ) ) ) )).

thf('90',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( v2_tdlat_3 @ X11 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_tdlat_3 @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc6_tdlat_3])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v2_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['91','92','93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v2_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( v7_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','88','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( sk_B
    = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('101',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( X17
       != ( u1_struct_0 @ X15 ) )
      | ~ ( v2_tex_2 @ X17 @ X16 )
      | ( v1_tdlat_3 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t26_tex_2])).

thf('102',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v1_tdlat_3 @ X15 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X15 ) @ X16 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) @ X0 )
      | ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['100','102'])).

thf('104',plain,
    ( sk_B
    = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ X0 )
      | ~ ( v2_tex_2 @ sk_B @ X0 )
      | ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['99','105'])).

thf('107',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['12'])).

thf('109',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ( v1_zfmisc_1 @ sk_B ) ),
    inference(split,[status(esa)],['12'])).

thf('110',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','75','109'])).

thf('111',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(simpl_trail,[status(thm)],['108','110'])).

thf('112',plain,(
    m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['9','10'])).

thf('113',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['106','107','111','112'])).

thf('114',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('116',plain,(
    ~ ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('117',plain,(
    v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['115','116'])).

thf('118',plain,(
    v7_struct_0 @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['98','117'])).

thf('119',plain,(
    v1_zfmisc_1 @ sk_B ),
    inference(demod,[status(thm)],['82','118'])).

thf('120',plain,(
    $false ),
    inference(demod,[status(thm)],['77','119'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.14eZMqOZHT
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:48:03 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 71 iterations in 0.033s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.48  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.48  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.48  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.20/0.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.20/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.48  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.20/0.48  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.20/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.20/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.48  thf(t44_tex_2, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.20/0.48         ( l1_pre_topc @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.48             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.48           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.48            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48          ( ![B:$i]:
% 0.20/0.48            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.48                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.48              ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t44_tex_2])).
% 0.20/0.48  thf('0', plain, ((~ (v1_zfmisc_1 @ sk_B) | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain, ((~ (v1_zfmisc_1 @ sk_B)) <= (~ ((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('2', plain, (~ ((v1_zfmisc_1 @ sk_B)) | ~ ((v2_tex_2 @ sk_B @ sk_A))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t10_tsep_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.48             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.48           ( ?[C:$i]:
% 0.20/0.48             ( ( ( B ) = ( u1_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) & 
% 0.20/0.48               ( v1_pre_topc @ C ) & ( ~( v2_struct_0 @ C ) ) ) ) ) ) ))).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X13 : $i, X14 : $i]:
% 0.20/0.48         ((v1_xboole_0 @ X13)
% 0.20/0.48          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.48          | (m1_pre_topc @ (sk_C @ X13 @ X14) @ X14)
% 0.20/0.48          | ~ (l1_pre_topc @ X14)
% 0.20/0.48          | (v2_struct_0 @ X14))),
% 0.20/0.48      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.20/0.48        | (v1_xboole_0 @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.48  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.20/0.48        | (v1_xboole_0 @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf('8', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (((v1_xboole_0 @ sk_B) | (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.20/0.48      inference('clc', [status(thm)], ['7', '8'])).
% 0.20/0.48  thf('10', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('11', plain, ((m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.20/0.48      inference('clc', [status(thm)], ['9', '10'])).
% 0.20/0.48  thf('12', plain, (((v1_zfmisc_1 @ sk_B) | (v2_tex_2 @ sk_B @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('13', plain, (((v1_zfmisc_1 @ sk_B)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.48      inference('split', [status(esa)], ['12'])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X13 : $i, X14 : $i]:
% 0.20/0.48         ((v1_xboole_0 @ X13)
% 0.20/0.48          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.48          | ((X13) = (u1_struct_0 @ (sk_C @ X13 @ X14)))
% 0.20/0.48          | ~ (l1_pre_topc @ X14)
% 0.20/0.48          | (v2_struct_0 @ X14))),
% 0.20/0.48      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | ((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A)))
% 0.20/0.48        | (v1_xboole_0 @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.48  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | ((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A)))
% 0.20/0.48        | (v1_xboole_0 @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.48  thf('19', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (((v1_xboole_0 @ sk_B) | ((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A))))),
% 0.20/0.48      inference('clc', [status(thm)], ['18', '19'])).
% 0.20/0.48  thf('21', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('22', plain, (((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.48      inference('clc', [status(thm)], ['20', '21'])).
% 0.20/0.48  thf(fc6_struct_0, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v7_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.48       ( ~( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (![X5 : $i]:
% 0.20/0.48         (~ (v1_zfmisc_1 @ (u1_struct_0 @ X5))
% 0.20/0.48          | ~ (l1_struct_0 @ X5)
% 0.20/0.48          | (v7_struct_0 @ X5))),
% 0.20/0.48      inference('cnf', [status(esa)], [fc6_struct_0])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      ((~ (v1_zfmisc_1 @ sk_B)
% 0.20/0.48        | (v7_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48        | ~ (l1_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.48  thf('25', plain, ((m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.20/0.48      inference('clc', [status(thm)], ['9', '10'])).
% 0.20/0.48  thf(dt_m1_pre_topc, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i]:
% 0.20/0.48         (~ (m1_pre_topc @ X3 @ X4) | (l1_pre_topc @ X3) | ~ (l1_pre_topc @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.48  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('29', plain, ((l1_pre_topc @ (sk_C @ sk_B @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.48  thf(dt_l1_pre_topc, axiom,
% 0.20/0.48    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.48  thf('30', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.48  thf('31', plain, ((l1_struct_0 @ (sk_C @ sk_B @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      ((~ (v1_zfmisc_1 @ sk_B) | (v7_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['24', '31'])).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      (((v7_struct_0 @ (sk_C @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['13', '32'])).
% 0.20/0.48  thf('34', plain, ((m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.20/0.48      inference('clc', [status(thm)], ['9', '10'])).
% 0.20/0.48  thf(cc25_tex_2, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.48           ( ( ( ~( v2_struct_0 @ B ) ) & ( v7_struct_0 @ B ) & 
% 0.20/0.48               ( v2_pre_topc @ B ) ) =>
% 0.20/0.48             ( ( ~( v2_struct_0 @ B ) ) & ( v1_tdlat_3 @ B ) & 
% 0.20/0.48               ( v2_tdlat_3 @ B ) ) ) ) ) ))).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i]:
% 0.20/0.48         (~ (m1_pre_topc @ X7 @ X8)
% 0.20/0.48          | (v1_tdlat_3 @ X7)
% 0.20/0.48          | ~ (v2_pre_topc @ X7)
% 0.20/0.48          | ~ (v7_struct_0 @ X7)
% 0.20/0.48          | (v2_struct_0 @ X7)
% 0.20/0.48          | ~ (l1_pre_topc @ X8)
% 0.20/0.48          | (v2_struct_0 @ X8))),
% 0.20/0.48      inference('cnf', [status(esa)], [cc25_tex_2])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48        | ~ (v7_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48        | ~ (v2_pre_topc @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48        | (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.48  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48        | ~ (v7_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48        | ~ (v2_pre_topc @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48        | (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.48  thf('39', plain, ((m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.20/0.48      inference('clc', [status(thm)], ['9', '10'])).
% 0.20/0.48  thf(cc1_pre_topc, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.20/0.48  thf('40', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.48          | (v2_pre_topc @ X0)
% 0.20/0.48          | ~ (l1_pre_topc @ X1)
% 0.20/0.48          | ~ (v2_pre_topc @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.20/0.48  thf('41', plain,
% 0.20/0.48      ((~ (v2_pre_topc @ sk_A)
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | (v2_pre_topc @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.48  thf('42', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('44', plain, ((v2_pre_topc @ (sk_C @ sk_B @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.20/0.48  thf('45', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48        | ~ (v7_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48        | (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['38', '44'])).
% 0.20/0.48  thf('46', plain,
% 0.20/0.48      ((((v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48         | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48         | (v2_struct_0 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['33', '45'])).
% 0.20/0.48  thf('47', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('48', plain,
% 0.20/0.48      (![X13 : $i, X14 : $i]:
% 0.20/0.48         ((v1_xboole_0 @ X13)
% 0.20/0.48          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.48          | ~ (v2_struct_0 @ (sk_C @ X13 @ X14))
% 0.20/0.48          | ~ (l1_pre_topc @ X14)
% 0.20/0.48          | (v2_struct_0 @ X14))),
% 0.20/0.48      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.20/0.48  thf('49', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | ~ (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48        | (v1_xboole_0 @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.48  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('51', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48        | (v1_xboole_0 @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.48  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('53', plain,
% 0.20/0.48      (((v1_xboole_0 @ sk_B) | ~ (v2_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.48      inference('clc', [status(thm)], ['51', '52'])).
% 0.20/0.48  thf('54', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('55', plain, (~ (v2_struct_0 @ (sk_C @ sk_B @ sk_A))),
% 0.20/0.48      inference('clc', [status(thm)], ['53', '54'])).
% 0.20/0.48  thf('56', plain,
% 0.20/0.48      ((((v2_struct_0 @ sk_A) | (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))))
% 0.20/0.48         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.48      inference('clc', [status(thm)], ['46', '55'])).
% 0.20/0.48  thf('57', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('58', plain,
% 0.20/0.48      (((v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.48      inference('clc', [status(thm)], ['56', '57'])).
% 0.20/0.48  thf('59', plain, (((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.48      inference('clc', [status(thm)], ['20', '21'])).
% 0.20/0.48  thf(t26_tex_2, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.20/0.48                 ( ( v2_tex_2 @ C @ A ) <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('60', plain,
% 0.20/0.48      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X15)
% 0.20/0.48          | ~ (m1_pre_topc @ X15 @ X16)
% 0.20/0.48          | ((X17) != (u1_struct_0 @ X15))
% 0.20/0.48          | ~ (v1_tdlat_3 @ X15)
% 0.20/0.48          | (v2_tex_2 @ X17 @ X16)
% 0.20/0.48          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.48          | ~ (l1_pre_topc @ X16)
% 0.20/0.48          | (v2_struct_0 @ X16))),
% 0.20/0.48      inference('cnf', [status(esa)], [t26_tex_2])).
% 0.20/0.48  thf('61', plain,
% 0.20/0.48      (![X15 : $i, X16 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X16)
% 0.20/0.48          | ~ (l1_pre_topc @ X16)
% 0.20/0.48          | ~ (m1_subset_1 @ (u1_struct_0 @ X15) @ 
% 0.20/0.48               (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.48          | (v2_tex_2 @ (u1_struct_0 @ X15) @ X16)
% 0.20/0.48          | ~ (v1_tdlat_3 @ X15)
% 0.20/0.48          | ~ (m1_pre_topc @ X15 @ X16)
% 0.20/0.48          | (v2_struct_0 @ X15))),
% 0.20/0.48      inference('simplify', [status(thm)], ['60'])).
% 0.20/0.48  thf('62', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.48          | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48          | ~ (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ X0)
% 0.20/0.48          | ~ (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48          | (v2_tex_2 @ (u1_struct_0 @ (sk_C @ sk_B @ sk_A)) @ X0)
% 0.20/0.48          | ~ (l1_pre_topc @ X0)
% 0.20/0.48          | (v2_struct_0 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['59', '61'])).
% 0.20/0.48  thf('63', plain, (((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.48      inference('clc', [status(thm)], ['20', '21'])).
% 0.20/0.48  thf('64', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.48          | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48          | ~ (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ X0)
% 0.20/0.48          | ~ (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48          | (v2_tex_2 @ sk_B @ X0)
% 0.20/0.48          | ~ (l1_pre_topc @ X0)
% 0.20/0.48          | (v2_struct_0 @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['62', '63'])).
% 0.20/0.48  thf('65', plain,
% 0.20/0.48      ((![X0 : $i]:
% 0.20/0.48          ((v2_struct_0 @ X0)
% 0.20/0.48           | ~ (l1_pre_topc @ X0)
% 0.20/0.48           | (v2_tex_2 @ sk_B @ X0)
% 0.20/0.48           | ~ (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ X0)
% 0.20/0.48           | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48           | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))))
% 0.20/0.48         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['58', '64'])).
% 0.20/0.48  thf('66', plain,
% 0.20/0.48      (((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48         | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48         | (v2_tex_2 @ sk_B @ sk_A)
% 0.20/0.48         | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48         | (v2_struct_0 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['11', '65'])).
% 0.20/0.48  thf('67', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('69', plain,
% 0.20/0.48      ((((v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48         | (v2_tex_2 @ sk_B @ sk_A)
% 0.20/0.48         | (v2_struct_0 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.48      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.20/0.48  thf('70', plain, (~ (v2_struct_0 @ (sk_C @ sk_B @ sk_A))),
% 0.20/0.48      inference('clc', [status(thm)], ['53', '54'])).
% 0.20/0.48  thf('71', plain,
% 0.20/0.48      ((((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B @ sk_A)))
% 0.20/0.48         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.48      inference('clc', [status(thm)], ['69', '70'])).
% 0.20/0.48  thf('72', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('73', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.20/0.48      inference('clc', [status(thm)], ['71', '72'])).
% 0.20/0.48  thf('74', plain,
% 0.20/0.48      ((~ (v2_tex_2 @ sk_B @ sk_A)) <= (~ ((v2_tex_2 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('75', plain, (((v2_tex_2 @ sk_B @ sk_A)) | ~ ((v1_zfmisc_1 @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['73', '74'])).
% 0.20/0.48  thf('76', plain, (~ ((v1_zfmisc_1 @ sk_B))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['2', '75'])).
% 0.20/0.48  thf('77', plain, (~ (v1_zfmisc_1 @ sk_B)),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['1', '76'])).
% 0.20/0.48  thf('78', plain, (((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.48      inference('clc', [status(thm)], ['20', '21'])).
% 0.20/0.48  thf(fc7_struct_0, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.48       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.20/0.48  thf('79', plain,
% 0.20/0.48      (![X6 : $i]:
% 0.20/0.48         ((v1_zfmisc_1 @ (u1_struct_0 @ X6))
% 0.20/0.48          | ~ (l1_struct_0 @ X6)
% 0.20/0.48          | ~ (v7_struct_0 @ X6))),
% 0.20/0.48      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.20/0.48  thf('80', plain,
% 0.20/0.48      (((v1_zfmisc_1 @ sk_B)
% 0.20/0.48        | ~ (v7_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48        | ~ (l1_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['78', '79'])).
% 0.20/0.48  thf('81', plain, ((l1_struct_0 @ (sk_C @ sk_B @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.48  thf('82', plain,
% 0.20/0.48      (((v1_zfmisc_1 @ sk_B) | ~ (v7_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['80', '81'])).
% 0.20/0.48  thf(cc2_tex_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.48           ( v1_tdlat_3 @ A ) & ( v2_tdlat_3 @ A ) ) =>
% 0.20/0.48         ( ( ~( v2_struct_0 @ A ) ) & ( v7_struct_0 @ A ) & ( v2_pre_topc @ A ) ) ) ))).
% 0.20/0.48  thf('83', plain,
% 0.20/0.48      (![X10 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X10)
% 0.20/0.48          | ~ (v2_pre_topc @ X10)
% 0.20/0.48          | ~ (v1_tdlat_3 @ X10)
% 0.20/0.48          | ~ (v2_tdlat_3 @ X10)
% 0.20/0.48          | (v7_struct_0 @ X10)
% 0.20/0.48          | ~ (l1_pre_topc @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [cc2_tex_1])).
% 0.20/0.48  thf('84', plain, (~ (v2_struct_0 @ (sk_C @ sk_B @ sk_A))),
% 0.20/0.48      inference('clc', [status(thm)], ['53', '54'])).
% 0.20/0.48  thf('85', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48        | (v7_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48        | ~ (v2_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48        | ~ (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48        | ~ (v2_pre_topc @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['83', '84'])).
% 0.20/0.48  thf('86', plain, ((v2_pre_topc @ (sk_C @ sk_B @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.20/0.48  thf('87', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48        | (v7_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48        | ~ (v2_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48        | ~ (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['85', '86'])).
% 0.20/0.48  thf('88', plain, ((l1_pre_topc @ (sk_C @ sk_B @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.48  thf('89', plain, ((m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.20/0.48      inference('clc', [status(thm)], ['9', '10'])).
% 0.20/0.48  thf(cc6_tdlat_3, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.20/0.48         ( l1_pre_topc @ A ) ) =>
% 0.20/0.48       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_tdlat_3 @ B ) ) ) ))).
% 0.20/0.48  thf('90', plain,
% 0.20/0.48      (![X11 : $i, X12 : $i]:
% 0.20/0.48         (~ (m1_pre_topc @ X11 @ X12)
% 0.20/0.48          | (v2_tdlat_3 @ X11)
% 0.20/0.48          | ~ (l1_pre_topc @ X12)
% 0.20/0.48          | ~ (v2_tdlat_3 @ X12)
% 0.20/0.48          | ~ (v2_pre_topc @ X12)
% 0.20/0.48          | (v2_struct_0 @ X12))),
% 0.20/0.48      inference('cnf', [status(esa)], [cc6_tdlat_3])).
% 0.20/0.48  thf('91', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.48        | ~ (v2_tdlat_3 @ sk_A)
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | (v2_tdlat_3 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['89', '90'])).
% 0.20/0.48  thf('92', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('93', plain, ((v2_tdlat_3 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('95', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A) | (v2_tdlat_3 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['91', '92', '93', '94'])).
% 0.20/0.48  thf('96', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('97', plain, ((v2_tdlat_3 @ (sk_C @ sk_B @ sk_A))),
% 0.20/0.48      inference('clc', [status(thm)], ['95', '96'])).
% 0.20/0.48  thf('98', plain,
% 0.20/0.48      (((v7_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48        | ~ (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['87', '88', '97'])).
% 0.20/0.48  thf('99', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('100', plain, (((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.48      inference('clc', [status(thm)], ['20', '21'])).
% 0.20/0.48  thf('101', plain,
% 0.20/0.48      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X15)
% 0.20/0.48          | ~ (m1_pre_topc @ X15 @ X16)
% 0.20/0.48          | ((X17) != (u1_struct_0 @ X15))
% 0.20/0.48          | ~ (v2_tex_2 @ X17 @ X16)
% 0.20/0.48          | (v1_tdlat_3 @ X15)
% 0.20/0.48          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.48          | ~ (l1_pre_topc @ X16)
% 0.20/0.48          | (v2_struct_0 @ X16))),
% 0.20/0.48      inference('cnf', [status(esa)], [t26_tex_2])).
% 0.20/0.48  thf('102', plain,
% 0.20/0.48      (![X15 : $i, X16 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X16)
% 0.20/0.48          | ~ (l1_pre_topc @ X16)
% 0.20/0.48          | ~ (m1_subset_1 @ (u1_struct_0 @ X15) @ 
% 0.20/0.48               (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.48          | (v1_tdlat_3 @ X15)
% 0.20/0.48          | ~ (v2_tex_2 @ (u1_struct_0 @ X15) @ X16)
% 0.20/0.48          | ~ (m1_pre_topc @ X15 @ X16)
% 0.20/0.48          | (v2_struct_0 @ X15))),
% 0.20/0.48      inference('simplify', [status(thm)], ['101'])).
% 0.20/0.48  thf('103', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.48          | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48          | ~ (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ X0)
% 0.20/0.48          | ~ (v2_tex_2 @ (u1_struct_0 @ (sk_C @ sk_B @ sk_A)) @ X0)
% 0.20/0.48          | (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48          | ~ (l1_pre_topc @ X0)
% 0.20/0.48          | (v2_struct_0 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['100', '102'])).
% 0.20/0.48  thf('104', plain, (((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.48      inference('clc', [status(thm)], ['20', '21'])).
% 0.20/0.48  thf('105', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.48          | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48          | ~ (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ X0)
% 0.20/0.48          | ~ (v2_tex_2 @ sk_B @ X0)
% 0.20/0.48          | (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48          | ~ (l1_pre_topc @ X0)
% 0.20/0.48          | (v2_struct_0 @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['103', '104'])).
% 0.20/0.48  thf('106', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48        | ~ (v2_tex_2 @ sk_B @ sk_A)
% 0.20/0.48        | ~ (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.20/0.48        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['99', '105'])).
% 0.20/0.48  thf('107', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('108', plain,
% 0.20/0.48      (((v2_tex_2 @ sk_B @ sk_A)) <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['12'])).
% 0.20/0.48  thf('109', plain, (((v2_tex_2 @ sk_B @ sk_A)) | ((v1_zfmisc_1 @ sk_B))),
% 0.20/0.48      inference('split', [status(esa)], ['12'])).
% 0.20/0.48  thf('110', plain, (((v2_tex_2 @ sk_B @ sk_A))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['2', '75', '109'])).
% 0.20/0.48  thf('111', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['108', '110'])).
% 0.20/0.48  thf('112', plain, ((m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.20/0.48      inference('clc', [status(thm)], ['9', '10'])).
% 0.20/0.48  thf('113', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['106', '107', '111', '112'])).
% 0.20/0.48  thf('114', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('115', plain,
% 0.20/0.48      (((v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48        | (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.48      inference('clc', [status(thm)], ['113', '114'])).
% 0.20/0.48  thf('116', plain, (~ (v2_struct_0 @ (sk_C @ sk_B @ sk_A))),
% 0.20/0.48      inference('clc', [status(thm)], ['53', '54'])).
% 0.20/0.48  thf('117', plain, ((v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))),
% 0.20/0.48      inference('clc', [status(thm)], ['115', '116'])).
% 0.20/0.48  thf('118', plain, ((v7_struct_0 @ (sk_C @ sk_B @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['98', '117'])).
% 0.20/0.48  thf('119', plain, ((v1_zfmisc_1 @ sk_B)),
% 0.20/0.48      inference('demod', [status(thm)], ['82', '118'])).
% 0.20/0.48  thf('120', plain, ($false), inference('demod', [status(thm)], ['77', '119'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.34/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
