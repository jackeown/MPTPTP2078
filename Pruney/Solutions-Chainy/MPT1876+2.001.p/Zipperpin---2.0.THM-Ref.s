%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.U5dSSDJktZ

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 500 expanded)
%              Number of leaves         :   29 ( 146 expanded)
%              Depth                    :   22
%              Number of atoms          : 1191 (6345 expanded)
%              Number of equality atoms :   14 (  52 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

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
    ! [X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( X13
        = ( u1_struct_0 @ ( sk_C @ X13 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
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

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v1_tdlat_3 @ X15 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X15 ) @ X16 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( v2_struct_0 @ X15 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( m1_pre_topc @ ( sk_C @ X13 @ X14 ) @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v2_struct_0 @ ( sk_C @ X13 @ X14 ) )
      | ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
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

thf(cc31_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v2_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( ~ ( v2_struct_0 @ B )
              & ( v1_tdlat_3 @ B ) )
           => ( ~ ( v2_struct_0 @ B )
              & ( v7_struct_0 @ B ) ) ) ) ) )).

thf('46',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( v7_struct_0 @ X9 )
      | ~ ( v1_tdlat_3 @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_tdlat_3 @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc31_tex_2])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v2_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v7_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
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
    | ~ ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v7_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
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
    ! [X4: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 )
      | ~ ( v7_struct_0 @ X4 ) ) ),
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
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X2 )
      | ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
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
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
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
    ! [X3: $i] :
      ( ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 )
      | ( v7_struct_0 @ X3 ) ) ),
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

thf('80',plain,(
    m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['28','29'])).

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

thf('81',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v1_tdlat_3 @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ~ ( v7_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc25_tex_2])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v7_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_pre_topc @ ( sk_C @ sk_B @ sk_A ) )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v7_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_pre_topc @ ( sk_C @ sk_B @ sk_A ) )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['28','29'])).

thf(cc15_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v2_tdlat_3 @ B )
           => ( v2_pre_topc @ B ) ) ) ) )).

thf('86',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( v2_pre_topc @ X5 )
      | ~ ( v2_tdlat_3 @ X5 )
      | ~ ( l1_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc15_tex_2])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_pre_topc @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_pre_topc @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['28','29'])).

thf(cc6_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v2_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_tdlat_3 @ B ) ) ) )).

thf('91',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( v2_tdlat_3 @ X11 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_tdlat_3 @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc6_tdlat_3])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v2_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['92','93','94','95'])).

thf('97',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v2_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_pre_topc @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['89','98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v2_pre_topc @ ( sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v7_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['84','101'])).

thf('103',plain,
    ( ( ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['79','102'])).

thf('104',plain,(
    ~ ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('105',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,
    ( sk_B
    = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('109',plain,(
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

thf('110',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ X15 ) @ X16 )
      | ~ ( v1_tdlat_3 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ X0 )
      | ~ ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['108','110'])).

thf('112',plain,
    ( sk_B
    = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ X0 )
      | ~ ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v2_tex_2 @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_tex_2 @ sk_B @ X0 )
        | ~ ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ X0 )
        | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['107','113'])).

thf('115',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v2_tex_2 @ sk_B @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['72','114'])).

thf('116',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( v2_tex_2 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['115','116','117'])).

thf('119',plain,(
    ~ ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('120',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('121',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,
    ( ~ ( v2_tex_2 @ sk_B @ sk_A )
   <= ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('124',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','70','71','124'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.U5dSSDJktZ
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:18:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 72 iterations in 0.042s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.51  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.21/0.51  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.21/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.51  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.51  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.51  thf(t44_tex_2, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.21/0.51         ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.51             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.51           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.51            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51          ( ![B:$i]:
% 0.21/0.51            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.51                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.51              ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t44_tex_2])).
% 0.21/0.51  thf('0', plain, ((~ (v1_zfmisc_1 @ sk_B) | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('1', plain, (~ ((v1_zfmisc_1 @ sk_B)) | ~ ((v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf('2', plain, (((v1_zfmisc_1 @ sk_B) | (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('3', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.51      inference('split', [status(esa)], ['2'])).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t10_tsep_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.51             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.51           ( ?[C:$i]:
% 0.21/0.51             ( ( ( B ) = ( u1_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) & 
% 0.21/0.51               ( v1_pre_topc @ C ) & ( ~( v2_struct_0 @ C ) ) ) ) ) ) ))).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ X13)
% 0.21/0.51          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.51          | ((X13) = (u1_struct_0 @ (sk_C @ X13 @ X14)))
% 0.21/0.51          | ~ (l1_pre_topc @ X14)
% 0.21/0.51          | (v2_struct_0 @ X14))),
% 0.21/0.51      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | ((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A)))
% 0.21/0.51        | (v1_xboole_0 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.51  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A)))
% 0.21/0.51        | (v1_xboole_0 @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (((v1_xboole_0 @ sk_B) | ((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A))))),
% 0.21/0.51      inference('clc', [status(thm)], ['9', '10'])).
% 0.21/0.51  thf('12', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('13', plain, (((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.21/0.51      inference('clc', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf(t26_tex_2, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.21/0.51                 ( ( v2_tex_2 @ C @ A ) <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X15)
% 0.21/0.51          | ~ (m1_pre_topc @ X15 @ X16)
% 0.21/0.51          | ((X17) != (u1_struct_0 @ X15))
% 0.21/0.51          | ~ (v2_tex_2 @ X17 @ X16)
% 0.21/0.51          | (v1_tdlat_3 @ X15)
% 0.21/0.51          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.51          | ~ (l1_pre_topc @ X16)
% 0.21/0.51          | (v2_struct_0 @ X16))),
% 0.21/0.51      inference('cnf', [status(esa)], [t26_tex_2])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X15 : $i, X16 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X16)
% 0.21/0.51          | ~ (l1_pre_topc @ X16)
% 0.21/0.51          | ~ (m1_subset_1 @ (u1_struct_0 @ X15) @ 
% 0.21/0.51               (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.51          | (v1_tdlat_3 @ X15)
% 0.21/0.51          | ~ (v2_tex_2 @ (u1_struct_0 @ X15) @ X16)
% 0.21/0.51          | ~ (m1_pre_topc @ X15 @ X16)
% 0.21/0.51          | (v2_struct_0 @ X15))),
% 0.21/0.51      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.51          | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51          | ~ (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ X0)
% 0.21/0.51          | ~ (v2_tex_2 @ (u1_struct_0 @ (sk_C @ sk_B @ sk_A)) @ X0)
% 0.21/0.51          | (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | (v2_struct_0 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['13', '15'])).
% 0.21/0.51  thf('17', plain, (((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.21/0.51      inference('clc', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.51          | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51          | ~ (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ X0)
% 0.21/0.51          | ~ (v2_tex_2 @ sk_B @ X0)
% 0.21/0.51          | (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | (v2_struct_0 @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51        | ~ (v2_tex_2 @ sk_B @ sk_A)
% 0.21/0.51        | ~ (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['4', '18'])).
% 0.21/0.51  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51        | ~ (v2_tex_2 @ sk_B @ sk_A)
% 0.21/0.51        | ~ (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ X13)
% 0.21/0.51          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.51          | (m1_pre_topc @ (sk_C @ X13 @ X14) @ X14)
% 0.21/0.51          | ~ (l1_pre_topc @ X14)
% 0.21/0.51          | (v2_struct_0 @ X14))),
% 0.21/0.51      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.21/0.51        | (v1_xboole_0 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.51  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.21/0.51        | (v1_xboole_0 @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.51  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      (((v1_xboole_0 @ sk_B) | (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.21/0.51      inference('clc', [status(thm)], ['26', '27'])).
% 0.21/0.51  thf('29', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('30', plain, ((m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.21/0.51      inference('clc', [status(thm)], ['28', '29'])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51        | ~ (v2_tex_2 @ sk_B @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['21', '30'])).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      ((((v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51         | (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['3', '31'])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ X13)
% 0.21/0.51          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.51          | ~ (v2_struct_0 @ (sk_C @ X13 @ X14))
% 0.21/0.51          | ~ (l1_pre_topc @ X14)
% 0.21/0.51          | (v2_struct_0 @ X14))),
% 0.21/0.51      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | ~ (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51        | (v1_xboole_0 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.51  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51        | (v1_xboole_0 @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['35', '36'])).
% 0.21/0.51  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      (((v1_xboole_0 @ sk_B) | ~ (v2_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.21/0.51      inference('clc', [status(thm)], ['37', '38'])).
% 0.21/0.51  thf('40', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('41', plain, (~ (v2_struct_0 @ (sk_C @ sk_B @ sk_A))),
% 0.21/0.51      inference('clc', [status(thm)], ['39', '40'])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      ((((v2_struct_0 @ sk_A) | (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))))
% 0.21/0.51         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.51      inference('clc', [status(thm)], ['32', '41'])).
% 0.21/0.51  thf('43', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('44', plain,
% 0.21/0.51      (((v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))) <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.51      inference('clc', [status(thm)], ['42', '43'])).
% 0.21/0.51  thf('45', plain, ((m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.21/0.51      inference('clc', [status(thm)], ['28', '29'])).
% 0.21/0.51  thf(cc31_tex_2, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.21/0.51         ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.51           ( ( ( ~( v2_struct_0 @ B ) ) & ( v1_tdlat_3 @ B ) ) =>
% 0.21/0.51             ( ( ~( v2_struct_0 @ B ) ) & ( v7_struct_0 @ B ) ) ) ) ) ))).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      (![X9 : $i, X10 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X9 @ X10)
% 0.21/0.51          | (v7_struct_0 @ X9)
% 0.21/0.51          | ~ (v1_tdlat_3 @ X9)
% 0.21/0.51          | (v2_struct_0 @ X9)
% 0.21/0.51          | ~ (l1_pre_topc @ X10)
% 0.21/0.51          | ~ (v2_tdlat_3 @ X10)
% 0.21/0.51          | ~ (v2_pre_topc @ X10)
% 0.21/0.51          | (v2_struct_0 @ X10))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc31_tex_2])).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.51        | ~ (v2_tdlat_3 @ sk_A)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51        | ~ (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51        | (v7_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.51  thf('48', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('49', plain, ((v2_tdlat_3 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('51', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51        | ~ (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51        | (v7_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 0.21/0.51  thf('52', plain,
% 0.21/0.51      ((((v7_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51         | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['44', '51'])).
% 0.21/0.51  thf('53', plain, (~ (v2_struct_0 @ (sk_C @ sk_B @ sk_A))),
% 0.21/0.51      inference('clc', [status(thm)], ['39', '40'])).
% 0.21/0.51  thf('54', plain,
% 0.21/0.51      ((((v2_struct_0 @ sk_A) | (v7_struct_0 @ (sk_C @ sk_B @ sk_A))))
% 0.21/0.51         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.51      inference('clc', [status(thm)], ['52', '53'])).
% 0.21/0.51  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('56', plain,
% 0.21/0.51      (((v7_struct_0 @ (sk_C @ sk_B @ sk_A))) <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.51      inference('clc', [status(thm)], ['54', '55'])).
% 0.21/0.51  thf('57', plain, (((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.21/0.51      inference('clc', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf(fc7_struct_0, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.51       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.21/0.51  thf('58', plain,
% 0.21/0.51      (![X4 : $i]:
% 0.21/0.51         ((v1_zfmisc_1 @ (u1_struct_0 @ X4))
% 0.21/0.51          | ~ (l1_struct_0 @ X4)
% 0.21/0.51          | ~ (v7_struct_0 @ X4))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.21/0.51  thf('59', plain,
% 0.21/0.51      (((v1_zfmisc_1 @ sk_B)
% 0.21/0.51        | ~ (v7_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51        | ~ (l1_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['57', '58'])).
% 0.21/0.51  thf('60', plain, ((m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.21/0.51      inference('clc', [status(thm)], ['28', '29'])).
% 0.21/0.51  thf(dt_m1_pre_topc, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.51  thf('61', plain,
% 0.21/0.51      (![X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X1 @ X2) | (l1_pre_topc @ X1) | ~ (l1_pre_topc @ X2))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.51  thf('62', plain,
% 0.21/0.51      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (sk_C @ sk_B @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['60', '61'])).
% 0.21/0.51  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('64', plain, ((l1_pre_topc @ (sk_C @ sk_B @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['62', '63'])).
% 0.21/0.51  thf(dt_l1_pre_topc, axiom,
% 0.21/0.51    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.51  thf('65', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('66', plain, ((l1_struct_0 @ (sk_C @ sk_B @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.51  thf('67', plain,
% 0.21/0.51      (((v1_zfmisc_1 @ sk_B) | ~ (v7_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['59', '66'])).
% 0.21/0.51  thf('68', plain, (((v1_zfmisc_1 @ sk_B)) <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['56', '67'])).
% 0.21/0.51  thf('69', plain, ((~ (v1_zfmisc_1 @ sk_B)) <= (~ ((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf('70', plain, (((v1_zfmisc_1 @ sk_B)) | ~ ((v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['68', '69'])).
% 0.21/0.51  thf('71', plain, (((v1_zfmisc_1 @ sk_B)) | ((v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.51      inference('split', [status(esa)], ['2'])).
% 0.21/0.51  thf('72', plain, ((m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.21/0.51      inference('clc', [status(thm)], ['28', '29'])).
% 0.21/0.51  thf('73', plain, (((v1_zfmisc_1 @ sk_B)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.51      inference('split', [status(esa)], ['2'])).
% 0.21/0.51  thf('74', plain, (((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.21/0.51      inference('clc', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf(fc6_struct_0, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v7_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.51       ( ~( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.51  thf('75', plain,
% 0.21/0.51      (![X3 : $i]:
% 0.21/0.51         (~ (v1_zfmisc_1 @ (u1_struct_0 @ X3))
% 0.21/0.51          | ~ (l1_struct_0 @ X3)
% 0.21/0.51          | (v7_struct_0 @ X3))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc6_struct_0])).
% 0.21/0.51  thf('76', plain,
% 0.21/0.51      ((~ (v1_zfmisc_1 @ sk_B)
% 0.21/0.51        | (v7_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51        | ~ (l1_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['74', '75'])).
% 0.21/0.51  thf('77', plain, ((l1_struct_0 @ (sk_C @ sk_B @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.51  thf('78', plain,
% 0.21/0.51      ((~ (v1_zfmisc_1 @ sk_B) | (v7_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['76', '77'])).
% 0.21/0.51  thf('79', plain,
% 0.21/0.51      (((v7_struct_0 @ (sk_C @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['73', '78'])).
% 0.21/0.51  thf('80', plain, ((m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.21/0.51      inference('clc', [status(thm)], ['28', '29'])).
% 0.21/0.51  thf(cc25_tex_2, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.51           ( ( ( ~( v2_struct_0 @ B ) ) & ( v7_struct_0 @ B ) & 
% 0.21/0.51               ( v2_pre_topc @ B ) ) =>
% 0.21/0.51             ( ( ~( v2_struct_0 @ B ) ) & ( v1_tdlat_3 @ B ) & 
% 0.21/0.51               ( v2_tdlat_3 @ B ) ) ) ) ) ))).
% 0.21/0.51  thf('81', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X7 @ X8)
% 0.21/0.51          | (v1_tdlat_3 @ X7)
% 0.21/0.51          | ~ (v2_pre_topc @ X7)
% 0.21/0.51          | ~ (v7_struct_0 @ X7)
% 0.21/0.51          | (v2_struct_0 @ X7)
% 0.21/0.51          | ~ (l1_pre_topc @ X8)
% 0.21/0.51          | (v2_struct_0 @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc25_tex_2])).
% 0.21/0.51  thf('82', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51        | ~ (v7_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51        | ~ (v2_pre_topc @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51        | (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['80', '81'])).
% 0.21/0.51  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('84', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51        | ~ (v7_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51        | ~ (v2_pre_topc @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51        | (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['82', '83'])).
% 0.21/0.51  thf('85', plain, ((m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.21/0.51      inference('clc', [status(thm)], ['28', '29'])).
% 0.21/0.51  thf(cc15_tex_2, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.51           ( ( v2_tdlat_3 @ B ) => ( v2_pre_topc @ B ) ) ) ) ))).
% 0.21/0.51  thf('86', plain,
% 0.21/0.51      (![X5 : $i, X6 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X5 @ X6)
% 0.21/0.51          | (v2_pre_topc @ X5)
% 0.21/0.51          | ~ (v2_tdlat_3 @ X5)
% 0.21/0.51          | ~ (l1_pre_topc @ X6)
% 0.21/0.51          | (v2_struct_0 @ X6))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc15_tex_2])).
% 0.21/0.51  thf('87', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | ~ (v2_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51        | (v2_pre_topc @ (sk_C @ sk_B @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['85', '86'])).
% 0.21/0.51  thf('88', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('89', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (v2_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51        | (v2_pre_topc @ (sk_C @ sk_B @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['87', '88'])).
% 0.21/0.51  thf('90', plain, ((m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.21/0.51      inference('clc', [status(thm)], ['28', '29'])).
% 0.21/0.51  thf(cc6_tdlat_3, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.21/0.51         ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_tdlat_3 @ B ) ) ) ))).
% 0.21/0.51  thf('91', plain,
% 0.21/0.51      (![X11 : $i, X12 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X11 @ X12)
% 0.21/0.51          | (v2_tdlat_3 @ X11)
% 0.21/0.51          | ~ (l1_pre_topc @ X12)
% 0.21/0.51          | ~ (v2_tdlat_3 @ X12)
% 0.21/0.51          | ~ (v2_pre_topc @ X12)
% 0.21/0.51          | (v2_struct_0 @ X12))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc6_tdlat_3])).
% 0.21/0.51  thf('92', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.51        | ~ (v2_tdlat_3 @ sk_A)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | (v2_tdlat_3 @ (sk_C @ sk_B @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['90', '91'])).
% 0.21/0.51  thf('93', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('94', plain, ((v2_tdlat_3 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('96', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A) | (v2_tdlat_3 @ (sk_C @ sk_B @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['92', '93', '94', '95'])).
% 0.21/0.51  thf('97', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('98', plain, ((v2_tdlat_3 @ (sk_C @ sk_B @ sk_A))),
% 0.21/0.51      inference('clc', [status(thm)], ['96', '97'])).
% 0.21/0.51  thf('99', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A) | (v2_pre_topc @ (sk_C @ sk_B @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['89', '98'])).
% 0.21/0.51  thf('100', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('101', plain, ((v2_pre_topc @ (sk_C @ sk_B @ sk_A))),
% 0.21/0.51      inference('clc', [status(thm)], ['99', '100'])).
% 0.21/0.51  thf('102', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51        | ~ (v7_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51        | (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['84', '101'])).
% 0.21/0.51  thf('103', plain,
% 0.21/0.51      ((((v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51         | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51         | (v2_struct_0 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['79', '102'])).
% 0.21/0.51  thf('104', plain, (~ (v2_struct_0 @ (sk_C @ sk_B @ sk_A))),
% 0.21/0.51      inference('clc', [status(thm)], ['39', '40'])).
% 0.21/0.51  thf('105', plain,
% 0.21/0.51      ((((v2_struct_0 @ sk_A) | (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))))
% 0.21/0.51         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.51      inference('clc', [status(thm)], ['103', '104'])).
% 0.21/0.51  thf('106', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('107', plain,
% 0.21/0.51      (((v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.51      inference('clc', [status(thm)], ['105', '106'])).
% 0.21/0.51  thf('108', plain, (((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.21/0.51      inference('clc', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf('109', plain,
% 0.21/0.51      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X15)
% 0.21/0.51          | ~ (m1_pre_topc @ X15 @ X16)
% 0.21/0.51          | ((X17) != (u1_struct_0 @ X15))
% 0.21/0.51          | ~ (v1_tdlat_3 @ X15)
% 0.21/0.51          | (v2_tex_2 @ X17 @ X16)
% 0.21/0.51          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.51          | ~ (l1_pre_topc @ X16)
% 0.21/0.51          | (v2_struct_0 @ X16))),
% 0.21/0.51      inference('cnf', [status(esa)], [t26_tex_2])).
% 0.21/0.51  thf('110', plain,
% 0.21/0.51      (![X15 : $i, X16 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X16)
% 0.21/0.51          | ~ (l1_pre_topc @ X16)
% 0.21/0.51          | ~ (m1_subset_1 @ (u1_struct_0 @ X15) @ 
% 0.21/0.51               (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.51          | (v2_tex_2 @ (u1_struct_0 @ X15) @ X16)
% 0.21/0.51          | ~ (v1_tdlat_3 @ X15)
% 0.21/0.51          | ~ (m1_pre_topc @ X15 @ X16)
% 0.21/0.51          | (v2_struct_0 @ X15))),
% 0.21/0.51      inference('simplify', [status(thm)], ['109'])).
% 0.21/0.51  thf('111', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.51          | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51          | ~ (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ X0)
% 0.21/0.51          | ~ (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51          | (v2_tex_2 @ (u1_struct_0 @ (sk_C @ sk_B @ sk_A)) @ X0)
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | (v2_struct_0 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['108', '110'])).
% 0.21/0.51  thf('112', plain, (((sk_B) = (u1_struct_0 @ (sk_C @ sk_B @ sk_A)))),
% 0.21/0.51      inference('clc', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf('113', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.51          | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51          | ~ (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ X0)
% 0.21/0.51          | ~ (v1_tdlat_3 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51          | (v2_tex_2 @ sk_B @ X0)
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | (v2_struct_0 @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['111', '112'])).
% 0.21/0.51  thf('114', plain,
% 0.21/0.51      ((![X0 : $i]:
% 0.21/0.51          ((v2_struct_0 @ X0)
% 0.21/0.51           | ~ (l1_pre_topc @ X0)
% 0.21/0.51           | (v2_tex_2 @ sk_B @ X0)
% 0.21/0.51           | ~ (m1_pre_topc @ (sk_C @ sk_B @ sk_A) @ X0)
% 0.21/0.51           | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51           | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))))
% 0.21/0.51         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['107', '113'])).
% 0.21/0.51  thf('115', plain,
% 0.21/0.51      (((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51         | (v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51         | (v2_tex_2 @ sk_B @ sk_A)
% 0.21/0.51         | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51         | (v2_struct_0 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['72', '114'])).
% 0.21/0.51  thf('116', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('117', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('118', plain,
% 0.21/0.51      ((((v2_struct_0 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51         | (v2_tex_2 @ sk_B @ sk_A)
% 0.21/0.51         | (v2_struct_0 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.51      inference('demod', [status(thm)], ['115', '116', '117'])).
% 0.21/0.51  thf('119', plain, (~ (v2_struct_0 @ (sk_C @ sk_B @ sk_A))),
% 0.21/0.51      inference('clc', [status(thm)], ['39', '40'])).
% 0.21/0.51  thf('120', plain,
% 0.21/0.51      ((((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B @ sk_A)))
% 0.21/0.51         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.51      inference('clc', [status(thm)], ['118', '119'])).
% 0.21/0.51  thf('121', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('122', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.51      inference('clc', [status(thm)], ['120', '121'])).
% 0.21/0.51  thf('123', plain,
% 0.21/0.51      ((~ (v2_tex_2 @ sk_B @ sk_A)) <= (~ ((v2_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf('124', plain, (~ ((v1_zfmisc_1 @ sk_B)) | ((v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['122', '123'])).
% 0.21/0.51  thf('125', plain, ($false),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['1', '70', '71', '124'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.36/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
