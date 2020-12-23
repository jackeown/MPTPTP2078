%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GS0HGBFAY6

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  156 (2904 expanded)
%              Number of leaves         :   28 ( 841 expanded)
%              Depth                    :   28
%              Number of atoms          : 1466 (49699 expanded)
%              Number of equality atoms :   19 ( 123 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(v4_tex_2_type,type,(
    v4_tex_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(t67_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v1_tdlat_3 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ? [C: $i] :
              ( ( v4_tex_2 @ C @ A )
              & ( m1_pre_topc @ B @ C )
              & ( m1_pre_topc @ C @ A )
              & ( v1_pre_topc @ C )
              & ~ ( v2_struct_0 @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v3_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v1_tdlat_3 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ? [C: $i] :
                ( ( v4_tex_2 @ C @ A )
                & ( m1_pre_topc @ B @ C )
                & ( m1_pre_topc @ C @ A )
                & ( v1_pre_topc @ C )
                & ~ ( v2_struct_0 @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t67_tex_2])).

thf('0',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t65_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ~ ( ( v2_tex_2 @ B @ A )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ~ ( ( r1_tarski @ B @ C )
                      & ( v3_tex_2 @ C @ A ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v2_tex_2 @ X15 @ X16 )
      | ( m1_subset_1 @ ( sk_C_2 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v3_tdlat_3 @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

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

thf('11',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ( X12
       != ( u1_struct_0 @ X10 ) )
      | ~ ( v1_tdlat_3 @ X10 )
      | ( v2_tex_2 @ X12 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t26_tex_2])).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ X10 ) @ X11 )
      | ~ ( v1_tdlat_3 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_B )
    | ( v2_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_tdlat_3 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v2_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['6','7','8','9','21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['22','23'])).

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

thf('25',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v2_struct_0 @ ( sk_C_1 @ X8 @ X9 ) )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf(t46_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( v3_tex_2 @ B @ A ) ) ) )).

thf('32',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v3_tex_2 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t46_tex_2])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tex_2 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A )
    | ~ ( v1_xboole_0 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('37',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v2_tex_2 @ X15 @ X16 )
      | ( v3_tex_2 @ ( sk_C_2 @ X15 @ X16 ) @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v3_tdlat_3 @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v2_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['19','20'])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v3_tex_2 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['38','39','40','41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v3_tex_2 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v1_xboole_0 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34','35','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ~ ( v1_xboole_0 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['30','48'])).

thf('50',plain,(
    m1_subset_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('51',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( m1_pre_topc @ ( sk_C_1 @ X8 @ X9 ) @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v1_xboole_0 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) )
    | ( m1_pre_topc @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( v1_xboole_0 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('58',plain,(
    m1_pre_topc @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['56','57'])).

thf(d8_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v4_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( C
                    = ( u1_struct_0 @ B ) )
                 => ( v3_tex_2 @ C @ A ) ) ) ) ) ) )).

thf('59',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( ( sk_C @ X5 @ X6 )
        = ( u1_struct_0 @ X5 ) )
      | ( v4_tex_2 @ X5 @ X6 )
      | ~ ( l1_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_tex_2])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_tex_2 @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A )
    | ( ( sk_C @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A )
      = ( u1_struct_0 @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v4_tex_2 @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A )
    | ( ( sk_C @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A )
      = ( u1_struct_0 @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('64',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( X8
        = ( u1_struct_0 @ ( sk_C_1 @ X8 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('65',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) )
    | ( v1_xboole_0 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) )
    | ( v1_xboole_0 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v1_xboole_0 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) )
    | ( ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( v1_xboole_0 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('71',plain,
    ( ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A )
    = ( u1_struct_0 @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v4_tex_2 @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A )
    | ( ( sk_C @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A )
      = ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ( sk_C @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A )
      = ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) )
    | ( v4_tex_2 @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X17: $i] :
      ( ~ ( v4_tex_2 @ X17 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X17 )
      | ~ ( m1_pre_topc @ X17 @ sk_A )
      | ~ ( v1_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( ( sk_C @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A )
      = ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) )
    | ~ ( v1_pre_topc @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) )
    | ~ ( m1_pre_topc @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('78',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v1_pre_topc @ ( sk_C_1 @ X8 @ X9 ) )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_pre_topc @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_pre_topc @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( v1_xboole_0 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) )
    | ( v1_pre_topc @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,(
    ~ ( v1_xboole_0 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('85',plain,(
    v1_pre_topc @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,(
    m1_pre_topc @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['56','57'])).

thf('87',plain,
    ( ( ( sk_C @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A )
      = ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) )
    | ~ ( m1_pre_topc @ sk_B @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','85','86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['30','48'])).

thf('89',plain,
    ( ~ ( m1_pre_topc @ sk_B @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) )
    | ( ( sk_C @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A )
      = ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('91',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v2_tex_2 @ X15 @ X16 )
      | ( r1_tarski @ X15 @ ( sk_C_2 @ X15 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v3_tdlat_3 @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) )
    | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v2_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['19','20'])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['92','93','94','95','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,(
    m1_pre_topc @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['56','57'])).

thf('101',plain,
    ( ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A )
    = ( u1_struct_0 @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf(t4_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) )
              <=> ( m1_pre_topc @ B @ C ) ) ) ) ) )).

thf('102',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X3 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X4 ) )
      | ( m1_pre_topc @ X2 @ X4 )
      | ~ ( m1_pre_topc @ X4 @ X3 )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ X1 )
      | ( m1_pre_topc @ X0 @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ X0 @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['100','103'])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ X0 @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,
    ( ( m1_pre_topc @ sk_B @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['99','107'])).

thf('109',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    m1_pre_topc @ sk_B @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( sk_C @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A )
    = ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['89','110'])).

thf('112',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ~ ( v3_tex_2 @ ( sk_C @ X5 @ X6 ) @ X6 )
      | ( v4_tex_2 @ X5 @ X6 )
      | ~ ( l1_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_tex_2])).

thf('113',plain,
    ( ~ ( v3_tex_2 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_tex_2 @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A )
    | ~ ( m1_pre_topc @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    v3_tex_2 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['43','44'])).

thf('115',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    m1_pre_topc @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['56','57'])).

thf('117',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v4_tex_2 @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['113','114','115','116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v4_tex_2 @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X17: $i] :
      ( ~ ( v4_tex_2 @ X17 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X17 )
      | ~ ( m1_pre_topc @ X17 @ sk_A )
      | ~ ( v1_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( v2_struct_0 @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) )
    | ~ ( v1_pre_topc @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) )
    | ~ ( m1_pre_topc @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v1_pre_topc @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('123',plain,(
    m1_pre_topc @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['56','57'])).

thf('124',plain,(
    m1_pre_topc @ sk_B @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('125',plain,(
    v2_struct_0 @ ( sk_C_1 @ ( sk_C_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['121','122','123','124'])).

thf('126',plain,(
    $false ),
    inference(demod,[status(thm)],['49','125'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GS0HGBFAY6
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:08:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 195 iterations in 0.104s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.55  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.20/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.55  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.55  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.20/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.55  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.55  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.20/0.55  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.20/0.55  thf(v4_tex_2_type, type, v4_tex_2: $i > $i > $o).
% 0.20/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.55  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.55  thf(t67_tex_2, conjecture,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.20/0.55         ( l1_pre_topc @ A ) ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v1_tdlat_3 @ B ) & 
% 0.20/0.55             ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.55           ( ?[C:$i]:
% 0.20/0.55             ( ( v4_tex_2 @ C @ A ) & ( m1_pre_topc @ B @ C ) & 
% 0.20/0.55               ( m1_pre_topc @ C @ A ) & ( v1_pre_topc @ C ) & 
% 0.20/0.55               ( ~( v2_struct_0 @ C ) ) ) ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i]:
% 0.20/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.55            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.55          ( ![B:$i]:
% 0.20/0.55            ( ( ( ~( v2_struct_0 @ B ) ) & ( v1_tdlat_3 @ B ) & 
% 0.20/0.55                ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.55              ( ?[C:$i]:
% 0.20/0.55                ( ( v4_tex_2 @ C @ A ) & ( m1_pre_topc @ B @ C ) & 
% 0.20/0.55                  ( m1_pre_topc @ C @ A ) & ( v1_pre_topc @ C ) & 
% 0.20/0.55                  ( ~( v2_struct_0 @ C ) ) ) ) ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t67_tex_2])).
% 0.20/0.55  thf('0', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(t1_tsep_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( l1_pre_topc @ A ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.55           ( m1_subset_1 @
% 0.20/0.55             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.55  thf('1', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.55          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.20/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.55          | ~ (l1_pre_topc @ X1))),
% 0.20/0.55      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.20/0.55  thf('2', plain,
% 0.20/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.55        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.55  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('4', plain,
% 0.20/0.55      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.55  thf(t65_tex_2, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.20/0.55         ( l1_pre_topc @ A ) ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.20/0.55                ( ![C:$i]:
% 0.20/0.55                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55                    ( ~( ( r1_tarski @ B @ C ) & ( v3_tex_2 @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf('5', plain,
% 0.20/0.55      (![X15 : $i, X16 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.55          | ~ (v2_tex_2 @ X15 @ X16)
% 0.20/0.55          | (m1_subset_1 @ (sk_C_2 @ X15 @ X16) @ 
% 0.20/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.55          | ~ (l1_pre_topc @ X16)
% 0.20/0.55          | ~ (v3_tdlat_3 @ X16)
% 0.20/0.55          | ~ (v2_pre_topc @ X16)
% 0.20/0.55          | (v2_struct_0 @ X16))),
% 0.20/0.55      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.20/0.55  thf('6', plain,
% 0.20/0.55      (((v2_struct_0 @ sk_A)
% 0.20/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.55        | ~ (v3_tdlat_3 @ sk_A)
% 0.20/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.55        | (m1_subset_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ 
% 0.20/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.55        | ~ (v2_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.55  thf('7', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('8', plain, ((v3_tdlat_3 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('10', plain,
% 0.20/0.55      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.55  thf(t26_tex_2, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.55           ( ![C:$i]:
% 0.20/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.20/0.55                 ( ( v2_tex_2 @ C @ A ) <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf('11', plain,
% 0.20/0.55      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.55         ((v2_struct_0 @ X10)
% 0.20/0.55          | ~ (m1_pre_topc @ X10 @ X11)
% 0.20/0.55          | ((X12) != (u1_struct_0 @ X10))
% 0.20/0.55          | ~ (v1_tdlat_3 @ X10)
% 0.20/0.55          | (v2_tex_2 @ X12 @ X11)
% 0.20/0.55          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.55          | ~ (l1_pre_topc @ X11)
% 0.20/0.55          | (v2_struct_0 @ X11))),
% 0.20/0.55      inference('cnf', [status(esa)], [t26_tex_2])).
% 0.20/0.55  thf('12', plain,
% 0.20/0.55      (![X10 : $i, X11 : $i]:
% 0.20/0.55         ((v2_struct_0 @ X11)
% 0.20/0.55          | ~ (l1_pre_topc @ X11)
% 0.20/0.55          | ~ (m1_subset_1 @ (u1_struct_0 @ X10) @ 
% 0.20/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.55          | (v2_tex_2 @ (u1_struct_0 @ X10) @ X11)
% 0.20/0.55          | ~ (v1_tdlat_3 @ X10)
% 0.20/0.55          | ~ (m1_pre_topc @ X10 @ X11)
% 0.20/0.55          | (v2_struct_0 @ X10))),
% 0.20/0.55      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.55  thf('13', plain,
% 0.20/0.55      (((v2_struct_0 @ sk_B)
% 0.20/0.55        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.20/0.55        | ~ (v1_tdlat_3 @ sk_B)
% 0.20/0.55        | (v2_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.20/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.55        | (v2_struct_0 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['10', '12'])).
% 0.20/0.55  thf('14', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('15', plain, ((v1_tdlat_3 @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('17', plain,
% 0.20/0.55      (((v2_struct_0 @ sk_B)
% 0.20/0.55        | (v2_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.20/0.55        | (v2_struct_0 @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['13', '14', '15', '16'])).
% 0.20/0.55  thf('18', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('19', plain,
% 0.20/0.55      (((v2_struct_0 @ sk_A) | (v2_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.20/0.55      inference('clc', [status(thm)], ['17', '18'])).
% 0.20/0.56  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('21', plain, ((v2_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A)),
% 0.20/0.56      inference('clc', [status(thm)], ['19', '20'])).
% 0.20/0.56  thf('22', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_A)
% 0.20/0.56        | (m1_subset_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ 
% 0.20/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.56      inference('demod', [status(thm)], ['6', '7', '8', '9', '21'])).
% 0.20/0.56  thf('23', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('24', plain,
% 0.20/0.56      ((m1_subset_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ 
% 0.20/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('clc', [status(thm)], ['22', '23'])).
% 0.20/0.56  thf(t10_tsep_1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.56             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.56           ( ?[C:$i]:
% 0.20/0.56             ( ( ( B ) = ( u1_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) & 
% 0.20/0.56               ( v1_pre_topc @ C ) & ( ~( v2_struct_0 @ C ) ) ) ) ) ) ))).
% 0.20/0.56  thf('25', plain,
% 0.20/0.56      (![X8 : $i, X9 : $i]:
% 0.20/0.56         ((v1_xboole_0 @ X8)
% 0.20/0.56          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.56          | ~ (v2_struct_0 @ (sk_C_1 @ X8 @ X9))
% 0.20/0.56          | ~ (l1_pre_topc @ X9)
% 0.20/0.56          | (v2_struct_0 @ X9))),
% 0.20/0.56      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.20/0.56  thf('26', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_A)
% 0.20/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.56        | ~ (v2_struct_0 @ 
% 0.20/0.56             (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))
% 0.20/0.56        | (v1_xboole_0 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.56  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('28', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_A)
% 0.20/0.56        | ~ (v2_struct_0 @ 
% 0.20/0.56             (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))
% 0.20/0.56        | (v1_xboole_0 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.56  thf('29', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('30', plain,
% 0.20/0.56      (((v1_xboole_0 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.20/0.56        | ~ (v2_struct_0 @ 
% 0.20/0.56             (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A)))),
% 0.20/0.56      inference('clc', [status(thm)], ['28', '29'])).
% 0.20/0.56  thf('31', plain,
% 0.20/0.56      ((m1_subset_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ 
% 0.20/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('clc', [status(thm)], ['22', '23'])).
% 0.20/0.56  thf(t46_tex_2, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( ( v1_xboole_0 @ B ) & 
% 0.20/0.56             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.56           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.20/0.56  thf('32', plain,
% 0.20/0.56      (![X13 : $i, X14 : $i]:
% 0.20/0.56         (~ (v1_xboole_0 @ X13)
% 0.20/0.56          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.56          | ~ (v3_tex_2 @ X13 @ X14)
% 0.20/0.56          | ~ (l1_pre_topc @ X14)
% 0.20/0.56          | ~ (v2_pre_topc @ X14)
% 0.20/0.56          | (v2_struct_0 @ X14))),
% 0.20/0.56      inference('cnf', [status(esa)], [t46_tex_2])).
% 0.20/0.56  thf('33', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_A)
% 0.20/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.56        | ~ (v3_tex_2 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A)
% 0.20/0.56        | ~ (v1_xboole_0 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.56  thf('34', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('36', plain,
% 0.20/0.56      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.56  thf('37', plain,
% 0.20/0.56      (![X15 : $i, X16 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.56          | ~ (v2_tex_2 @ X15 @ X16)
% 0.20/0.56          | (v3_tex_2 @ (sk_C_2 @ X15 @ X16) @ X16)
% 0.20/0.56          | ~ (l1_pre_topc @ X16)
% 0.20/0.56          | ~ (v3_tdlat_3 @ X16)
% 0.20/0.56          | ~ (v2_pre_topc @ X16)
% 0.20/0.56          | (v2_struct_0 @ X16))),
% 0.20/0.56      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.20/0.56  thf('38', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_A)
% 0.20/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.56        | ~ (v3_tdlat_3 @ sk_A)
% 0.20/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.56        | (v3_tex_2 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A)
% 0.20/0.56        | ~ (v2_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.56  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('40', plain, ((v3_tdlat_3 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('42', plain, ((v2_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A)),
% 0.20/0.56      inference('clc', [status(thm)], ['19', '20'])).
% 0.20/0.56  thf('43', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_A)
% 0.20/0.56        | (v3_tex_2 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 0.20/0.56  thf('44', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('45', plain,
% 0.20/0.56      ((v3_tex_2 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A)),
% 0.20/0.56      inference('clc', [status(thm)], ['43', '44'])).
% 0.20/0.56  thf('46', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_A)
% 0.20/0.56        | ~ (v1_xboole_0 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['33', '34', '35', '45'])).
% 0.20/0.56  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('48', plain, (~ (v1_xboole_0 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.20/0.56      inference('clc', [status(thm)], ['46', '47'])).
% 0.20/0.56  thf('49', plain,
% 0.20/0.56      (~ (v2_struct_0 @ 
% 0.20/0.56          (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))),
% 0.20/0.56      inference('clc', [status(thm)], ['30', '48'])).
% 0.20/0.56  thf('50', plain,
% 0.20/0.56      ((m1_subset_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ 
% 0.20/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('clc', [status(thm)], ['22', '23'])).
% 0.20/0.56  thf('51', plain,
% 0.20/0.56      (![X8 : $i, X9 : $i]:
% 0.20/0.56         ((v1_xboole_0 @ X8)
% 0.20/0.56          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.56          | (m1_pre_topc @ (sk_C_1 @ X8 @ X9) @ X9)
% 0.20/0.56          | ~ (l1_pre_topc @ X9)
% 0.20/0.56          | (v2_struct_0 @ X9))),
% 0.20/0.56      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.20/0.56  thf('52', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_A)
% 0.20/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.56        | (m1_pre_topc @ 
% 0.20/0.56           (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A) @ sk_A)
% 0.20/0.56        | (v1_xboole_0 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.56  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('54', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_A)
% 0.20/0.56        | (m1_pre_topc @ 
% 0.20/0.56           (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A) @ sk_A)
% 0.20/0.56        | (v1_xboole_0 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['52', '53'])).
% 0.20/0.56  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('56', plain,
% 0.20/0.56      (((v1_xboole_0 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.20/0.56        | (m1_pre_topc @ 
% 0.20/0.56           (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A) @ sk_A))),
% 0.20/0.56      inference('clc', [status(thm)], ['54', '55'])).
% 0.20/0.56  thf('57', plain, (~ (v1_xboole_0 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.20/0.56      inference('clc', [status(thm)], ['46', '47'])).
% 0.20/0.56  thf('58', plain,
% 0.20/0.56      ((m1_pre_topc @ 
% 0.20/0.56        (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A) @ sk_A)),
% 0.20/0.56      inference('clc', [status(thm)], ['56', '57'])).
% 0.20/0.56  thf(d8_tex_2, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.56           ( ( v4_tex_2 @ B @ A ) <=>
% 0.20/0.56             ( ![C:$i]:
% 0.20/0.56               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56                 ( ( ( C ) = ( u1_struct_0 @ B ) ) => ( v3_tex_2 @ C @ A ) ) ) ) ) ) ) ))).
% 0.20/0.56  thf('59', plain,
% 0.20/0.56      (![X5 : $i, X6 : $i]:
% 0.20/0.56         (~ (m1_pre_topc @ X5 @ X6)
% 0.20/0.56          | ((sk_C @ X5 @ X6) = (u1_struct_0 @ X5))
% 0.20/0.56          | (v4_tex_2 @ X5 @ X6)
% 0.20/0.56          | ~ (l1_pre_topc @ X6)
% 0.20/0.56          | (v2_struct_0 @ X6))),
% 0.20/0.56      inference('cnf', [status(esa)], [d8_tex_2])).
% 0.20/0.56  thf('60', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_A)
% 0.20/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.56        | (v4_tex_2 @ 
% 0.20/0.56           (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A) @ sk_A)
% 0.20/0.56        | ((sk_C @ (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A) @ 
% 0.20/0.56            sk_A)
% 0.20/0.56            = (u1_struct_0 @ 
% 0.20/0.56               (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['58', '59'])).
% 0.20/0.56  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('62', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_A)
% 0.20/0.56        | (v4_tex_2 @ 
% 0.20/0.56           (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A) @ sk_A)
% 0.20/0.56        | ((sk_C @ (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A) @ 
% 0.20/0.56            sk_A)
% 0.20/0.56            = (u1_struct_0 @ 
% 0.20/0.56               (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))))),
% 0.20/0.56      inference('demod', [status(thm)], ['60', '61'])).
% 0.20/0.56  thf('63', plain,
% 0.20/0.56      ((m1_subset_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ 
% 0.20/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('clc', [status(thm)], ['22', '23'])).
% 0.20/0.56  thf('64', plain,
% 0.20/0.56      (![X8 : $i, X9 : $i]:
% 0.20/0.56         ((v1_xboole_0 @ X8)
% 0.20/0.56          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.56          | ((X8) = (u1_struct_0 @ (sk_C_1 @ X8 @ X9)))
% 0.20/0.56          | ~ (l1_pre_topc @ X9)
% 0.20/0.56          | (v2_struct_0 @ X9))),
% 0.20/0.56      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.20/0.56  thf('65', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_A)
% 0.20/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.56        | ((sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.20/0.56            = (u1_struct_0 @ 
% 0.20/0.56               (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A)))
% 0.20/0.56        | (v1_xboole_0 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.56  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('67', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_A)
% 0.20/0.56        | ((sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.20/0.56            = (u1_struct_0 @ 
% 0.20/0.56               (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A)))
% 0.20/0.56        | (v1_xboole_0 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['65', '66'])).
% 0.20/0.56  thf('68', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('69', plain,
% 0.20/0.56      (((v1_xboole_0 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.20/0.56        | ((sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.20/0.56            = (u1_struct_0 @ 
% 0.20/0.56               (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))))),
% 0.20/0.56      inference('clc', [status(thm)], ['67', '68'])).
% 0.20/0.56  thf('70', plain, (~ (v1_xboole_0 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.20/0.56      inference('clc', [status(thm)], ['46', '47'])).
% 0.20/0.56  thf('71', plain,
% 0.20/0.56      (((sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.20/0.56         = (u1_struct_0 @ 
% 0.20/0.56            (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A)))),
% 0.20/0.56      inference('clc', [status(thm)], ['69', '70'])).
% 0.20/0.56  thf('72', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_A)
% 0.20/0.56        | (v4_tex_2 @ 
% 0.20/0.56           (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A) @ sk_A)
% 0.20/0.56        | ((sk_C @ (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A) @ 
% 0.20/0.56            sk_A) = (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['62', '71'])).
% 0.20/0.56  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('74', plain,
% 0.20/0.56      ((((sk_C @ (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A) @ 
% 0.20/0.56          sk_A) = (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.20/0.56        | (v4_tex_2 @ 
% 0.20/0.56           (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A) @ sk_A))),
% 0.20/0.56      inference('clc', [status(thm)], ['72', '73'])).
% 0.20/0.56  thf('75', plain,
% 0.20/0.56      (![X17 : $i]:
% 0.20/0.56         (~ (v4_tex_2 @ X17 @ sk_A)
% 0.20/0.56          | ~ (m1_pre_topc @ sk_B @ X17)
% 0.20/0.56          | ~ (m1_pre_topc @ X17 @ sk_A)
% 0.20/0.56          | ~ (v1_pre_topc @ X17)
% 0.20/0.56          | (v2_struct_0 @ X17))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('76', plain,
% 0.20/0.56      ((((sk_C @ (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A) @ 
% 0.20/0.56          sk_A) = (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.20/0.56        | (v2_struct_0 @ 
% 0.20/0.56           (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))
% 0.20/0.56        | ~ (v1_pre_topc @ 
% 0.20/0.56             (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))
% 0.20/0.56        | ~ (m1_pre_topc @ 
% 0.20/0.56             (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A) @ sk_A)
% 0.20/0.56        | ~ (m1_pre_topc @ sk_B @ 
% 0.20/0.56             (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['74', '75'])).
% 0.20/0.56  thf('77', plain,
% 0.20/0.56      ((m1_subset_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ 
% 0.20/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('clc', [status(thm)], ['22', '23'])).
% 0.20/0.56  thf('78', plain,
% 0.20/0.56      (![X8 : $i, X9 : $i]:
% 0.20/0.56         ((v1_xboole_0 @ X8)
% 0.20/0.56          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.56          | (v1_pre_topc @ (sk_C_1 @ X8 @ X9))
% 0.20/0.56          | ~ (l1_pre_topc @ X9)
% 0.20/0.56          | (v2_struct_0 @ X9))),
% 0.20/0.56      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.20/0.56  thf('79', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_A)
% 0.20/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.56        | (v1_pre_topc @ 
% 0.20/0.56           (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))
% 0.20/0.56        | (v1_xboole_0 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['77', '78'])).
% 0.20/0.56  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('81', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_A)
% 0.20/0.56        | (v1_pre_topc @ 
% 0.20/0.56           (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))
% 0.20/0.56        | (v1_xboole_0 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['79', '80'])).
% 0.20/0.56  thf('82', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('83', plain,
% 0.20/0.56      (((v1_xboole_0 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.20/0.56        | (v1_pre_topc @ 
% 0.20/0.56           (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A)))),
% 0.20/0.56      inference('clc', [status(thm)], ['81', '82'])).
% 0.20/0.56  thf('84', plain, (~ (v1_xboole_0 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.20/0.56      inference('clc', [status(thm)], ['46', '47'])).
% 0.20/0.56  thf('85', plain,
% 0.20/0.56      ((v1_pre_topc @ (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))),
% 0.20/0.56      inference('clc', [status(thm)], ['83', '84'])).
% 0.20/0.56  thf('86', plain,
% 0.20/0.56      ((m1_pre_topc @ 
% 0.20/0.56        (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A) @ sk_A)),
% 0.20/0.56      inference('clc', [status(thm)], ['56', '57'])).
% 0.20/0.56  thf('87', plain,
% 0.20/0.56      ((((sk_C @ (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A) @ 
% 0.20/0.56          sk_A) = (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.20/0.56        | (v2_struct_0 @ 
% 0.20/0.56           (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))
% 0.20/0.56        | ~ (m1_pre_topc @ sk_B @ 
% 0.20/0.56             (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['76', '85', '86'])).
% 0.20/0.56  thf('88', plain,
% 0.20/0.56      (~ (v2_struct_0 @ 
% 0.20/0.56          (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))),
% 0.20/0.56      inference('clc', [status(thm)], ['30', '48'])).
% 0.20/0.56  thf('89', plain,
% 0.20/0.56      ((~ (m1_pre_topc @ sk_B @ 
% 0.20/0.56           (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))
% 0.20/0.56        | ((sk_C @ (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A) @ 
% 0.20/0.56            sk_A) = (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A)))),
% 0.20/0.56      inference('clc', [status(thm)], ['87', '88'])).
% 0.20/0.56  thf('90', plain,
% 0.20/0.56      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.56  thf('91', plain,
% 0.20/0.56      (![X15 : $i, X16 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.56          | ~ (v2_tex_2 @ X15 @ X16)
% 0.20/0.56          | (r1_tarski @ X15 @ (sk_C_2 @ X15 @ X16))
% 0.20/0.56          | ~ (l1_pre_topc @ X16)
% 0.20/0.56          | ~ (v3_tdlat_3 @ X16)
% 0.20/0.56          | ~ (v2_pre_topc @ X16)
% 0.20/0.56          | (v2_struct_0 @ X16))),
% 0.20/0.56      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.20/0.56  thf('92', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_A)
% 0.20/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.56        | ~ (v3_tdlat_3 @ sk_A)
% 0.20/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.56        | (r1_tarski @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.56           (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.20/0.56        | ~ (v2_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['90', '91'])).
% 0.20/0.56  thf('93', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('94', plain, ((v3_tdlat_3 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('96', plain, ((v2_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A)),
% 0.20/0.56      inference('clc', [status(thm)], ['19', '20'])).
% 0.20/0.56  thf('97', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_A)
% 0.20/0.56        | (r1_tarski @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.56           (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['92', '93', '94', '95', '96'])).
% 0.20/0.56  thf('98', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('99', plain,
% 0.20/0.56      ((r1_tarski @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.56        (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.20/0.56      inference('clc', [status(thm)], ['97', '98'])).
% 0.20/0.56  thf('100', plain,
% 0.20/0.56      ((m1_pre_topc @ 
% 0.20/0.56        (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A) @ sk_A)),
% 0.20/0.56      inference('clc', [status(thm)], ['56', '57'])).
% 0.20/0.56  thf('101', plain,
% 0.20/0.56      (((sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.20/0.56         = (u1_struct_0 @ 
% 0.20/0.56            (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A)))),
% 0.20/0.56      inference('clc', [status(thm)], ['69', '70'])).
% 0.20/0.56  thf(t4_tsep_1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.56           ( ![C:$i]:
% 0.20/0.56             ( ( m1_pre_topc @ C @ A ) =>
% 0.20/0.56               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.20/0.56                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.20/0.56  thf('102', plain,
% 0.20/0.56      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.56         (~ (m1_pre_topc @ X2 @ X3)
% 0.20/0.56          | ~ (r1_tarski @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X4))
% 0.20/0.56          | (m1_pre_topc @ X2 @ X4)
% 0.20/0.56          | ~ (m1_pre_topc @ X4 @ X3)
% 0.20/0.56          | ~ (l1_pre_topc @ X3)
% 0.20/0.56          | ~ (v2_pre_topc @ X3))),
% 0.20/0.56      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.20/0.56  thf('103', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (~ (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.20/0.56             (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.20/0.56          | ~ (v2_pre_topc @ X1)
% 0.20/0.56          | ~ (l1_pre_topc @ X1)
% 0.20/0.56          | ~ (m1_pre_topc @ 
% 0.20/0.56               (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A) @ X1)
% 0.20/0.56          | (m1_pre_topc @ X0 @ 
% 0.20/0.56             (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))
% 0.20/0.56          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['101', '102'])).
% 0.20/0.56  thf('104', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.56          | (m1_pre_topc @ X0 @ 
% 0.20/0.56             (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))
% 0.20/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.56          | ~ (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.20/0.56               (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['100', '103'])).
% 0.20/0.56  thf('105', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('106', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('107', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.56          | (m1_pre_topc @ X0 @ 
% 0.20/0.56             (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))
% 0.20/0.56          | ~ (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.20/0.56               (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['104', '105', '106'])).
% 0.20/0.56  thf('108', plain,
% 0.20/0.56      (((m1_pre_topc @ sk_B @ 
% 0.20/0.56         (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))
% 0.20/0.56        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['99', '107'])).
% 0.20/0.56  thf('109', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('110', plain,
% 0.20/0.56      ((m1_pre_topc @ sk_B @ 
% 0.20/0.56        (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['108', '109'])).
% 0.20/0.56  thf('111', plain,
% 0.20/0.56      (((sk_C @ (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A) @ sk_A)
% 0.20/0.56         = (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['89', '110'])).
% 0.20/0.56  thf('112', plain,
% 0.20/0.56      (![X5 : $i, X6 : $i]:
% 0.20/0.56         (~ (m1_pre_topc @ X5 @ X6)
% 0.20/0.56          | ~ (v3_tex_2 @ (sk_C @ X5 @ X6) @ X6)
% 0.20/0.56          | (v4_tex_2 @ X5 @ X6)
% 0.20/0.56          | ~ (l1_pre_topc @ X6)
% 0.20/0.56          | (v2_struct_0 @ X6))),
% 0.20/0.56      inference('cnf', [status(esa)], [d8_tex_2])).
% 0.20/0.56  thf('113', plain,
% 0.20/0.56      ((~ (v3_tex_2 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A)
% 0.20/0.56        | (v2_struct_0 @ sk_A)
% 0.20/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.56        | (v4_tex_2 @ 
% 0.20/0.56           (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A) @ sk_A)
% 0.20/0.56        | ~ (m1_pre_topc @ 
% 0.20/0.56             (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A) @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['111', '112'])).
% 0.20/0.56  thf('114', plain,
% 0.20/0.56      ((v3_tex_2 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A)),
% 0.20/0.56      inference('clc', [status(thm)], ['43', '44'])).
% 0.20/0.56  thf('115', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('116', plain,
% 0.20/0.56      ((m1_pre_topc @ 
% 0.20/0.56        (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A) @ sk_A)),
% 0.20/0.56      inference('clc', [status(thm)], ['56', '57'])).
% 0.20/0.56  thf('117', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_A)
% 0.20/0.56        | (v4_tex_2 @ 
% 0.20/0.56           (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A) @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['113', '114', '115', '116'])).
% 0.20/0.56  thf('118', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('119', plain,
% 0.20/0.56      ((v4_tex_2 @ (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A) @ 
% 0.20/0.56        sk_A)),
% 0.20/0.56      inference('clc', [status(thm)], ['117', '118'])).
% 0.20/0.56  thf('120', plain,
% 0.20/0.56      (![X17 : $i]:
% 0.20/0.56         (~ (v4_tex_2 @ X17 @ sk_A)
% 0.20/0.56          | ~ (m1_pre_topc @ sk_B @ X17)
% 0.20/0.56          | ~ (m1_pre_topc @ X17 @ sk_A)
% 0.20/0.56          | ~ (v1_pre_topc @ X17)
% 0.20/0.56          | (v2_struct_0 @ X17))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('121', plain,
% 0.20/0.56      (((v2_struct_0 @ (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))
% 0.20/0.56        | ~ (v1_pre_topc @ 
% 0.20/0.56             (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))
% 0.20/0.56        | ~ (m1_pre_topc @ 
% 0.20/0.56             (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A) @ sk_A)
% 0.20/0.56        | ~ (m1_pre_topc @ sk_B @ 
% 0.20/0.56             (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['119', '120'])).
% 0.20/0.56  thf('122', plain,
% 0.20/0.56      ((v1_pre_topc @ (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))),
% 0.20/0.56      inference('clc', [status(thm)], ['83', '84'])).
% 0.20/0.56  thf('123', plain,
% 0.20/0.56      ((m1_pre_topc @ 
% 0.20/0.56        (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A) @ sk_A)),
% 0.20/0.56      inference('clc', [status(thm)], ['56', '57'])).
% 0.20/0.56  thf('124', plain,
% 0.20/0.56      ((m1_pre_topc @ sk_B @ 
% 0.20/0.56        (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['108', '109'])).
% 0.20/0.56  thf('125', plain,
% 0.20/0.56      ((v2_struct_0 @ (sk_C_1 @ (sk_C_2 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['121', '122', '123', '124'])).
% 0.20/0.56  thf('126', plain, ($false), inference('demod', [status(thm)], ['49', '125'])).
% 0.20/0.56  
% 0.20/0.56  % SZS output end Refutation
% 0.20/0.56  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
