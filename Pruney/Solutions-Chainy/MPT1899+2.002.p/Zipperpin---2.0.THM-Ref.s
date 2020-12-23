%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TOj70PxRlp

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:43 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  146 (1804 expanded)
%              Number of leaves         :   27 ( 527 expanded)
%              Depth                    :   24
%              Number of atoms          : 1309 (30705 expanded)
%              Number of equality atoms :   11 (  72 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v4_tex_2_type,type,(
    v4_tex_2: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
      | ( m1_subset_1 @ ( sk_C_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
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
    | ( m1_subset_1 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( m1_pre_topc @ X7 @ X8 )
      | ( X9
       != ( u1_struct_0 @ X7 ) )
      | ~ ( v1_tdlat_3 @ X7 )
      | ( v2_tex_2 @ X9 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t26_tex_2])).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ X7 ) @ X8 )
      | ~ ( v1_tdlat_3 @ X7 )
      | ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_struct_0 @ X7 ) ) ),
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
    | ( m1_subset_1 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['6','7','8','9','21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( m1_pre_topc @ ( sk_C @ X5 @ X6 ) @ X6 )
      | ~ ( l1_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) )
    | ( m1_pre_topc @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v3_tex_2 @ X10 @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t46_tex_2])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tex_2 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A )
    | ~ ( v1_xboole_0 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
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
      | ( v3_tex_2 @ ( sk_C_1 @ X15 @ X16 ) @ X16 )
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
    | ( v3_tex_2 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A )
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
    | ( v3_tex_2 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['38','39','40','41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v3_tex_2 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v1_xboole_0 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34','35','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ~ ( v1_xboole_0 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    m1_pre_topc @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['30','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('51',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf(t51_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( v3_tex_2 @ C @ A )
                <=> ( v4_tex_2 @ B @ A ) ) ) ) ) ) )).

thf('54',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( X14
       != ( u1_struct_0 @ X12 ) )
      | ~ ( v3_tex_2 @ X14 @ X13 )
      | ( v4_tex_2 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t51_tex_2])).

thf('55',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v4_tex_2 @ X12 @ X13 )
      | ~ ( v3_tex_2 @ ( u1_struct_0 @ X12 ) @ X13 )
      | ~ ( m1_pre_topc @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ~ ( m1_pre_topc @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A )
    | ~ ( v3_tex_2 @ ( u1_struct_0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) @ sk_A )
    | ( v4_tex_2 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf('57',plain,(
    m1_pre_topc @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['30','48'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ~ ( v3_tex_2 @ ( u1_struct_0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) @ sk_A )
    | ( v4_tex_2 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v4_tex_2 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A )
    | ~ ( v3_tex_2 @ ( u1_struct_0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) @ sk_A ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('63',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( X5
        = ( u1_struct_0 @ ( sk_C @ X5 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) )
    | ( v1_xboole_0 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) )
    | ( v1_xboole_0 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v1_xboole_0 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) )
    | ( ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( v1_xboole_0 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('70',plain,
    ( ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A )
    = ( u1_struct_0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    v3_tex_2 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['43','44'])).

thf('72',plain,(
    v4_tex_2 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['61','70','71'])).

thf('73',plain,(
    ! [X17: $i] :
      ( ~ ( v4_tex_2 @ X17 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X17 )
      | ~ ( m1_pre_topc @ X17 @ sk_A )
      | ~ ( v1_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v2_struct_0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) )
    | ~ ( v1_pre_topc @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) )
    | ~ ( m1_pre_topc @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    m1_subset_1 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('76',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( v1_pre_topc @ ( sk_C @ X5 @ X6 ) )
      | ~ ( l1_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_pre_topc @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_pre_topc @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( v1_xboole_0 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) )
    | ( v1_pre_topc @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( v1_xboole_0 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('83',plain,(
    v1_pre_topc @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,(
    m1_pre_topc @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['30','48'])).

thf('85',plain,
    ( ( v2_struct_0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) )
    | ~ ( m1_pre_topc @ sk_B @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['74','83','84'])).

thf('86',plain,(
    m1_subset_1 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('87',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( v2_struct_0 @ ( sk_C @ X5 @ X6 ) )
      | ~ ( l1_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('88',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( v1_xboole_0 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) )
    | ~ ( v2_struct_0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( v1_xboole_0 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    ~ ( m1_pre_topc @ sk_B @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['85','94'])).

thf('96',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('97',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v2_tex_2 @ X15 @ X16 )
      | ( r1_tarski @ X15 @ ( sk_C_1 @ X15 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v3_tdlat_3 @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) )
    | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v2_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['19','20'])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','99','100','101','102'])).

thf('104',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,(
    m1_pre_topc @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['30','48'])).

thf('107',plain,
    ( ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A )
    = ( u1_struct_0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['68','69'])).

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

thf('108',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X3 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X4 ) )
      | ( m1_pre_topc @ X2 @ X4 )
      | ~ ( m1_pre_topc @ X4 @ X3 )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ X1 )
      | ( m1_pre_topc @ X0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ X0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['106','109'])).

thf('111',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ X0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('114',plain,
    ( ( m1_pre_topc @ sk_B @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['105','113'])).

thf('115',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    m1_pre_topc @ sk_B @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    $false ),
    inference(demod,[status(thm)],['95','116'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TOj70PxRlp
% 0.14/0.37  % Computer   : n013.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 14:42:25 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.39/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.61  % Solved by: fo/fo7.sh
% 0.39/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.61  % done 167 iterations in 0.122s
% 0.39/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.61  % SZS output start Refutation
% 0.39/0.61  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.39/0.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.39/0.61  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.39/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.61  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.39/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.61  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.39/0.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.39/0.61  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.39/0.61  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.39/0.61  thf(v4_tex_2_type, type, v4_tex_2: $i > $i > $o).
% 0.39/0.61  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.39/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.61  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.39/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.61  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.39/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.61  thf(t67_tex_2, conjecture,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.39/0.61         ( l1_pre_topc @ A ) ) =>
% 0.39/0.61       ( ![B:$i]:
% 0.39/0.61         ( ( ( ~( v2_struct_0 @ B ) ) & ( v1_tdlat_3 @ B ) & 
% 0.39/0.61             ( m1_pre_topc @ B @ A ) ) =>
% 0.39/0.61           ( ?[C:$i]:
% 0.39/0.61             ( ( v4_tex_2 @ C @ A ) & ( m1_pre_topc @ B @ C ) & 
% 0.39/0.61               ( m1_pre_topc @ C @ A ) & ( v1_pre_topc @ C ) & 
% 0.39/0.61               ( ~( v2_struct_0 @ C ) ) ) ) ) ) ))).
% 0.39/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.61    (~( ![A:$i]:
% 0.39/0.61        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.39/0.61            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.61          ( ![B:$i]:
% 0.39/0.61            ( ( ( ~( v2_struct_0 @ B ) ) & ( v1_tdlat_3 @ B ) & 
% 0.39/0.61                ( m1_pre_topc @ B @ A ) ) =>
% 0.39/0.61              ( ?[C:$i]:
% 0.39/0.61                ( ( v4_tex_2 @ C @ A ) & ( m1_pre_topc @ B @ C ) & 
% 0.39/0.61                  ( m1_pre_topc @ C @ A ) & ( v1_pre_topc @ C ) & 
% 0.39/0.61                  ( ~( v2_struct_0 @ C ) ) ) ) ) ) ) )),
% 0.39/0.61    inference('cnf.neg', [status(esa)], [t67_tex_2])).
% 0.39/0.61  thf('0', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf(t1_tsep_1, axiom,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( l1_pre_topc @ A ) =>
% 0.39/0.61       ( ![B:$i]:
% 0.39/0.61         ( ( m1_pre_topc @ B @ A ) =>
% 0.39/0.61           ( m1_subset_1 @
% 0.39/0.61             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.39/0.61  thf('1', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (~ (m1_pre_topc @ X0 @ X1)
% 0.39/0.61          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.39/0.61             (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.39/0.61          | ~ (l1_pre_topc @ X1))),
% 0.39/0.61      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.39/0.61  thf('2', plain,
% 0.39/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.39/0.61        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.61           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.61      inference('sup-', [status(thm)], ['0', '1'])).
% 0.39/0.61  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('4', plain,
% 0.39/0.61      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.61      inference('demod', [status(thm)], ['2', '3'])).
% 0.39/0.61  thf(t65_tex_2, axiom,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.39/0.61         ( l1_pre_topc @ A ) ) =>
% 0.39/0.61       ( ![B:$i]:
% 0.39/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.61           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.39/0.61                ( ![C:$i]:
% 0.39/0.61                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.61                    ( ~( ( r1_tarski @ B @ C ) & ( v3_tex_2 @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.61  thf('5', plain,
% 0.39/0.61      (![X15 : $i, X16 : $i]:
% 0.39/0.61         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.39/0.61          | ~ (v2_tex_2 @ X15 @ X16)
% 0.39/0.61          | (m1_subset_1 @ (sk_C_1 @ X15 @ X16) @ 
% 0.39/0.61             (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.39/0.61          | ~ (l1_pre_topc @ X16)
% 0.39/0.61          | ~ (v3_tdlat_3 @ X16)
% 0.39/0.61          | ~ (v2_pre_topc @ X16)
% 0.39/0.61          | (v2_struct_0 @ X16))),
% 0.39/0.61      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.39/0.61  thf('6', plain,
% 0.39/0.61      (((v2_struct_0 @ sk_A)
% 0.39/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.39/0.61        | ~ (v3_tdlat_3 @ sk_A)
% 0.39/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.39/0.61        | (m1_subset_1 @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ 
% 0.39/0.61           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.61        | ~ (v2_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.39/0.61      inference('sup-', [status(thm)], ['4', '5'])).
% 0.39/0.61  thf('7', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('8', plain, ((v3_tdlat_3 @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('10', plain,
% 0.39/0.61      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.61      inference('demod', [status(thm)], ['2', '3'])).
% 0.39/0.61  thf(t26_tex_2, axiom,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.61       ( ![B:$i]:
% 0.39/0.61         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.39/0.61           ( ![C:$i]:
% 0.39/0.61             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.61               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.39/0.61                 ( ( v2_tex_2 @ C @ A ) <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) ) ))).
% 0.39/0.61  thf('11', plain,
% 0.39/0.61      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.39/0.61         ((v2_struct_0 @ X7)
% 0.39/0.61          | ~ (m1_pre_topc @ X7 @ X8)
% 0.39/0.61          | ((X9) != (u1_struct_0 @ X7))
% 0.39/0.61          | ~ (v1_tdlat_3 @ X7)
% 0.39/0.61          | (v2_tex_2 @ X9 @ X8)
% 0.39/0.61          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.39/0.61          | ~ (l1_pre_topc @ X8)
% 0.39/0.61          | (v2_struct_0 @ X8))),
% 0.39/0.61      inference('cnf', [status(esa)], [t26_tex_2])).
% 0.39/0.61  thf('12', plain,
% 0.39/0.61      (![X7 : $i, X8 : $i]:
% 0.39/0.61         ((v2_struct_0 @ X8)
% 0.39/0.61          | ~ (l1_pre_topc @ X8)
% 0.39/0.61          | ~ (m1_subset_1 @ (u1_struct_0 @ X7) @ 
% 0.39/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.39/0.61          | (v2_tex_2 @ (u1_struct_0 @ X7) @ X8)
% 0.39/0.61          | ~ (v1_tdlat_3 @ X7)
% 0.39/0.61          | ~ (m1_pre_topc @ X7 @ X8)
% 0.39/0.61          | (v2_struct_0 @ X7))),
% 0.39/0.61      inference('simplify', [status(thm)], ['11'])).
% 0.39/0.61  thf('13', plain,
% 0.39/0.61      (((v2_struct_0 @ sk_B)
% 0.39/0.61        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.39/0.61        | ~ (v1_tdlat_3 @ sk_B)
% 0.39/0.61        | (v2_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.39/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.39/0.61        | (v2_struct_0 @ sk_A))),
% 0.39/0.61      inference('sup-', [status(thm)], ['10', '12'])).
% 0.39/0.61  thf('14', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('15', plain, ((v1_tdlat_3 @ sk_B)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('17', plain,
% 0.39/0.61      (((v2_struct_0 @ sk_B)
% 0.39/0.61        | (v2_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.39/0.61        | (v2_struct_0 @ sk_A))),
% 0.39/0.61      inference('demod', [status(thm)], ['13', '14', '15', '16'])).
% 0.39/0.61  thf('18', plain, (~ (v2_struct_0 @ sk_B)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('19', plain,
% 0.39/0.61      (((v2_struct_0 @ sk_A) | (v2_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.39/0.61      inference('clc', [status(thm)], ['17', '18'])).
% 0.39/0.61  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('21', plain, ((v2_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A)),
% 0.39/0.61      inference('clc', [status(thm)], ['19', '20'])).
% 0.39/0.61  thf('22', plain,
% 0.39/0.61      (((v2_struct_0 @ sk_A)
% 0.39/0.61        | (m1_subset_1 @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ 
% 0.39/0.61           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.61      inference('demod', [status(thm)], ['6', '7', '8', '9', '21'])).
% 0.39/0.61  thf('23', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('24', plain,
% 0.39/0.61      ((m1_subset_1 @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ 
% 0.39/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.61      inference('clc', [status(thm)], ['22', '23'])).
% 0.39/0.61  thf(t10_tsep_1, axiom,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.61       ( ![B:$i]:
% 0.39/0.61         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.39/0.61             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.39/0.61           ( ?[C:$i]:
% 0.39/0.61             ( ( ( B ) = ( u1_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) & 
% 0.39/0.61               ( v1_pre_topc @ C ) & ( ~( v2_struct_0 @ C ) ) ) ) ) ) ))).
% 0.39/0.61  thf('25', plain,
% 0.39/0.61      (![X5 : $i, X6 : $i]:
% 0.39/0.61         ((v1_xboole_0 @ X5)
% 0.39/0.61          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.39/0.61          | (m1_pre_topc @ (sk_C @ X5 @ X6) @ X6)
% 0.39/0.61          | ~ (l1_pre_topc @ X6)
% 0.39/0.61          | (v2_struct_0 @ X6))),
% 0.39/0.61      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.39/0.61  thf('26', plain,
% 0.39/0.61      (((v2_struct_0 @ sk_A)
% 0.39/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.39/0.61        | (m1_pre_topc @ 
% 0.39/0.61           (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A) @ sk_A)
% 0.39/0.61        | (v1_xboole_0 @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['24', '25'])).
% 0.39/0.61  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('28', plain,
% 0.39/0.61      (((v2_struct_0 @ sk_A)
% 0.39/0.61        | (m1_pre_topc @ 
% 0.39/0.61           (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A) @ sk_A)
% 0.39/0.61        | (v1_xboole_0 @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A)))),
% 0.39/0.61      inference('demod', [status(thm)], ['26', '27'])).
% 0.39/0.61  thf('29', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('30', plain,
% 0.39/0.61      (((v1_xboole_0 @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.39/0.61        | (m1_pre_topc @ 
% 0.39/0.61           (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A) @ sk_A))),
% 0.39/0.61      inference('clc', [status(thm)], ['28', '29'])).
% 0.39/0.61  thf('31', plain,
% 0.39/0.61      ((m1_subset_1 @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ 
% 0.39/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.61      inference('clc', [status(thm)], ['22', '23'])).
% 0.39/0.61  thf(t46_tex_2, axiom,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.61       ( ![B:$i]:
% 0.39/0.61         ( ( ( v1_xboole_0 @ B ) & 
% 0.39/0.61             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.39/0.61           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.39/0.61  thf('32', plain,
% 0.39/0.61      (![X10 : $i, X11 : $i]:
% 0.39/0.61         (~ (v1_xboole_0 @ X10)
% 0.39/0.61          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.39/0.61          | ~ (v3_tex_2 @ X10 @ X11)
% 0.39/0.61          | ~ (l1_pre_topc @ X11)
% 0.39/0.61          | ~ (v2_pre_topc @ X11)
% 0.39/0.61          | (v2_struct_0 @ X11))),
% 0.39/0.61      inference('cnf', [status(esa)], [t46_tex_2])).
% 0.39/0.61  thf('33', plain,
% 0.39/0.61      (((v2_struct_0 @ sk_A)
% 0.39/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.39/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.39/0.61        | ~ (v3_tex_2 @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A)
% 0.39/0.61        | ~ (v1_xboole_0 @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['31', '32'])).
% 0.39/0.61  thf('34', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('36', plain,
% 0.39/0.61      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.61      inference('demod', [status(thm)], ['2', '3'])).
% 0.39/0.61  thf('37', plain,
% 0.39/0.61      (![X15 : $i, X16 : $i]:
% 0.39/0.61         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.39/0.61          | ~ (v2_tex_2 @ X15 @ X16)
% 0.39/0.61          | (v3_tex_2 @ (sk_C_1 @ X15 @ X16) @ X16)
% 0.39/0.61          | ~ (l1_pre_topc @ X16)
% 0.39/0.61          | ~ (v3_tdlat_3 @ X16)
% 0.39/0.61          | ~ (v2_pre_topc @ X16)
% 0.39/0.61          | (v2_struct_0 @ X16))),
% 0.39/0.61      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.39/0.61  thf('38', plain,
% 0.39/0.61      (((v2_struct_0 @ sk_A)
% 0.39/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.39/0.61        | ~ (v3_tdlat_3 @ sk_A)
% 0.39/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.39/0.61        | (v3_tex_2 @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A)
% 0.39/0.61        | ~ (v2_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.39/0.61      inference('sup-', [status(thm)], ['36', '37'])).
% 0.39/0.61  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('40', plain, ((v3_tdlat_3 @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('42', plain, ((v2_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A)),
% 0.39/0.61      inference('clc', [status(thm)], ['19', '20'])).
% 0.39/0.61  thf('43', plain,
% 0.39/0.61      (((v2_struct_0 @ sk_A)
% 0.39/0.61        | (v3_tex_2 @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))),
% 0.39/0.61      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 0.39/0.61  thf('44', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('45', plain,
% 0.39/0.61      ((v3_tex_2 @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A)),
% 0.39/0.61      inference('clc', [status(thm)], ['43', '44'])).
% 0.39/0.61  thf('46', plain,
% 0.39/0.61      (((v2_struct_0 @ sk_A)
% 0.39/0.61        | ~ (v1_xboole_0 @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A)))),
% 0.39/0.61      inference('demod', [status(thm)], ['33', '34', '35', '45'])).
% 0.39/0.61  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('48', plain, (~ (v1_xboole_0 @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.39/0.61      inference('clc', [status(thm)], ['46', '47'])).
% 0.39/0.61  thf('49', plain,
% 0.39/0.61      ((m1_pre_topc @ (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A) @ 
% 0.39/0.61        sk_A)),
% 0.39/0.61      inference('clc', [status(thm)], ['30', '48'])).
% 0.39/0.61  thf('50', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (~ (m1_pre_topc @ X0 @ X1)
% 0.39/0.61          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.39/0.61             (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.39/0.61          | ~ (l1_pre_topc @ X1))),
% 0.39/0.61      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.39/0.61  thf('51', plain,
% 0.39/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.39/0.61        | (m1_subset_1 @ 
% 0.39/0.61           (u1_struct_0 @ 
% 0.39/0.61            (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A)) @ 
% 0.39/0.61           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.61      inference('sup-', [status(thm)], ['49', '50'])).
% 0.39/0.61  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('53', plain,
% 0.39/0.61      ((m1_subset_1 @ 
% 0.39/0.61        (u1_struct_0 @ (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A)) @ 
% 0.39/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.61      inference('demod', [status(thm)], ['51', '52'])).
% 0.39/0.61  thf(t51_tex_2, axiom,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.61       ( ![B:$i]:
% 0.39/0.61         ( ( m1_pre_topc @ B @ A ) =>
% 0.39/0.61           ( ![C:$i]:
% 0.39/0.61             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.61               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.39/0.61                 ( ( v3_tex_2 @ C @ A ) <=> ( v4_tex_2 @ B @ A ) ) ) ) ) ) ) ))).
% 0.39/0.61  thf('54', plain,
% 0.39/0.61      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.39/0.61         (~ (m1_pre_topc @ X12 @ X13)
% 0.39/0.61          | ((X14) != (u1_struct_0 @ X12))
% 0.39/0.61          | ~ (v3_tex_2 @ X14 @ X13)
% 0.39/0.61          | (v4_tex_2 @ X12 @ X13)
% 0.39/0.61          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.39/0.61          | ~ (l1_pre_topc @ X13)
% 0.39/0.61          | (v2_struct_0 @ X13))),
% 0.39/0.61      inference('cnf', [status(esa)], [t51_tex_2])).
% 0.39/0.61  thf('55', plain,
% 0.39/0.61      (![X12 : $i, X13 : $i]:
% 0.39/0.61         ((v2_struct_0 @ X13)
% 0.39/0.61          | ~ (l1_pre_topc @ X13)
% 0.39/0.61          | ~ (m1_subset_1 @ (u1_struct_0 @ X12) @ 
% 0.39/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.39/0.61          | (v4_tex_2 @ X12 @ X13)
% 0.39/0.61          | ~ (v3_tex_2 @ (u1_struct_0 @ X12) @ X13)
% 0.39/0.61          | ~ (m1_pre_topc @ X12 @ X13))),
% 0.39/0.61      inference('simplify', [status(thm)], ['54'])).
% 0.39/0.61  thf('56', plain,
% 0.39/0.61      ((~ (m1_pre_topc @ 
% 0.39/0.61           (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A) @ sk_A)
% 0.39/0.61        | ~ (v3_tex_2 @ 
% 0.39/0.61             (u1_struct_0 @ 
% 0.39/0.61              (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A)) @ 
% 0.39/0.61             sk_A)
% 0.39/0.61        | (v4_tex_2 @ (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A) @ 
% 0.39/0.61           sk_A)
% 0.39/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.39/0.61        | (v2_struct_0 @ sk_A))),
% 0.39/0.61      inference('sup-', [status(thm)], ['53', '55'])).
% 0.39/0.61  thf('57', plain,
% 0.39/0.61      ((m1_pre_topc @ (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A) @ 
% 0.39/0.61        sk_A)),
% 0.39/0.61      inference('clc', [status(thm)], ['30', '48'])).
% 0.39/0.61  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('59', plain,
% 0.39/0.61      ((~ (v3_tex_2 @ 
% 0.39/0.61           (u1_struct_0 @ 
% 0.39/0.61            (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A)) @ 
% 0.39/0.61           sk_A)
% 0.39/0.61        | (v4_tex_2 @ (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A) @ 
% 0.39/0.61           sk_A)
% 0.39/0.61        | (v2_struct_0 @ sk_A))),
% 0.39/0.61      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.39/0.61  thf('60', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('61', plain,
% 0.39/0.61      (((v4_tex_2 @ (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A) @ 
% 0.39/0.61         sk_A)
% 0.39/0.61        | ~ (v3_tex_2 @ 
% 0.39/0.61             (u1_struct_0 @ 
% 0.39/0.61              (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A)) @ 
% 0.39/0.61             sk_A))),
% 0.39/0.61      inference('clc', [status(thm)], ['59', '60'])).
% 0.39/0.61  thf('62', plain,
% 0.39/0.61      ((m1_subset_1 @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ 
% 0.39/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.61      inference('clc', [status(thm)], ['22', '23'])).
% 0.39/0.61  thf('63', plain,
% 0.39/0.61      (![X5 : $i, X6 : $i]:
% 0.39/0.61         ((v1_xboole_0 @ X5)
% 0.39/0.61          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.39/0.61          | ((X5) = (u1_struct_0 @ (sk_C @ X5 @ X6)))
% 0.39/0.61          | ~ (l1_pre_topc @ X6)
% 0.39/0.61          | (v2_struct_0 @ X6))),
% 0.39/0.61      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.39/0.61  thf('64', plain,
% 0.39/0.61      (((v2_struct_0 @ sk_A)
% 0.39/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.39/0.61        | ((sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.39/0.61            = (u1_struct_0 @ 
% 0.39/0.61               (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A)))
% 0.39/0.61        | (v1_xboole_0 @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['62', '63'])).
% 0.39/0.61  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('66', plain,
% 0.39/0.61      (((v2_struct_0 @ sk_A)
% 0.39/0.61        | ((sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.39/0.61            = (u1_struct_0 @ 
% 0.39/0.61               (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A)))
% 0.39/0.61        | (v1_xboole_0 @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A)))),
% 0.39/0.61      inference('demod', [status(thm)], ['64', '65'])).
% 0.39/0.61  thf('67', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('68', plain,
% 0.39/0.61      (((v1_xboole_0 @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.39/0.61        | ((sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.39/0.61            = (u1_struct_0 @ 
% 0.39/0.61               (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))))),
% 0.39/0.61      inference('clc', [status(thm)], ['66', '67'])).
% 0.39/0.61  thf('69', plain, (~ (v1_xboole_0 @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.39/0.61      inference('clc', [status(thm)], ['46', '47'])).
% 0.39/0.61  thf('70', plain,
% 0.39/0.61      (((sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.39/0.61         = (u1_struct_0 @ 
% 0.39/0.61            (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A)))),
% 0.39/0.61      inference('clc', [status(thm)], ['68', '69'])).
% 0.39/0.61  thf('71', plain,
% 0.39/0.61      ((v3_tex_2 @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A)),
% 0.39/0.61      inference('clc', [status(thm)], ['43', '44'])).
% 0.39/0.61  thf('72', plain,
% 0.39/0.61      ((v4_tex_2 @ (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A) @ 
% 0.39/0.61        sk_A)),
% 0.39/0.61      inference('demod', [status(thm)], ['61', '70', '71'])).
% 0.39/0.61  thf('73', plain,
% 0.39/0.61      (![X17 : $i]:
% 0.39/0.61         (~ (v4_tex_2 @ X17 @ sk_A)
% 0.39/0.61          | ~ (m1_pre_topc @ sk_B @ X17)
% 0.39/0.61          | ~ (m1_pre_topc @ X17 @ sk_A)
% 0.39/0.61          | ~ (v1_pre_topc @ X17)
% 0.39/0.61          | (v2_struct_0 @ X17))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('74', plain,
% 0.39/0.61      (((v2_struct_0 @ (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))
% 0.39/0.61        | ~ (v1_pre_topc @ 
% 0.39/0.61             (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))
% 0.39/0.61        | ~ (m1_pre_topc @ 
% 0.39/0.61             (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A) @ sk_A)
% 0.39/0.61        | ~ (m1_pre_topc @ sk_B @ 
% 0.39/0.61             (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['72', '73'])).
% 0.39/0.61  thf('75', plain,
% 0.39/0.61      ((m1_subset_1 @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ 
% 0.39/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.61      inference('clc', [status(thm)], ['22', '23'])).
% 0.39/0.61  thf('76', plain,
% 0.39/0.61      (![X5 : $i, X6 : $i]:
% 0.39/0.61         ((v1_xboole_0 @ X5)
% 0.39/0.61          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.39/0.61          | (v1_pre_topc @ (sk_C @ X5 @ X6))
% 0.39/0.61          | ~ (l1_pre_topc @ X6)
% 0.39/0.61          | (v2_struct_0 @ X6))),
% 0.39/0.61      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.39/0.61  thf('77', plain,
% 0.39/0.61      (((v2_struct_0 @ sk_A)
% 0.39/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.39/0.61        | (v1_pre_topc @ (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))
% 0.39/0.61        | (v1_xboole_0 @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['75', '76'])).
% 0.39/0.61  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('79', plain,
% 0.39/0.61      (((v2_struct_0 @ sk_A)
% 0.39/0.61        | (v1_pre_topc @ (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))
% 0.39/0.61        | (v1_xboole_0 @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A)))),
% 0.39/0.61      inference('demod', [status(thm)], ['77', '78'])).
% 0.39/0.61  thf('80', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('81', plain,
% 0.39/0.61      (((v1_xboole_0 @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.39/0.61        | (v1_pre_topc @ (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A)))),
% 0.39/0.61      inference('clc', [status(thm)], ['79', '80'])).
% 0.39/0.61  thf('82', plain, (~ (v1_xboole_0 @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.39/0.61      inference('clc', [status(thm)], ['46', '47'])).
% 0.39/0.61  thf('83', plain,
% 0.39/0.61      ((v1_pre_topc @ (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))),
% 0.39/0.61      inference('clc', [status(thm)], ['81', '82'])).
% 0.39/0.61  thf('84', plain,
% 0.39/0.61      ((m1_pre_topc @ (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A) @ 
% 0.39/0.61        sk_A)),
% 0.39/0.61      inference('clc', [status(thm)], ['30', '48'])).
% 0.39/0.61  thf('85', plain,
% 0.39/0.61      (((v2_struct_0 @ (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))
% 0.39/0.61        | ~ (m1_pre_topc @ sk_B @ 
% 0.39/0.61             (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A)))),
% 0.39/0.61      inference('demod', [status(thm)], ['74', '83', '84'])).
% 0.39/0.61  thf('86', plain,
% 0.39/0.61      ((m1_subset_1 @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ 
% 0.39/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.61      inference('clc', [status(thm)], ['22', '23'])).
% 0.39/0.61  thf('87', plain,
% 0.39/0.61      (![X5 : $i, X6 : $i]:
% 0.39/0.61         ((v1_xboole_0 @ X5)
% 0.39/0.61          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.39/0.61          | ~ (v2_struct_0 @ (sk_C @ X5 @ X6))
% 0.39/0.61          | ~ (l1_pre_topc @ X6)
% 0.39/0.61          | (v2_struct_0 @ X6))),
% 0.39/0.61      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.39/0.61  thf('88', plain,
% 0.39/0.61      (((v2_struct_0 @ sk_A)
% 0.39/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.39/0.61        | ~ (v2_struct_0 @ 
% 0.39/0.61             (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))
% 0.39/0.61        | (v1_xboole_0 @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['86', '87'])).
% 0.39/0.61  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('90', plain,
% 0.39/0.61      (((v2_struct_0 @ sk_A)
% 0.39/0.61        | ~ (v2_struct_0 @ 
% 0.39/0.61             (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))
% 0.39/0.61        | (v1_xboole_0 @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A)))),
% 0.39/0.61      inference('demod', [status(thm)], ['88', '89'])).
% 0.39/0.61  thf('91', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('92', plain,
% 0.39/0.61      (((v1_xboole_0 @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.39/0.61        | ~ (v2_struct_0 @ 
% 0.39/0.61             (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A)))),
% 0.39/0.61      inference('clc', [status(thm)], ['90', '91'])).
% 0.39/0.61  thf('93', plain, (~ (v1_xboole_0 @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.39/0.61      inference('clc', [status(thm)], ['46', '47'])).
% 0.39/0.61  thf('94', plain,
% 0.39/0.61      (~ (v2_struct_0 @ (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))),
% 0.39/0.61      inference('clc', [status(thm)], ['92', '93'])).
% 0.39/0.61  thf('95', plain,
% 0.39/0.61      (~ (m1_pre_topc @ sk_B @ 
% 0.39/0.61          (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))),
% 0.39/0.61      inference('clc', [status(thm)], ['85', '94'])).
% 0.39/0.61  thf('96', plain,
% 0.39/0.61      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.61      inference('demod', [status(thm)], ['2', '3'])).
% 0.39/0.61  thf('97', plain,
% 0.39/0.61      (![X15 : $i, X16 : $i]:
% 0.39/0.61         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.39/0.61          | ~ (v2_tex_2 @ X15 @ X16)
% 0.39/0.61          | (r1_tarski @ X15 @ (sk_C_1 @ X15 @ X16))
% 0.39/0.61          | ~ (l1_pre_topc @ X16)
% 0.39/0.61          | ~ (v3_tdlat_3 @ X16)
% 0.39/0.61          | ~ (v2_pre_topc @ X16)
% 0.39/0.61          | (v2_struct_0 @ X16))),
% 0.39/0.61      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.39/0.61  thf('98', plain,
% 0.39/0.61      (((v2_struct_0 @ sk_A)
% 0.39/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.39/0.61        | ~ (v3_tdlat_3 @ sk_A)
% 0.39/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.39/0.61        | (r1_tarski @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.61           (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.39/0.61        | ~ (v2_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.39/0.61      inference('sup-', [status(thm)], ['96', '97'])).
% 0.39/0.61  thf('99', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('100', plain, ((v3_tdlat_3 @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('102', plain, ((v2_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A)),
% 0.39/0.61      inference('clc', [status(thm)], ['19', '20'])).
% 0.39/0.61  thf('103', plain,
% 0.39/0.61      (((v2_struct_0 @ sk_A)
% 0.39/0.61        | (r1_tarski @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.61           (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A)))),
% 0.39/0.61      inference('demod', [status(thm)], ['98', '99', '100', '101', '102'])).
% 0.39/0.61  thf('104', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('105', plain,
% 0.39/0.61      ((r1_tarski @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.61        (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.39/0.61      inference('clc', [status(thm)], ['103', '104'])).
% 0.39/0.61  thf('106', plain,
% 0.39/0.61      ((m1_pre_topc @ (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A) @ 
% 0.39/0.61        sk_A)),
% 0.39/0.61      inference('clc', [status(thm)], ['30', '48'])).
% 0.39/0.61  thf('107', plain,
% 0.39/0.61      (((sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.39/0.61         = (u1_struct_0 @ 
% 0.39/0.61            (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A)))),
% 0.39/0.61      inference('clc', [status(thm)], ['68', '69'])).
% 0.39/0.61  thf(t4_tsep_1, axiom,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.61       ( ![B:$i]:
% 0.39/0.61         ( ( m1_pre_topc @ B @ A ) =>
% 0.39/0.61           ( ![C:$i]:
% 0.39/0.61             ( ( m1_pre_topc @ C @ A ) =>
% 0.39/0.61               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.39/0.61                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.39/0.61  thf('108', plain,
% 0.39/0.61      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.39/0.61         (~ (m1_pre_topc @ X2 @ X3)
% 0.39/0.61          | ~ (r1_tarski @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X4))
% 0.39/0.61          | (m1_pre_topc @ X2 @ X4)
% 0.39/0.61          | ~ (m1_pre_topc @ X4 @ X3)
% 0.39/0.61          | ~ (l1_pre_topc @ X3)
% 0.39/0.61          | ~ (v2_pre_topc @ X3))),
% 0.39/0.61      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.39/0.61  thf('109', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (~ (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.39/0.61             (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.39/0.61          | ~ (v2_pre_topc @ X1)
% 0.39/0.61          | ~ (l1_pre_topc @ X1)
% 0.39/0.61          | ~ (m1_pre_topc @ 
% 0.39/0.61               (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A) @ X1)
% 0.39/0.61          | (m1_pre_topc @ X0 @ 
% 0.39/0.61             (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))
% 0.39/0.61          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.39/0.61      inference('sup-', [status(thm)], ['107', '108'])).
% 0.39/0.61  thf('110', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.39/0.61          | (m1_pre_topc @ X0 @ 
% 0.39/0.61             (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))
% 0.39/0.61          | ~ (l1_pre_topc @ sk_A)
% 0.39/0.61          | ~ (v2_pre_topc @ sk_A)
% 0.39/0.61          | ~ (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.39/0.61               (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['106', '109'])).
% 0.39/0.61  thf('111', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('112', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('113', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.39/0.61          | (m1_pre_topc @ X0 @ 
% 0.39/0.61             (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))
% 0.39/0.61          | ~ (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.39/0.61               (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A)))),
% 0.39/0.61      inference('demod', [status(thm)], ['110', '111', '112'])).
% 0.39/0.61  thf('114', plain,
% 0.39/0.61      (((m1_pre_topc @ sk_B @ 
% 0.39/0.61         (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))
% 0.39/0.61        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.39/0.61      inference('sup-', [status(thm)], ['105', '113'])).
% 0.39/0.61  thf('115', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('116', plain,
% 0.39/0.61      ((m1_pre_topc @ sk_B @ 
% 0.39/0.61        (sk_C @ (sk_C_1 @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))),
% 0.39/0.61      inference('demod', [status(thm)], ['114', '115'])).
% 0.39/0.61  thf('117', plain, ($false), inference('demod', [status(thm)], ['95', '116'])).
% 0.39/0.61  
% 0.39/0.61  % SZS output end Refutation
% 0.39/0.61  
% 0.39/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
