%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rg6ieWt0Zr

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:58 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  188 ( 413 expanded)
%              Number of leaves         :   40 ( 129 expanded)
%              Depth                    :   22
%              Number of atoms          : 1419 (5151 expanded)
%              Number of equality atoms :   22 (  46 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

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
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t34_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( ( v2_tex_2 @ B @ A )
              & ! [C: $i] :
                  ( ( ~ ( v2_struct_0 @ C )
                    & ( v1_pre_topc @ C )
                    & ( v1_tdlat_3 @ C )
                    & ( m1_pre_topc @ C @ A ) )
                 => ( B
                   != ( u1_struct_0 @ C ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v2_tex_2 @ X27 @ X28 )
      | ( X27
        = ( u1_struct_0 @ ( sk_C_1 @ X27 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( sk_B_1
        = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( sk_B_1
        = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['12','13'])).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('15',plain,(
    ! [X14: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 )
      | ~ ( v7_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('16',plain,
    ( ( ( v1_zfmisc_1 @ sk_B_1 )
      | ~ ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( l1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('18',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v2_tex_2 @ X27 @ X28 )
      | ( m1_pre_topc @ ( sk_C_1 @ X27 @ X28 ) @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('20',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['26','27'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('29',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( l1_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('30',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( l1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( l1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('33',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('34',plain,
    ( ( l1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( v1_zfmisc_1 @ sk_B_1 )
      | ~ ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['16','34'])).

thf('36',plain,
    ( ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['26','27'])).

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

thf('37',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ~ ( v1_tdlat_3 @ X21 )
      | ( v7_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_tdlat_3 @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc32_tex_2])).

thf('38',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v2_tdlat_3 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('43',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v2_tex_2 @ X27 @ X28 )
      | ( v1_tdlat_3 @ ( sk_C_1 @ X27 @ X28 ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['38','39','40','41','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v2_tex_2 @ X27 @ X28 )
      | ~ ( v2_struct_0 @ ( sk_C_1 @ X27 @ X28 ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf('64',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('65',plain,
    ( ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['35','69'])).

thf('71',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
   <= ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('72',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('74',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['2'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('75',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('76',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X4 ) @ X6 )
      | ~ ( r2_hidden @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('78',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ~ ( v1_zfmisc_1 @ X25 )
      | ( X26 = X25 )
      | ~ ( r1_tarski @ X26 @ X25 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('81',plain,(
    ! [X3: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('84',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( m1_pre_topc @ ( sk_C @ X23 @ X24 ) @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('93',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ X9 @ X10 )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf(t55_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('95',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_pre_topc])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_B @ ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['91','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( X23
        = ( u1_struct_0 @ ( sk_C @ X23 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( sk_B_1
    = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( sk_B_1
    = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('109',plain,
    ( ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['97','106','107','108'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('110',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ X18 )
      | ( ( k6_domain_1 @ X18 @ X19 )
        = ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('111',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['97','106','107','108'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('113',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X30 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X30 ) @ X29 ) @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('114',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,
    ( ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,
    ( ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['111','118'])).

thf('120',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['82','120'])).

thf('122',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,
    ( ( ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['74','122'])).

thf('124',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v2_struct_0 @ ( sk_C @ X23 @ X24 ) )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('126',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['128','129'])).

thf('131',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['130','131'])).

thf('133',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['123','132'])).

thf('134',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('135',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_xboole_0 @ X7 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('136',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['136','137'])).

thf('139',plain,
    ( ( ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['133','138'])).

thf('140',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['139','140'])).

thf('142',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['141','142'])).

thf('144',plain,
    ( ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('145',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','72','73','145'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rg6ieWt0Zr
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:29:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.52  % Solved by: fo/fo7.sh
% 0.19/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.52  % done 175 iterations in 0.074s
% 0.19/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.52  % SZS output start Refutation
% 0.19/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.52  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.19/0.52  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.19/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.52  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.19/0.52  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.19/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.52  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.19/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.52  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.19/0.52  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.19/0.52  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.19/0.52  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.19/0.52  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.19/0.52  thf(t44_tex_2, conjecture,
% 0.19/0.52    (![A:$i]:
% 0.19/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.19/0.52         ( l1_pre_topc @ A ) ) =>
% 0.19/0.52       ( ![B:$i]:
% 0.19/0.52         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.19/0.52             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.52           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.19/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.52    (~( ![A:$i]:
% 0.19/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.52            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.52          ( ![B:$i]:
% 0.19/0.52            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.19/0.52                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.52              ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.19/0.52    inference('cnf.neg', [status(esa)], [t44_tex_2])).
% 0.19/0.52  thf('0', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('1', plain,
% 0.19/0.52      (~ ((v1_zfmisc_1 @ sk_B_1)) | ~ ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.19/0.52      inference('split', [status(esa)], ['0'])).
% 0.19/0.52  thf('2', plain, (((v1_zfmisc_1 @ sk_B_1) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('3', plain,
% 0.19/0.52      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.19/0.52      inference('split', [status(esa)], ['2'])).
% 0.19/0.52  thf('4', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(t34_tex_2, axiom,
% 0.19/0.52    (![A:$i]:
% 0.19/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.52       ( ![B:$i]:
% 0.19/0.52         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.19/0.52             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.52           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.19/0.52                ( ![C:$i]:
% 0.19/0.52                  ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.19/0.52                      ( v1_tdlat_3 @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.19/0.52                    ( ( B ) != ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ))).
% 0.19/0.52  thf('5', plain,
% 0.19/0.52      (![X27 : $i, X28 : $i]:
% 0.19/0.52         ((v1_xboole_0 @ X27)
% 0.19/0.52          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.19/0.52          | ~ (v2_tex_2 @ X27 @ X28)
% 0.19/0.52          | ((X27) = (u1_struct_0 @ (sk_C_1 @ X27 @ X28)))
% 0.19/0.52          | ~ (l1_pre_topc @ X28)
% 0.19/0.52          | ~ (v2_pre_topc @ X28)
% 0.19/0.52          | (v2_struct_0 @ X28))),
% 0.19/0.52      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.19/0.52  thf('6', plain,
% 0.19/0.52      (((v2_struct_0 @ sk_A)
% 0.19/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.19/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.52        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.19/0.52        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.19/0.52        | (v1_xboole_0 @ sk_B_1))),
% 0.19/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.52  thf('7', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('9', plain,
% 0.19/0.52      (((v2_struct_0 @ sk_A)
% 0.19/0.52        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.19/0.52        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.19/0.52        | (v1_xboole_0 @ sk_B_1))),
% 0.19/0.52      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.19/0.52  thf('10', plain,
% 0.19/0.52      ((((v1_xboole_0 @ sk_B_1)
% 0.19/0.52         | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.19/0.52         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['3', '9'])).
% 0.19/0.52  thf('11', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('12', plain,
% 0.19/0.52      ((((v2_struct_0 @ sk_A)
% 0.19/0.52         | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))))
% 0.19/0.52         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.19/0.52      inference('clc', [status(thm)], ['10', '11'])).
% 0.19/0.52  thf('13', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('14', plain,
% 0.19/0.52      ((((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.19/0.52         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.19/0.52      inference('clc', [status(thm)], ['12', '13'])).
% 0.19/0.52  thf(fc7_struct_0, axiom,
% 0.19/0.52    (![A:$i]:
% 0.19/0.52     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.52       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.19/0.52  thf('15', plain,
% 0.19/0.52      (![X14 : $i]:
% 0.19/0.52         ((v1_zfmisc_1 @ (u1_struct_0 @ X14))
% 0.19/0.52          | ~ (l1_struct_0 @ X14)
% 0.19/0.52          | ~ (v7_struct_0 @ X14))),
% 0.19/0.52      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.19/0.52  thf('16', plain,
% 0.19/0.52      ((((v1_zfmisc_1 @ sk_B_1)
% 0.19/0.52         | ~ (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.19/0.52         | ~ (l1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.19/0.52         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.19/0.52      inference('sup+', [status(thm)], ['14', '15'])).
% 0.19/0.52  thf('17', plain,
% 0.19/0.52      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.19/0.52      inference('split', [status(esa)], ['2'])).
% 0.19/0.52  thf('18', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('19', plain,
% 0.19/0.52      (![X27 : $i, X28 : $i]:
% 0.19/0.52         ((v1_xboole_0 @ X27)
% 0.19/0.52          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.19/0.52          | ~ (v2_tex_2 @ X27 @ X28)
% 0.19/0.52          | (m1_pre_topc @ (sk_C_1 @ X27 @ X28) @ X28)
% 0.19/0.52          | ~ (l1_pre_topc @ X28)
% 0.19/0.52          | ~ (v2_pre_topc @ X28)
% 0.19/0.52          | (v2_struct_0 @ X28))),
% 0.19/0.52      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.19/0.52  thf('20', plain,
% 0.19/0.52      (((v2_struct_0 @ sk_A)
% 0.19/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.19/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.52        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.19/0.52        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.19/0.52        | (v1_xboole_0 @ sk_B_1))),
% 0.19/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.52  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('23', plain,
% 0.19/0.52      (((v2_struct_0 @ sk_A)
% 0.19/0.52        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.19/0.52        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.19/0.52        | (v1_xboole_0 @ sk_B_1))),
% 0.19/0.52      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.19/0.52  thf('24', plain,
% 0.19/0.52      ((((v1_xboole_0 @ sk_B_1)
% 0.19/0.52         | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.19/0.52         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['17', '23'])).
% 0.19/0.52  thf('25', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('26', plain,
% 0.19/0.52      ((((v2_struct_0 @ sk_A) | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)))
% 0.19/0.52         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.19/0.52      inference('clc', [status(thm)], ['24', '25'])).
% 0.19/0.52  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('28', plain,
% 0.19/0.52      (((m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A))
% 0.19/0.52         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.19/0.52      inference('clc', [status(thm)], ['26', '27'])).
% 0.19/0.52  thf(dt_m1_pre_topc, axiom,
% 0.19/0.52    (![A:$i]:
% 0.19/0.52     ( ( l1_pre_topc @ A ) =>
% 0.19/0.52       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.19/0.52  thf('29', plain,
% 0.19/0.52      (![X12 : $i, X13 : $i]:
% 0.19/0.52         (~ (m1_pre_topc @ X12 @ X13)
% 0.19/0.52          | (l1_pre_topc @ X12)
% 0.19/0.52          | ~ (l1_pre_topc @ X13))),
% 0.19/0.52      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.19/0.52  thf('30', plain,
% 0.19/0.52      (((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.19/0.52         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.19/0.52  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('32', plain,
% 0.19/0.52      (((l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.19/0.52         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.19/0.52      inference('demod', [status(thm)], ['30', '31'])).
% 0.19/0.52  thf(dt_l1_pre_topc, axiom,
% 0.19/0.52    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.19/0.52  thf('33', plain,
% 0.19/0.52      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.19/0.52      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.52  thf('34', plain,
% 0.19/0.52      (((l1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.19/0.52         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.19/0.52  thf('35', plain,
% 0.19/0.52      ((((v1_zfmisc_1 @ sk_B_1) | ~ (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.19/0.52         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.19/0.52      inference('demod', [status(thm)], ['16', '34'])).
% 0.19/0.52  thf('36', plain,
% 0.19/0.52      (((m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A))
% 0.19/0.52         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.19/0.52      inference('clc', [status(thm)], ['26', '27'])).
% 0.19/0.52  thf(cc32_tex_2, axiom,
% 0.19/0.52    (![A:$i]:
% 0.19/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.19/0.52         ( l1_pre_topc @ A ) ) =>
% 0.19/0.52       ( ![B:$i]:
% 0.19/0.52         ( ( m1_pre_topc @ B @ A ) =>
% 0.19/0.52           ( ( ( ~( v2_struct_0 @ B ) ) & ( ~( v7_struct_0 @ B ) ) ) =>
% 0.19/0.52             ( ( ~( v2_struct_0 @ B ) ) & ( ~( v1_tdlat_3 @ B ) ) ) ) ) ) ))).
% 0.19/0.52  thf('37', plain,
% 0.19/0.52      (![X21 : $i, X22 : $i]:
% 0.19/0.52         (~ (m1_pre_topc @ X21 @ X22)
% 0.19/0.52          | ~ (v1_tdlat_3 @ X21)
% 0.19/0.52          | (v7_struct_0 @ X21)
% 0.19/0.52          | (v2_struct_0 @ X21)
% 0.19/0.52          | ~ (l1_pre_topc @ X22)
% 0.19/0.52          | ~ (v2_tdlat_3 @ X22)
% 0.19/0.52          | ~ (v2_pre_topc @ X22)
% 0.19/0.52          | (v2_struct_0 @ X22))),
% 0.19/0.52      inference('cnf', [status(esa)], [cc32_tex_2])).
% 0.19/0.52  thf('38', plain,
% 0.19/0.52      ((((v2_struct_0 @ sk_A)
% 0.19/0.52         | ~ (v2_pre_topc @ sk_A)
% 0.19/0.52         | ~ (v2_tdlat_3 @ sk_A)
% 0.19/0.52         | ~ (l1_pre_topc @ sk_A)
% 0.19/0.52         | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.19/0.52         | (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.19/0.52         | ~ (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.19/0.52         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['36', '37'])).
% 0.19/0.52  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('40', plain, ((v2_tdlat_3 @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('42', plain,
% 0.19/0.52      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.19/0.52      inference('split', [status(esa)], ['2'])).
% 0.19/0.52  thf('43', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('44', plain,
% 0.19/0.52      (![X27 : $i, X28 : $i]:
% 0.19/0.52         ((v1_xboole_0 @ X27)
% 0.19/0.52          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.19/0.52          | ~ (v2_tex_2 @ X27 @ X28)
% 0.19/0.52          | (v1_tdlat_3 @ (sk_C_1 @ X27 @ X28))
% 0.19/0.52          | ~ (l1_pre_topc @ X28)
% 0.19/0.52          | ~ (v2_pre_topc @ X28)
% 0.19/0.52          | (v2_struct_0 @ X28))),
% 0.19/0.52      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.19/0.52  thf('45', plain,
% 0.19/0.52      (((v2_struct_0 @ sk_A)
% 0.19/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.19/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.52        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.19/0.52        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.19/0.52        | (v1_xboole_0 @ sk_B_1))),
% 0.19/0.52      inference('sup-', [status(thm)], ['43', '44'])).
% 0.19/0.52  thf('46', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('48', plain,
% 0.19/0.52      (((v2_struct_0 @ sk_A)
% 0.19/0.52        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.19/0.52        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.19/0.52        | (v1_xboole_0 @ sk_B_1))),
% 0.19/0.52      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.19/0.52  thf('49', plain,
% 0.19/0.52      ((((v1_xboole_0 @ sk_B_1)
% 0.19/0.52         | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.19/0.52         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['42', '48'])).
% 0.19/0.52  thf('50', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('51', plain,
% 0.19/0.52      ((((v2_struct_0 @ sk_A) | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.19/0.52         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.19/0.52      inference('clc', [status(thm)], ['49', '50'])).
% 0.19/0.52  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('53', plain,
% 0.19/0.52      (((v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.19/0.52         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.19/0.52      inference('clc', [status(thm)], ['51', '52'])).
% 0.19/0.52  thf('54', plain,
% 0.19/0.52      ((((v2_struct_0 @ sk_A)
% 0.19/0.52         | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.19/0.52         | (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.19/0.52         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.19/0.52      inference('demod', [status(thm)], ['38', '39', '40', '41', '53'])).
% 0.19/0.52  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('56', plain,
% 0.19/0.52      ((((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.19/0.52         | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.19/0.52         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.19/0.52      inference('clc', [status(thm)], ['54', '55'])).
% 0.19/0.52  thf('57', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('58', plain,
% 0.19/0.52      (![X27 : $i, X28 : $i]:
% 0.19/0.52         ((v1_xboole_0 @ X27)
% 0.19/0.52          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.19/0.52          | ~ (v2_tex_2 @ X27 @ X28)
% 0.19/0.52          | ~ (v2_struct_0 @ (sk_C_1 @ X27 @ X28))
% 0.19/0.52          | ~ (l1_pre_topc @ X28)
% 0.19/0.52          | ~ (v2_pre_topc @ X28)
% 0.19/0.52          | (v2_struct_0 @ X28))),
% 0.19/0.52      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.19/0.52  thf('59', plain,
% 0.19/0.52      (((v2_struct_0 @ sk_A)
% 0.19/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.19/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.52        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.19/0.52        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.19/0.52        | (v1_xboole_0 @ sk_B_1))),
% 0.19/0.52      inference('sup-', [status(thm)], ['57', '58'])).
% 0.19/0.52  thf('60', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('62', plain,
% 0.19/0.52      (((v2_struct_0 @ sk_A)
% 0.19/0.52        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.19/0.52        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.19/0.52        | (v1_xboole_0 @ sk_B_1))),
% 0.19/0.52      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.19/0.52  thf('63', plain,
% 0.19/0.52      ((((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.19/0.52         | (v1_xboole_0 @ sk_B_1)
% 0.19/0.52         | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.19/0.52         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['56', '62'])).
% 0.19/0.52  thf('64', plain,
% 0.19/0.52      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.19/0.52      inference('split', [status(esa)], ['2'])).
% 0.19/0.52  thf('65', plain,
% 0.19/0.52      ((((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.19/0.52         | (v1_xboole_0 @ sk_B_1)
% 0.19/0.52         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.19/0.52      inference('demod', [status(thm)], ['63', '64'])).
% 0.19/0.52  thf('66', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('67', plain,
% 0.19/0.52      ((((v2_struct_0 @ sk_A) | (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.19/0.52         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.19/0.52      inference('clc', [status(thm)], ['65', '66'])).
% 0.19/0.52  thf('68', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('69', plain,
% 0.19/0.52      (((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.19/0.52         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.19/0.52      inference('clc', [status(thm)], ['67', '68'])).
% 0.19/0.52  thf('70', plain,
% 0.19/0.52      (((v1_zfmisc_1 @ sk_B_1)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.19/0.52      inference('demod', [status(thm)], ['35', '69'])).
% 0.19/0.52  thf('71', plain,
% 0.19/0.52      ((~ (v1_zfmisc_1 @ sk_B_1)) <= (~ ((v1_zfmisc_1 @ sk_B_1)))),
% 0.19/0.52      inference('split', [status(esa)], ['0'])).
% 0.19/0.52  thf('72', plain, (((v1_zfmisc_1 @ sk_B_1)) | ~ ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.19/0.52      inference('sup-', [status(thm)], ['70', '71'])).
% 0.19/0.52  thf('73', plain, (((v1_zfmisc_1 @ sk_B_1)) | ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.19/0.52      inference('split', [status(esa)], ['2'])).
% 0.19/0.52  thf('74', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.19/0.52      inference('split', [status(esa)], ['2'])).
% 0.19/0.52  thf(d1_xboole_0, axiom,
% 0.19/0.52    (![A:$i]:
% 0.19/0.52     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.19/0.52  thf('75', plain,
% 0.19/0.52      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.19/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.52  thf(l1_zfmisc_1, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.19/0.52  thf('76', plain,
% 0.19/0.52      (![X4 : $i, X6 : $i]:
% 0.19/0.52         ((r1_tarski @ (k1_tarski @ X4) @ X6) | ~ (r2_hidden @ X4 @ X6))),
% 0.19/0.52      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.19/0.52  thf('77', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.19/0.52      inference('sup-', [status(thm)], ['75', '76'])).
% 0.19/0.52  thf(t1_tex_2, axiom,
% 0.19/0.52    (![A:$i]:
% 0.19/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.52       ( ![B:$i]:
% 0.19/0.52         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.19/0.52           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.19/0.52  thf('78', plain,
% 0.19/0.52      (![X25 : $i, X26 : $i]:
% 0.19/0.52         ((v1_xboole_0 @ X25)
% 0.19/0.52          | ~ (v1_zfmisc_1 @ X25)
% 0.19/0.52          | ((X26) = (X25))
% 0.19/0.52          | ~ (r1_tarski @ X26 @ X25)
% 0.19/0.52          | (v1_xboole_0 @ X26))),
% 0.19/0.52      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.19/0.52  thf('79', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         ((v1_xboole_0 @ X0)
% 0.19/0.52          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.19/0.52          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.19/0.52          | ~ (v1_zfmisc_1 @ X0)
% 0.19/0.52          | (v1_xboole_0 @ X0))),
% 0.19/0.52      inference('sup-', [status(thm)], ['77', '78'])).
% 0.19/0.52  thf('80', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         (~ (v1_zfmisc_1 @ X0)
% 0.19/0.52          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.19/0.52          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.19/0.52          | (v1_xboole_0 @ X0))),
% 0.19/0.52      inference('simplify', [status(thm)], ['79'])).
% 0.19/0.52  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.19/0.52  thf('81', plain, (![X3 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X3))),
% 0.19/0.52      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.19/0.52  thf('82', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         ((v1_xboole_0 @ X0)
% 0.19/0.52          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.19/0.52          | ~ (v1_zfmisc_1 @ X0))),
% 0.19/0.52      inference('sup-', [status(thm)], ['80', '81'])).
% 0.19/0.52  thf('83', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(t10_tsep_1, axiom,
% 0.19/0.52    (![A:$i]:
% 0.19/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.52       ( ![B:$i]:
% 0.19/0.52         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.19/0.52             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.52           ( ?[C:$i]:
% 0.19/0.52             ( ( ( B ) = ( u1_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) & 
% 0.19/0.52               ( v1_pre_topc @ C ) & ( ~( v2_struct_0 @ C ) ) ) ) ) ) ))).
% 0.19/0.52  thf('84', plain,
% 0.19/0.52      (![X23 : $i, X24 : $i]:
% 0.19/0.52         ((v1_xboole_0 @ X23)
% 0.19/0.52          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.19/0.52          | (m1_pre_topc @ (sk_C @ X23 @ X24) @ X24)
% 0.19/0.52          | ~ (l1_pre_topc @ X24)
% 0.19/0.52          | (v2_struct_0 @ X24))),
% 0.19/0.52      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.19/0.52  thf('85', plain,
% 0.19/0.52      (((v2_struct_0 @ sk_A)
% 0.19/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.52        | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.19/0.52        | (v1_xboole_0 @ sk_B_1))),
% 0.19/0.52      inference('sup-', [status(thm)], ['83', '84'])).
% 0.19/0.52  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('87', plain,
% 0.19/0.52      (((v2_struct_0 @ sk_A)
% 0.19/0.52        | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.19/0.52        | (v1_xboole_0 @ sk_B_1))),
% 0.19/0.52      inference('demod', [status(thm)], ['85', '86'])).
% 0.19/0.52  thf('88', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('89', plain,
% 0.19/0.52      (((v1_xboole_0 @ sk_B_1) | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A))),
% 0.19/0.52      inference('clc', [status(thm)], ['87', '88'])).
% 0.19/0.52  thf('90', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('91', plain, ((m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)),
% 0.19/0.52      inference('clc', [status(thm)], ['89', '90'])).
% 0.19/0.52  thf('92', plain,
% 0.19/0.52      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.19/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.52  thf(t1_subset, axiom,
% 0.19/0.52    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.19/0.52  thf('93', plain,
% 0.19/0.52      (![X9 : $i, X10 : $i]:
% 0.19/0.52         ((m1_subset_1 @ X9 @ X10) | ~ (r2_hidden @ X9 @ X10))),
% 0.19/0.52      inference('cnf', [status(esa)], [t1_subset])).
% 0.19/0.52  thf('94', plain,
% 0.19/0.52      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.19/0.52      inference('sup-', [status(thm)], ['92', '93'])).
% 0.19/0.52  thf(t55_pre_topc, axiom,
% 0.19/0.52    (![A:$i]:
% 0.19/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.52       ( ![B:$i]:
% 0.19/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.19/0.52           ( ![C:$i]:
% 0.19/0.52             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.19/0.52               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.19/0.52  thf('95', plain,
% 0.19/0.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.52         ((v2_struct_0 @ X15)
% 0.19/0.52          | ~ (m1_pre_topc @ X15 @ X16)
% 0.19/0.52          | (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.19/0.52          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X15))
% 0.19/0.52          | ~ (l1_pre_topc @ X16)
% 0.19/0.52          | (v2_struct_0 @ X16))),
% 0.19/0.52      inference('cnf', [status(esa)], [t55_pre_topc])).
% 0.19/0.52  thf('96', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.19/0.52          | (v2_struct_0 @ X1)
% 0.19/0.52          | ~ (l1_pre_topc @ X1)
% 0.19/0.52          | (m1_subset_1 @ (sk_B @ (u1_struct_0 @ X0)) @ (u1_struct_0 @ X1))
% 0.19/0.52          | ~ (m1_pre_topc @ X0 @ X1)
% 0.19/0.52          | (v2_struct_0 @ X0))),
% 0.19/0.52      inference('sup-', [status(thm)], ['94', '95'])).
% 0.19/0.52  thf('97', plain,
% 0.19/0.52      (((v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.19/0.52        | (m1_subset_1 @ (sk_B @ (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.19/0.52           (u1_struct_0 @ sk_A))
% 0.19/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.52        | (v2_struct_0 @ sk_A)
% 0.19/0.52        | (v1_xboole_0 @ (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))))),
% 0.19/0.52      inference('sup-', [status(thm)], ['91', '96'])).
% 0.19/0.52  thf('98', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('99', plain,
% 0.19/0.52      (![X23 : $i, X24 : $i]:
% 0.19/0.52         ((v1_xboole_0 @ X23)
% 0.19/0.52          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.19/0.53          | ((X23) = (u1_struct_0 @ (sk_C @ X23 @ X24)))
% 0.19/0.53          | ~ (l1_pre_topc @ X24)
% 0.19/0.53          | (v2_struct_0 @ X24))),
% 0.19/0.53      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.19/0.53  thf('100', plain,
% 0.19/0.53      (((v2_struct_0 @ sk_A)
% 0.19/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.53        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.19/0.53        | (v1_xboole_0 @ sk_B_1))),
% 0.19/0.53      inference('sup-', [status(thm)], ['98', '99'])).
% 0.19/0.53  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('102', plain,
% 0.19/0.53      (((v2_struct_0 @ sk_A)
% 0.19/0.53        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.19/0.53        | (v1_xboole_0 @ sk_B_1))),
% 0.19/0.53      inference('demod', [status(thm)], ['100', '101'])).
% 0.19/0.53  thf('103', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('104', plain,
% 0.19/0.53      (((v1_xboole_0 @ sk_B_1)
% 0.19/0.53        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))))),
% 0.19/0.53      inference('clc', [status(thm)], ['102', '103'])).
% 0.19/0.53  thf('105', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('106', plain, (((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.19/0.53      inference('clc', [status(thm)], ['104', '105'])).
% 0.19/0.53  thf('107', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('108', plain, (((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.19/0.53      inference('clc', [status(thm)], ['104', '105'])).
% 0.19/0.53  thf('109', plain,
% 0.19/0.53      (((v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.19/0.53        | (m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.19/0.53        | (v2_struct_0 @ sk_A)
% 0.19/0.53        | (v1_xboole_0 @ sk_B_1))),
% 0.19/0.53      inference('demod', [status(thm)], ['97', '106', '107', '108'])).
% 0.19/0.53  thf(redefinition_k6_domain_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.19/0.53       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.19/0.53  thf('110', plain,
% 0.19/0.53      (![X18 : $i, X19 : $i]:
% 0.19/0.53         ((v1_xboole_0 @ X18)
% 0.19/0.53          | ~ (m1_subset_1 @ X19 @ X18)
% 0.19/0.53          | ((k6_domain_1 @ X18 @ X19) = (k1_tarski @ X19)))),
% 0.19/0.53      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.19/0.53  thf('111', plain,
% 0.19/0.53      (((v1_xboole_0 @ sk_B_1)
% 0.19/0.53        | (v2_struct_0 @ sk_A)
% 0.19/0.53        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.19/0.53        | ((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.19/0.53            = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.19/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['109', '110'])).
% 0.19/0.53  thf('112', plain,
% 0.19/0.53      (((v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.19/0.53        | (m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.19/0.53        | (v2_struct_0 @ sk_A)
% 0.19/0.53        | (v1_xboole_0 @ sk_B_1))),
% 0.19/0.53      inference('demod', [status(thm)], ['97', '106', '107', '108'])).
% 0.19/0.53  thf(t36_tex_2, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.53       ( ![B:$i]:
% 0.19/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.53           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.19/0.53  thf('113', plain,
% 0.19/0.53      (![X29 : $i, X30 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X30))
% 0.19/0.53          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X30) @ X29) @ X30)
% 0.19/0.53          | ~ (l1_pre_topc @ X30)
% 0.19/0.53          | ~ (v2_pre_topc @ X30)
% 0.19/0.53          | (v2_struct_0 @ X30))),
% 0.19/0.53      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.19/0.53  thf('114', plain,
% 0.19/0.53      (((v1_xboole_0 @ sk_B_1)
% 0.19/0.53        | (v2_struct_0 @ sk_A)
% 0.19/0.53        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.19/0.53        | (v2_struct_0 @ sk_A)
% 0.19/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.19/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.53        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.19/0.53           sk_A))),
% 0.19/0.53      inference('sup-', [status(thm)], ['112', '113'])).
% 0.19/0.53  thf('115', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('116', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('117', plain,
% 0.19/0.53      (((v1_xboole_0 @ sk_B_1)
% 0.19/0.53        | (v2_struct_0 @ sk_A)
% 0.19/0.53        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.19/0.53        | (v2_struct_0 @ sk_A)
% 0.19/0.53        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.19/0.53           sk_A))),
% 0.19/0.53      inference('demod', [status(thm)], ['114', '115', '116'])).
% 0.19/0.53  thf('118', plain,
% 0.19/0.53      (((v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.19/0.53         sk_A)
% 0.19/0.53        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.19/0.53        | (v2_struct_0 @ sk_A)
% 0.19/0.53        | (v1_xboole_0 @ sk_B_1))),
% 0.19/0.53      inference('simplify', [status(thm)], ['117'])).
% 0.19/0.53  thf('119', plain,
% 0.19/0.53      (((v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A)
% 0.19/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.53        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.19/0.53        | (v2_struct_0 @ sk_A)
% 0.19/0.53        | (v1_xboole_0 @ sk_B_1)
% 0.19/0.53        | (v1_xboole_0 @ sk_B_1)
% 0.19/0.53        | (v2_struct_0 @ sk_A)
% 0.19/0.53        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.19/0.53      inference('sup+', [status(thm)], ['111', '118'])).
% 0.19/0.53  thf('120', plain,
% 0.19/0.53      (((v1_xboole_0 @ sk_B_1)
% 0.19/0.53        | (v2_struct_0 @ sk_A)
% 0.19/0.53        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.19/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.53        | (v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A))),
% 0.19/0.53      inference('simplify', [status(thm)], ['119'])).
% 0.19/0.53  thf('121', plain,
% 0.19/0.53      (((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.19/0.53        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.19/0.53        | (v1_xboole_0 @ sk_B_1)
% 0.19/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.53        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.19/0.53        | (v2_struct_0 @ sk_A)
% 0.19/0.53        | (v1_xboole_0 @ sk_B_1))),
% 0.19/0.53      inference('sup+', [status(thm)], ['82', '120'])).
% 0.19/0.53  thf('122', plain,
% 0.19/0.53      (((v2_struct_0 @ sk_A)
% 0.19/0.53        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.19/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.53        | (v1_xboole_0 @ sk_B_1)
% 0.19/0.53        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.19/0.53        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.19/0.53      inference('simplify', [status(thm)], ['121'])).
% 0.19/0.53  thf('123', plain,
% 0.19/0.53      ((((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.19/0.53         | (v1_xboole_0 @ sk_B_1)
% 0.19/0.53         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.53         | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.19/0.53         | (v2_struct_0 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['74', '122'])).
% 0.19/0.53  thf('124', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('125', plain,
% 0.19/0.53      (![X23 : $i, X24 : $i]:
% 0.19/0.53         ((v1_xboole_0 @ X23)
% 0.19/0.53          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.19/0.53          | ~ (v2_struct_0 @ (sk_C @ X23 @ X24))
% 0.19/0.53          | ~ (l1_pre_topc @ X24)
% 0.19/0.53          | (v2_struct_0 @ X24))),
% 0.19/0.53      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.19/0.53  thf('126', plain,
% 0.19/0.53      (((v2_struct_0 @ sk_A)
% 0.19/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.53        | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.19/0.53        | (v1_xboole_0 @ sk_B_1))),
% 0.19/0.53      inference('sup-', [status(thm)], ['124', '125'])).
% 0.19/0.53  thf('127', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('128', plain,
% 0.19/0.53      (((v2_struct_0 @ sk_A)
% 0.19/0.53        | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.19/0.53        | (v1_xboole_0 @ sk_B_1))),
% 0.19/0.53      inference('demod', [status(thm)], ['126', '127'])).
% 0.19/0.53  thf('129', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('130', plain,
% 0.19/0.53      (((v1_xboole_0 @ sk_B_1) | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.19/0.53      inference('clc', [status(thm)], ['128', '129'])).
% 0.19/0.53  thf('131', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('132', plain, (~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.19/0.53      inference('clc', [status(thm)], ['130', '131'])).
% 0.19/0.53  thf('133', plain,
% 0.19/0.53      ((((v2_struct_0 @ sk_A)
% 0.19/0.53         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.53         | (v1_xboole_0 @ sk_B_1)
% 0.19/0.53         | (v2_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['123', '132'])).
% 0.19/0.53  thf('134', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(cc1_subset_1, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( v1_xboole_0 @ A ) =>
% 0.19/0.53       ( ![B:$i]:
% 0.19/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.19/0.53  thf('135', plain,
% 0.19/0.53      (![X7 : $i, X8 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.19/0.53          | (v1_xboole_0 @ X7)
% 0.19/0.53          | ~ (v1_xboole_0 @ X8))),
% 0.19/0.53      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.19/0.53  thf('136', plain,
% 0.19/0.53      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_B_1))),
% 0.19/0.53      inference('sup-', [status(thm)], ['134', '135'])).
% 0.19/0.53  thf('137', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('138', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.19/0.53      inference('clc', [status(thm)], ['136', '137'])).
% 0.19/0.53  thf('139', plain,
% 0.19/0.53      ((((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.19/0.53         | (v1_xboole_0 @ sk_B_1)
% 0.19/0.53         | (v2_struct_0 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['133', '138'])).
% 0.19/0.53  thf('140', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('141', plain,
% 0.19/0.53      ((((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B_1 @ sk_A)))
% 0.19/0.53         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.19/0.53      inference('clc', [status(thm)], ['139', '140'])).
% 0.19/0.53  thf('142', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('143', plain,
% 0.19/0.53      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.19/0.53      inference('clc', [status(thm)], ['141', '142'])).
% 0.19/0.53  thf('144', plain,
% 0.19/0.53      ((~ (v2_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.19/0.53      inference('split', [status(esa)], ['0'])).
% 0.19/0.53  thf('145', plain,
% 0.19/0.53      (~ ((v1_zfmisc_1 @ sk_B_1)) | ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.19/0.53      inference('sup-', [status(thm)], ['143', '144'])).
% 0.19/0.53  thf('146', plain, ($false),
% 0.19/0.53      inference('sat_resolution*', [status(thm)], ['1', '72', '73', '145'])).
% 0.19/0.53  
% 0.19/0.53  % SZS output end Refutation
% 0.19/0.53  
% 0.35/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
