%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BtLHL3DdKA

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:56 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :  293 ( 837 expanded)
%              Number of leaves         :   48 ( 260 expanded)
%              Depth                    :   29
%              Number of atoms          : 2247 (8827 expanded)
%              Number of equality atoms :   51 (  66 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

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
    ! [X44: $i,X45: $i] :
      ( ( v1_xboole_0 @ X44 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( v2_tex_2 @ X44 @ X45 )
      | ( X44
        = ( u1_struct_0 @ ( sk_C_1 @ X44 @ X45 ) ) )
      | ~ ( l1_pre_topc @ X45 )
      | ~ ( v2_pre_topc @ X45 )
      | ( v2_struct_0 @ X45 ) ) ),
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
    ! [X22: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 )
      | ~ ( v7_struct_0 @ X22 ) ) ),
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
    ! [X44: $i,X45: $i] :
      ( ( v1_xboole_0 @ X44 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( v2_tex_2 @ X44 @ X45 )
      | ( m1_pre_topc @ ( sk_C_1 @ X44 @ X45 ) @ X45 )
      | ~ ( l1_pre_topc @ X45 )
      | ~ ( v2_pre_topc @ X45 )
      | ( v2_struct_0 @ X45 ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( l1_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
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
    ! [X19: $i] :
      ( ( l1_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
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
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ~ ( v1_tdlat_3 @ X30 )
      | ( v7_struct_0 @ X30 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_tdlat_3 @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
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
    ! [X44: $i,X45: $i] :
      ( ( v1_xboole_0 @ X44 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( v2_tex_2 @ X44 @ X45 )
      | ( v1_tdlat_3 @ ( sk_C_1 @ X44 @ X45 ) )
      | ~ ( l1_pre_topc @ X45 )
      | ~ ( v2_pre_topc @ X45 )
      | ( v2_struct_0 @ X45 ) ) ),
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
    ! [X44: $i,X45: $i] :
      ( ( v1_xboole_0 @ X44 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( v2_tex_2 @ X44 @ X45 )
      | ~ ( v2_struct_0 @ ( sk_C_1 @ X44 @ X45 ) )
      | ~ ( l1_pre_topc @ X45 )
      | ~ ( v2_pre_topc @ X45 )
      | ( v2_struct_0 @ X45 ) ) ),
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

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('74',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('75',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ X12 @ X13 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('77',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ X23 )
      | ( ( k6_domain_1 @ X23 @ X24 )
        = ( k1_tarski @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('81',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X9 ) @ X11 )
      | ~ ( r2_hidden @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('83',plain,(
    ! [X39: $i,X40: $i] :
      ( ( v1_xboole_0 @ X39 )
      | ~ ( v1_zfmisc_1 @ X39 )
      | ( X40 = X39 )
      | ~ ( r1_tarski @ X40 @ X39 )
      | ( v1_xboole_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('86',plain,(
    ! [X8: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['79','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('92',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('93',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('94',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('95',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('96',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('97',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['93','98'])).

thf('100',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X9 ) @ X11 )
      | ~ ( r2_hidden @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('103',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( r2_hidden @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['92','105'])).

thf('107',plain,(
    ! [X8: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('108',plain,(
    r2_hidden @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ X12 @ X13 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('110',plain,(
    m1_subset_1 @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ X23 )
      | ( ( k6_domain_1 @ X23 @ X24 )
        = ( k1_tarski @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('112',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) )
      = ( k1_tarski @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('115',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) )
    = ( k1_tarski @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['112','115'])).

thf('117',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ) )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['91','116'])).

thf('118',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('119',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ X12 @ X13 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('120',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ X23 )
      | ( ( k6_domain_1 @ X23 @ X24 )
        = ( k1_tarski @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('122',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('124',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
    = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ) )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['117','124'])).

thf('126',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ) ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['90','127'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('129',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('130',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('131',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('132',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('133',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_tarski @ ( k1_tarski @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('137',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['131','137'])).

thf('139',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X9 ) @ X11 )
      | ~ ( r2_hidden @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('140',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_B @ ( k1_tarski @ X0 ) ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['130','142'])).

thf('144',plain,(
    ! [X8: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('145',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_B @ ( k1_tarski @ X0 ) ) @ ( k2_tarski @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_B @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['129','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('148',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ ( k1_tarski @ ( sk_B @ X0 ) ) ) @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['146','149'])).

thf('151',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X9 ) @ X11 )
      | ~ ( r2_hidden @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ ( k1_tarski @ ( sk_B @ X0 ) ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,
    ( ( ( r1_tarski @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['128','152'])).

thf('154',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( r1_tarski @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_tarski @ ( k1_tarski @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('157',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ X12 @ X13 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('159',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ X23 )
      | ( ( k6_domain_1 @ X23 @ X24 )
        = ( k1_tarski @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('161',plain,
    ( ( ( ( k6_domain_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
        = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( ( k6_domain_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['161','162'])).

thf('164',plain,
    ( ( ( sk_B_1
        = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_zfmisc_1 @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['89','163'])).

thf('165',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('166',plain,
    ( ( ( sk_B_1
        = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( sk_B_1
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['166','167'])).

thf('169',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf(dt_k1_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) )
        & ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ) )).

thf('170',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( l1_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X35 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X35 @ X36 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('171',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['171','172'])).

thf('174',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ sk_A ),
    inference(clc,[status(thm)],['173','174'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('176',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('177',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['177','178'])).

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

thf('180',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( v2_struct_0 @ X41 )
      | ~ ( m1_pre_topc @ X41 @ X42 )
      | ( X43
       != ( u1_struct_0 @ X41 ) )
      | ~ ( v1_tdlat_3 @ X41 )
      | ( v2_tex_2 @ X43 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( l1_pre_topc @ X42 )
      | ( v2_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t26_tex_2])).

thf('181',plain,(
    ! [X41: $i,X42: $i] :
      ( ( v2_struct_0 @ X42 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X41 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ X41 ) @ X42 )
      | ~ ( v1_tdlat_3 @ X41 )
      | ~ ( m1_pre_topc @ X41 @ X42 )
      | ( v2_struct_0 @ X41 ) ) ),
    inference(simplify,[status(thm)],['180'])).

thf('182',plain,
    ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ sk_A )
    | ~ ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_tex_2 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['179','181'])).

thf('183',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ sk_A ),
    inference(clc,[status(thm)],['173','174'])).

thf('184',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ~ ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_tex_2 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['182','183','184'])).

thf('186',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ sk_A ),
    inference(clc,[status(thm)],['173','174'])).

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

thf('187',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ( v1_tdlat_3 @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ~ ( v7_struct_0 @ X27 )
      | ( v2_struct_0 @ X27 )
      | ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[cc25_tex_2])).

thf('188',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ~ ( v2_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf(fc2_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ) )).

thf('191',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( l1_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X37 ) )
      | ( v7_struct_0 @ ( k1_tex_2 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_tex_2])).

thf('192',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('195',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    v7_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['194','195'])).

thf('197',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ~ ( v2_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['188','189','196'])).

thf('198',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ sk_A ),
    inference(clc,[status(thm)],['173','174'])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('199',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('200',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    v2_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['200','201','202'])).

thf('204',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['197','203'])).

thf('205',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,
    ( ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['204','205'])).

thf('207',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('208',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( l1_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X35 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('209',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['207','208'])).

thf('210',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['209','210'])).

thf('212',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['211','212'])).

thf('214',plain,(
    v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['206','213'])).

thf('215',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('216',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( l1_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X35 ) )
      | ( v1_pre_topc @ ( k1_tex_2 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('217',plain,
    ( ( v1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['215','216'])).

thf('218',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,
    ( ( v1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['217','218'])).

thf('220',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    v1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['219','220'])).

thf(d4_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( v1_pre_topc @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( C
                  = ( k1_tex_2 @ A @ B ) )
              <=> ( ( u1_struct_0 @ C )
                  = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('222',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X33 ) )
      | ( X34
       != ( k1_tex_2 @ X33 @ X32 ) )
      | ( ( u1_struct_0 @ X34 )
        = ( k6_domain_1 @ ( u1_struct_0 @ X33 ) @ X32 ) )
      | ~ ( m1_pre_topc @ X34 @ X33 )
      | ~ ( v1_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 )
      | ~ ( l1_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d4_tex_2])).

thf('223',plain,(
    ! [X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ( v2_struct_0 @ ( k1_tex_2 @ X33 @ X32 ) )
      | ~ ( v1_pre_topc @ ( k1_tex_2 @ X33 @ X32 ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ X33 @ X32 ) @ X33 )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ X33 @ X32 ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ X33 ) @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X33 ) ) ) ),
    inference(simplify,[status(thm)],['222'])).

thf('224',plain,
    ( ~ ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['221','223'])).

thf('225',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('226',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
    = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('227',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['224','225','226','227'])).

thf('229',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ sk_A ),
    inference(clc,[status(thm)],['173','174'])).

thf('230',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['228','229'])).

thf('231',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['211','212'])).

thf('232',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['230','231'])).

thf('233',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['232','233'])).

thf('235',plain,
    ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['185','214','234'])).

thf('236',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['211','212'])).

thf('237',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference(clc,[status(thm)],['235','236'])).

thf('238',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,(
    v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ),
    inference(clc,[status(thm)],['237','238'])).

thf('240',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['168','239'])).

thf('241',plain,
    ( ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('242',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['240','241'])).

thf('243',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','72','73','242'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BtLHL3DdKA
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:35:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.06/1.25  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.06/1.25  % Solved by: fo/fo7.sh
% 1.06/1.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.06/1.25  % done 1786 iterations in 0.800s
% 1.06/1.25  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.06/1.25  % SZS output start Refutation
% 1.06/1.25  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.06/1.25  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.06/1.25  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 1.06/1.25  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.06/1.25  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.06/1.25  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.06/1.25  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.06/1.25  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.06/1.25  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.06/1.25  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 1.06/1.25  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.06/1.25  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.06/1.25  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.06/1.25  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.06/1.25  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 1.06/1.25  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.06/1.25  thf(sk_B_type, type, sk_B: $i > $i).
% 1.06/1.25  thf(sk_A_type, type, sk_A: $i).
% 1.06/1.25  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.06/1.25  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 1.06/1.25  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 1.06/1.25  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.06/1.25  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.06/1.25  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 1.06/1.25  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 1.06/1.25  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 1.06/1.25  thf(t44_tex_2, conjecture,
% 1.06/1.25    (![A:$i]:
% 1.06/1.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 1.06/1.25         ( l1_pre_topc @ A ) ) =>
% 1.06/1.25       ( ![B:$i]:
% 1.06/1.25         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 1.06/1.25             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.06/1.25           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 1.06/1.25  thf(zf_stmt_0, negated_conjecture,
% 1.06/1.25    (~( ![A:$i]:
% 1.06/1.25        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.06/1.25            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.25          ( ![B:$i]:
% 1.06/1.25            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 1.06/1.25                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.06/1.25              ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 1.06/1.25    inference('cnf.neg', [status(esa)], [t44_tex_2])).
% 1.06/1.25  thf('0', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('1', plain,
% 1.06/1.25      (~ ((v1_zfmisc_1 @ sk_B_1)) | ~ ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 1.06/1.25      inference('split', [status(esa)], ['0'])).
% 1.06/1.25  thf('2', plain, (((v1_zfmisc_1 @ sk_B_1) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('3', plain,
% 1.06/1.25      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.06/1.25      inference('split', [status(esa)], ['2'])).
% 1.06/1.25  thf('4', plain,
% 1.06/1.25      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf(t34_tex_2, axiom,
% 1.06/1.25    (![A:$i]:
% 1.06/1.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.25       ( ![B:$i]:
% 1.06/1.25         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 1.06/1.25             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.06/1.25           ( ~( ( v2_tex_2 @ B @ A ) & 
% 1.06/1.25                ( ![C:$i]:
% 1.06/1.25                  ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 1.06/1.25                      ( v1_tdlat_3 @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.06/1.25                    ( ( B ) != ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ))).
% 1.06/1.25  thf('5', plain,
% 1.06/1.25      (![X44 : $i, X45 : $i]:
% 1.06/1.25         ((v1_xboole_0 @ X44)
% 1.06/1.25          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 1.06/1.25          | ~ (v2_tex_2 @ X44 @ X45)
% 1.06/1.25          | ((X44) = (u1_struct_0 @ (sk_C_1 @ X44 @ X45)))
% 1.06/1.25          | ~ (l1_pre_topc @ X45)
% 1.06/1.25          | ~ (v2_pre_topc @ X45)
% 1.06/1.25          | (v2_struct_0 @ X45))),
% 1.06/1.25      inference('cnf', [status(esa)], [t34_tex_2])).
% 1.06/1.25  thf('6', plain,
% 1.06/1.25      (((v2_struct_0 @ sk_A)
% 1.06/1.25        | ~ (v2_pre_topc @ sk_A)
% 1.06/1.25        | ~ (l1_pre_topc @ sk_A)
% 1.06/1.25        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 1.06/1.25        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 1.06/1.25        | (v1_xboole_0 @ sk_B_1))),
% 1.06/1.25      inference('sup-', [status(thm)], ['4', '5'])).
% 1.06/1.25  thf('7', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('9', plain,
% 1.06/1.25      (((v2_struct_0 @ sk_A)
% 1.06/1.25        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 1.06/1.25        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 1.06/1.25        | (v1_xboole_0 @ sk_B_1))),
% 1.06/1.25      inference('demod', [status(thm)], ['6', '7', '8'])).
% 1.06/1.25  thf('10', plain,
% 1.06/1.25      ((((v1_xboole_0 @ sk_B_1)
% 1.06/1.25         | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 1.06/1.25         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['3', '9'])).
% 1.06/1.25  thf('11', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('12', plain,
% 1.06/1.25      ((((v2_struct_0 @ sk_A)
% 1.06/1.25         | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))))
% 1.06/1.25         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.06/1.25      inference('clc', [status(thm)], ['10', '11'])).
% 1.06/1.25  thf('13', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('14', plain,
% 1.06/1.25      ((((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 1.06/1.25         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.06/1.25      inference('clc', [status(thm)], ['12', '13'])).
% 1.06/1.25  thf(fc7_struct_0, axiom,
% 1.06/1.25    (![A:$i]:
% 1.06/1.25     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 1.06/1.25       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 1.06/1.25  thf('15', plain,
% 1.06/1.25      (![X22 : $i]:
% 1.06/1.25         ((v1_zfmisc_1 @ (u1_struct_0 @ X22))
% 1.06/1.25          | ~ (l1_struct_0 @ X22)
% 1.06/1.25          | ~ (v7_struct_0 @ X22))),
% 1.06/1.25      inference('cnf', [status(esa)], [fc7_struct_0])).
% 1.06/1.25  thf('16', plain,
% 1.06/1.25      ((((v1_zfmisc_1 @ sk_B_1)
% 1.06/1.25         | ~ (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.06/1.25         | ~ (l1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 1.06/1.25         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.06/1.25      inference('sup+', [status(thm)], ['14', '15'])).
% 1.06/1.25  thf('17', plain,
% 1.06/1.25      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.06/1.25      inference('split', [status(esa)], ['2'])).
% 1.06/1.25  thf('18', plain,
% 1.06/1.25      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('19', plain,
% 1.06/1.25      (![X44 : $i, X45 : $i]:
% 1.06/1.25         ((v1_xboole_0 @ X44)
% 1.06/1.25          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 1.06/1.25          | ~ (v2_tex_2 @ X44 @ X45)
% 1.06/1.25          | (m1_pre_topc @ (sk_C_1 @ X44 @ X45) @ X45)
% 1.06/1.25          | ~ (l1_pre_topc @ X45)
% 1.06/1.25          | ~ (v2_pre_topc @ X45)
% 1.06/1.25          | (v2_struct_0 @ X45))),
% 1.06/1.25      inference('cnf', [status(esa)], [t34_tex_2])).
% 1.06/1.25  thf('20', plain,
% 1.06/1.25      (((v2_struct_0 @ sk_A)
% 1.06/1.25        | ~ (v2_pre_topc @ sk_A)
% 1.06/1.25        | ~ (l1_pre_topc @ sk_A)
% 1.06/1.25        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 1.06/1.25        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 1.06/1.25        | (v1_xboole_0 @ sk_B_1))),
% 1.06/1.25      inference('sup-', [status(thm)], ['18', '19'])).
% 1.06/1.25  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('23', plain,
% 1.06/1.25      (((v2_struct_0 @ sk_A)
% 1.06/1.25        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 1.06/1.25        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 1.06/1.25        | (v1_xboole_0 @ sk_B_1))),
% 1.06/1.25      inference('demod', [status(thm)], ['20', '21', '22'])).
% 1.06/1.25  thf('24', plain,
% 1.06/1.25      ((((v1_xboole_0 @ sk_B_1)
% 1.06/1.25         | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 1.06/1.25         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['17', '23'])).
% 1.06/1.25  thf('25', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('26', plain,
% 1.06/1.25      ((((v2_struct_0 @ sk_A) | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)))
% 1.06/1.25         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.06/1.25      inference('clc', [status(thm)], ['24', '25'])).
% 1.06/1.25  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('28', plain,
% 1.06/1.25      (((m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A))
% 1.06/1.25         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.06/1.25      inference('clc', [status(thm)], ['26', '27'])).
% 1.06/1.25  thf(dt_m1_pre_topc, axiom,
% 1.06/1.25    (![A:$i]:
% 1.06/1.25     ( ( l1_pre_topc @ A ) =>
% 1.06/1.25       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.06/1.25  thf('29', plain,
% 1.06/1.25      (![X20 : $i, X21 : $i]:
% 1.06/1.25         (~ (m1_pre_topc @ X20 @ X21)
% 1.06/1.25          | (l1_pre_topc @ X20)
% 1.06/1.25          | ~ (l1_pre_topc @ X21))),
% 1.06/1.25      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.06/1.25  thf('30', plain,
% 1.06/1.25      (((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 1.06/1.25         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['28', '29'])).
% 1.06/1.25  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('32', plain,
% 1.06/1.25      (((l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 1.06/1.25         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.06/1.25      inference('demod', [status(thm)], ['30', '31'])).
% 1.06/1.25  thf(dt_l1_pre_topc, axiom,
% 1.06/1.25    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.06/1.25  thf('33', plain,
% 1.06/1.25      (![X19 : $i]: ((l1_struct_0 @ X19) | ~ (l1_pre_topc @ X19))),
% 1.06/1.25      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.06/1.25  thf('34', plain,
% 1.06/1.25      (((l1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 1.06/1.25         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['32', '33'])).
% 1.06/1.25  thf('35', plain,
% 1.06/1.25      ((((v1_zfmisc_1 @ sk_B_1) | ~ (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 1.06/1.25         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.06/1.25      inference('demod', [status(thm)], ['16', '34'])).
% 1.06/1.25  thf('36', plain,
% 1.06/1.25      (((m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A))
% 1.06/1.25         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.06/1.25      inference('clc', [status(thm)], ['26', '27'])).
% 1.06/1.25  thf(cc32_tex_2, axiom,
% 1.06/1.25    (![A:$i]:
% 1.06/1.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 1.06/1.25         ( l1_pre_topc @ A ) ) =>
% 1.06/1.25       ( ![B:$i]:
% 1.06/1.25         ( ( m1_pre_topc @ B @ A ) =>
% 1.06/1.25           ( ( ( ~( v2_struct_0 @ B ) ) & ( ~( v7_struct_0 @ B ) ) ) =>
% 1.06/1.25             ( ( ~( v2_struct_0 @ B ) ) & ( ~( v1_tdlat_3 @ B ) ) ) ) ) ) ))).
% 1.06/1.25  thf('37', plain,
% 1.06/1.25      (![X30 : $i, X31 : $i]:
% 1.06/1.25         (~ (m1_pre_topc @ X30 @ X31)
% 1.06/1.25          | ~ (v1_tdlat_3 @ X30)
% 1.06/1.25          | (v7_struct_0 @ X30)
% 1.06/1.25          | (v2_struct_0 @ X30)
% 1.06/1.25          | ~ (l1_pre_topc @ X31)
% 1.06/1.25          | ~ (v2_tdlat_3 @ X31)
% 1.06/1.25          | ~ (v2_pre_topc @ X31)
% 1.06/1.25          | (v2_struct_0 @ X31))),
% 1.06/1.25      inference('cnf', [status(esa)], [cc32_tex_2])).
% 1.06/1.25  thf('38', plain,
% 1.06/1.25      ((((v2_struct_0 @ sk_A)
% 1.06/1.25         | ~ (v2_pre_topc @ sk_A)
% 1.06/1.25         | ~ (v2_tdlat_3 @ sk_A)
% 1.06/1.25         | ~ (l1_pre_topc @ sk_A)
% 1.06/1.25         | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.06/1.25         | (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.06/1.25         | ~ (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 1.06/1.25         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['36', '37'])).
% 1.06/1.25  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('40', plain, ((v2_tdlat_3 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('42', plain,
% 1.06/1.25      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.06/1.25      inference('split', [status(esa)], ['2'])).
% 1.06/1.25  thf('43', plain,
% 1.06/1.25      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('44', plain,
% 1.06/1.25      (![X44 : $i, X45 : $i]:
% 1.06/1.25         ((v1_xboole_0 @ X44)
% 1.06/1.25          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 1.06/1.25          | ~ (v2_tex_2 @ X44 @ X45)
% 1.06/1.25          | (v1_tdlat_3 @ (sk_C_1 @ X44 @ X45))
% 1.06/1.25          | ~ (l1_pre_topc @ X45)
% 1.06/1.25          | ~ (v2_pre_topc @ X45)
% 1.06/1.25          | (v2_struct_0 @ X45))),
% 1.06/1.25      inference('cnf', [status(esa)], [t34_tex_2])).
% 1.06/1.25  thf('45', plain,
% 1.06/1.25      (((v2_struct_0 @ sk_A)
% 1.06/1.25        | ~ (v2_pre_topc @ sk_A)
% 1.06/1.25        | ~ (l1_pre_topc @ sk_A)
% 1.06/1.25        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.06/1.25        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 1.06/1.25        | (v1_xboole_0 @ sk_B_1))),
% 1.06/1.25      inference('sup-', [status(thm)], ['43', '44'])).
% 1.06/1.25  thf('46', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('48', plain,
% 1.06/1.25      (((v2_struct_0 @ sk_A)
% 1.06/1.25        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.06/1.25        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 1.06/1.25        | (v1_xboole_0 @ sk_B_1))),
% 1.06/1.25      inference('demod', [status(thm)], ['45', '46', '47'])).
% 1.06/1.25  thf('49', plain,
% 1.06/1.25      ((((v1_xboole_0 @ sk_B_1)
% 1.06/1.25         | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.06/1.25         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['42', '48'])).
% 1.06/1.25  thf('50', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('51', plain,
% 1.06/1.25      ((((v2_struct_0 @ sk_A) | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 1.06/1.25         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.06/1.25      inference('clc', [status(thm)], ['49', '50'])).
% 1.06/1.25  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('53', plain,
% 1.06/1.25      (((v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 1.06/1.25         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.06/1.25      inference('clc', [status(thm)], ['51', '52'])).
% 1.06/1.25  thf('54', plain,
% 1.06/1.25      ((((v2_struct_0 @ sk_A)
% 1.06/1.25         | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.06/1.25         | (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 1.06/1.25         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.06/1.25      inference('demod', [status(thm)], ['38', '39', '40', '41', '53'])).
% 1.06/1.25  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('56', plain,
% 1.06/1.25      ((((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.06/1.25         | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 1.06/1.25         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.06/1.25      inference('clc', [status(thm)], ['54', '55'])).
% 1.06/1.25  thf('57', plain,
% 1.06/1.25      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('58', plain,
% 1.06/1.25      (![X44 : $i, X45 : $i]:
% 1.06/1.25         ((v1_xboole_0 @ X44)
% 1.06/1.25          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 1.06/1.25          | ~ (v2_tex_2 @ X44 @ X45)
% 1.06/1.25          | ~ (v2_struct_0 @ (sk_C_1 @ X44 @ X45))
% 1.06/1.25          | ~ (l1_pre_topc @ X45)
% 1.06/1.25          | ~ (v2_pre_topc @ X45)
% 1.06/1.25          | (v2_struct_0 @ X45))),
% 1.06/1.25      inference('cnf', [status(esa)], [t34_tex_2])).
% 1.06/1.25  thf('59', plain,
% 1.06/1.25      (((v2_struct_0 @ sk_A)
% 1.06/1.25        | ~ (v2_pre_topc @ sk_A)
% 1.06/1.25        | ~ (l1_pre_topc @ sk_A)
% 1.06/1.25        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.06/1.25        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 1.06/1.25        | (v1_xboole_0 @ sk_B_1))),
% 1.06/1.25      inference('sup-', [status(thm)], ['57', '58'])).
% 1.06/1.25  thf('60', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('62', plain,
% 1.06/1.25      (((v2_struct_0 @ sk_A)
% 1.06/1.25        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.06/1.25        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 1.06/1.25        | (v1_xboole_0 @ sk_B_1))),
% 1.06/1.25      inference('demod', [status(thm)], ['59', '60', '61'])).
% 1.06/1.25  thf('63', plain,
% 1.06/1.25      ((((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.06/1.25         | (v1_xboole_0 @ sk_B_1)
% 1.06/1.25         | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 1.06/1.25         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['56', '62'])).
% 1.06/1.25  thf('64', plain,
% 1.06/1.25      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.06/1.25      inference('split', [status(esa)], ['2'])).
% 1.06/1.25  thf('65', plain,
% 1.06/1.25      ((((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.06/1.25         | (v1_xboole_0 @ sk_B_1)
% 1.06/1.25         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.06/1.25      inference('demod', [status(thm)], ['63', '64'])).
% 1.06/1.25  thf('66', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('67', plain,
% 1.06/1.25      ((((v2_struct_0 @ sk_A) | (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 1.06/1.25         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.06/1.25      inference('clc', [status(thm)], ['65', '66'])).
% 1.06/1.25  thf('68', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('69', plain,
% 1.06/1.25      (((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 1.06/1.25         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.06/1.25      inference('clc', [status(thm)], ['67', '68'])).
% 1.06/1.25  thf('70', plain,
% 1.06/1.25      (((v1_zfmisc_1 @ sk_B_1)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.06/1.25      inference('demod', [status(thm)], ['35', '69'])).
% 1.06/1.25  thf('71', plain,
% 1.06/1.25      ((~ (v1_zfmisc_1 @ sk_B_1)) <= (~ ((v1_zfmisc_1 @ sk_B_1)))),
% 1.06/1.25      inference('split', [status(esa)], ['0'])).
% 1.06/1.25  thf('72', plain, (((v1_zfmisc_1 @ sk_B_1)) | ~ ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 1.06/1.25      inference('sup-', [status(thm)], ['70', '71'])).
% 1.06/1.25  thf('73', plain, (((v1_zfmisc_1 @ sk_B_1)) | ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 1.06/1.25      inference('split', [status(esa)], ['2'])).
% 1.06/1.25  thf(d1_xboole_0, axiom,
% 1.06/1.25    (![A:$i]:
% 1.06/1.25     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.06/1.25  thf('74', plain,
% 1.06/1.25      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.06/1.25      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.06/1.25  thf(t1_subset, axiom,
% 1.06/1.25    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 1.06/1.25  thf('75', plain,
% 1.06/1.25      (![X12 : $i, X13 : $i]:
% 1.06/1.25         ((m1_subset_1 @ X12 @ X13) | ~ (r2_hidden @ X12 @ X13))),
% 1.06/1.25      inference('cnf', [status(esa)], [t1_subset])).
% 1.06/1.25  thf('76', plain,
% 1.06/1.25      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 1.06/1.25      inference('sup-', [status(thm)], ['74', '75'])).
% 1.06/1.25  thf(redefinition_k6_domain_1, axiom,
% 1.06/1.25    (![A:$i,B:$i]:
% 1.06/1.25     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 1.06/1.25       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 1.06/1.25  thf('77', plain,
% 1.06/1.25      (![X23 : $i, X24 : $i]:
% 1.06/1.25         ((v1_xboole_0 @ X23)
% 1.06/1.25          | ~ (m1_subset_1 @ X24 @ X23)
% 1.06/1.25          | ((k6_domain_1 @ X23 @ X24) = (k1_tarski @ X24)))),
% 1.06/1.25      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 1.06/1.25  thf('78', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         ((v1_xboole_0 @ X0)
% 1.06/1.25          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 1.06/1.25          | (v1_xboole_0 @ X0))),
% 1.06/1.25      inference('sup-', [status(thm)], ['76', '77'])).
% 1.06/1.25  thf('79', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 1.06/1.25          | (v1_xboole_0 @ X0))),
% 1.06/1.25      inference('simplify', [status(thm)], ['78'])).
% 1.06/1.25  thf('80', plain,
% 1.06/1.25      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.06/1.25      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.06/1.25  thf(l1_zfmisc_1, axiom,
% 1.06/1.25    (![A:$i,B:$i]:
% 1.06/1.25     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 1.06/1.25  thf('81', plain,
% 1.06/1.25      (![X9 : $i, X11 : $i]:
% 1.06/1.25         ((r1_tarski @ (k1_tarski @ X9) @ X11) | ~ (r2_hidden @ X9 @ X11))),
% 1.06/1.25      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.06/1.25  thf('82', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 1.06/1.25      inference('sup-', [status(thm)], ['80', '81'])).
% 1.06/1.25  thf(t1_tex_2, axiom,
% 1.06/1.25    (![A:$i]:
% 1.06/1.25     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.06/1.25       ( ![B:$i]:
% 1.06/1.25         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 1.06/1.25           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 1.06/1.25  thf('83', plain,
% 1.06/1.25      (![X39 : $i, X40 : $i]:
% 1.06/1.25         ((v1_xboole_0 @ X39)
% 1.06/1.25          | ~ (v1_zfmisc_1 @ X39)
% 1.06/1.25          | ((X40) = (X39))
% 1.06/1.25          | ~ (r1_tarski @ X40 @ X39)
% 1.06/1.25          | (v1_xboole_0 @ X40))),
% 1.06/1.25      inference('cnf', [status(esa)], [t1_tex_2])).
% 1.06/1.25  thf('84', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         ((v1_xboole_0 @ X0)
% 1.06/1.25          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 1.06/1.25          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 1.06/1.25          | ~ (v1_zfmisc_1 @ X0)
% 1.06/1.25          | (v1_xboole_0 @ X0))),
% 1.06/1.25      inference('sup-', [status(thm)], ['82', '83'])).
% 1.06/1.25  thf('85', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (~ (v1_zfmisc_1 @ X0)
% 1.06/1.25          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 1.06/1.25          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 1.06/1.25          | (v1_xboole_0 @ X0))),
% 1.06/1.25      inference('simplify', [status(thm)], ['84'])).
% 1.06/1.25  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 1.06/1.25  thf('86', plain, (![X8 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X8))),
% 1.06/1.25      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 1.06/1.25  thf('87', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         ((v1_xboole_0 @ X0)
% 1.06/1.25          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 1.06/1.25          | ~ (v1_zfmisc_1 @ X0))),
% 1.06/1.25      inference('sup-', [status(thm)], ['85', '86'])).
% 1.06/1.25  thf('88', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (X0))
% 1.06/1.25          | (v1_xboole_0 @ X0)
% 1.06/1.25          | ~ (v1_zfmisc_1 @ X0)
% 1.06/1.25          | (v1_xboole_0 @ X0))),
% 1.06/1.25      inference('sup+', [status(thm)], ['79', '87'])).
% 1.06/1.25  thf('89', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (~ (v1_zfmisc_1 @ X0)
% 1.06/1.25          | (v1_xboole_0 @ X0)
% 1.06/1.25          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (X0)))),
% 1.06/1.25      inference('simplify', [status(thm)], ['88'])).
% 1.06/1.25  thf('90', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 1.06/1.25      inference('split', [status(esa)], ['2'])).
% 1.06/1.25  thf('91', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         ((v1_xboole_0 @ X0)
% 1.06/1.25          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 1.06/1.25          | ~ (v1_zfmisc_1 @ X0))),
% 1.06/1.25      inference('sup-', [status(thm)], ['85', '86'])).
% 1.06/1.25  thf('92', plain,
% 1.06/1.25      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.06/1.25      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.06/1.25  thf('93', plain,
% 1.06/1.25      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.06/1.25      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.06/1.25  thf('94', plain,
% 1.06/1.25      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf(t3_subset, axiom,
% 1.06/1.25    (![A:$i,B:$i]:
% 1.06/1.25     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.06/1.25  thf('95', plain,
% 1.06/1.25      (![X14 : $i, X15 : $i]:
% 1.06/1.25         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 1.06/1.25      inference('cnf', [status(esa)], [t3_subset])).
% 1.06/1.25  thf('96', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 1.06/1.25      inference('sup-', [status(thm)], ['94', '95'])).
% 1.06/1.25  thf(d3_tarski, axiom,
% 1.06/1.25    (![A:$i,B:$i]:
% 1.06/1.25     ( ( r1_tarski @ A @ B ) <=>
% 1.06/1.25       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.06/1.25  thf('97', plain,
% 1.06/1.25      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.06/1.25         (~ (r2_hidden @ X3 @ X4)
% 1.06/1.25          | (r2_hidden @ X3 @ X5)
% 1.06/1.25          | ~ (r1_tarski @ X4 @ X5))),
% 1.06/1.25      inference('cnf', [status(esa)], [d3_tarski])).
% 1.06/1.25  thf('98', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 1.06/1.25      inference('sup-', [status(thm)], ['96', '97'])).
% 1.06/1.25  thf('99', plain,
% 1.06/1.25      (((v1_xboole_0 @ sk_B_1)
% 1.06/1.25        | (r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['93', '98'])).
% 1.06/1.25  thf('100', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('101', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 1.06/1.25      inference('clc', [status(thm)], ['99', '100'])).
% 1.06/1.25  thf('102', plain,
% 1.06/1.25      (![X9 : $i, X11 : $i]:
% 1.06/1.25         ((r1_tarski @ (k1_tarski @ X9) @ X11) | ~ (r2_hidden @ X9 @ X11))),
% 1.06/1.25      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.06/1.25  thf('103', plain,
% 1.06/1.25      ((r1_tarski @ (k1_tarski @ (sk_B @ sk_B_1)) @ (u1_struct_0 @ sk_A))),
% 1.06/1.25      inference('sup-', [status(thm)], ['101', '102'])).
% 1.06/1.25  thf('104', plain,
% 1.06/1.25      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.06/1.25         (~ (r2_hidden @ X3 @ X4)
% 1.06/1.25          | (r2_hidden @ X3 @ X5)
% 1.06/1.25          | ~ (r1_tarski @ X4 @ X5))),
% 1.06/1.25      inference('cnf', [status(esa)], [d3_tarski])).
% 1.06/1.25  thf('105', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 1.06/1.25          | ~ (r2_hidden @ X0 @ (k1_tarski @ (sk_B @ sk_B_1))))),
% 1.06/1.25      inference('sup-', [status(thm)], ['103', '104'])).
% 1.06/1.25  thf('106', plain,
% 1.06/1.25      (((v1_xboole_0 @ (k1_tarski @ (sk_B @ sk_B_1)))
% 1.06/1.25        | (r2_hidden @ (sk_B @ (k1_tarski @ (sk_B @ sk_B_1))) @ 
% 1.06/1.25           (u1_struct_0 @ sk_A)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['92', '105'])).
% 1.06/1.25  thf('107', plain, (![X8 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X8))),
% 1.06/1.25      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 1.06/1.25  thf('108', plain,
% 1.06/1.25      ((r2_hidden @ (sk_B @ (k1_tarski @ (sk_B @ sk_B_1))) @ 
% 1.06/1.25        (u1_struct_0 @ sk_A))),
% 1.06/1.25      inference('clc', [status(thm)], ['106', '107'])).
% 1.06/1.25  thf('109', plain,
% 1.06/1.25      (![X12 : $i, X13 : $i]:
% 1.06/1.25         ((m1_subset_1 @ X12 @ X13) | ~ (r2_hidden @ X12 @ X13))),
% 1.06/1.25      inference('cnf', [status(esa)], [t1_subset])).
% 1.06/1.25  thf('110', plain,
% 1.06/1.25      ((m1_subset_1 @ (sk_B @ (k1_tarski @ (sk_B @ sk_B_1))) @ 
% 1.06/1.25        (u1_struct_0 @ sk_A))),
% 1.06/1.25      inference('sup-', [status(thm)], ['108', '109'])).
% 1.06/1.25  thf('111', plain,
% 1.06/1.25      (![X23 : $i, X24 : $i]:
% 1.06/1.25         ((v1_xboole_0 @ X23)
% 1.06/1.25          | ~ (m1_subset_1 @ X24 @ X23)
% 1.06/1.25          | ((k6_domain_1 @ X23 @ X24) = (k1_tarski @ X24)))),
% 1.06/1.25      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 1.06/1.25  thf('112', plain,
% 1.06/1.25      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.25          (sk_B @ (k1_tarski @ (sk_B @ sk_B_1))))
% 1.06/1.25          = (k1_tarski @ (sk_B @ (k1_tarski @ (sk_B @ sk_B_1)))))
% 1.06/1.25        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['110', '111'])).
% 1.06/1.25  thf('113', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 1.06/1.25      inference('clc', [status(thm)], ['99', '100'])).
% 1.06/1.25  thf('114', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.06/1.25      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.06/1.25  thf('115', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 1.06/1.25      inference('sup-', [status(thm)], ['113', '114'])).
% 1.06/1.25  thf('116', plain,
% 1.06/1.25      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.25         (sk_B @ (k1_tarski @ (sk_B @ sk_B_1))))
% 1.06/1.25         = (k1_tarski @ (sk_B @ (k1_tarski @ (sk_B @ sk_B_1)))))),
% 1.06/1.25      inference('clc', [status(thm)], ['112', '115'])).
% 1.06/1.25  thf('117', plain,
% 1.06/1.25      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 1.06/1.25          = (k1_tarski @ (sk_B @ (k1_tarski @ (sk_B @ sk_B_1)))))
% 1.06/1.25        | ~ (v1_zfmisc_1 @ sk_B_1)
% 1.06/1.25        | (v1_xboole_0 @ sk_B_1))),
% 1.06/1.25      inference('sup+', [status(thm)], ['91', '116'])).
% 1.06/1.25  thf('118', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 1.06/1.25      inference('clc', [status(thm)], ['99', '100'])).
% 1.06/1.25  thf('119', plain,
% 1.06/1.25      (![X12 : $i, X13 : $i]:
% 1.06/1.25         ((m1_subset_1 @ X12 @ X13) | ~ (r2_hidden @ X12 @ X13))),
% 1.06/1.25      inference('cnf', [status(esa)], [t1_subset])).
% 1.06/1.25  thf('120', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 1.06/1.25      inference('sup-', [status(thm)], ['118', '119'])).
% 1.06/1.25  thf('121', plain,
% 1.06/1.25      (![X23 : $i, X24 : $i]:
% 1.06/1.25         ((v1_xboole_0 @ X23)
% 1.06/1.25          | ~ (m1_subset_1 @ X24 @ X23)
% 1.06/1.25          | ((k6_domain_1 @ X23 @ X24) = (k1_tarski @ X24)))),
% 1.06/1.25      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 1.06/1.25  thf('122', plain,
% 1.06/1.25      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 1.06/1.25          = (k1_tarski @ (sk_B @ sk_B_1)))
% 1.06/1.25        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['120', '121'])).
% 1.06/1.25  thf('123', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 1.06/1.25      inference('sup-', [status(thm)], ['113', '114'])).
% 1.06/1.25  thf('124', plain,
% 1.06/1.25      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 1.06/1.25         = (k1_tarski @ (sk_B @ sk_B_1)))),
% 1.06/1.25      inference('clc', [status(thm)], ['122', '123'])).
% 1.06/1.25  thf('125', plain,
% 1.06/1.25      ((((k1_tarski @ (sk_B @ sk_B_1))
% 1.06/1.25          = (k1_tarski @ (sk_B @ (k1_tarski @ (sk_B @ sk_B_1)))))
% 1.06/1.25        | ~ (v1_zfmisc_1 @ sk_B_1)
% 1.06/1.25        | (v1_xboole_0 @ sk_B_1))),
% 1.06/1.25      inference('demod', [status(thm)], ['117', '124'])).
% 1.06/1.25  thf('126', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('127', plain,
% 1.06/1.25      ((~ (v1_zfmisc_1 @ sk_B_1)
% 1.06/1.25        | ((k1_tarski @ (sk_B @ sk_B_1))
% 1.06/1.25            = (k1_tarski @ (sk_B @ (k1_tarski @ (sk_B @ sk_B_1))))))),
% 1.06/1.25      inference('clc', [status(thm)], ['125', '126'])).
% 1.06/1.25  thf('128', plain,
% 1.06/1.25      ((((k1_tarski @ (sk_B @ sk_B_1))
% 1.06/1.25          = (k1_tarski @ (sk_B @ (k1_tarski @ (sk_B @ sk_B_1))))))
% 1.06/1.25         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['90', '127'])).
% 1.06/1.25  thf(t69_enumset1, axiom,
% 1.06/1.25    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.06/1.25  thf('129', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 1.06/1.25      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.06/1.25  thf('130', plain,
% 1.06/1.25      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.06/1.25      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.06/1.25  thf('131', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 1.06/1.25      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.06/1.25  thf('132', plain,
% 1.06/1.25      (![X4 : $i, X6 : $i]:
% 1.06/1.25         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.06/1.25      inference('cnf', [status(esa)], [d3_tarski])).
% 1.06/1.25  thf('133', plain,
% 1.06/1.25      (![X4 : $i, X6 : $i]:
% 1.06/1.25         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 1.06/1.25      inference('cnf', [status(esa)], [d3_tarski])).
% 1.06/1.25  thf('134', plain,
% 1.06/1.25      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 1.06/1.25      inference('sup-', [status(thm)], ['132', '133'])).
% 1.06/1.25  thf('135', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.06/1.25      inference('simplify', [status(thm)], ['134'])).
% 1.06/1.25  thf('136', plain,
% 1.06/1.25      (![X9 : $i, X10 : $i]:
% 1.06/1.25         ((r2_hidden @ X9 @ X10) | ~ (r1_tarski @ (k1_tarski @ X9) @ X10))),
% 1.06/1.25      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.06/1.25  thf('137', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.06/1.25      inference('sup-', [status(thm)], ['135', '136'])).
% 1.06/1.25  thf('138', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X0))),
% 1.06/1.25      inference('sup+', [status(thm)], ['131', '137'])).
% 1.06/1.25  thf('139', plain,
% 1.06/1.25      (![X9 : $i, X11 : $i]:
% 1.06/1.25         ((r1_tarski @ (k1_tarski @ X9) @ X11) | ~ (r2_hidden @ X9 @ X11))),
% 1.06/1.25      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.06/1.25  thf('140', plain,
% 1.06/1.25      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X0))),
% 1.06/1.25      inference('sup-', [status(thm)], ['138', '139'])).
% 1.06/1.25  thf('141', plain,
% 1.06/1.25      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.06/1.25         (~ (r2_hidden @ X3 @ X4)
% 1.06/1.25          | (r2_hidden @ X3 @ X5)
% 1.06/1.25          | ~ (r1_tarski @ X4 @ X5))),
% 1.06/1.25      inference('cnf', [status(esa)], [d3_tarski])).
% 1.06/1.25  thf('142', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]:
% 1.06/1.25         ((r2_hidden @ X1 @ (k2_tarski @ X0 @ X0))
% 1.06/1.25          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['140', '141'])).
% 1.06/1.25  thf('143', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         ((v1_xboole_0 @ (k1_tarski @ X0))
% 1.06/1.25          | (r2_hidden @ (sk_B @ (k1_tarski @ X0)) @ (k2_tarski @ X0 @ X0)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['130', '142'])).
% 1.06/1.25  thf('144', plain, (![X8 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X8))),
% 1.06/1.25      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 1.06/1.25  thf('145', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (r2_hidden @ (sk_B @ (k1_tarski @ X0)) @ (k2_tarski @ X0 @ X0))),
% 1.06/1.25      inference('clc', [status(thm)], ['143', '144'])).
% 1.06/1.25  thf('146', plain,
% 1.06/1.25      (![X0 : $i]: (r2_hidden @ (sk_B @ (k1_tarski @ X0)) @ (k1_tarski @ X0))),
% 1.06/1.25      inference('sup+', [status(thm)], ['129', '145'])).
% 1.06/1.25  thf('147', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 1.06/1.25      inference('sup-', [status(thm)], ['80', '81'])).
% 1.06/1.25  thf('148', plain,
% 1.06/1.25      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.06/1.25         (~ (r2_hidden @ X3 @ X4)
% 1.06/1.25          | (r2_hidden @ X3 @ X5)
% 1.06/1.25          | ~ (r1_tarski @ X4 @ X5))),
% 1.06/1.25      inference('cnf', [status(esa)], [d3_tarski])).
% 1.06/1.25  thf('149', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]:
% 1.06/1.25         ((v1_xboole_0 @ X0)
% 1.06/1.25          | (r2_hidden @ X1 @ X0)
% 1.06/1.25          | ~ (r2_hidden @ X1 @ (k1_tarski @ (sk_B @ X0))))),
% 1.06/1.25      inference('sup-', [status(thm)], ['147', '148'])).
% 1.06/1.25  thf('150', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         ((r2_hidden @ (sk_B @ (k1_tarski @ (sk_B @ X0))) @ X0)
% 1.06/1.25          | (v1_xboole_0 @ X0))),
% 1.06/1.25      inference('sup-', [status(thm)], ['146', '149'])).
% 1.06/1.25  thf('151', plain,
% 1.06/1.25      (![X9 : $i, X11 : $i]:
% 1.06/1.25         ((r1_tarski @ (k1_tarski @ X9) @ X11) | ~ (r2_hidden @ X9 @ X11))),
% 1.06/1.25      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.06/1.25  thf('152', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         ((v1_xboole_0 @ X0)
% 1.06/1.25          | (r1_tarski @ (k1_tarski @ (sk_B @ (k1_tarski @ (sk_B @ X0)))) @ X0))),
% 1.06/1.25      inference('sup-', [status(thm)], ['150', '151'])).
% 1.06/1.25  thf('153', plain,
% 1.06/1.25      ((((r1_tarski @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_B_1)
% 1.06/1.25         | (v1_xboole_0 @ sk_B_1))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 1.06/1.25      inference('sup+', [status(thm)], ['128', '152'])).
% 1.06/1.25  thf('154', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('155', plain,
% 1.06/1.25      (((r1_tarski @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_B_1))
% 1.06/1.25         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 1.06/1.25      inference('clc', [status(thm)], ['153', '154'])).
% 1.06/1.25  thf('156', plain,
% 1.06/1.25      (![X9 : $i, X10 : $i]:
% 1.06/1.25         ((r2_hidden @ X9 @ X10) | ~ (r1_tarski @ (k1_tarski @ X9) @ X10))),
% 1.06/1.25      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.06/1.25  thf('157', plain,
% 1.06/1.25      (((r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['155', '156'])).
% 1.06/1.25  thf('158', plain,
% 1.06/1.25      (![X12 : $i, X13 : $i]:
% 1.06/1.25         ((m1_subset_1 @ X12 @ X13) | ~ (r2_hidden @ X12 @ X13))),
% 1.06/1.25      inference('cnf', [status(esa)], [t1_subset])).
% 1.06/1.25  thf('159', plain,
% 1.06/1.25      (((m1_subset_1 @ (sk_B @ sk_B_1) @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['157', '158'])).
% 1.06/1.25  thf('160', plain,
% 1.06/1.25      (![X23 : $i, X24 : $i]:
% 1.06/1.25         ((v1_xboole_0 @ X23)
% 1.06/1.25          | ~ (m1_subset_1 @ X24 @ X23)
% 1.06/1.25          | ((k6_domain_1 @ X23 @ X24) = (k1_tarski @ X24)))),
% 1.06/1.25      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 1.06/1.25  thf('161', plain,
% 1.06/1.25      (((((k6_domain_1 @ sk_B_1 @ (sk_B @ sk_B_1))
% 1.06/1.25           = (k1_tarski @ (sk_B @ sk_B_1)))
% 1.06/1.25         | (v1_xboole_0 @ sk_B_1))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['159', '160'])).
% 1.06/1.25  thf('162', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('163', plain,
% 1.06/1.25      ((((k6_domain_1 @ sk_B_1 @ (sk_B @ sk_B_1))
% 1.06/1.25          = (k1_tarski @ (sk_B @ sk_B_1))))
% 1.06/1.25         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 1.06/1.25      inference('clc', [status(thm)], ['161', '162'])).
% 1.06/1.25  thf('164', plain,
% 1.06/1.25      (((((sk_B_1) = (k1_tarski @ (sk_B @ sk_B_1)))
% 1.06/1.25         | (v1_xboole_0 @ sk_B_1)
% 1.06/1.25         | ~ (v1_zfmisc_1 @ sk_B_1))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 1.06/1.25      inference('sup+', [status(thm)], ['89', '163'])).
% 1.06/1.25  thf('165', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 1.06/1.25      inference('split', [status(esa)], ['2'])).
% 1.06/1.25  thf('166', plain,
% 1.06/1.25      (((((sk_B_1) = (k1_tarski @ (sk_B @ sk_B_1))) | (v1_xboole_0 @ sk_B_1)))
% 1.06/1.25         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 1.06/1.25      inference('demod', [status(thm)], ['164', '165'])).
% 1.06/1.25  thf('167', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('168', plain,
% 1.06/1.25      ((((sk_B_1) = (k1_tarski @ (sk_B @ sk_B_1))))
% 1.06/1.25         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 1.06/1.25      inference('clc', [status(thm)], ['166', '167'])).
% 1.06/1.25  thf('169', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 1.06/1.25      inference('sup-', [status(thm)], ['118', '119'])).
% 1.06/1.25  thf(dt_k1_tex_2, axiom,
% 1.06/1.25    (![A:$i,B:$i]:
% 1.06/1.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 1.06/1.25         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.25       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 1.06/1.25         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 1.06/1.25         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 1.06/1.25  thf('170', plain,
% 1.06/1.25      (![X35 : $i, X36 : $i]:
% 1.06/1.25         (~ (l1_pre_topc @ X35)
% 1.06/1.25          | (v2_struct_0 @ X35)
% 1.06/1.25          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X35))
% 1.06/1.25          | (m1_pre_topc @ (k1_tex_2 @ X35 @ X36) @ X35))),
% 1.06/1.25      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 1.06/1.25  thf('171', plain,
% 1.06/1.25      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)) @ sk_A)
% 1.06/1.25        | (v2_struct_0 @ sk_A)
% 1.06/1.25        | ~ (l1_pre_topc @ sk_A))),
% 1.06/1.25      inference('sup-', [status(thm)], ['169', '170'])).
% 1.06/1.25  thf('172', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('173', plain,
% 1.06/1.25      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)) @ sk_A)
% 1.06/1.25        | (v2_struct_0 @ sk_A))),
% 1.06/1.25      inference('demod', [status(thm)], ['171', '172'])).
% 1.06/1.25  thf('174', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('175', plain,
% 1.06/1.25      ((m1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)) @ sk_A)),
% 1.06/1.25      inference('clc', [status(thm)], ['173', '174'])).
% 1.06/1.25  thf(t1_tsep_1, axiom,
% 1.06/1.25    (![A:$i]:
% 1.06/1.25     ( ( l1_pre_topc @ A ) =>
% 1.06/1.25       ( ![B:$i]:
% 1.06/1.25         ( ( m1_pre_topc @ B @ A ) =>
% 1.06/1.25           ( m1_subset_1 @
% 1.06/1.25             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 1.06/1.25  thf('176', plain,
% 1.06/1.25      (![X25 : $i, X26 : $i]:
% 1.06/1.25         (~ (m1_pre_topc @ X25 @ X26)
% 1.06/1.25          | (m1_subset_1 @ (u1_struct_0 @ X25) @ 
% 1.06/1.25             (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 1.06/1.25          | ~ (l1_pre_topc @ X26))),
% 1.06/1.25      inference('cnf', [status(esa)], [t1_tsep_1])).
% 1.06/1.25  thf('177', plain,
% 1.06/1.25      ((~ (l1_pre_topc @ sk_A)
% 1.06/1.25        | (m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1))) @ 
% 1.06/1.25           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.06/1.25      inference('sup-', [status(thm)], ['175', '176'])).
% 1.06/1.25  thf('178', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('179', plain,
% 1.06/1.25      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1))) @ 
% 1.06/1.25        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.25      inference('demod', [status(thm)], ['177', '178'])).
% 1.06/1.25  thf(t26_tex_2, axiom,
% 1.06/1.25    (![A:$i]:
% 1.06/1.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.25       ( ![B:$i]:
% 1.06/1.25         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.06/1.25           ( ![C:$i]:
% 1.06/1.25             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.25               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 1.06/1.25                 ( ( v2_tex_2 @ C @ A ) <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) ) ))).
% 1.06/1.25  thf('180', plain,
% 1.06/1.25      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.06/1.25         ((v2_struct_0 @ X41)
% 1.06/1.25          | ~ (m1_pre_topc @ X41 @ X42)
% 1.06/1.25          | ((X43) != (u1_struct_0 @ X41))
% 1.06/1.25          | ~ (v1_tdlat_3 @ X41)
% 1.06/1.25          | (v2_tex_2 @ X43 @ X42)
% 1.06/1.25          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 1.06/1.25          | ~ (l1_pre_topc @ X42)
% 1.06/1.25          | (v2_struct_0 @ X42))),
% 1.06/1.25      inference('cnf', [status(esa)], [t26_tex_2])).
% 1.06/1.25  thf('181', plain,
% 1.06/1.25      (![X41 : $i, X42 : $i]:
% 1.06/1.25         ((v2_struct_0 @ X42)
% 1.06/1.25          | ~ (l1_pre_topc @ X42)
% 1.06/1.25          | ~ (m1_subset_1 @ (u1_struct_0 @ X41) @ 
% 1.06/1.25               (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 1.06/1.25          | (v2_tex_2 @ (u1_struct_0 @ X41) @ X42)
% 1.06/1.25          | ~ (v1_tdlat_3 @ X41)
% 1.06/1.25          | ~ (m1_pre_topc @ X41 @ X42)
% 1.06/1.25          | (v2_struct_0 @ X41))),
% 1.06/1.25      inference('simplify', [status(thm)], ['180'])).
% 1.06/1.25  thf('182', plain,
% 1.06/1.25      (((v2_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 1.06/1.25        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)) @ sk_A)
% 1.06/1.25        | ~ (v1_tdlat_3 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 1.06/1.25        | (v2_tex_2 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1))) @ 
% 1.06/1.25           sk_A)
% 1.06/1.25        | ~ (l1_pre_topc @ sk_A)
% 1.06/1.25        | (v2_struct_0 @ sk_A))),
% 1.06/1.25      inference('sup-', [status(thm)], ['179', '181'])).
% 1.06/1.25  thf('183', plain,
% 1.06/1.25      ((m1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)) @ sk_A)),
% 1.06/1.25      inference('clc', [status(thm)], ['173', '174'])).
% 1.06/1.25  thf('184', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('185', plain,
% 1.06/1.25      (((v2_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 1.06/1.25        | ~ (v1_tdlat_3 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 1.06/1.25        | (v2_tex_2 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1))) @ 
% 1.06/1.25           sk_A)
% 1.06/1.25        | (v2_struct_0 @ sk_A))),
% 1.06/1.25      inference('demod', [status(thm)], ['182', '183', '184'])).
% 1.06/1.25  thf('186', plain,
% 1.06/1.25      ((m1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)) @ sk_A)),
% 1.06/1.25      inference('clc', [status(thm)], ['173', '174'])).
% 1.06/1.25  thf(cc25_tex_2, axiom,
% 1.06/1.25    (![A:$i]:
% 1.06/1.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.25       ( ![B:$i]:
% 1.06/1.25         ( ( m1_pre_topc @ B @ A ) =>
% 1.06/1.25           ( ( ( ~( v2_struct_0 @ B ) ) & ( v7_struct_0 @ B ) & 
% 1.06/1.25               ( v2_pre_topc @ B ) ) =>
% 1.06/1.25             ( ( ~( v2_struct_0 @ B ) ) & ( v1_tdlat_3 @ B ) & 
% 1.06/1.25               ( v2_tdlat_3 @ B ) ) ) ) ) ))).
% 1.06/1.25  thf('187', plain,
% 1.06/1.25      (![X27 : $i, X28 : $i]:
% 1.06/1.25         (~ (m1_pre_topc @ X27 @ X28)
% 1.06/1.25          | (v1_tdlat_3 @ X27)
% 1.06/1.25          | ~ (v2_pre_topc @ X27)
% 1.06/1.25          | ~ (v7_struct_0 @ X27)
% 1.06/1.25          | (v2_struct_0 @ X27)
% 1.06/1.25          | ~ (l1_pre_topc @ X28)
% 1.06/1.25          | (v2_struct_0 @ X28))),
% 1.06/1.25      inference('cnf', [status(esa)], [cc25_tex_2])).
% 1.06/1.25  thf('188', plain,
% 1.06/1.25      (((v2_struct_0 @ sk_A)
% 1.06/1.25        | ~ (l1_pre_topc @ sk_A)
% 1.06/1.25        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 1.06/1.25        | ~ (v7_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 1.06/1.25        | ~ (v2_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 1.06/1.25        | (v1_tdlat_3 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1))))),
% 1.06/1.25      inference('sup-', [status(thm)], ['186', '187'])).
% 1.06/1.25  thf('189', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('190', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 1.06/1.25      inference('sup-', [status(thm)], ['118', '119'])).
% 1.06/1.25  thf(fc2_tex_2, axiom,
% 1.06/1.25    (![A:$i,B:$i]:
% 1.06/1.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 1.06/1.25         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.25       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 1.06/1.25         ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) ) & 
% 1.06/1.25         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ))).
% 1.06/1.25  thf('191', plain,
% 1.06/1.25      (![X37 : $i, X38 : $i]:
% 1.06/1.25         (~ (l1_pre_topc @ X37)
% 1.06/1.25          | (v2_struct_0 @ X37)
% 1.06/1.25          | ~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X37))
% 1.06/1.25          | (v7_struct_0 @ (k1_tex_2 @ X37 @ X38)))),
% 1.06/1.25      inference('cnf', [status(esa)], [fc2_tex_2])).
% 1.06/1.25  thf('192', plain,
% 1.06/1.25      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 1.06/1.25        | (v2_struct_0 @ sk_A)
% 1.06/1.25        | ~ (l1_pre_topc @ sk_A))),
% 1.06/1.25      inference('sup-', [status(thm)], ['190', '191'])).
% 1.06/1.25  thf('193', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('194', plain,
% 1.06/1.25      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 1.06/1.25        | (v2_struct_0 @ sk_A))),
% 1.06/1.25      inference('demod', [status(thm)], ['192', '193'])).
% 1.06/1.25  thf('195', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('196', plain, ((v7_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))),
% 1.06/1.25      inference('clc', [status(thm)], ['194', '195'])).
% 1.06/1.25  thf('197', plain,
% 1.06/1.25      (((v2_struct_0 @ sk_A)
% 1.06/1.25        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 1.06/1.25        | ~ (v2_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 1.06/1.25        | (v1_tdlat_3 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1))))),
% 1.06/1.25      inference('demod', [status(thm)], ['188', '189', '196'])).
% 1.06/1.25  thf('198', plain,
% 1.06/1.25      ((m1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)) @ sk_A)),
% 1.06/1.25      inference('clc', [status(thm)], ['173', '174'])).
% 1.06/1.25  thf(cc1_pre_topc, axiom,
% 1.06/1.25    (![A:$i]:
% 1.06/1.25     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.25       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 1.06/1.25  thf('199', plain,
% 1.06/1.25      (![X17 : $i, X18 : $i]:
% 1.06/1.25         (~ (m1_pre_topc @ X17 @ X18)
% 1.06/1.25          | (v2_pre_topc @ X17)
% 1.06/1.25          | ~ (l1_pre_topc @ X18)
% 1.06/1.25          | ~ (v2_pre_topc @ X18))),
% 1.06/1.25      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 1.06/1.25  thf('200', plain,
% 1.06/1.25      ((~ (v2_pre_topc @ sk_A)
% 1.06/1.25        | ~ (l1_pre_topc @ sk_A)
% 1.06/1.25        | (v2_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1))))),
% 1.06/1.25      inference('sup-', [status(thm)], ['198', '199'])).
% 1.06/1.25  thf('201', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('202', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('203', plain, ((v2_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))),
% 1.06/1.25      inference('demod', [status(thm)], ['200', '201', '202'])).
% 1.06/1.25  thf('204', plain,
% 1.06/1.25      (((v2_struct_0 @ sk_A)
% 1.06/1.25        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 1.06/1.25        | (v1_tdlat_3 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1))))),
% 1.06/1.25      inference('demod', [status(thm)], ['197', '203'])).
% 1.06/1.25  thf('205', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('206', plain,
% 1.06/1.25      (((v1_tdlat_3 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 1.06/1.25        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1))))),
% 1.06/1.25      inference('clc', [status(thm)], ['204', '205'])).
% 1.06/1.25  thf('207', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 1.06/1.25      inference('sup-', [status(thm)], ['118', '119'])).
% 1.06/1.25  thf('208', plain,
% 1.06/1.25      (![X35 : $i, X36 : $i]:
% 1.06/1.25         (~ (l1_pre_topc @ X35)
% 1.06/1.25          | (v2_struct_0 @ X35)
% 1.06/1.25          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X35))
% 1.06/1.25          | ~ (v2_struct_0 @ (k1_tex_2 @ X35 @ X36)))),
% 1.06/1.25      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 1.06/1.25  thf('209', plain,
% 1.06/1.25      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 1.06/1.25        | (v2_struct_0 @ sk_A)
% 1.06/1.25        | ~ (l1_pre_topc @ sk_A))),
% 1.06/1.25      inference('sup-', [status(thm)], ['207', '208'])).
% 1.06/1.25  thf('210', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('211', plain,
% 1.06/1.25      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 1.06/1.25        | (v2_struct_0 @ sk_A))),
% 1.06/1.25      inference('demod', [status(thm)], ['209', '210'])).
% 1.06/1.25  thf('212', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('213', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))),
% 1.06/1.25      inference('clc', [status(thm)], ['211', '212'])).
% 1.06/1.25  thf('214', plain, ((v1_tdlat_3 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))),
% 1.06/1.25      inference('clc', [status(thm)], ['206', '213'])).
% 1.06/1.25  thf('215', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 1.06/1.25      inference('sup-', [status(thm)], ['118', '119'])).
% 1.06/1.25  thf('216', plain,
% 1.06/1.25      (![X35 : $i, X36 : $i]:
% 1.06/1.25         (~ (l1_pre_topc @ X35)
% 1.06/1.25          | (v2_struct_0 @ X35)
% 1.06/1.25          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X35))
% 1.06/1.25          | (v1_pre_topc @ (k1_tex_2 @ X35 @ X36)))),
% 1.06/1.25      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 1.06/1.25  thf('217', plain,
% 1.06/1.25      (((v1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 1.06/1.25        | (v2_struct_0 @ sk_A)
% 1.06/1.25        | ~ (l1_pre_topc @ sk_A))),
% 1.06/1.25      inference('sup-', [status(thm)], ['215', '216'])).
% 1.06/1.25  thf('218', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('219', plain,
% 1.06/1.25      (((v1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 1.06/1.25        | (v2_struct_0 @ sk_A))),
% 1.06/1.25      inference('demod', [status(thm)], ['217', '218'])).
% 1.06/1.25  thf('220', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('221', plain, ((v1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))),
% 1.06/1.25      inference('clc', [status(thm)], ['219', '220'])).
% 1.06/1.25  thf(d4_tex_2, axiom,
% 1.06/1.25    (![A:$i]:
% 1.06/1.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.25       ( ![B:$i]:
% 1.06/1.25         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.06/1.25           ( ![C:$i]:
% 1.06/1.25             ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 1.06/1.25                 ( m1_pre_topc @ C @ A ) ) =>
% 1.06/1.25               ( ( ( C ) = ( k1_tex_2 @ A @ B ) ) <=>
% 1.06/1.25                 ( ( u1_struct_0 @ C ) =
% 1.06/1.25                   ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) ))).
% 1.06/1.25  thf('222', plain,
% 1.06/1.25      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.06/1.25         (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X33))
% 1.06/1.25          | ((X34) != (k1_tex_2 @ X33 @ X32))
% 1.06/1.25          | ((u1_struct_0 @ X34) = (k6_domain_1 @ (u1_struct_0 @ X33) @ X32))
% 1.06/1.25          | ~ (m1_pre_topc @ X34 @ X33)
% 1.06/1.25          | ~ (v1_pre_topc @ X34)
% 1.06/1.25          | (v2_struct_0 @ X34)
% 1.06/1.25          | ~ (l1_pre_topc @ X33)
% 1.06/1.25          | (v2_struct_0 @ X33))),
% 1.06/1.25      inference('cnf', [status(esa)], [d4_tex_2])).
% 1.06/1.25  thf('223', plain,
% 1.06/1.25      (![X32 : $i, X33 : $i]:
% 1.06/1.25         ((v2_struct_0 @ X33)
% 1.06/1.25          | ~ (l1_pre_topc @ X33)
% 1.06/1.25          | (v2_struct_0 @ (k1_tex_2 @ X33 @ X32))
% 1.06/1.25          | ~ (v1_pre_topc @ (k1_tex_2 @ X33 @ X32))
% 1.06/1.25          | ~ (m1_pre_topc @ (k1_tex_2 @ X33 @ X32) @ X33)
% 1.06/1.25          | ((u1_struct_0 @ (k1_tex_2 @ X33 @ X32))
% 1.06/1.25              = (k6_domain_1 @ (u1_struct_0 @ X33) @ X32))
% 1.06/1.25          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X33)))),
% 1.06/1.25      inference('simplify', [status(thm)], ['222'])).
% 1.06/1.25  thf('224', plain,
% 1.06/1.25      ((~ (m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 1.06/1.25        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 1.06/1.25            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)))
% 1.06/1.25        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)) @ sk_A)
% 1.06/1.25        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 1.06/1.25        | ~ (l1_pre_topc @ sk_A)
% 1.06/1.25        | (v2_struct_0 @ sk_A))),
% 1.06/1.25      inference('sup-', [status(thm)], ['221', '223'])).
% 1.06/1.25  thf('225', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 1.06/1.25      inference('sup-', [status(thm)], ['118', '119'])).
% 1.06/1.25  thf('226', plain,
% 1.06/1.25      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 1.06/1.25         = (k1_tarski @ (sk_B @ sk_B_1)))),
% 1.06/1.25      inference('clc', [status(thm)], ['122', '123'])).
% 1.06/1.25  thf('227', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('228', plain,
% 1.06/1.25      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 1.06/1.25          = (k1_tarski @ (sk_B @ sk_B_1)))
% 1.06/1.25        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)) @ sk_A)
% 1.06/1.25        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 1.06/1.25        | (v2_struct_0 @ sk_A))),
% 1.06/1.25      inference('demod', [status(thm)], ['224', '225', '226', '227'])).
% 1.06/1.25  thf('229', plain,
% 1.06/1.25      ((m1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)) @ sk_A)),
% 1.06/1.25      inference('clc', [status(thm)], ['173', '174'])).
% 1.06/1.25  thf('230', plain,
% 1.06/1.25      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 1.06/1.25          = (k1_tarski @ (sk_B @ sk_B_1)))
% 1.06/1.25        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 1.06/1.25        | (v2_struct_0 @ sk_A))),
% 1.06/1.25      inference('demod', [status(thm)], ['228', '229'])).
% 1.06/1.25  thf('231', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))),
% 1.06/1.25      inference('clc', [status(thm)], ['211', '212'])).
% 1.06/1.25  thf('232', plain,
% 1.06/1.25      (((v2_struct_0 @ sk_A)
% 1.06/1.25        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 1.06/1.25            = (k1_tarski @ (sk_B @ sk_B_1))))),
% 1.06/1.25      inference('clc', [status(thm)], ['230', '231'])).
% 1.06/1.25  thf('233', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('234', plain,
% 1.06/1.25      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 1.06/1.25         = (k1_tarski @ (sk_B @ sk_B_1)))),
% 1.06/1.25      inference('clc', [status(thm)], ['232', '233'])).
% 1.06/1.25  thf('235', plain,
% 1.06/1.25      (((v2_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 1.06/1.25        | (v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A)
% 1.06/1.25        | (v2_struct_0 @ sk_A))),
% 1.06/1.25      inference('demod', [status(thm)], ['185', '214', '234'])).
% 1.06/1.25  thf('236', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))),
% 1.06/1.25      inference('clc', [status(thm)], ['211', '212'])).
% 1.06/1.25  thf('237', plain,
% 1.06/1.25      (((v2_struct_0 @ sk_A)
% 1.06/1.25        | (v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A))),
% 1.06/1.25      inference('clc', [status(thm)], ['235', '236'])).
% 1.06/1.25  thf('238', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('239', plain, ((v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A)),
% 1.06/1.25      inference('clc', [status(thm)], ['237', '238'])).
% 1.06/1.25  thf('240', plain,
% 1.06/1.25      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 1.06/1.25      inference('sup+', [status(thm)], ['168', '239'])).
% 1.06/1.25  thf('241', plain,
% 1.06/1.25      ((~ (v2_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.06/1.25      inference('split', [status(esa)], ['0'])).
% 1.06/1.25  thf('242', plain,
% 1.06/1.25      (~ ((v1_zfmisc_1 @ sk_B_1)) | ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 1.06/1.25      inference('sup-', [status(thm)], ['240', '241'])).
% 1.06/1.25  thf('243', plain, ($false),
% 1.06/1.25      inference('sat_resolution*', [status(thm)], ['1', '72', '73', '242'])).
% 1.06/1.25  
% 1.06/1.25  % SZS output end Refutation
% 1.06/1.25  
% 1.06/1.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
