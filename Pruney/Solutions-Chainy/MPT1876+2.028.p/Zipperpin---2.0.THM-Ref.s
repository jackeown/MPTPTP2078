%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5R1n5ql6rU

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:59 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 416 expanded)
%              Number of leaves         :   40 ( 131 expanded)
%              Depth                    :   19
%              Number of atoms          : 1187 (4833 expanded)
%              Number of equality atoms :   18 (  25 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

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
    ! [X32: $i,X33: $i] :
      ( ( v1_xboole_0 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( v2_tex_2 @ X32 @ X33 )
      | ( X32
        = ( u1_struct_0 @ ( sk_C_1 @ X32 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
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
    ! [X32: $i,X33: $i] :
      ( ( v1_xboole_0 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( v2_tex_2 @ X32 @ X33 )
      | ( m1_pre_topc @ ( sk_C_1 @ X32 @ X33 ) @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
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
    ( ( l1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

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

thf('37',plain,(
    ! [X27: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ~ ( v1_tdlat_3 @ X27 )
      | ~ ( v2_tdlat_3 @ X27 )
      | ( v7_struct_0 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[cc2_tex_1])).

thf('38',plain,
    ( ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v2_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v2_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('40',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X32: $i,X33: $i] :
      ( ( v1_xboole_0 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( v2_tex_2 @ X32 @ X33 )
      | ( v1_tdlat_3 @ ( sk_C_1 @ X32 @ X33 ) )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v2_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v2_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['38','50'])).

thf('52',plain,
    ( ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['26','27'])).

thf(cc6_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v2_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_tdlat_3 @ B ) ) ) )).

thf('53',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_pre_topc @ X28 @ X29 )
      | ( v2_tdlat_3 @ X28 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_tdlat_3 @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[cc6_tdlat_3])).

thf('54',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v2_tdlat_3 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55','56','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v2_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( l1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(cc1_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_tdlat_3 @ A )
       => ( v2_pre_topc @ A ) ) ) )).

thf('62',plain,(
    ! [X25: $i] :
      ( ~ ( v1_tdlat_3 @ X25 )
      | ( v2_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[cc1_tdlat_3])).

thf('63',plain,
    ( ( ( v2_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('65',plain,
    ( ( v2_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['51','60','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X32: $i,X33: $i] :
      ( ( v1_xboole_0 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( v2_tex_2 @ X32 @ X33 )
      | ~ ( v2_struct_0 @ ( sk_C_1 @ X32 @ X33 ) )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,
    ( ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['66','72'])).

thf('74',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('75',plain,
    ( ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['35','79'])).

thf('81',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
   <= ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('82',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('84',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['2'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('85',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('86',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X10 ) @ X12 )
      | ~ ( r2_hidden @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('88',plain,(
    ! [X30: $i,X31: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( v1_zfmisc_1 @ X30 )
      | ( X31 = X30 )
      | ~ ( r1_tarski @ X31 @ X30 )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('91',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('92',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_tarski @ ( k1_tarski @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('96',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','96'])).

thf('98',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('99',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('100',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('101',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('102',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['98','103'])).

thf('105',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['104','105'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('107',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ( m1_subset_1 @ X13 @ X14 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('109',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ X13 @ X14 )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['106','109'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('111',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X35 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X35 ) @ X34 ) @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('112',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['106','109'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('116',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ X23 )
      | ( ( k6_domain_1 @ X23 @ X24 )
        = ( k1_tarski @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('117',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('120',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
    = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['117','120'])).

thf('122',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['112','113','114','121'])).

thf('123',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['97','124'])).

thf('126',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['84','127'])).

thf('129',plain,
    ( ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('130',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','82','83','130'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5R1n5ql6rU
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:34:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.31/1.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.31/1.49  % Solved by: fo/fo7.sh
% 1.31/1.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.31/1.49  % done 1066 iterations in 1.034s
% 1.31/1.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.31/1.49  % SZS output start Refutation
% 1.31/1.49  thf(sk_A_type, type, sk_A: $i).
% 1.31/1.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.31/1.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.31/1.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.31/1.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.31/1.49  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 1.31/1.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.31/1.49  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.31/1.49  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 1.31/1.49  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 1.31/1.49  thf(sk_B_type, type, sk_B: $i > $i).
% 1.31/1.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.31/1.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.31/1.49  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.31/1.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.31/1.49  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 1.31/1.49  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 1.31/1.49  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 1.31/1.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.31/1.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.31/1.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.31/1.49  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 1.31/1.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.31/1.49  thf(t44_tex_2, conjecture,
% 1.31/1.49    (![A:$i]:
% 1.31/1.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 1.31/1.49         ( l1_pre_topc @ A ) ) =>
% 1.31/1.49       ( ![B:$i]:
% 1.31/1.49         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 1.31/1.49             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.31/1.49           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 1.31/1.49  thf(zf_stmt_0, negated_conjecture,
% 1.31/1.49    (~( ![A:$i]:
% 1.31/1.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.31/1.49            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.31/1.49          ( ![B:$i]:
% 1.31/1.49            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 1.31/1.49                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.31/1.49              ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 1.31/1.49    inference('cnf.neg', [status(esa)], [t44_tex_2])).
% 1.31/1.49  thf('0', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 1.31/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.49  thf('1', plain,
% 1.31/1.49      (~ ((v1_zfmisc_1 @ sk_B_1)) | ~ ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 1.31/1.49      inference('split', [status(esa)], ['0'])).
% 1.31/1.49  thf('2', plain, (((v1_zfmisc_1 @ sk_B_1) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 1.31/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.49  thf('3', plain,
% 1.31/1.49      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.31/1.49      inference('split', [status(esa)], ['2'])).
% 1.31/1.49  thf('4', plain,
% 1.31/1.49      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.31/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.49  thf(t34_tex_2, axiom,
% 1.31/1.49    (![A:$i]:
% 1.31/1.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.31/1.49       ( ![B:$i]:
% 1.31/1.49         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 1.31/1.49             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.31/1.49           ( ~( ( v2_tex_2 @ B @ A ) & 
% 1.31/1.49                ( ![C:$i]:
% 1.31/1.49                  ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 1.31/1.49                      ( v1_tdlat_3 @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.31/1.49                    ( ( B ) != ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ))).
% 1.31/1.49  thf('5', plain,
% 1.31/1.49      (![X32 : $i, X33 : $i]:
% 1.31/1.49         ((v1_xboole_0 @ X32)
% 1.31/1.49          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 1.31/1.49          | ~ (v2_tex_2 @ X32 @ X33)
% 1.31/1.49          | ((X32) = (u1_struct_0 @ (sk_C_1 @ X32 @ X33)))
% 1.31/1.49          | ~ (l1_pre_topc @ X33)
% 1.31/1.49          | ~ (v2_pre_topc @ X33)
% 1.31/1.49          | (v2_struct_0 @ X33))),
% 1.31/1.49      inference('cnf', [status(esa)], [t34_tex_2])).
% 1.31/1.49  thf('6', plain,
% 1.31/1.49      (((v2_struct_0 @ sk_A)
% 1.31/1.49        | ~ (v2_pre_topc @ sk_A)
% 1.31/1.49        | ~ (l1_pre_topc @ sk_A)
% 1.31/1.49        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 1.31/1.49        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 1.31/1.49        | (v1_xboole_0 @ sk_B_1))),
% 1.31/1.49      inference('sup-', [status(thm)], ['4', '5'])).
% 1.31/1.49  thf('7', plain, ((v2_pre_topc @ sk_A)),
% 1.31/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.49  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 1.31/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.49  thf('9', plain,
% 1.31/1.49      (((v2_struct_0 @ sk_A)
% 1.31/1.49        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 1.31/1.49        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 1.31/1.49        | (v1_xboole_0 @ sk_B_1))),
% 1.31/1.49      inference('demod', [status(thm)], ['6', '7', '8'])).
% 1.31/1.49  thf('10', plain,
% 1.31/1.49      ((((v1_xboole_0 @ sk_B_1)
% 1.31/1.49         | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 1.31/1.49         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.31/1.49      inference('sup-', [status(thm)], ['3', '9'])).
% 1.31/1.49  thf('11', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.31/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.49  thf('12', plain,
% 1.31/1.49      ((((v2_struct_0 @ sk_A)
% 1.31/1.49         | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))))
% 1.31/1.49         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.31/1.49      inference('clc', [status(thm)], ['10', '11'])).
% 1.31/1.49  thf('13', plain, (~ (v2_struct_0 @ sk_A)),
% 1.31/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.49  thf('14', plain,
% 1.31/1.49      ((((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 1.31/1.49         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.31/1.49      inference('clc', [status(thm)], ['12', '13'])).
% 1.31/1.49  thf(fc7_struct_0, axiom,
% 1.31/1.49    (![A:$i]:
% 1.31/1.49     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 1.31/1.49       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 1.31/1.49  thf('15', plain,
% 1.31/1.49      (![X22 : $i]:
% 1.31/1.49         ((v1_zfmisc_1 @ (u1_struct_0 @ X22))
% 1.31/1.49          | ~ (l1_struct_0 @ X22)
% 1.31/1.49          | ~ (v7_struct_0 @ X22))),
% 1.31/1.49      inference('cnf', [status(esa)], [fc7_struct_0])).
% 1.31/1.49  thf('16', plain,
% 1.31/1.49      ((((v1_zfmisc_1 @ sk_B_1)
% 1.31/1.49         | ~ (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.31/1.49         | ~ (l1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 1.31/1.49         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.31/1.49      inference('sup+', [status(thm)], ['14', '15'])).
% 1.31/1.49  thf('17', plain,
% 1.31/1.49      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.31/1.49      inference('split', [status(esa)], ['2'])).
% 1.31/1.49  thf('18', plain,
% 1.31/1.49      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.31/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.49  thf('19', plain,
% 1.31/1.49      (![X32 : $i, X33 : $i]:
% 1.31/1.49         ((v1_xboole_0 @ X32)
% 1.31/1.49          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 1.31/1.49          | ~ (v2_tex_2 @ X32 @ X33)
% 1.31/1.49          | (m1_pre_topc @ (sk_C_1 @ X32 @ X33) @ X33)
% 1.31/1.49          | ~ (l1_pre_topc @ X33)
% 1.31/1.49          | ~ (v2_pre_topc @ X33)
% 1.31/1.49          | (v2_struct_0 @ X33))),
% 1.31/1.49      inference('cnf', [status(esa)], [t34_tex_2])).
% 1.31/1.49  thf('20', plain,
% 1.31/1.49      (((v2_struct_0 @ sk_A)
% 1.31/1.49        | ~ (v2_pre_topc @ sk_A)
% 1.31/1.49        | ~ (l1_pre_topc @ sk_A)
% 1.31/1.49        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 1.31/1.49        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 1.31/1.49        | (v1_xboole_0 @ sk_B_1))),
% 1.31/1.49      inference('sup-', [status(thm)], ['18', '19'])).
% 1.31/1.49  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 1.31/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.49  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 1.31/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.49  thf('23', plain,
% 1.31/1.49      (((v2_struct_0 @ sk_A)
% 1.31/1.49        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 1.31/1.49        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 1.31/1.49        | (v1_xboole_0 @ sk_B_1))),
% 1.31/1.49      inference('demod', [status(thm)], ['20', '21', '22'])).
% 1.31/1.49  thf('24', plain,
% 1.31/1.49      ((((v1_xboole_0 @ sk_B_1)
% 1.31/1.49         | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 1.31/1.49         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.31/1.49      inference('sup-', [status(thm)], ['17', '23'])).
% 1.31/1.49  thf('25', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.31/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.49  thf('26', plain,
% 1.31/1.49      ((((v2_struct_0 @ sk_A) | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)))
% 1.31/1.49         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.31/1.49      inference('clc', [status(thm)], ['24', '25'])).
% 1.31/1.49  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 1.31/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.49  thf('28', plain,
% 1.31/1.49      (((m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A))
% 1.31/1.49         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.31/1.49      inference('clc', [status(thm)], ['26', '27'])).
% 1.31/1.49  thf(dt_m1_pre_topc, axiom,
% 1.31/1.49    (![A:$i]:
% 1.31/1.49     ( ( l1_pre_topc @ A ) =>
% 1.31/1.49       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.31/1.49  thf('29', plain,
% 1.31/1.49      (![X20 : $i, X21 : $i]:
% 1.31/1.49         (~ (m1_pre_topc @ X20 @ X21)
% 1.31/1.49          | (l1_pre_topc @ X20)
% 1.31/1.49          | ~ (l1_pre_topc @ X21))),
% 1.31/1.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.31/1.49  thf('30', plain,
% 1.31/1.49      (((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 1.31/1.49         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.31/1.49      inference('sup-', [status(thm)], ['28', '29'])).
% 1.31/1.49  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 1.31/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.49  thf('32', plain,
% 1.31/1.49      (((l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 1.31/1.49         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.31/1.49      inference('demod', [status(thm)], ['30', '31'])).
% 1.31/1.49  thf(dt_l1_pre_topc, axiom,
% 1.31/1.49    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.31/1.49  thf('33', plain,
% 1.31/1.49      (![X19 : $i]: ((l1_struct_0 @ X19) | ~ (l1_pre_topc @ X19))),
% 1.31/1.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.31/1.49  thf('34', plain,
% 1.31/1.49      (((l1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 1.31/1.49         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.31/1.49      inference('sup-', [status(thm)], ['32', '33'])).
% 1.31/1.49  thf('35', plain,
% 1.31/1.49      ((((v1_zfmisc_1 @ sk_B_1) | ~ (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 1.31/1.49         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.31/1.49      inference('demod', [status(thm)], ['16', '34'])).
% 1.31/1.49  thf('36', plain,
% 1.31/1.49      (((l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 1.31/1.49         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.31/1.49      inference('demod', [status(thm)], ['30', '31'])).
% 1.31/1.49  thf(cc2_tex_1, axiom,
% 1.31/1.49    (![A:$i]:
% 1.31/1.49     ( ( l1_pre_topc @ A ) =>
% 1.31/1.49       ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.31/1.49           ( v1_tdlat_3 @ A ) & ( v2_tdlat_3 @ A ) ) =>
% 1.31/1.49         ( ( ~( v2_struct_0 @ A ) ) & ( v7_struct_0 @ A ) & ( v2_pre_topc @ A ) ) ) ))).
% 1.31/1.49  thf('37', plain,
% 1.31/1.49      (![X27 : $i]:
% 1.31/1.49         ((v2_struct_0 @ X27)
% 1.31/1.49          | ~ (v2_pre_topc @ X27)
% 1.31/1.49          | ~ (v1_tdlat_3 @ X27)
% 1.31/1.49          | ~ (v2_tdlat_3 @ X27)
% 1.31/1.49          | (v7_struct_0 @ X27)
% 1.31/1.49          | ~ (l1_pre_topc @ X27))),
% 1.31/1.49      inference('cnf', [status(esa)], [cc2_tex_1])).
% 1.31/1.49  thf('38', plain,
% 1.31/1.49      ((((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.31/1.49         | ~ (v2_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.31/1.49         | ~ (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.31/1.49         | ~ (v2_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.31/1.49         | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 1.31/1.49         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.31/1.49      inference('sup-', [status(thm)], ['36', '37'])).
% 1.31/1.49  thf('39', plain,
% 1.31/1.49      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.31/1.49      inference('split', [status(esa)], ['2'])).
% 1.31/1.49  thf('40', plain,
% 1.31/1.49      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.31/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.49  thf('41', plain,
% 1.31/1.49      (![X32 : $i, X33 : $i]:
% 1.31/1.49         ((v1_xboole_0 @ X32)
% 1.31/1.49          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 1.31/1.49          | ~ (v2_tex_2 @ X32 @ X33)
% 1.31/1.49          | (v1_tdlat_3 @ (sk_C_1 @ X32 @ X33))
% 1.31/1.49          | ~ (l1_pre_topc @ X33)
% 1.31/1.49          | ~ (v2_pre_topc @ X33)
% 1.31/1.49          | (v2_struct_0 @ X33))),
% 1.31/1.49      inference('cnf', [status(esa)], [t34_tex_2])).
% 1.31/1.49  thf('42', plain,
% 1.31/1.49      (((v2_struct_0 @ sk_A)
% 1.31/1.49        | ~ (v2_pre_topc @ sk_A)
% 1.31/1.49        | ~ (l1_pre_topc @ sk_A)
% 1.31/1.49        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.31/1.49        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 1.31/1.49        | (v1_xboole_0 @ sk_B_1))),
% 1.31/1.49      inference('sup-', [status(thm)], ['40', '41'])).
% 1.31/1.49  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 1.31/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.49  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 1.31/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.49  thf('45', plain,
% 1.31/1.49      (((v2_struct_0 @ sk_A)
% 1.31/1.49        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.31/1.49        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 1.31/1.49        | (v1_xboole_0 @ sk_B_1))),
% 1.31/1.49      inference('demod', [status(thm)], ['42', '43', '44'])).
% 1.31/1.49  thf('46', plain,
% 1.31/1.49      ((((v1_xboole_0 @ sk_B_1)
% 1.31/1.49         | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.31/1.49         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.31/1.49      inference('sup-', [status(thm)], ['39', '45'])).
% 1.31/1.49  thf('47', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.31/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.49  thf('48', plain,
% 1.31/1.49      ((((v2_struct_0 @ sk_A) | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 1.31/1.49         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.31/1.49      inference('clc', [status(thm)], ['46', '47'])).
% 1.31/1.49  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 1.31/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.49  thf('50', plain,
% 1.31/1.49      (((v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 1.31/1.49         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.31/1.49      inference('clc', [status(thm)], ['48', '49'])).
% 1.31/1.49  thf('51', plain,
% 1.31/1.49      ((((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.31/1.49         | ~ (v2_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.31/1.49         | ~ (v2_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.31/1.49         | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 1.31/1.49         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.31/1.49      inference('demod', [status(thm)], ['38', '50'])).
% 1.31/1.49  thf('52', plain,
% 1.31/1.49      (((m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A))
% 1.31/1.49         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.31/1.49      inference('clc', [status(thm)], ['26', '27'])).
% 1.31/1.49  thf(cc6_tdlat_3, axiom,
% 1.31/1.49    (![A:$i]:
% 1.31/1.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 1.31/1.49         ( l1_pre_topc @ A ) ) =>
% 1.31/1.49       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_tdlat_3 @ B ) ) ) ))).
% 1.31/1.49  thf('53', plain,
% 1.31/1.49      (![X28 : $i, X29 : $i]:
% 1.31/1.49         (~ (m1_pre_topc @ X28 @ X29)
% 1.31/1.49          | (v2_tdlat_3 @ X28)
% 1.31/1.49          | ~ (l1_pre_topc @ X29)
% 1.31/1.49          | ~ (v2_tdlat_3 @ X29)
% 1.31/1.49          | ~ (v2_pre_topc @ X29)
% 1.31/1.49          | (v2_struct_0 @ X29))),
% 1.31/1.49      inference('cnf', [status(esa)], [cc6_tdlat_3])).
% 1.31/1.49  thf('54', plain,
% 1.31/1.49      ((((v2_struct_0 @ sk_A)
% 1.31/1.49         | ~ (v2_pre_topc @ sk_A)
% 1.31/1.49         | ~ (v2_tdlat_3 @ sk_A)
% 1.31/1.49         | ~ (l1_pre_topc @ sk_A)
% 1.31/1.49         | (v2_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 1.31/1.49         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.31/1.49      inference('sup-', [status(thm)], ['52', '53'])).
% 1.31/1.49  thf('55', plain, ((v2_pre_topc @ sk_A)),
% 1.31/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.49  thf('56', plain, ((v2_tdlat_3 @ sk_A)),
% 1.31/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.49  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 1.31/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.49  thf('58', plain,
% 1.31/1.49      ((((v2_struct_0 @ sk_A) | (v2_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 1.31/1.49         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.31/1.49      inference('demod', [status(thm)], ['54', '55', '56', '57'])).
% 1.31/1.49  thf('59', plain, (~ (v2_struct_0 @ sk_A)),
% 1.31/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.49  thf('60', plain,
% 1.31/1.49      (((v2_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 1.31/1.49         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.31/1.49      inference('clc', [status(thm)], ['58', '59'])).
% 1.31/1.49  thf('61', plain,
% 1.31/1.49      (((l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 1.31/1.49         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.31/1.49      inference('demod', [status(thm)], ['30', '31'])).
% 1.31/1.49  thf(cc1_tdlat_3, axiom,
% 1.31/1.49    (![A:$i]:
% 1.31/1.49     ( ( l1_pre_topc @ A ) => ( ( v1_tdlat_3 @ A ) => ( v2_pre_topc @ A ) ) ))).
% 1.31/1.49  thf('62', plain,
% 1.31/1.49      (![X25 : $i]:
% 1.31/1.49         (~ (v1_tdlat_3 @ X25) | (v2_pre_topc @ X25) | ~ (l1_pre_topc @ X25))),
% 1.31/1.49      inference('cnf', [status(esa)], [cc1_tdlat_3])).
% 1.31/1.49  thf('63', plain,
% 1.31/1.49      ((((v2_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.31/1.49         | ~ (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 1.31/1.49         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.31/1.49      inference('sup-', [status(thm)], ['61', '62'])).
% 1.31/1.49  thf('64', plain,
% 1.31/1.49      (((v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 1.31/1.49         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.31/1.49      inference('clc', [status(thm)], ['48', '49'])).
% 1.31/1.49  thf('65', plain,
% 1.31/1.49      (((v2_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 1.31/1.49         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.31/1.49      inference('demod', [status(thm)], ['63', '64'])).
% 1.31/1.49  thf('66', plain,
% 1.31/1.49      ((((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.31/1.49         | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 1.31/1.49         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.31/1.49      inference('demod', [status(thm)], ['51', '60', '65'])).
% 1.31/1.49  thf('67', plain,
% 1.31/1.49      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.31/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.49  thf('68', plain,
% 1.31/1.49      (![X32 : $i, X33 : $i]:
% 1.31/1.49         ((v1_xboole_0 @ X32)
% 1.31/1.49          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 1.31/1.49          | ~ (v2_tex_2 @ X32 @ X33)
% 1.31/1.49          | ~ (v2_struct_0 @ (sk_C_1 @ X32 @ X33))
% 1.31/1.49          | ~ (l1_pre_topc @ X33)
% 1.31/1.49          | ~ (v2_pre_topc @ X33)
% 1.31/1.49          | (v2_struct_0 @ X33))),
% 1.31/1.49      inference('cnf', [status(esa)], [t34_tex_2])).
% 1.31/1.49  thf('69', plain,
% 1.31/1.49      (((v2_struct_0 @ sk_A)
% 1.31/1.49        | ~ (v2_pre_topc @ sk_A)
% 1.31/1.49        | ~ (l1_pre_topc @ sk_A)
% 1.31/1.49        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.31/1.49        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 1.31/1.49        | (v1_xboole_0 @ sk_B_1))),
% 1.31/1.49      inference('sup-', [status(thm)], ['67', '68'])).
% 1.31/1.49  thf('70', plain, ((v2_pre_topc @ sk_A)),
% 1.31/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.49  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 1.31/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.49  thf('72', plain,
% 1.31/1.49      (((v2_struct_0 @ sk_A)
% 1.31/1.49        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.31/1.49        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 1.31/1.49        | (v1_xboole_0 @ sk_B_1))),
% 1.31/1.49      inference('demod', [status(thm)], ['69', '70', '71'])).
% 1.31/1.49  thf('73', plain,
% 1.31/1.49      ((((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.31/1.49         | (v1_xboole_0 @ sk_B_1)
% 1.31/1.49         | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 1.31/1.49         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.31/1.49      inference('sup-', [status(thm)], ['66', '72'])).
% 1.31/1.49  thf('74', plain,
% 1.31/1.49      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.31/1.49      inference('split', [status(esa)], ['2'])).
% 1.31/1.49  thf('75', plain,
% 1.31/1.49      ((((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.31/1.49         | (v1_xboole_0 @ sk_B_1)
% 1.31/1.49         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.31/1.49      inference('demod', [status(thm)], ['73', '74'])).
% 1.31/1.49  thf('76', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.31/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.49  thf('77', plain,
% 1.31/1.49      ((((v2_struct_0 @ sk_A) | (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 1.31/1.49         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.31/1.49      inference('clc', [status(thm)], ['75', '76'])).
% 1.31/1.49  thf('78', plain, (~ (v2_struct_0 @ sk_A)),
% 1.31/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.49  thf('79', plain,
% 1.31/1.49      (((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 1.31/1.49         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.31/1.49      inference('clc', [status(thm)], ['77', '78'])).
% 1.31/1.49  thf('80', plain,
% 1.31/1.49      (((v1_zfmisc_1 @ sk_B_1)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.31/1.49      inference('demod', [status(thm)], ['35', '79'])).
% 1.31/1.49  thf('81', plain,
% 1.31/1.49      ((~ (v1_zfmisc_1 @ sk_B_1)) <= (~ ((v1_zfmisc_1 @ sk_B_1)))),
% 1.31/1.49      inference('split', [status(esa)], ['0'])).
% 1.31/1.49  thf('82', plain, (((v1_zfmisc_1 @ sk_B_1)) | ~ ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 1.31/1.49      inference('sup-', [status(thm)], ['80', '81'])).
% 1.31/1.49  thf('83', plain, (((v1_zfmisc_1 @ sk_B_1)) | ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 1.31/1.49      inference('split', [status(esa)], ['2'])).
% 1.31/1.49  thf('84', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 1.31/1.49      inference('split', [status(esa)], ['2'])).
% 1.31/1.49  thf(d1_xboole_0, axiom,
% 1.31/1.49    (![A:$i]:
% 1.31/1.49     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.31/1.49  thf('85', plain,
% 1.31/1.49      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.31/1.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.31/1.49  thf(l1_zfmisc_1, axiom,
% 1.31/1.49    (![A:$i,B:$i]:
% 1.31/1.49     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 1.31/1.49  thf('86', plain,
% 1.31/1.49      (![X10 : $i, X12 : $i]:
% 1.31/1.49         ((r1_tarski @ (k1_tarski @ X10) @ X12) | ~ (r2_hidden @ X10 @ X12))),
% 1.31/1.49      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.31/1.49  thf('87', plain,
% 1.31/1.49      (![X0 : $i]:
% 1.31/1.49         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 1.31/1.49      inference('sup-', [status(thm)], ['85', '86'])).
% 1.31/1.49  thf(t1_tex_2, axiom,
% 1.31/1.49    (![A:$i]:
% 1.31/1.49     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.31/1.49       ( ![B:$i]:
% 1.31/1.49         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 1.31/1.49           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 1.31/1.49  thf('88', plain,
% 1.31/1.49      (![X30 : $i, X31 : $i]:
% 1.31/1.49         ((v1_xboole_0 @ X30)
% 1.31/1.49          | ~ (v1_zfmisc_1 @ X30)
% 1.31/1.49          | ((X31) = (X30))
% 1.31/1.49          | ~ (r1_tarski @ X31 @ X30)
% 1.31/1.49          | (v1_xboole_0 @ X31))),
% 1.31/1.49      inference('cnf', [status(esa)], [t1_tex_2])).
% 1.31/1.49  thf('89', plain,
% 1.31/1.49      (![X0 : $i]:
% 1.31/1.49         ((v1_xboole_0 @ X0)
% 1.31/1.49          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 1.31/1.49          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 1.31/1.49          | ~ (v1_zfmisc_1 @ X0)
% 1.31/1.49          | (v1_xboole_0 @ X0))),
% 1.31/1.49      inference('sup-', [status(thm)], ['87', '88'])).
% 1.31/1.49  thf('90', plain,
% 1.31/1.49      (![X0 : $i]:
% 1.31/1.49         (~ (v1_zfmisc_1 @ X0)
% 1.31/1.49          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 1.31/1.49          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 1.31/1.49          | (v1_xboole_0 @ X0))),
% 1.31/1.49      inference('simplify', [status(thm)], ['89'])).
% 1.31/1.49  thf(d10_xboole_0, axiom,
% 1.31/1.49    (![A:$i,B:$i]:
% 1.31/1.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.31/1.49  thf('91', plain,
% 1.31/1.49      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 1.31/1.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.31/1.49  thf('92', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 1.31/1.49      inference('simplify', [status(thm)], ['91'])).
% 1.31/1.49  thf('93', plain,
% 1.31/1.49      (![X10 : $i, X11 : $i]:
% 1.31/1.49         ((r2_hidden @ X10 @ X11) | ~ (r1_tarski @ (k1_tarski @ X10) @ X11))),
% 1.31/1.49      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.31/1.49  thf('94', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.31/1.49      inference('sup-', [status(thm)], ['92', '93'])).
% 1.31/1.49  thf('95', plain,
% 1.31/1.49      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.31/1.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.31/1.49  thf('96', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 1.31/1.49      inference('sup-', [status(thm)], ['94', '95'])).
% 1.31/1.49  thf('97', plain,
% 1.31/1.49      (![X0 : $i]:
% 1.31/1.49         ((v1_xboole_0 @ X0)
% 1.31/1.49          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 1.31/1.49          | ~ (v1_zfmisc_1 @ X0))),
% 1.31/1.49      inference('sup-', [status(thm)], ['90', '96'])).
% 1.31/1.49  thf('98', plain,
% 1.31/1.49      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.31/1.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.31/1.49  thf('99', plain,
% 1.31/1.49      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.31/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.49  thf(t3_subset, axiom,
% 1.31/1.49    (![A:$i,B:$i]:
% 1.31/1.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.31/1.49  thf('100', plain,
% 1.31/1.49      (![X16 : $i, X17 : $i]:
% 1.31/1.49         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 1.31/1.49      inference('cnf', [status(esa)], [t3_subset])).
% 1.31/1.49  thf('101', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 1.31/1.49      inference('sup-', [status(thm)], ['99', '100'])).
% 1.31/1.49  thf(d3_tarski, axiom,
% 1.31/1.49    (![A:$i,B:$i]:
% 1.31/1.49     ( ( r1_tarski @ A @ B ) <=>
% 1.31/1.49       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.31/1.49  thf('102', plain,
% 1.31/1.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.31/1.49         (~ (r2_hidden @ X3 @ X4)
% 1.31/1.49          | (r2_hidden @ X3 @ X5)
% 1.31/1.49          | ~ (r1_tarski @ X4 @ X5))),
% 1.31/1.49      inference('cnf', [status(esa)], [d3_tarski])).
% 1.31/1.49  thf('103', plain,
% 1.31/1.49      (![X0 : $i]:
% 1.31/1.49         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 1.31/1.49      inference('sup-', [status(thm)], ['101', '102'])).
% 1.31/1.49  thf('104', plain,
% 1.31/1.49      (((v1_xboole_0 @ sk_B_1)
% 1.31/1.49        | (r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 1.31/1.49      inference('sup-', [status(thm)], ['98', '103'])).
% 1.31/1.49  thf('105', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.31/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.49  thf('106', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 1.31/1.49      inference('clc', [status(thm)], ['104', '105'])).
% 1.31/1.49  thf(d2_subset_1, axiom,
% 1.31/1.49    (![A:$i,B:$i]:
% 1.31/1.49     ( ( ( v1_xboole_0 @ A ) =>
% 1.31/1.49         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.31/1.49       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.31/1.49         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.31/1.49  thf('107', plain,
% 1.31/1.49      (![X13 : $i, X14 : $i]:
% 1.31/1.49         (~ (r2_hidden @ X13 @ X14)
% 1.31/1.49          | (m1_subset_1 @ X13 @ X14)
% 1.31/1.49          | (v1_xboole_0 @ X14))),
% 1.31/1.49      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.31/1.49  thf('108', plain,
% 1.31/1.49      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.31/1.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.31/1.49  thf('109', plain,
% 1.31/1.49      (![X13 : $i, X14 : $i]:
% 1.31/1.49         ((m1_subset_1 @ X13 @ X14) | ~ (r2_hidden @ X13 @ X14))),
% 1.31/1.49      inference('clc', [status(thm)], ['107', '108'])).
% 1.31/1.49  thf('110', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 1.31/1.49      inference('sup-', [status(thm)], ['106', '109'])).
% 1.31/1.49  thf(t36_tex_2, axiom,
% 1.31/1.49    (![A:$i]:
% 1.31/1.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.31/1.49       ( ![B:$i]:
% 1.31/1.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.31/1.49           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 1.31/1.49  thf('111', plain,
% 1.31/1.49      (![X34 : $i, X35 : $i]:
% 1.31/1.49         (~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X35))
% 1.31/1.49          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X35) @ X34) @ X35)
% 1.31/1.49          | ~ (l1_pre_topc @ X35)
% 1.31/1.49          | ~ (v2_pre_topc @ X35)
% 1.31/1.49          | (v2_struct_0 @ X35))),
% 1.31/1.49      inference('cnf', [status(esa)], [t36_tex_2])).
% 1.31/1.49  thf('112', plain,
% 1.31/1.49      (((v2_struct_0 @ sk_A)
% 1.31/1.49        | ~ (v2_pre_topc @ sk_A)
% 1.31/1.49        | ~ (l1_pre_topc @ sk_A)
% 1.31/1.49        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 1.31/1.49           sk_A))),
% 1.31/1.49      inference('sup-', [status(thm)], ['110', '111'])).
% 1.31/1.49  thf('113', plain, ((v2_pre_topc @ sk_A)),
% 1.31/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.49  thf('114', plain, ((l1_pre_topc @ sk_A)),
% 1.31/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.49  thf('115', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 1.31/1.49      inference('sup-', [status(thm)], ['106', '109'])).
% 1.31/1.49  thf(redefinition_k6_domain_1, axiom,
% 1.31/1.49    (![A:$i,B:$i]:
% 1.31/1.49     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 1.31/1.49       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 1.31/1.49  thf('116', plain,
% 1.31/1.49      (![X23 : $i, X24 : $i]:
% 1.31/1.49         ((v1_xboole_0 @ X23)
% 1.31/1.49          | ~ (m1_subset_1 @ X24 @ X23)
% 1.31/1.49          | ((k6_domain_1 @ X23 @ X24) = (k1_tarski @ X24)))),
% 1.31/1.49      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 1.31/1.49  thf('117', plain,
% 1.31/1.49      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 1.31/1.49          = (k1_tarski @ (sk_B @ sk_B_1)))
% 1.31/1.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.31/1.49      inference('sup-', [status(thm)], ['115', '116'])).
% 1.31/1.49  thf('118', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 1.31/1.49      inference('clc', [status(thm)], ['104', '105'])).
% 1.31/1.49  thf('119', plain,
% 1.31/1.49      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.31/1.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.31/1.49  thf('120', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 1.31/1.49      inference('sup-', [status(thm)], ['118', '119'])).
% 1.31/1.49  thf('121', plain,
% 1.31/1.49      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 1.31/1.49         = (k1_tarski @ (sk_B @ sk_B_1)))),
% 1.31/1.49      inference('clc', [status(thm)], ['117', '120'])).
% 1.31/1.49  thf('122', plain,
% 1.31/1.49      (((v2_struct_0 @ sk_A)
% 1.31/1.49        | (v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A))),
% 1.31/1.49      inference('demod', [status(thm)], ['112', '113', '114', '121'])).
% 1.31/1.49  thf('123', plain, (~ (v2_struct_0 @ sk_A)),
% 1.31/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.49  thf('124', plain, ((v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A)),
% 1.31/1.49      inference('clc', [status(thm)], ['122', '123'])).
% 1.31/1.49  thf('125', plain,
% 1.31/1.49      (((v2_tex_2 @ sk_B_1 @ sk_A)
% 1.31/1.49        | ~ (v1_zfmisc_1 @ sk_B_1)
% 1.31/1.49        | (v1_xboole_0 @ sk_B_1))),
% 1.31/1.49      inference('sup+', [status(thm)], ['97', '124'])).
% 1.31/1.49  thf('126', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.31/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.49  thf('127', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 1.31/1.49      inference('clc', [status(thm)], ['125', '126'])).
% 1.31/1.49  thf('128', plain,
% 1.31/1.49      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 1.31/1.49      inference('sup-', [status(thm)], ['84', '127'])).
% 1.31/1.49  thf('129', plain,
% 1.31/1.49      ((~ (v2_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.31/1.49      inference('split', [status(esa)], ['0'])).
% 1.31/1.49  thf('130', plain,
% 1.31/1.49      (~ ((v1_zfmisc_1 @ sk_B_1)) | ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 1.31/1.49      inference('sup-', [status(thm)], ['128', '129'])).
% 1.31/1.49  thf('131', plain, ($false),
% 1.31/1.49      inference('sat_resolution*', [status(thm)], ['1', '82', '83', '130'])).
% 1.31/1.49  
% 1.31/1.49  % SZS output end Refutation
% 1.31/1.49  
% 1.31/1.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
