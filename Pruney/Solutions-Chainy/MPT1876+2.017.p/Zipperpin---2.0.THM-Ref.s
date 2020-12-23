%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.101BCZgx5B

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:57 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 421 expanded)
%              Number of leaves         :   46 ( 134 expanded)
%              Depth                    :   19
%              Number of atoms          : 1200 (4960 expanded)
%              Number of equality atoms :   26 (  33 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

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
    ! [X34: $i,X35: $i] :
      ( ( v1_xboole_0 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( v2_tex_2 @ X34 @ X35 )
      | ( X34
        = ( u1_struct_0 @ ( sk_C_1 @ X34 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
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
    ! [X25: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 )
      | ~ ( v7_struct_0 @ X25 ) ) ),
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
    ! [X34: $i,X35: $i] :
      ( ( v1_xboole_0 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( v2_tex_2 @ X34 @ X35 )
      | ( m1_pre_topc @ ( sk_C_1 @ X34 @ X35 ) @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( l1_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
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

thf('33',plain,(
    ! [X29: $i] :
      ( ( v2_struct_0 @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ~ ( v1_tdlat_3 @ X29 )
      | ~ ( v2_tdlat_3 @ X29 )
      | ( v7_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[cc2_tex_1])).

thf('34',plain,
    ( ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v2_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v2_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('36',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X34: $i,X35: $i] :
      ( ( v1_xboole_0 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( v2_tex_2 @ X34 @ X35 )
      | ( v1_tdlat_3 @ ( sk_C_1 @ X34 @ X35 ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','41'])).

thf('43',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v2_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v2_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['34','46'])).

thf('48',plain,
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

thf('49',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( v2_tdlat_3 @ X30 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_tdlat_3 @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[cc6_tdlat_3])).

thf('50',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v2_tdlat_3 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v2_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( l1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(cc2_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_tdlat_3 @ A )
       => ( v2_pre_topc @ A ) ) ) )).

thf('58',plain,(
    ! [X28: $i] :
      ( ~ ( v2_tdlat_3 @ X28 )
      | ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[cc2_tdlat_3])).

thf('59',plain,
    ( ( ( v2_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v2_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( v2_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('61',plain,
    ( ( v2_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['47','56','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X34: $i,X35: $i] :
      ( ( v1_xboole_0 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( v2_tex_2 @ X34 @ X35 )
      | ~ ( v2_struct_0 @ ( sk_C_1 @ X34 @ X35 ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('65',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,
    ( ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['62','68'])).

thf('70',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('71',plain,
    ( ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( l1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('77',plain,(
    ! [X22: $i] :
      ( ( l1_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('78',plain,
    ( ( l1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['16','75','78'])).

thf('80',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
   <= ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('81',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('83',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['2'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('84',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('85',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X10 ) @ X12 )
      | ~ ( r2_hidden @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('87',plain,(
    ! [X32: $i,X33: $i] :
      ( ( v1_xboole_0 @ X32 )
      | ~ ( v1_zfmisc_1 @ X32 )
      | ( X33 = X32 )
      | ~ ( r1_tarski @ X33 @ X32 )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('90',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('91',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ~ ( v1_xboole_0 @ X9 )
      | ( X8 = X9 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['89','92'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('94',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('95',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X13 ) @ X14 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['93','96'])).

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
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
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

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('107',plain,(
    ! [X17: $i,X18: $i] :
      ( ( m1_subset_1 @ X17 @ X18 )
      | ~ ( r2_hidden @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('108',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('109',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X37 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X37 ) @ X36 ) @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('114',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ X26 )
      | ( ( k6_domain_1 @ X26 @ X27 )
        = ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('115',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('117',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( v1_xboole_0 @ X15 )
      | ~ ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('118',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('121',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
    = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['115','120'])).

thf('122',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['110','111','112','121'])).

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
    inference('sup-',[status(thm)],['83','127'])).

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
    inference('sat_resolution*',[status(thm)],['1','81','82','130'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.101BCZgx5B
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:55:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.67/0.88  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.67/0.88  % Solved by: fo/fo7.sh
% 0.67/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.88  % done 553 iterations in 0.421s
% 0.67/0.88  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.67/0.88  % SZS output start Refutation
% 0.67/0.88  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.67/0.88  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.67/0.88  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.67/0.88  thf(sk_B_type, type, sk_B: $i > $i).
% 0.67/0.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.67/0.88  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.67/0.88  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.67/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.88  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.67/0.88  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.67/0.88  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.67/0.88  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.67/0.88  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.67/0.88  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.67/0.88  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.67/0.88  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.67/0.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.67/0.88  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.67/0.88  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.67/0.88  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.67/0.88  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.67/0.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.67/0.88  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.67/0.88  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.67/0.88  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.67/0.88  thf(t44_tex_2, conjecture,
% 0.67/0.88    (![A:$i]:
% 0.67/0.88     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.67/0.88         ( l1_pre_topc @ A ) ) =>
% 0.67/0.88       ( ![B:$i]:
% 0.67/0.88         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.67/0.88             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.67/0.88           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.67/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.67/0.88    (~( ![A:$i]:
% 0.67/0.88        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.67/0.88            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.67/0.88          ( ![B:$i]:
% 0.67/0.88            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.67/0.88                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.67/0.88              ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.67/0.88    inference('cnf.neg', [status(esa)], [t44_tex_2])).
% 0.67/0.88  thf('0', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('1', plain,
% 0.67/0.88      (~ ((v1_zfmisc_1 @ sk_B_1)) | ~ ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.67/0.88      inference('split', [status(esa)], ['0'])).
% 0.67/0.88  thf('2', plain, (((v1_zfmisc_1 @ sk_B_1) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('3', plain,
% 0.67/0.88      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.67/0.88      inference('split', [status(esa)], ['2'])).
% 0.67/0.88  thf('4', plain,
% 0.67/0.88      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf(t34_tex_2, axiom,
% 0.67/0.88    (![A:$i]:
% 0.67/0.88     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.67/0.88       ( ![B:$i]:
% 0.67/0.88         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.67/0.88             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.67/0.88           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.67/0.88                ( ![C:$i]:
% 0.67/0.88                  ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.67/0.88                      ( v1_tdlat_3 @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.67/0.88                    ( ( B ) != ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ))).
% 0.67/0.88  thf('5', plain,
% 0.67/0.88      (![X34 : $i, X35 : $i]:
% 0.67/0.88         ((v1_xboole_0 @ X34)
% 0.67/0.88          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.67/0.88          | ~ (v2_tex_2 @ X34 @ X35)
% 0.67/0.88          | ((X34) = (u1_struct_0 @ (sk_C_1 @ X34 @ X35)))
% 0.67/0.88          | ~ (l1_pre_topc @ X35)
% 0.67/0.88          | ~ (v2_pre_topc @ X35)
% 0.67/0.88          | (v2_struct_0 @ X35))),
% 0.67/0.88      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.67/0.88  thf('6', plain,
% 0.67/0.88      (((v2_struct_0 @ sk_A)
% 0.67/0.88        | ~ (v2_pre_topc @ sk_A)
% 0.67/0.88        | ~ (l1_pre_topc @ sk_A)
% 0.67/0.88        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.67/0.88        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.67/0.88        | (v1_xboole_0 @ sk_B_1))),
% 0.67/0.88      inference('sup-', [status(thm)], ['4', '5'])).
% 0.67/0.88  thf('7', plain, ((v2_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('9', plain,
% 0.67/0.88      (((v2_struct_0 @ sk_A)
% 0.67/0.88        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.67/0.88        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.67/0.88        | (v1_xboole_0 @ sk_B_1))),
% 0.67/0.88      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.67/0.88  thf('10', plain,
% 0.67/0.88      ((((v1_xboole_0 @ sk_B_1)
% 0.67/0.88         | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.67/0.88         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.67/0.88      inference('sup-', [status(thm)], ['3', '9'])).
% 0.67/0.88  thf('11', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('12', plain,
% 0.67/0.88      ((((v2_struct_0 @ sk_A)
% 0.67/0.88         | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))))
% 0.67/0.88         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.67/0.88      inference('clc', [status(thm)], ['10', '11'])).
% 0.67/0.88  thf('13', plain, (~ (v2_struct_0 @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('14', plain,
% 0.67/0.88      ((((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.67/0.88         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.67/0.88      inference('clc', [status(thm)], ['12', '13'])).
% 0.67/0.88  thf(fc7_struct_0, axiom,
% 0.67/0.88    (![A:$i]:
% 0.67/0.88     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.67/0.88       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.67/0.88  thf('15', plain,
% 0.67/0.88      (![X25 : $i]:
% 0.67/0.88         ((v1_zfmisc_1 @ (u1_struct_0 @ X25))
% 0.67/0.88          | ~ (l1_struct_0 @ X25)
% 0.67/0.88          | ~ (v7_struct_0 @ X25))),
% 0.67/0.88      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.67/0.88  thf('16', plain,
% 0.67/0.88      ((((v1_zfmisc_1 @ sk_B_1)
% 0.67/0.88         | ~ (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.67/0.88         | ~ (l1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.67/0.88         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.67/0.88      inference('sup+', [status(thm)], ['14', '15'])).
% 0.67/0.88  thf('17', plain,
% 0.67/0.88      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.67/0.88      inference('split', [status(esa)], ['2'])).
% 0.67/0.88  thf('18', plain,
% 0.67/0.88      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('19', plain,
% 0.67/0.88      (![X34 : $i, X35 : $i]:
% 0.67/0.88         ((v1_xboole_0 @ X34)
% 0.67/0.88          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.67/0.88          | ~ (v2_tex_2 @ X34 @ X35)
% 0.67/0.88          | (m1_pre_topc @ (sk_C_1 @ X34 @ X35) @ X35)
% 0.67/0.88          | ~ (l1_pre_topc @ X35)
% 0.67/0.88          | ~ (v2_pre_topc @ X35)
% 0.67/0.88          | (v2_struct_0 @ X35))),
% 0.67/0.88      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.67/0.88  thf('20', plain,
% 0.67/0.88      (((v2_struct_0 @ sk_A)
% 0.67/0.88        | ~ (v2_pre_topc @ sk_A)
% 0.67/0.88        | ~ (l1_pre_topc @ sk_A)
% 0.67/0.88        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.67/0.88        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.67/0.88        | (v1_xboole_0 @ sk_B_1))),
% 0.67/0.88      inference('sup-', [status(thm)], ['18', '19'])).
% 0.67/0.88  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('23', plain,
% 0.67/0.88      (((v2_struct_0 @ sk_A)
% 0.67/0.88        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.67/0.88        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.67/0.88        | (v1_xboole_0 @ sk_B_1))),
% 0.67/0.88      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.67/0.88  thf('24', plain,
% 0.67/0.88      ((((v1_xboole_0 @ sk_B_1)
% 0.67/0.88         | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.67/0.88         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.67/0.88      inference('sup-', [status(thm)], ['17', '23'])).
% 0.67/0.88  thf('25', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('26', plain,
% 0.67/0.88      ((((v2_struct_0 @ sk_A) | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)))
% 0.67/0.88         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.67/0.88      inference('clc', [status(thm)], ['24', '25'])).
% 0.67/0.88  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('28', plain,
% 0.67/0.88      (((m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A))
% 0.67/0.88         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.67/0.88      inference('clc', [status(thm)], ['26', '27'])).
% 0.67/0.88  thf(dt_m1_pre_topc, axiom,
% 0.67/0.88    (![A:$i]:
% 0.67/0.88     ( ( l1_pre_topc @ A ) =>
% 0.67/0.88       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.67/0.88  thf('29', plain,
% 0.67/0.88      (![X23 : $i, X24 : $i]:
% 0.67/0.88         (~ (m1_pre_topc @ X23 @ X24)
% 0.67/0.88          | (l1_pre_topc @ X23)
% 0.67/0.88          | ~ (l1_pre_topc @ X24))),
% 0.67/0.88      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.67/0.88  thf('30', plain,
% 0.67/0.88      (((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.67/0.88         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.67/0.88      inference('sup-', [status(thm)], ['28', '29'])).
% 0.67/0.88  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('32', plain,
% 0.67/0.88      (((l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.67/0.88         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.67/0.88      inference('demod', [status(thm)], ['30', '31'])).
% 0.67/0.88  thf(cc2_tex_1, axiom,
% 0.67/0.88    (![A:$i]:
% 0.67/0.88     ( ( l1_pre_topc @ A ) =>
% 0.67/0.88       ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.67/0.88           ( v1_tdlat_3 @ A ) & ( v2_tdlat_3 @ A ) ) =>
% 0.67/0.88         ( ( ~( v2_struct_0 @ A ) ) & ( v7_struct_0 @ A ) & ( v2_pre_topc @ A ) ) ) ))).
% 0.67/0.88  thf('33', plain,
% 0.67/0.88      (![X29 : $i]:
% 0.67/0.88         ((v2_struct_0 @ X29)
% 0.67/0.88          | ~ (v2_pre_topc @ X29)
% 0.67/0.88          | ~ (v1_tdlat_3 @ X29)
% 0.67/0.88          | ~ (v2_tdlat_3 @ X29)
% 0.67/0.88          | (v7_struct_0 @ X29)
% 0.67/0.88          | ~ (l1_pre_topc @ X29))),
% 0.67/0.88      inference('cnf', [status(esa)], [cc2_tex_1])).
% 0.67/0.88  thf('34', plain,
% 0.67/0.88      ((((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.67/0.88         | ~ (v2_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.67/0.88         | ~ (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.67/0.88         | ~ (v2_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.67/0.88         | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.67/0.88         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.67/0.88      inference('sup-', [status(thm)], ['32', '33'])).
% 0.67/0.88  thf('35', plain,
% 0.67/0.88      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.67/0.88      inference('split', [status(esa)], ['2'])).
% 0.67/0.88  thf('36', plain,
% 0.67/0.88      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('37', plain,
% 0.67/0.88      (![X34 : $i, X35 : $i]:
% 0.67/0.88         ((v1_xboole_0 @ X34)
% 0.67/0.88          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.67/0.88          | ~ (v2_tex_2 @ X34 @ X35)
% 0.67/0.88          | (v1_tdlat_3 @ (sk_C_1 @ X34 @ X35))
% 0.67/0.88          | ~ (l1_pre_topc @ X35)
% 0.67/0.88          | ~ (v2_pre_topc @ X35)
% 0.67/0.88          | (v2_struct_0 @ X35))),
% 0.67/0.88      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.67/0.88  thf('38', plain,
% 0.67/0.88      (((v2_struct_0 @ sk_A)
% 0.67/0.88        | ~ (v2_pre_topc @ sk_A)
% 0.67/0.88        | ~ (l1_pre_topc @ sk_A)
% 0.67/0.88        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.67/0.88        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.67/0.88        | (v1_xboole_0 @ sk_B_1))),
% 0.67/0.88      inference('sup-', [status(thm)], ['36', '37'])).
% 0.67/0.88  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('41', plain,
% 0.67/0.88      (((v2_struct_0 @ sk_A)
% 0.67/0.88        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.67/0.88        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.67/0.88        | (v1_xboole_0 @ sk_B_1))),
% 0.67/0.88      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.67/0.88  thf('42', plain,
% 0.67/0.88      ((((v1_xboole_0 @ sk_B_1)
% 0.67/0.88         | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.67/0.88         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.67/0.88      inference('sup-', [status(thm)], ['35', '41'])).
% 0.67/0.88  thf('43', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('44', plain,
% 0.67/0.88      ((((v2_struct_0 @ sk_A) | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.67/0.88         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.67/0.88      inference('clc', [status(thm)], ['42', '43'])).
% 0.67/0.88  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('46', plain,
% 0.67/0.88      (((v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.67/0.88         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.67/0.88      inference('clc', [status(thm)], ['44', '45'])).
% 0.67/0.88  thf('47', plain,
% 0.67/0.88      ((((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.67/0.88         | ~ (v2_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.67/0.88         | ~ (v2_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.67/0.88         | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.67/0.88         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.67/0.88      inference('demod', [status(thm)], ['34', '46'])).
% 0.67/0.88  thf('48', plain,
% 0.67/0.88      (((m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A))
% 0.67/0.88         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.67/0.88      inference('clc', [status(thm)], ['26', '27'])).
% 0.67/0.88  thf(cc6_tdlat_3, axiom,
% 0.67/0.88    (![A:$i]:
% 0.67/0.88     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.67/0.88         ( l1_pre_topc @ A ) ) =>
% 0.67/0.88       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_tdlat_3 @ B ) ) ) ))).
% 0.67/0.88  thf('49', plain,
% 0.67/0.88      (![X30 : $i, X31 : $i]:
% 0.67/0.88         (~ (m1_pre_topc @ X30 @ X31)
% 0.67/0.88          | (v2_tdlat_3 @ X30)
% 0.67/0.88          | ~ (l1_pre_topc @ X31)
% 0.67/0.88          | ~ (v2_tdlat_3 @ X31)
% 0.67/0.88          | ~ (v2_pre_topc @ X31)
% 0.67/0.88          | (v2_struct_0 @ X31))),
% 0.67/0.88      inference('cnf', [status(esa)], [cc6_tdlat_3])).
% 0.67/0.88  thf('50', plain,
% 0.67/0.88      ((((v2_struct_0 @ sk_A)
% 0.67/0.88         | ~ (v2_pre_topc @ sk_A)
% 0.67/0.88         | ~ (v2_tdlat_3 @ sk_A)
% 0.67/0.88         | ~ (l1_pre_topc @ sk_A)
% 0.67/0.88         | (v2_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.67/0.88         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.67/0.88      inference('sup-', [status(thm)], ['48', '49'])).
% 0.67/0.88  thf('51', plain, ((v2_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('52', plain, ((v2_tdlat_3 @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('54', plain,
% 0.67/0.88      ((((v2_struct_0 @ sk_A) | (v2_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.67/0.88         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.67/0.88      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 0.67/0.88  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('56', plain,
% 0.67/0.88      (((v2_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.67/0.88         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.67/0.88      inference('clc', [status(thm)], ['54', '55'])).
% 0.67/0.88  thf('57', plain,
% 0.67/0.88      (((l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.67/0.88         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.67/0.88      inference('demod', [status(thm)], ['30', '31'])).
% 0.67/0.88  thf(cc2_tdlat_3, axiom,
% 0.67/0.88    (![A:$i]:
% 0.67/0.88     ( ( l1_pre_topc @ A ) => ( ( v2_tdlat_3 @ A ) => ( v2_pre_topc @ A ) ) ))).
% 0.67/0.88  thf('58', plain,
% 0.67/0.88      (![X28 : $i]:
% 0.67/0.88         (~ (v2_tdlat_3 @ X28) | (v2_pre_topc @ X28) | ~ (l1_pre_topc @ X28))),
% 0.67/0.88      inference('cnf', [status(esa)], [cc2_tdlat_3])).
% 0.67/0.88  thf('59', plain,
% 0.67/0.88      ((((v2_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.67/0.88         | ~ (v2_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.67/0.88         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.67/0.88      inference('sup-', [status(thm)], ['57', '58'])).
% 0.67/0.88  thf('60', plain,
% 0.67/0.88      (((v2_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.67/0.88         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.67/0.88      inference('clc', [status(thm)], ['54', '55'])).
% 0.67/0.88  thf('61', plain,
% 0.67/0.88      (((v2_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.67/0.88         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.67/0.88      inference('demod', [status(thm)], ['59', '60'])).
% 0.67/0.88  thf('62', plain,
% 0.67/0.88      ((((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.67/0.88         | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.67/0.88         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.67/0.88      inference('demod', [status(thm)], ['47', '56', '61'])).
% 0.67/0.88  thf('63', plain,
% 0.67/0.88      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('64', plain,
% 0.67/0.88      (![X34 : $i, X35 : $i]:
% 0.67/0.88         ((v1_xboole_0 @ X34)
% 0.67/0.88          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.67/0.88          | ~ (v2_tex_2 @ X34 @ X35)
% 0.67/0.88          | ~ (v2_struct_0 @ (sk_C_1 @ X34 @ X35))
% 0.67/0.88          | ~ (l1_pre_topc @ X35)
% 0.67/0.88          | ~ (v2_pre_topc @ X35)
% 0.67/0.88          | (v2_struct_0 @ X35))),
% 0.67/0.88      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.67/0.88  thf('65', plain,
% 0.67/0.88      (((v2_struct_0 @ sk_A)
% 0.67/0.88        | ~ (v2_pre_topc @ sk_A)
% 0.67/0.88        | ~ (l1_pre_topc @ sk_A)
% 0.67/0.88        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.67/0.88        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.67/0.88        | (v1_xboole_0 @ sk_B_1))),
% 0.67/0.88      inference('sup-', [status(thm)], ['63', '64'])).
% 0.67/0.88  thf('66', plain, ((v2_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('68', plain,
% 0.67/0.88      (((v2_struct_0 @ sk_A)
% 0.67/0.88        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.67/0.88        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.67/0.88        | (v1_xboole_0 @ sk_B_1))),
% 0.67/0.88      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.67/0.88  thf('69', plain,
% 0.67/0.88      ((((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.67/0.88         | (v1_xboole_0 @ sk_B_1)
% 0.67/0.88         | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.67/0.88         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.67/0.88      inference('sup-', [status(thm)], ['62', '68'])).
% 0.67/0.88  thf('70', plain,
% 0.67/0.88      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.67/0.88      inference('split', [status(esa)], ['2'])).
% 0.67/0.88  thf('71', plain,
% 0.67/0.88      ((((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.67/0.88         | (v1_xboole_0 @ sk_B_1)
% 0.67/0.88         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.67/0.88      inference('demod', [status(thm)], ['69', '70'])).
% 0.67/0.88  thf('72', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('73', plain,
% 0.67/0.88      ((((v2_struct_0 @ sk_A) | (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.67/0.88         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.67/0.88      inference('clc', [status(thm)], ['71', '72'])).
% 0.67/0.88  thf('74', plain, (~ (v2_struct_0 @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('75', plain,
% 0.67/0.88      (((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.67/0.88         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.67/0.88      inference('clc', [status(thm)], ['73', '74'])).
% 0.67/0.88  thf('76', plain,
% 0.67/0.88      (((l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.67/0.88         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.67/0.88      inference('demod', [status(thm)], ['30', '31'])).
% 0.67/0.88  thf(dt_l1_pre_topc, axiom,
% 0.67/0.88    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.67/0.88  thf('77', plain,
% 0.67/0.88      (![X22 : $i]: ((l1_struct_0 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.67/0.88      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.67/0.88  thf('78', plain,
% 0.67/0.88      (((l1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.67/0.88         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.67/0.88      inference('sup-', [status(thm)], ['76', '77'])).
% 0.67/0.88  thf('79', plain,
% 0.67/0.88      (((v1_zfmisc_1 @ sk_B_1)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.67/0.88      inference('demod', [status(thm)], ['16', '75', '78'])).
% 0.67/0.88  thf('80', plain,
% 0.67/0.88      ((~ (v1_zfmisc_1 @ sk_B_1)) <= (~ ((v1_zfmisc_1 @ sk_B_1)))),
% 0.67/0.88      inference('split', [status(esa)], ['0'])).
% 0.67/0.88  thf('81', plain, (((v1_zfmisc_1 @ sk_B_1)) | ~ ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.67/0.88      inference('sup-', [status(thm)], ['79', '80'])).
% 0.67/0.88  thf('82', plain, (((v1_zfmisc_1 @ sk_B_1)) | ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.67/0.88      inference('split', [status(esa)], ['2'])).
% 0.67/0.88  thf('83', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.67/0.88      inference('split', [status(esa)], ['2'])).
% 0.67/0.88  thf(d1_xboole_0, axiom,
% 0.67/0.88    (![A:$i]:
% 0.67/0.88     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.67/0.88  thf('84', plain,
% 0.67/0.88      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.67/0.88      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.67/0.88  thf(l1_zfmisc_1, axiom,
% 0.67/0.88    (![A:$i,B:$i]:
% 0.67/0.88     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.67/0.88  thf('85', plain,
% 0.67/0.88      (![X10 : $i, X12 : $i]:
% 0.67/0.88         ((r1_tarski @ (k1_tarski @ X10) @ X12) | ~ (r2_hidden @ X10 @ X12))),
% 0.67/0.88      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.67/0.88  thf('86', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.67/0.88      inference('sup-', [status(thm)], ['84', '85'])).
% 0.67/0.88  thf(t1_tex_2, axiom,
% 0.67/0.88    (![A:$i]:
% 0.67/0.88     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.67/0.88       ( ![B:$i]:
% 0.67/0.88         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.67/0.88           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.67/0.88  thf('87', plain,
% 0.67/0.88      (![X32 : $i, X33 : $i]:
% 0.67/0.88         ((v1_xboole_0 @ X32)
% 0.67/0.88          | ~ (v1_zfmisc_1 @ X32)
% 0.67/0.88          | ((X33) = (X32))
% 0.67/0.88          | ~ (r1_tarski @ X33 @ X32)
% 0.67/0.88          | (v1_xboole_0 @ X33))),
% 0.67/0.88      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.67/0.88  thf('88', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         ((v1_xboole_0 @ X0)
% 0.67/0.88          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.67/0.88          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.67/0.88          | ~ (v1_zfmisc_1 @ X0)
% 0.67/0.88          | (v1_xboole_0 @ X0))),
% 0.67/0.88      inference('sup-', [status(thm)], ['86', '87'])).
% 0.67/0.88  thf('89', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         (~ (v1_zfmisc_1 @ X0)
% 0.67/0.88          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.67/0.88          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.67/0.88          | (v1_xboole_0 @ X0))),
% 0.67/0.88      inference('simplify', [status(thm)], ['88'])).
% 0.67/0.88  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.67/0.88  thf('90', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.67/0.88      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.67/0.88  thf(t8_boole, axiom,
% 0.67/0.88    (![A:$i,B:$i]:
% 0.67/0.88     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.67/0.88  thf('91', plain,
% 0.67/0.88      (![X8 : $i, X9 : $i]:
% 0.67/0.88         (~ (v1_xboole_0 @ X8) | ~ (v1_xboole_0 @ X9) | ((X8) = (X9)))),
% 0.67/0.88      inference('cnf', [status(esa)], [t8_boole])).
% 0.67/0.88  thf('92', plain,
% 0.67/0.88      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.67/0.88      inference('sup-', [status(thm)], ['90', '91'])).
% 0.67/0.88  thf('93', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         ((v1_xboole_0 @ X0)
% 0.67/0.88          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.67/0.88          | ~ (v1_zfmisc_1 @ X0)
% 0.67/0.88          | ((k1_xboole_0) = (k1_tarski @ (sk_B @ X0))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['89', '92'])).
% 0.67/0.88  thf(t1_boole, axiom,
% 0.67/0.88    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.67/0.88  thf('94', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.67/0.88      inference('cnf', [status(esa)], [t1_boole])).
% 0.67/0.88  thf(t49_zfmisc_1, axiom,
% 0.67/0.88    (![A:$i,B:$i]:
% 0.67/0.88     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.67/0.88  thf('95', plain,
% 0.67/0.88      (![X13 : $i, X14 : $i]:
% 0.67/0.88         ((k2_xboole_0 @ (k1_tarski @ X13) @ X14) != (k1_xboole_0))),
% 0.67/0.88      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.67/0.88  thf('96', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.67/0.88      inference('sup-', [status(thm)], ['94', '95'])).
% 0.67/0.88  thf('97', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         ((v1_xboole_0 @ X0)
% 0.67/0.88          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.67/0.88          | ~ (v1_zfmisc_1 @ X0))),
% 0.67/0.88      inference('simplify_reflect-', [status(thm)], ['93', '96'])).
% 0.67/0.88  thf('98', plain,
% 0.67/0.88      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.67/0.88      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.67/0.88  thf('99', plain,
% 0.67/0.88      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf(t3_subset, axiom,
% 0.67/0.88    (![A:$i,B:$i]:
% 0.67/0.88     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.67/0.88  thf('100', plain,
% 0.67/0.88      (![X19 : $i, X20 : $i]:
% 0.67/0.88         ((r1_tarski @ X19 @ X20) | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.67/0.88      inference('cnf', [status(esa)], [t3_subset])).
% 0.67/0.88  thf('101', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.67/0.88      inference('sup-', [status(thm)], ['99', '100'])).
% 0.67/0.88  thf(d3_tarski, axiom,
% 0.67/0.88    (![A:$i,B:$i]:
% 0.67/0.88     ( ( r1_tarski @ A @ B ) <=>
% 0.67/0.88       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.67/0.88  thf('102', plain,
% 0.67/0.88      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.67/0.88         (~ (r2_hidden @ X3 @ X4)
% 0.67/0.88          | (r2_hidden @ X3 @ X5)
% 0.67/0.88          | ~ (r1_tarski @ X4 @ X5))),
% 0.67/0.88      inference('cnf', [status(esa)], [d3_tarski])).
% 0.67/0.88  thf('103', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.67/0.88      inference('sup-', [status(thm)], ['101', '102'])).
% 0.67/0.88  thf('104', plain,
% 0.67/0.88      (((v1_xboole_0 @ sk_B_1)
% 0.67/0.88        | (r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('sup-', [status(thm)], ['98', '103'])).
% 0.67/0.88  thf('105', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('106', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.67/0.88      inference('clc', [status(thm)], ['104', '105'])).
% 0.67/0.88  thf(t1_subset, axiom,
% 0.67/0.88    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.67/0.88  thf('107', plain,
% 0.67/0.88      (![X17 : $i, X18 : $i]:
% 0.67/0.88         ((m1_subset_1 @ X17 @ X18) | ~ (r2_hidden @ X17 @ X18))),
% 0.67/0.88      inference('cnf', [status(esa)], [t1_subset])).
% 0.67/0.88  thf('108', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.67/0.88      inference('sup-', [status(thm)], ['106', '107'])).
% 0.67/0.88  thf(t36_tex_2, axiom,
% 0.67/0.88    (![A:$i]:
% 0.67/0.88     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.67/0.88       ( ![B:$i]:
% 0.67/0.88         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.67/0.88           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.67/0.88  thf('109', plain,
% 0.67/0.88      (![X36 : $i, X37 : $i]:
% 0.67/0.88         (~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X37))
% 0.67/0.88          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X37) @ X36) @ X37)
% 0.67/0.88          | ~ (l1_pre_topc @ X37)
% 0.67/0.88          | ~ (v2_pre_topc @ X37)
% 0.67/0.88          | (v2_struct_0 @ X37))),
% 0.67/0.88      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.67/0.88  thf('110', plain,
% 0.67/0.88      (((v2_struct_0 @ sk_A)
% 0.67/0.88        | ~ (v2_pre_topc @ sk_A)
% 0.67/0.88        | ~ (l1_pre_topc @ sk_A)
% 0.67/0.88        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.67/0.88           sk_A))),
% 0.67/0.88      inference('sup-', [status(thm)], ['108', '109'])).
% 0.67/0.88  thf('111', plain, ((v2_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('112', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('113', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.67/0.88      inference('sup-', [status(thm)], ['106', '107'])).
% 0.67/0.88  thf(redefinition_k6_domain_1, axiom,
% 0.67/0.88    (![A:$i,B:$i]:
% 0.67/0.88     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.67/0.88       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.67/0.88  thf('114', plain,
% 0.67/0.88      (![X26 : $i, X27 : $i]:
% 0.67/0.88         ((v1_xboole_0 @ X26)
% 0.67/0.88          | ~ (m1_subset_1 @ X27 @ X26)
% 0.67/0.88          | ((k6_domain_1 @ X26 @ X27) = (k1_tarski @ X27)))),
% 0.67/0.88      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.67/0.88  thf('115', plain,
% 0.67/0.88      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.67/0.88          = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.67/0.88        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('sup-', [status(thm)], ['113', '114'])).
% 0.67/0.88  thf('116', plain,
% 0.67/0.88      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf(cc1_subset_1, axiom,
% 0.67/0.88    (![A:$i]:
% 0.67/0.88     ( ( v1_xboole_0 @ A ) =>
% 0.67/0.88       ( ![B:$i]:
% 0.67/0.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.67/0.88  thf('117', plain,
% 0.67/0.88      (![X15 : $i, X16 : $i]:
% 0.67/0.88         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.67/0.88          | (v1_xboole_0 @ X15)
% 0.67/0.88          | ~ (v1_xboole_0 @ X16))),
% 0.67/0.88      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.67/0.88  thf('118', plain,
% 0.67/0.88      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_B_1))),
% 0.67/0.88      inference('sup-', [status(thm)], ['116', '117'])).
% 0.67/0.88  thf('119', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('120', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.67/0.88      inference('clc', [status(thm)], ['118', '119'])).
% 0.67/0.88  thf('121', plain,
% 0.67/0.88      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.67/0.88         = (k1_tarski @ (sk_B @ sk_B_1)))),
% 0.67/0.88      inference('clc', [status(thm)], ['115', '120'])).
% 0.67/0.88  thf('122', plain,
% 0.67/0.88      (((v2_struct_0 @ sk_A)
% 0.67/0.88        | (v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A))),
% 0.67/0.88      inference('demod', [status(thm)], ['110', '111', '112', '121'])).
% 0.67/0.88  thf('123', plain, (~ (v2_struct_0 @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('124', plain, ((v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A)),
% 0.67/0.88      inference('clc', [status(thm)], ['122', '123'])).
% 0.67/0.88  thf('125', plain,
% 0.67/0.88      (((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.67/0.88        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.67/0.88        | (v1_xboole_0 @ sk_B_1))),
% 0.67/0.88      inference('sup+', [status(thm)], ['97', '124'])).
% 0.67/0.88  thf('126', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('127', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.67/0.88      inference('clc', [status(thm)], ['125', '126'])).
% 0.67/0.88  thf('128', plain,
% 0.67/0.88      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.67/0.88      inference('sup-', [status(thm)], ['83', '127'])).
% 0.67/0.88  thf('129', plain,
% 0.67/0.88      ((~ (v2_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.67/0.88      inference('split', [status(esa)], ['0'])).
% 0.67/0.88  thf('130', plain,
% 0.67/0.88      (~ ((v1_zfmisc_1 @ sk_B_1)) | ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.67/0.88      inference('sup-', [status(thm)], ['128', '129'])).
% 0.67/0.88  thf('131', plain, ($false),
% 0.67/0.88      inference('sat_resolution*', [status(thm)], ['1', '81', '82', '130'])).
% 0.67/0.88  
% 0.67/0.88  % SZS output end Refutation
% 0.67/0.88  
% 0.67/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
