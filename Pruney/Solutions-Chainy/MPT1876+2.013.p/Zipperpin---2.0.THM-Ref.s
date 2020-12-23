%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QS5h1DdjNe

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:57 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 406 expanded)
%              Number of leaves         :   41 ( 127 expanded)
%              Depth                    :   19
%              Number of atoms          : 1257 (4819 expanded)
%              Number of equality atoms :   19 (  27 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

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
    ! [X36: $i,X37: $i] :
      ( ( v1_xboole_0 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( v2_tex_2 @ X36 @ X37 )
      | ( X36
        = ( u1_struct_0 @ ( sk_C @ X36 @ X37 ) ) )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
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
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( sk_B_1
        = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( sk_B_1
        = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['12','13'])).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('15',plain,(
    ! [X24: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 )
      | ~ ( v7_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('16',plain,
    ( ( ( v1_zfmisc_1 @ sk_B_1 )
      | ~ ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( l1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
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
    ! [X36: $i,X37: $i] :
      ( ( v1_xboole_0 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( v2_tex_2 @ X36 @ X37 )
      | ( m1_pre_topc @ ( sk_C @ X36 @ X37 ) @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('20',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
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
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['26','27'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('29',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ( l1_pre_topc @ X22 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('30',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( l1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( l1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('33',plain,(
    ! [X21: $i] :
      ( ( l1_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('34',plain,
    ( ( l1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( v1_zfmisc_1 @ sk_B_1 )
      | ~ ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['16','34'])).

thf('36',plain,
    ( ( l1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) )
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
    ! [X31: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ~ ( v1_tdlat_3 @ X31 )
      | ~ ( v2_tdlat_3 @ X31 )
      | ( v7_struct_0 @ X31 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[cc2_tex_1])).

thf('38',plain,
    ( ( ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( v2_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( v2_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
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
    ! [X36: $i,X37: $i] :
      ( ( v1_xboole_0 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( v2_tex_2 @ X36 @ X37 )
      | ( v1_tdlat_3 @ ( sk_C @ X36 @ X37 ) )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
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
    | ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( v2_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( v2_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['38','50'])).

thf('52',plain,
    ( ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
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
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_pre_topc @ X32 @ X33 )
      | ( v2_tdlat_3 @ X32 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_tdlat_3 @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[cc6_tdlat_3])).

thf('54',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v2_tdlat_3 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
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
      | ( v2_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55','56','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v2_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( l1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(cc1_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_tdlat_3 @ A )
       => ( v2_pre_topc @ A ) ) ) )).

thf('62',plain,(
    ! [X29: $i] :
      ( ~ ( v1_tdlat_3 @ X29 )
      | ( v2_pre_topc @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[cc1_tdlat_3])).

thf('63',plain,
    ( ( ( v2_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('65',plain,
    ( ( v2_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['51','60','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X36: $i,X37: $i] :
      ( ( v1_xboole_0 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( v2_tex_2 @ X36 @ X37 )
      | ~ ( v2_struct_0 @ ( sk_C @ X36 @ X37 ) )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
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
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,
    ( ( ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
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
    ( ( ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
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

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('86',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ( m1_subset_1 @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('88',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('90',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ X27 )
      | ( ( k6_domain_1 @ X27 @ X28 )
        = ( k1_tarski @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('94',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ X25 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X25 @ X26 ) @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('97',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['92','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('101',plain,(
    ! [X34: $i,X35: $i] :
      ( ( v1_xboole_0 @ X34 )
      | ~ ( v1_zfmisc_1 @ X34 )
      | ( X35 = X34 )
      | ~ ( r1_tarski @ X35 @ X34 )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('104',plain,(
    ! [X9: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('107',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('108',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( m1_subset_1 @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['106','109'])).

thf('111',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['110','111'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('113',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X39 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X39 ) @ X38 ) @ X39 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('114',plain,
    ( ( v2_struct_0 @ sk_A )
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

thf('117',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('118',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ X27 )
      | ( ( k6_domain_1 @ X27 @ X28 )
        = ( k1_tarski @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('119',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('121',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_xboole_0 @ X13 )
      | ~ ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('122',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
    = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['119','124'])).

thf('126',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['114','115','116','125'])).

thf('127',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ),
    inference(clc,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['105','128'])).

thf('130',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['129','130'])).

thf('132',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['84','131'])).

thf('133',plain,
    ( ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('134',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','82','83','134'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QS5h1DdjNe
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:05:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.41/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.59  % Solved by: fo/fo7.sh
% 0.41/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.59  % done 250 iterations in 0.129s
% 0.41/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.59  % SZS output start Refutation
% 0.41/0.59  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.41/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.41/0.59  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.41/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.41/0.59  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.41/0.59  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.41/0.59  thf(sk_B_type, type, sk_B: $i > $i).
% 0.41/0.59  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.41/0.59  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.41/0.59  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.41/0.59  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.41/0.59  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.41/0.59  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.41/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.41/0.59  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.41/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.59  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.41/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.59  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.41/0.59  thf(t44_tex_2, conjecture,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.41/0.59         ( l1_pre_topc @ A ) ) =>
% 0.41/0.59       ( ![B:$i]:
% 0.41/0.59         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.41/0.59             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.41/0.59           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.41/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.59    (~( ![A:$i]:
% 0.41/0.59        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.41/0.59            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.59          ( ![B:$i]:
% 0.41/0.59            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.41/0.59                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.41/0.59              ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.41/0.59    inference('cnf.neg', [status(esa)], [t44_tex_2])).
% 0.41/0.59  thf('0', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('1', plain,
% 0.41/0.59      (~ ((v1_zfmisc_1 @ sk_B_1)) | ~ ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.41/0.59      inference('split', [status(esa)], ['0'])).
% 0.41/0.59  thf('2', plain, (((v1_zfmisc_1 @ sk_B_1) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('3', plain,
% 0.41/0.59      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.59      inference('split', [status(esa)], ['2'])).
% 0.41/0.59  thf('4', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(t34_tex_2, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.59       ( ![B:$i]:
% 0.41/0.59         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.41/0.59             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.41/0.59           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.41/0.59                ( ![C:$i]:
% 0.41/0.59                  ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.41/0.59                      ( v1_tdlat_3 @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.41/0.59                    ( ( B ) != ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ))).
% 0.41/0.59  thf('5', plain,
% 0.41/0.59      (![X36 : $i, X37 : $i]:
% 0.41/0.59         ((v1_xboole_0 @ X36)
% 0.41/0.59          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.41/0.59          | ~ (v2_tex_2 @ X36 @ X37)
% 0.41/0.59          | ((X36) = (u1_struct_0 @ (sk_C @ X36 @ X37)))
% 0.41/0.59          | ~ (l1_pre_topc @ X37)
% 0.41/0.59          | ~ (v2_pre_topc @ X37)
% 0.41/0.59          | (v2_struct_0 @ X37))),
% 0.41/0.59      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.41/0.59  thf('6', plain,
% 0.41/0.59      (((v2_struct_0 @ sk_A)
% 0.41/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.41/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.41/0.59        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.41/0.59        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.41/0.59        | (v1_xboole_0 @ sk_B_1))),
% 0.41/0.59      inference('sup-', [status(thm)], ['4', '5'])).
% 0.41/0.59  thf('7', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('9', plain,
% 0.41/0.59      (((v2_struct_0 @ sk_A)
% 0.41/0.59        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.41/0.59        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.41/0.59        | (v1_xboole_0 @ sk_B_1))),
% 0.41/0.59      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.41/0.59  thf('10', plain,
% 0.41/0.59      ((((v1_xboole_0 @ sk_B_1)
% 0.41/0.59         | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.41/0.59         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['3', '9'])).
% 0.41/0.59  thf('11', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('12', plain,
% 0.41/0.59      ((((v2_struct_0 @ sk_A)
% 0.41/0.59         | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))))
% 0.41/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.59      inference('clc', [status(thm)], ['10', '11'])).
% 0.41/0.59  thf('13', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('14', plain,
% 0.41/0.59      ((((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.41/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.59      inference('clc', [status(thm)], ['12', '13'])).
% 0.41/0.59  thf(fc7_struct_0, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.41/0.59       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.41/0.59  thf('15', plain,
% 0.41/0.59      (![X24 : $i]:
% 0.41/0.59         ((v1_zfmisc_1 @ (u1_struct_0 @ X24))
% 0.41/0.59          | ~ (l1_struct_0 @ X24)
% 0.41/0.59          | ~ (v7_struct_0 @ X24))),
% 0.41/0.59      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.41/0.59  thf('16', plain,
% 0.41/0.59      ((((v1_zfmisc_1 @ sk_B_1)
% 0.41/0.59         | ~ (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.41/0.59         | ~ (l1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.41/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.59      inference('sup+', [status(thm)], ['14', '15'])).
% 0.41/0.59  thf('17', plain,
% 0.41/0.59      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.59      inference('split', [status(esa)], ['2'])).
% 0.41/0.59  thf('18', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('19', plain,
% 0.41/0.59      (![X36 : $i, X37 : $i]:
% 0.41/0.59         ((v1_xboole_0 @ X36)
% 0.41/0.59          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.41/0.59          | ~ (v2_tex_2 @ X36 @ X37)
% 0.41/0.59          | (m1_pre_topc @ (sk_C @ X36 @ X37) @ X37)
% 0.41/0.59          | ~ (l1_pre_topc @ X37)
% 0.41/0.59          | ~ (v2_pre_topc @ X37)
% 0.41/0.59          | (v2_struct_0 @ X37))),
% 0.41/0.59      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.41/0.59  thf('20', plain,
% 0.41/0.59      (((v2_struct_0 @ sk_A)
% 0.41/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.41/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.41/0.59        | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.41/0.59        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.41/0.59        | (v1_xboole_0 @ sk_B_1))),
% 0.41/0.59      inference('sup-', [status(thm)], ['18', '19'])).
% 0.41/0.59  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('23', plain,
% 0.41/0.59      (((v2_struct_0 @ sk_A)
% 0.41/0.59        | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.41/0.59        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.41/0.59        | (v1_xboole_0 @ sk_B_1))),
% 0.41/0.59      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.41/0.59  thf('24', plain,
% 0.41/0.59      ((((v1_xboole_0 @ sk_B_1)
% 0.41/0.59         | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.41/0.59         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['17', '23'])).
% 0.41/0.59  thf('25', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('26', plain,
% 0.41/0.59      ((((v2_struct_0 @ sk_A) | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)))
% 0.41/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.59      inference('clc', [status(thm)], ['24', '25'])).
% 0.41/0.59  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('28', plain,
% 0.41/0.59      (((m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A))
% 0.41/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.59      inference('clc', [status(thm)], ['26', '27'])).
% 0.41/0.59  thf(dt_m1_pre_topc, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( l1_pre_topc @ A ) =>
% 0.41/0.59       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.41/0.59  thf('29', plain,
% 0.41/0.59      (![X22 : $i, X23 : $i]:
% 0.41/0.59         (~ (m1_pre_topc @ X22 @ X23)
% 0.41/0.59          | (l1_pre_topc @ X22)
% 0.41/0.59          | ~ (l1_pre_topc @ X23))),
% 0.41/0.59      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.41/0.59  thf('30', plain,
% 0.41/0.59      (((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (sk_C @ sk_B_1 @ sk_A))))
% 0.41/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['28', '29'])).
% 0.41/0.59  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('32', plain,
% 0.41/0.59      (((l1_pre_topc @ (sk_C @ sk_B_1 @ sk_A)))
% 0.41/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.59      inference('demod', [status(thm)], ['30', '31'])).
% 0.41/0.59  thf(dt_l1_pre_topc, axiom,
% 0.41/0.59    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.41/0.59  thf('33', plain,
% 0.41/0.59      (![X21 : $i]: ((l1_struct_0 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.41/0.59      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.41/0.59  thf('34', plain,
% 0.41/0.59      (((l1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.41/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['32', '33'])).
% 0.41/0.59  thf('35', plain,
% 0.41/0.59      ((((v1_zfmisc_1 @ sk_B_1) | ~ (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.41/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.59      inference('demod', [status(thm)], ['16', '34'])).
% 0.41/0.59  thf('36', plain,
% 0.41/0.59      (((l1_pre_topc @ (sk_C @ sk_B_1 @ sk_A)))
% 0.41/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.59      inference('demod', [status(thm)], ['30', '31'])).
% 0.41/0.59  thf(cc2_tex_1, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( l1_pre_topc @ A ) =>
% 0.41/0.59       ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.41/0.59           ( v1_tdlat_3 @ A ) & ( v2_tdlat_3 @ A ) ) =>
% 0.41/0.59         ( ( ~( v2_struct_0 @ A ) ) & ( v7_struct_0 @ A ) & ( v2_pre_topc @ A ) ) ) ))).
% 0.41/0.59  thf('37', plain,
% 0.41/0.59      (![X31 : $i]:
% 0.41/0.59         ((v2_struct_0 @ X31)
% 0.41/0.59          | ~ (v2_pre_topc @ X31)
% 0.41/0.59          | ~ (v1_tdlat_3 @ X31)
% 0.41/0.59          | ~ (v2_tdlat_3 @ X31)
% 0.41/0.59          | (v7_struct_0 @ X31)
% 0.41/0.59          | ~ (l1_pre_topc @ X31))),
% 0.41/0.59      inference('cnf', [status(esa)], [cc2_tex_1])).
% 0.41/0.59  thf('38', plain,
% 0.41/0.59      ((((v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.41/0.59         | ~ (v2_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))
% 0.41/0.59         | ~ (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))
% 0.41/0.59         | ~ (v2_pre_topc @ (sk_C @ sk_B_1 @ sk_A))
% 0.41/0.59         | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.41/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['36', '37'])).
% 0.41/0.59  thf('39', plain,
% 0.41/0.59      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.59      inference('split', [status(esa)], ['2'])).
% 0.41/0.59  thf('40', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('41', plain,
% 0.41/0.59      (![X36 : $i, X37 : $i]:
% 0.41/0.59         ((v1_xboole_0 @ X36)
% 0.41/0.59          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.41/0.59          | ~ (v2_tex_2 @ X36 @ X37)
% 0.41/0.59          | (v1_tdlat_3 @ (sk_C @ X36 @ X37))
% 0.41/0.59          | ~ (l1_pre_topc @ X37)
% 0.41/0.59          | ~ (v2_pre_topc @ X37)
% 0.41/0.59          | (v2_struct_0 @ X37))),
% 0.41/0.59      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.41/0.59  thf('42', plain,
% 0.41/0.59      (((v2_struct_0 @ sk_A)
% 0.41/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.41/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.41/0.59        | (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))
% 0.41/0.59        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.41/0.59        | (v1_xboole_0 @ sk_B_1))),
% 0.41/0.59      inference('sup-', [status(thm)], ['40', '41'])).
% 0.41/0.59  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('45', plain,
% 0.41/0.59      (((v2_struct_0 @ sk_A)
% 0.41/0.59        | (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))
% 0.41/0.59        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.41/0.59        | (v1_xboole_0 @ sk_B_1))),
% 0.41/0.59      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.41/0.59  thf('46', plain,
% 0.41/0.59      ((((v1_xboole_0 @ sk_B_1)
% 0.41/0.59         | (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))
% 0.41/0.59         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['39', '45'])).
% 0.41/0.59  thf('47', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('48', plain,
% 0.41/0.59      ((((v2_struct_0 @ sk_A) | (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.41/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.59      inference('clc', [status(thm)], ['46', '47'])).
% 0.41/0.59  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('50', plain,
% 0.41/0.59      (((v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.41/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.59      inference('clc', [status(thm)], ['48', '49'])).
% 0.41/0.59  thf('51', plain,
% 0.41/0.59      ((((v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.41/0.59         | ~ (v2_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))
% 0.41/0.59         | ~ (v2_pre_topc @ (sk_C @ sk_B_1 @ sk_A))
% 0.41/0.59         | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.41/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.59      inference('demod', [status(thm)], ['38', '50'])).
% 0.41/0.59  thf('52', plain,
% 0.41/0.59      (((m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A))
% 0.41/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.59      inference('clc', [status(thm)], ['26', '27'])).
% 0.41/0.59  thf(cc6_tdlat_3, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.41/0.59         ( l1_pre_topc @ A ) ) =>
% 0.41/0.59       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_tdlat_3 @ B ) ) ) ))).
% 0.41/0.59  thf('53', plain,
% 0.41/0.59      (![X32 : $i, X33 : $i]:
% 0.41/0.59         (~ (m1_pre_topc @ X32 @ X33)
% 0.41/0.59          | (v2_tdlat_3 @ X32)
% 0.41/0.59          | ~ (l1_pre_topc @ X33)
% 0.41/0.59          | ~ (v2_tdlat_3 @ X33)
% 0.41/0.59          | ~ (v2_pre_topc @ X33)
% 0.41/0.59          | (v2_struct_0 @ X33))),
% 0.41/0.59      inference('cnf', [status(esa)], [cc6_tdlat_3])).
% 0.41/0.59  thf('54', plain,
% 0.41/0.59      ((((v2_struct_0 @ sk_A)
% 0.41/0.59         | ~ (v2_pre_topc @ sk_A)
% 0.41/0.59         | ~ (v2_tdlat_3 @ sk_A)
% 0.41/0.59         | ~ (l1_pre_topc @ sk_A)
% 0.41/0.59         | (v2_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.41/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['52', '53'])).
% 0.41/0.59  thf('55', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('56', plain, ((v2_tdlat_3 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('58', plain,
% 0.41/0.59      ((((v2_struct_0 @ sk_A) | (v2_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.41/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.59      inference('demod', [status(thm)], ['54', '55', '56', '57'])).
% 0.41/0.59  thf('59', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('60', plain,
% 0.41/0.59      (((v2_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.41/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.59      inference('clc', [status(thm)], ['58', '59'])).
% 0.41/0.59  thf('61', plain,
% 0.41/0.59      (((l1_pre_topc @ (sk_C @ sk_B_1 @ sk_A)))
% 0.41/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.59      inference('demod', [status(thm)], ['30', '31'])).
% 0.41/0.59  thf(cc1_tdlat_3, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( l1_pre_topc @ A ) => ( ( v1_tdlat_3 @ A ) => ( v2_pre_topc @ A ) ) ))).
% 0.41/0.59  thf('62', plain,
% 0.41/0.59      (![X29 : $i]:
% 0.41/0.59         (~ (v1_tdlat_3 @ X29) | (v2_pre_topc @ X29) | ~ (l1_pre_topc @ X29))),
% 0.41/0.59      inference('cnf', [status(esa)], [cc1_tdlat_3])).
% 0.41/0.59  thf('63', plain,
% 0.41/0.59      ((((v2_pre_topc @ (sk_C @ sk_B_1 @ sk_A))
% 0.41/0.59         | ~ (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.41/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['61', '62'])).
% 0.41/0.59  thf('64', plain,
% 0.41/0.59      (((v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.41/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.59      inference('clc', [status(thm)], ['48', '49'])).
% 0.41/0.59  thf('65', plain,
% 0.41/0.59      (((v2_pre_topc @ (sk_C @ sk_B_1 @ sk_A)))
% 0.41/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.59      inference('demod', [status(thm)], ['63', '64'])).
% 0.41/0.59  thf('66', plain,
% 0.41/0.59      ((((v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.41/0.59         | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.41/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.59      inference('demod', [status(thm)], ['51', '60', '65'])).
% 0.41/0.59  thf('67', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('68', plain,
% 0.41/0.59      (![X36 : $i, X37 : $i]:
% 0.41/0.59         ((v1_xboole_0 @ X36)
% 0.41/0.59          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.41/0.59          | ~ (v2_tex_2 @ X36 @ X37)
% 0.41/0.59          | ~ (v2_struct_0 @ (sk_C @ X36 @ X37))
% 0.41/0.59          | ~ (l1_pre_topc @ X37)
% 0.41/0.59          | ~ (v2_pre_topc @ X37)
% 0.41/0.59          | (v2_struct_0 @ X37))),
% 0.41/0.59      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.41/0.59  thf('69', plain,
% 0.41/0.59      (((v2_struct_0 @ sk_A)
% 0.41/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.41/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.41/0.59        | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.41/0.59        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.41/0.59        | (v1_xboole_0 @ sk_B_1))),
% 0.41/0.59      inference('sup-', [status(thm)], ['67', '68'])).
% 0.41/0.59  thf('70', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('72', plain,
% 0.41/0.59      (((v2_struct_0 @ sk_A)
% 0.41/0.59        | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.41/0.59        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.41/0.59        | (v1_xboole_0 @ sk_B_1))),
% 0.41/0.59      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.41/0.59  thf('73', plain,
% 0.41/0.59      ((((v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.41/0.59         | (v1_xboole_0 @ sk_B_1)
% 0.41/0.59         | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.41/0.59         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['66', '72'])).
% 0.41/0.59  thf('74', plain,
% 0.41/0.59      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.59      inference('split', [status(esa)], ['2'])).
% 0.41/0.59  thf('75', plain,
% 0.41/0.59      ((((v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.41/0.59         | (v1_xboole_0 @ sk_B_1)
% 0.41/0.59         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.59      inference('demod', [status(thm)], ['73', '74'])).
% 0.41/0.59  thf('76', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('77', plain,
% 0.41/0.59      ((((v2_struct_0 @ sk_A) | (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.41/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.59      inference('clc', [status(thm)], ['75', '76'])).
% 0.41/0.59  thf('78', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('79', plain,
% 0.41/0.59      (((v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.41/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.59      inference('clc', [status(thm)], ['77', '78'])).
% 0.41/0.59  thf('80', plain,
% 0.41/0.59      (((v1_zfmisc_1 @ sk_B_1)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.59      inference('demod', [status(thm)], ['35', '79'])).
% 0.41/0.59  thf('81', plain,
% 0.41/0.59      ((~ (v1_zfmisc_1 @ sk_B_1)) <= (~ ((v1_zfmisc_1 @ sk_B_1)))),
% 0.41/0.59      inference('split', [status(esa)], ['0'])).
% 0.41/0.59  thf('82', plain, (((v1_zfmisc_1 @ sk_B_1)) | ~ ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.41/0.59      inference('sup-', [status(thm)], ['80', '81'])).
% 0.41/0.59  thf('83', plain, (((v1_zfmisc_1 @ sk_B_1)) | ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.41/0.59      inference('split', [status(esa)], ['2'])).
% 0.41/0.59  thf('84', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.41/0.59      inference('split', [status(esa)], ['2'])).
% 0.41/0.59  thf(d1_xboole_0, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.41/0.59  thf('85', plain,
% 0.41/0.59      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.41/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.59  thf(d2_subset_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( ( v1_xboole_0 @ A ) =>
% 0.41/0.59         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.41/0.59       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.41/0.59         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.41/0.59  thf('86', plain,
% 0.41/0.59      (![X10 : $i, X11 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X10 @ X11)
% 0.41/0.59          | (m1_subset_1 @ X10 @ X11)
% 0.41/0.59          | (v1_xboole_0 @ X11))),
% 0.41/0.59      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.41/0.59  thf('87', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.41/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.59  thf('88', plain,
% 0.41/0.59      (![X10 : $i, X11 : $i]:
% 0.41/0.59         ((m1_subset_1 @ X10 @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 0.41/0.59      inference('clc', [status(thm)], ['86', '87'])).
% 0.41/0.59  thf('89', plain,
% 0.41/0.59      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['85', '88'])).
% 0.41/0.59  thf(redefinition_k6_domain_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.41/0.59       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.41/0.59  thf('90', plain,
% 0.41/0.59      (![X27 : $i, X28 : $i]:
% 0.41/0.59         ((v1_xboole_0 @ X27)
% 0.41/0.59          | ~ (m1_subset_1 @ X28 @ X27)
% 0.41/0.59          | ((k6_domain_1 @ X27 @ X28) = (k1_tarski @ X28)))),
% 0.41/0.59      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.41/0.59  thf('91', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((v1_xboole_0 @ X0)
% 0.41/0.59          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.41/0.59          | (v1_xboole_0 @ X0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['89', '90'])).
% 0.41/0.59  thf('92', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.41/0.59          | (v1_xboole_0 @ X0))),
% 0.41/0.59      inference('simplify', [status(thm)], ['91'])).
% 0.41/0.59  thf('93', plain,
% 0.41/0.59      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['85', '88'])).
% 0.41/0.59  thf(dt_k6_domain_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.41/0.59       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.41/0.59  thf('94', plain,
% 0.41/0.59      (![X25 : $i, X26 : $i]:
% 0.41/0.59         ((v1_xboole_0 @ X25)
% 0.41/0.59          | ~ (m1_subset_1 @ X26 @ X25)
% 0.41/0.59          | (m1_subset_1 @ (k6_domain_1 @ X25 @ X26) @ (k1_zfmisc_1 @ X25)))),
% 0.41/0.59      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.41/0.59  thf('95', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((v1_xboole_0 @ X0)
% 0.41/0.59          | (m1_subset_1 @ (k6_domain_1 @ X0 @ (sk_B @ X0)) @ 
% 0.41/0.59             (k1_zfmisc_1 @ X0))
% 0.41/0.59          | (v1_xboole_0 @ X0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['93', '94'])).
% 0.41/0.59  thf('96', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((m1_subset_1 @ (k6_domain_1 @ X0 @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 0.41/0.59          | (v1_xboole_0 @ X0))),
% 0.41/0.59      inference('simplify', [status(thm)], ['95'])).
% 0.41/0.59  thf(t3_subset, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.41/0.59  thf('97', plain,
% 0.41/0.59      (![X15 : $i, X16 : $i]:
% 0.41/0.59         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.41/0.59  thf('98', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((v1_xboole_0 @ X0)
% 0.41/0.59          | (r1_tarski @ (k6_domain_1 @ X0 @ (sk_B @ X0)) @ X0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['96', '97'])).
% 0.41/0.59  thf('99', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0)
% 0.41/0.59          | (v1_xboole_0 @ X0)
% 0.41/0.59          | (v1_xboole_0 @ X0))),
% 0.41/0.59      inference('sup+', [status(thm)], ['92', '98'])).
% 0.41/0.59  thf('100', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.41/0.59      inference('simplify', [status(thm)], ['99'])).
% 0.41/0.59  thf(t1_tex_2, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.41/0.59       ( ![B:$i]:
% 0.41/0.59         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.41/0.59           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.41/0.59  thf('101', plain,
% 0.41/0.59      (![X34 : $i, X35 : $i]:
% 0.41/0.59         ((v1_xboole_0 @ X34)
% 0.41/0.59          | ~ (v1_zfmisc_1 @ X34)
% 0.41/0.59          | ((X35) = (X34))
% 0.41/0.59          | ~ (r1_tarski @ X35 @ X34)
% 0.41/0.59          | (v1_xboole_0 @ X35))),
% 0.41/0.59      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.41/0.59  thf('102', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((v1_xboole_0 @ X0)
% 0.41/0.59          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.41/0.59          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.41/0.59          | ~ (v1_zfmisc_1 @ X0)
% 0.41/0.59          | (v1_xboole_0 @ X0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['100', '101'])).
% 0.41/0.59  thf('103', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (~ (v1_zfmisc_1 @ X0)
% 0.41/0.59          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.41/0.59          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.41/0.59          | (v1_xboole_0 @ X0))),
% 0.41/0.59      inference('simplify', [status(thm)], ['102'])).
% 0.41/0.59  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.41/0.59  thf('104', plain, (![X9 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X9))),
% 0.41/0.59      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.41/0.59  thf('105', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((v1_xboole_0 @ X0)
% 0.41/0.59          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.41/0.59          | ~ (v1_zfmisc_1 @ X0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['103', '104'])).
% 0.41/0.59  thf('106', plain,
% 0.41/0.59      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.41/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.59  thf('107', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(t4_subset, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.41/0.59       ( m1_subset_1 @ A @ C ) ))).
% 0.41/0.59  thf('108', plain,
% 0.41/0.59      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X18 @ X19)
% 0.41/0.59          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 0.41/0.59          | (m1_subset_1 @ X18 @ X20))),
% 0.41/0.59      inference('cnf', [status(esa)], [t4_subset])).
% 0.41/0.59  thf('109', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.41/0.59          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.41/0.59      inference('sup-', [status(thm)], ['107', '108'])).
% 0.41/0.59  thf('110', plain,
% 0.41/0.59      (((v1_xboole_0 @ sk_B_1)
% 0.41/0.59        | (m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['106', '109'])).
% 0.41/0.59  thf('111', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('112', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.41/0.59      inference('clc', [status(thm)], ['110', '111'])).
% 0.41/0.59  thf(t36_tex_2, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.59       ( ![B:$i]:
% 0.41/0.59         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.41/0.59           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.41/0.59  thf('113', plain,
% 0.41/0.59      (![X38 : $i, X39 : $i]:
% 0.41/0.59         (~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X39))
% 0.41/0.59          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X39) @ X38) @ X39)
% 0.41/0.59          | ~ (l1_pre_topc @ X39)
% 0.41/0.59          | ~ (v2_pre_topc @ X39)
% 0.41/0.59          | (v2_struct_0 @ X39))),
% 0.41/0.59      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.41/0.59  thf('114', plain,
% 0.41/0.59      (((v2_struct_0 @ sk_A)
% 0.41/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.41/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.41/0.59        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.41/0.59           sk_A))),
% 0.41/0.59      inference('sup-', [status(thm)], ['112', '113'])).
% 0.41/0.59  thf('115', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('116', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('117', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.41/0.59      inference('clc', [status(thm)], ['110', '111'])).
% 0.41/0.59  thf('118', plain,
% 0.41/0.59      (![X27 : $i, X28 : $i]:
% 0.41/0.59         ((v1_xboole_0 @ X27)
% 0.41/0.59          | ~ (m1_subset_1 @ X28 @ X27)
% 0.41/0.59          | ((k6_domain_1 @ X27 @ X28) = (k1_tarski @ X28)))),
% 0.41/0.59      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.41/0.59  thf('119', plain,
% 0.41/0.59      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.41/0.59          = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.41/0.59        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['117', '118'])).
% 0.41/0.59  thf('120', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(cc1_subset_1, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( v1_xboole_0 @ A ) =>
% 0.41/0.59       ( ![B:$i]:
% 0.41/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.41/0.59  thf('121', plain,
% 0.41/0.59      (![X13 : $i, X14 : $i]:
% 0.41/0.59         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.41/0.59          | (v1_xboole_0 @ X13)
% 0.41/0.59          | ~ (v1_xboole_0 @ X14))),
% 0.41/0.59      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.41/0.59  thf('122', plain,
% 0.41/0.59      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_B_1))),
% 0.41/0.59      inference('sup-', [status(thm)], ['120', '121'])).
% 0.41/0.59  thf('123', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('124', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.41/0.59      inference('clc', [status(thm)], ['122', '123'])).
% 0.41/0.59  thf('125', plain,
% 0.41/0.59      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.41/0.59         = (k1_tarski @ (sk_B @ sk_B_1)))),
% 0.41/0.59      inference('clc', [status(thm)], ['119', '124'])).
% 0.41/0.59  thf('126', plain,
% 0.41/0.59      (((v2_struct_0 @ sk_A)
% 0.41/0.59        | (v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A))),
% 0.41/0.59      inference('demod', [status(thm)], ['114', '115', '116', '125'])).
% 0.41/0.59  thf('127', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('128', plain, ((v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A)),
% 0.41/0.59      inference('clc', [status(thm)], ['126', '127'])).
% 0.41/0.59  thf('129', plain,
% 0.41/0.59      (((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.41/0.59        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.41/0.59        | (v1_xboole_0 @ sk_B_1))),
% 0.41/0.59      inference('sup+', [status(thm)], ['105', '128'])).
% 0.41/0.59  thf('130', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('131', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.41/0.59      inference('clc', [status(thm)], ['129', '130'])).
% 0.41/0.59  thf('132', plain,
% 0.41/0.59      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['84', '131'])).
% 0.41/0.59  thf('133', plain,
% 0.41/0.59      ((~ (v2_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.41/0.59      inference('split', [status(esa)], ['0'])).
% 0.41/0.59  thf('134', plain,
% 0.41/0.59      (~ ((v1_zfmisc_1 @ sk_B_1)) | ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.41/0.59      inference('sup-', [status(thm)], ['132', '133'])).
% 0.41/0.59  thf('135', plain, ($false),
% 0.41/0.59      inference('sat_resolution*', [status(thm)], ['1', '82', '83', '134'])).
% 0.41/0.59  
% 0.41/0.59  % SZS output end Refutation
% 0.41/0.59  
% 0.44/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
