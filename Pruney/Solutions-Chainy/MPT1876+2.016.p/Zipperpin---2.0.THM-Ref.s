%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mpdAvlI6YA

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:57 EST 2020

% Result     : Theorem 0.81s
% Output     : Refutation 0.81s
% Verified   : 
% Statistics : Number of formulae       :  262 (1028 expanded)
%              Number of leaves         :   48 ( 299 expanded)
%              Depth                    :   34
%              Number of atoms          : 2055 (12283 expanded)
%              Number of equality atoms :   47 ( 143 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m2_subset_1_type,type,(
    m2_subset_1: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X41: $i,X42: $i] :
      ( ( v1_xboole_0 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( v2_tex_2 @ X41 @ X42 )
      | ( X41
        = ( u1_struct_0 @ ( sk_C_3 @ X41 @ X42 ) ) )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v2_pre_topc @ X42 )
      | ( v2_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_3 @ sk_B_1 @ sk_A ) ) )
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
      = ( u1_struct_0 @ ( sk_C_3 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( sk_B_1
        = ( u1_struct_0 @ ( sk_C_3 @ sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( sk_B_1
        = ( u1_struct_0 @ ( sk_C_3 @ sk_B_1 @ sk_A ) ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_3 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['12','13'])).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('15',plain,(
    ! [X27: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 )
      | ~ ( v7_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('16',plain,
    ( ( ( v1_zfmisc_1 @ sk_B_1 )
      | ~ ( v7_struct_0 @ ( sk_C_3 @ sk_B_1 @ sk_A ) )
      | ~ ( l1_struct_0 @ ( sk_C_3 @ sk_B_1 @ sk_A ) ) )
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
    ! [X41: $i,X42: $i] :
      ( ( v1_xboole_0 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( v2_tex_2 @ X41 @ X42 )
      | ( m1_pre_topc @ ( sk_C_3 @ X41 @ X42 ) @ X42 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v2_pre_topc @ X42 )
      | ( v2_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('20',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C_3 @ sk_B_1 @ sk_A ) @ sk_A )
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
    | ( m1_pre_topc @ ( sk_C_3 @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( m1_pre_topc @ ( sk_C_3 @ sk_B_1 @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_pre_topc @ ( sk_C_3 @ sk_B_1 @ sk_A ) @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( m1_pre_topc @ ( sk_C_3 @ sk_B_1 @ sk_A ) @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['26','27'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('29',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ( l1_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('30',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( l1_pre_topc @ ( sk_C_3 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( l1_pre_topc @ ( sk_C_3 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('33',plain,(
    ! [X24: $i] :
      ( ( l1_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('34',plain,
    ( ( l1_struct_0 @ ( sk_C_3 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( v1_zfmisc_1 @ sk_B_1 )
      | ~ ( v7_struct_0 @ ( sk_C_3 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['16','34'])).

thf('36',plain,
    ( ( l1_pre_topc @ ( sk_C_3 @ sk_B_1 @ sk_A ) )
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
    ! [X34: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ~ ( v1_tdlat_3 @ X34 )
      | ~ ( v2_tdlat_3 @ X34 )
      | ( v7_struct_0 @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[cc2_tex_1])).

thf('38',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X41: $i,X42: $i] :
      ( ( v1_xboole_0 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( v2_tex_2 @ X41 @ X42 )
      | ~ ( v2_struct_0 @ ( sk_C_3 @ X41 @ X42 ) )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v2_pre_topc @ X42 )
      | ( v2_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_3 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_3 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ~ ( l1_pre_topc @ ( sk_C_3 @ sk_B_1 @ sk_A ) )
    | ( v7_struct_0 @ ( sk_C_3 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tdlat_3 @ ( sk_C_3 @ sk_B_1 @ sk_A ) )
    | ~ ( v1_tdlat_3 @ ( sk_C_3 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_pre_topc @ ( sk_C_3 @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','43'])).

thf('45',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v2_pre_topc @ ( sk_C_3 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_tdlat_3 @ ( sk_C_3 @ sk_B_1 @ sk_A ) )
      | ~ ( v2_tdlat_3 @ ( sk_C_3 @ sk_B_1 @ sk_A ) )
      | ( v7_struct_0 @ ( sk_C_3 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','44'])).

thf('46',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('47',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('48',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X41: $i,X42: $i] :
      ( ( v1_xboole_0 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( v2_tex_2 @ X41 @ X42 )
      | ( v1_tdlat_3 @ ( sk_C_3 @ X41 @ X42 ) )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v2_pre_topc @ X42 )
      | ( v2_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_3 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_3 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_tdlat_3 @ ( sk_C_3 @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','53'])).

thf('55',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_tdlat_3 @ ( sk_C_3 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v1_tdlat_3 @ ( sk_C_3 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v2_pre_topc @ ( sk_C_3 @ sk_B_1 @ sk_A ) )
      | ~ ( v2_tdlat_3 @ ( sk_C_3 @ sk_B_1 @ sk_A ) )
      | ( v7_struct_0 @ ( sk_C_3 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['45','46','58'])).

thf('60',plain,
    ( ( l1_pre_topc @ ( sk_C_3 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(cc2_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_tdlat_3 @ A )
       => ( v2_pre_topc @ A ) ) ) )).

thf('61',plain,(
    ! [X33: $i] :
      ( ~ ( v2_tdlat_3 @ X33 )
      | ( v2_pre_topc @ X33 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[cc2_tdlat_3])).

thf('62',plain,
    ( ( ( v2_pre_topc @ ( sk_C_3 @ sk_B_1 @ sk_A ) )
      | ~ ( v2_tdlat_3 @ ( sk_C_3 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( m1_pre_topc @ ( sk_C_3 @ sk_B_1 @ sk_A ) @ sk_A )
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

thf('64',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_pre_topc @ X35 @ X36 )
      | ( v2_tdlat_3 @ X35 )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_tdlat_3 @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[cc6_tdlat_3])).

thf('65',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v2_tdlat_3 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_tdlat_3 @ ( sk_C_3 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_tdlat_3 @ ( sk_C_3 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['65','66','67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v2_tdlat_3 @ ( sk_C_3 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( v2_pre_topc @ ( sk_C_3 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['62','71'])).

thf('73',plain,
    ( ( v2_tdlat_3 @ ( sk_C_3 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('74',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v7_struct_0 @ ( sk_C_3 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['59','72','73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( ( v7_struct_0 @ ( sk_C_3 @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( v7_struct_0 @ ( sk_C_3 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['35','78'])).

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

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('83',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('84',plain,(
    ! [X14: $i,X15: $i] :
      ( ( m1_subset_1 @ X14 @ X15 )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('86',plain,(
    ! [X31: $i,X32: $i] :
      ( ( v1_xboole_0 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ X31 )
      | ( ( k6_domain_1 @ X31 @ X32 )
        = ( k1_tarski @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('90',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X9 ) @ X11 )
      | ~ ( r2_hidden @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('92',plain,(
    ! [X39: $i,X40: $i] :
      ( ( v1_xboole_0 @ X39 )
      | ~ ( v1_zfmisc_1 @ X39 )
      | ( X40 = X39 )
      | ~ ( r1_tarski @ X40 @ X39 )
      | ( v1_xboole_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('95',plain,(
    ! [X8: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['88','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('100',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(existence_m2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) )
     => ? [C: $i] :
          ( m2_subset_1 @ C @ A @ B ) ) )).

thf('101',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) )
      | ( m2_subset_1 @ ( sk_C_1 @ X19 @ X18 ) @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[existence_m2_subset_1])).

thf('102',plain,
    ( ( m2_subset_1 @ ( sk_C_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m2_subset_1 @ ( sk_C_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('106',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( v1_xboole_0 @ X12 )
      | ~ ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('107',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,(
    m2_subset_1 @ ( sk_C_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ),
    inference(clc,[status(thm)],['104','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_m2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m2_subset_1 @ C @ A @ B )
        <=> ( m1_subset_1 @ C @ B ) ) ) )).

thf('112',plain,(
    ! [X20: $i,X21: $i,X23: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) )
      | ( m1_subset_1 @ X23 @ X21 )
      | ~ ( m2_subset_1 @ X23 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_m2_subset_1])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( m2_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      | ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['110','113'])).

thf('115',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('116',plain,
    ( ( m1_subset_1 @ ( sk_C_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['114','115'])).

thf('117',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    m1_subset_1 @ ( sk_C_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 ),
    inference(clc,[status(thm)],['116','117'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('119',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r2_hidden @ X16 @ X17 )
      | ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('120',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_C_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('124',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( X6 = X3 )
      | ( X5
       != ( k1_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('125',plain,(
    ! [X3: $i,X6: $i] :
      ( ( X6 = X3 )
      | ~ ( r2_hidden @ X6 @ ( k1_tarski @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X1
        = ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['123','125'])).

thf('127',plain,
    ( ( ( sk_C_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      = ( sk_B @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['122','126'])).

thf('128',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( ( sk_C_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      = ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('130',plain,
    ( ( ( sk_C_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      = ( sk_B @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['99','129'])).

thf('131',plain,(
    m1_subset_1 @ ( sk_C_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 ),
    inference(clc,[status(thm)],['116','117'])).

thf('132',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X31: $i,X32: $i] :
      ( ( v1_xboole_0 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ X31 )
      | ( ( k6_domain_1 @ X31 @ X32 )
        = ( k1_tarski @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('134',plain,
    ( ( ( ( k6_domain_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
        = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( ( k6_domain_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['134','135'])).

thf('137',plain,
    ( ( ( sk_B_1
        = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_zfmisc_1 @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['98','136'])).

thf('138',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('139',plain,
    ( ( ( sk_B_1
        = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( sk_B_1
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['139','140'])).

thf('142',plain,(
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

thf('143',plain,(
    ! [X37: $i,X38: $i] :
      ( ( v1_xboole_0 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( m1_pre_topc @ ( sk_C_2 @ X37 @ X38 ) @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('144',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C_2 @ sk_B_1 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C_2 @ sk_B_1 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m1_pre_topc @ ( sk_C_2 @ sk_B_1 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('149',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    m1_pre_topc @ ( sk_C_2 @ sk_B_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

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

thf('152',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X29 )
      | ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t55_pre_topc])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,
    ( ( v2_struct_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_B @ ( u1_struct_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['150','153'])).

thf('155',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    ! [X37: $i,X38: $i] :
      ( ( v1_xboole_0 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( X37
        = ( u1_struct_0 @ ( sk_C_2 @ X37 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('157',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['159','160'])).

thf('162',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( sk_B_1
    = ( u1_struct_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['161','162'])).

thf('164',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( sk_B_1
    = ( u1_struct_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['161','162'])).

thf('166',plain,
    ( ( v2_struct_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['154','163','164','165'])).

thf('167',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r2_hidden @ X16 @ X17 )
      | ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('168',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X9 ) @ X11 )
      | ~ ( r2_hidden @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('170',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( r1_tarski @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,
    ( ( ( r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['141','170'])).

thf('172',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    ! [X37: $i,X38: $i] :
      ( ( v1_xboole_0 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( v2_struct_0 @ ( sk_C_2 @ X37 @ X38 ) )
      | ~ ( l1_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('174',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v2_struct_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['176','177'])).

thf('179',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    ~ ( v2_struct_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['178','179'])).

thf('181',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['171','180'])).

thf('182',plain,
    ( ( sk_B_1
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['139','140'])).

thf('183',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_tarski @ ( k1_tarski @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('184',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_B_1 @ X0 )
        | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ X0 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['181','184'])).

thf('186',plain,(
    ! [X14: $i,X15: $i] :
      ( ( m1_subset_1 @ X14 @ X15 )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('187',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,(
    ! [X31: $i,X32: $i] :
      ( ( v1_xboole_0 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ X31 )
      | ( ( k6_domain_1 @ X31 @ X32 )
        = ( k1_tarski @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('189',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
        = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,
    ( ( sk_B_1
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['139','140'])).

thf('191',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
        = sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['189','190'])).

thf('192',plain,
    ( ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
        = sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['191'])).

thf('193',plain,
    ( ( v2_struct_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['154','163','164','165'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('194',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( u1_struct_0 @ X44 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X44 ) @ X43 ) @ X44 )
      | ~ ( l1_pre_topc @ X44 )
      | ~ ( v2_pre_topc @ X44 )
      | ( v2_struct_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('195',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['195','196','197'])).

thf('199',plain,
    ( ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A )
    | ( v2_struct_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['198'])).

thf('200',plain,
    ( ( ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['192','199'])).

thf('201',plain,
    ( ( ( v2_struct_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['200'])).

thf('202',plain,(
    ~ ( v2_struct_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['178','179'])).

thf('203',plain,
    ( ( ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('205',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ( ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['205','206'])).

thf('208',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['207','208'])).

thf('210',plain,
    ( ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('211',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['209','210'])).

thf('212',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','81','82','211'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mpdAvlI6YA
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:11:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.81/1.01  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.81/1.01  % Solved by: fo/fo7.sh
% 0.81/1.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.81/1.01  % done 669 iterations in 0.505s
% 0.81/1.01  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.81/1.01  % SZS output start Refutation
% 0.81/1.01  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.81/1.01  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.81/1.01  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.81/1.01  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.81/1.01  thf(sk_B_type, type, sk_B: $i > $i).
% 0.81/1.01  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.81/1.01  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.81/1.01  thf(sk_A_type, type, sk_A: $i).
% 0.81/1.01  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.81/1.01  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.81/1.01  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.81/1.01  thf(m2_subset_1_type, type, m2_subset_1: $i > $i > $i > $o).
% 0.81/1.01  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.81/1.01  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.81/1.01  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.81/1.01  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.81/1.01  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 0.81/1.01  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.81/1.01  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.81/1.01  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.81/1.01  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.81/1.01  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.81/1.01  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.81/1.01  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.81/1.01  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.81/1.01  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.81/1.01  thf(t44_tex_2, conjecture,
% 0.81/1.01    (![A:$i]:
% 0.81/1.01     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.81/1.01         ( l1_pre_topc @ A ) ) =>
% 0.81/1.01       ( ![B:$i]:
% 0.81/1.01         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.81/1.01             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.81/1.01           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.81/1.01  thf(zf_stmt_0, negated_conjecture,
% 0.81/1.01    (~( ![A:$i]:
% 0.81/1.01        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.81/1.01            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.81/1.01          ( ![B:$i]:
% 0.81/1.01            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.81/1.01                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.81/1.01              ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.81/1.01    inference('cnf.neg', [status(esa)], [t44_tex_2])).
% 0.81/1.01  thf('0', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('1', plain,
% 0.81/1.01      (~ ((v1_zfmisc_1 @ sk_B_1)) | ~ ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.81/1.01      inference('split', [status(esa)], ['0'])).
% 0.81/1.01  thf('2', plain, (((v1_zfmisc_1 @ sk_B_1) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('3', plain,
% 0.81/1.01      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.81/1.01      inference('split', [status(esa)], ['2'])).
% 0.81/1.01  thf('4', plain,
% 0.81/1.01      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf(t34_tex_2, axiom,
% 0.81/1.01    (![A:$i]:
% 0.81/1.01     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.81/1.01       ( ![B:$i]:
% 0.81/1.01         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.81/1.01             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.81/1.01           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.81/1.01                ( ![C:$i]:
% 0.81/1.01                  ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.81/1.01                      ( v1_tdlat_3 @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.81/1.01                    ( ( B ) != ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ))).
% 0.81/1.01  thf('5', plain,
% 0.81/1.01      (![X41 : $i, X42 : $i]:
% 0.81/1.01         ((v1_xboole_0 @ X41)
% 0.81/1.01          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.81/1.01          | ~ (v2_tex_2 @ X41 @ X42)
% 0.81/1.01          | ((X41) = (u1_struct_0 @ (sk_C_3 @ X41 @ X42)))
% 0.81/1.01          | ~ (l1_pre_topc @ X42)
% 0.81/1.01          | ~ (v2_pre_topc @ X42)
% 0.81/1.01          | (v2_struct_0 @ X42))),
% 0.81/1.01      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.81/1.01  thf('6', plain,
% 0.81/1.01      (((v2_struct_0 @ sk_A)
% 0.81/1.01        | ~ (v2_pre_topc @ sk_A)
% 0.81/1.01        | ~ (l1_pre_topc @ sk_A)
% 0.81/1.01        | ((sk_B_1) = (u1_struct_0 @ (sk_C_3 @ sk_B_1 @ sk_A)))
% 0.81/1.01        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.81/1.01        | (v1_xboole_0 @ sk_B_1))),
% 0.81/1.01      inference('sup-', [status(thm)], ['4', '5'])).
% 0.81/1.01  thf('7', plain, ((v2_pre_topc @ sk_A)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('9', plain,
% 0.81/1.01      (((v2_struct_0 @ sk_A)
% 0.81/1.01        | ((sk_B_1) = (u1_struct_0 @ (sk_C_3 @ sk_B_1 @ sk_A)))
% 0.81/1.01        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.81/1.01        | (v1_xboole_0 @ sk_B_1))),
% 0.81/1.01      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.81/1.01  thf('10', plain,
% 0.81/1.01      ((((v1_xboole_0 @ sk_B_1)
% 0.81/1.01         | ((sk_B_1) = (u1_struct_0 @ (sk_C_3 @ sk_B_1 @ sk_A)))
% 0.81/1.01         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.81/1.01      inference('sup-', [status(thm)], ['3', '9'])).
% 0.81/1.01  thf('11', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('12', plain,
% 0.81/1.01      ((((v2_struct_0 @ sk_A)
% 0.81/1.01         | ((sk_B_1) = (u1_struct_0 @ (sk_C_3 @ sk_B_1 @ sk_A)))))
% 0.81/1.01         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.81/1.01      inference('clc', [status(thm)], ['10', '11'])).
% 0.81/1.01  thf('13', plain, (~ (v2_struct_0 @ sk_A)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('14', plain,
% 0.81/1.01      ((((sk_B_1) = (u1_struct_0 @ (sk_C_3 @ sk_B_1 @ sk_A))))
% 0.81/1.01         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.81/1.01      inference('clc', [status(thm)], ['12', '13'])).
% 0.81/1.01  thf(fc7_struct_0, axiom,
% 0.81/1.01    (![A:$i]:
% 0.81/1.01     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.81/1.01       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.81/1.01  thf('15', plain,
% 0.81/1.01      (![X27 : $i]:
% 0.81/1.01         ((v1_zfmisc_1 @ (u1_struct_0 @ X27))
% 0.81/1.01          | ~ (l1_struct_0 @ X27)
% 0.81/1.01          | ~ (v7_struct_0 @ X27))),
% 0.81/1.01      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.81/1.01  thf('16', plain,
% 0.81/1.01      ((((v1_zfmisc_1 @ sk_B_1)
% 0.81/1.01         | ~ (v7_struct_0 @ (sk_C_3 @ sk_B_1 @ sk_A))
% 0.81/1.01         | ~ (l1_struct_0 @ (sk_C_3 @ sk_B_1 @ sk_A))))
% 0.81/1.01         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.81/1.01      inference('sup+', [status(thm)], ['14', '15'])).
% 0.81/1.01  thf('17', plain,
% 0.81/1.01      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.81/1.01      inference('split', [status(esa)], ['2'])).
% 0.81/1.01  thf('18', plain,
% 0.81/1.01      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('19', plain,
% 0.81/1.01      (![X41 : $i, X42 : $i]:
% 0.81/1.01         ((v1_xboole_0 @ X41)
% 0.81/1.01          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.81/1.01          | ~ (v2_tex_2 @ X41 @ X42)
% 0.81/1.01          | (m1_pre_topc @ (sk_C_3 @ X41 @ X42) @ X42)
% 0.81/1.01          | ~ (l1_pre_topc @ X42)
% 0.81/1.01          | ~ (v2_pre_topc @ X42)
% 0.81/1.01          | (v2_struct_0 @ X42))),
% 0.81/1.01      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.81/1.01  thf('20', plain,
% 0.81/1.01      (((v2_struct_0 @ sk_A)
% 0.81/1.01        | ~ (v2_pre_topc @ sk_A)
% 0.81/1.01        | ~ (l1_pre_topc @ sk_A)
% 0.81/1.01        | (m1_pre_topc @ (sk_C_3 @ sk_B_1 @ sk_A) @ sk_A)
% 0.81/1.01        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.81/1.01        | (v1_xboole_0 @ sk_B_1))),
% 0.81/1.01      inference('sup-', [status(thm)], ['18', '19'])).
% 0.81/1.01  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('23', plain,
% 0.81/1.01      (((v2_struct_0 @ sk_A)
% 0.81/1.01        | (m1_pre_topc @ (sk_C_3 @ sk_B_1 @ sk_A) @ sk_A)
% 0.81/1.01        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.81/1.01        | (v1_xboole_0 @ sk_B_1))),
% 0.81/1.01      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.81/1.01  thf('24', plain,
% 0.81/1.01      ((((v1_xboole_0 @ sk_B_1)
% 0.81/1.01         | (m1_pre_topc @ (sk_C_3 @ sk_B_1 @ sk_A) @ sk_A)
% 0.81/1.01         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.81/1.01      inference('sup-', [status(thm)], ['17', '23'])).
% 0.81/1.01  thf('25', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('26', plain,
% 0.81/1.01      ((((v2_struct_0 @ sk_A) | (m1_pre_topc @ (sk_C_3 @ sk_B_1 @ sk_A) @ sk_A)))
% 0.81/1.01         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.81/1.01      inference('clc', [status(thm)], ['24', '25'])).
% 0.81/1.01  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('28', plain,
% 0.81/1.01      (((m1_pre_topc @ (sk_C_3 @ sk_B_1 @ sk_A) @ sk_A))
% 0.81/1.01         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.81/1.01      inference('clc', [status(thm)], ['26', '27'])).
% 0.81/1.01  thf(dt_m1_pre_topc, axiom,
% 0.81/1.01    (![A:$i]:
% 0.81/1.01     ( ( l1_pre_topc @ A ) =>
% 0.81/1.01       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.81/1.01  thf('29', plain,
% 0.81/1.01      (![X25 : $i, X26 : $i]:
% 0.81/1.01         (~ (m1_pre_topc @ X25 @ X26)
% 0.81/1.01          | (l1_pre_topc @ X25)
% 0.81/1.01          | ~ (l1_pre_topc @ X26))),
% 0.81/1.01      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.81/1.01  thf('30', plain,
% 0.81/1.01      (((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (sk_C_3 @ sk_B_1 @ sk_A))))
% 0.81/1.01         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.81/1.01      inference('sup-', [status(thm)], ['28', '29'])).
% 0.81/1.01  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('32', plain,
% 0.81/1.01      (((l1_pre_topc @ (sk_C_3 @ sk_B_1 @ sk_A)))
% 0.81/1.01         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.81/1.01      inference('demod', [status(thm)], ['30', '31'])).
% 0.81/1.01  thf(dt_l1_pre_topc, axiom,
% 0.81/1.01    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.81/1.01  thf('33', plain,
% 0.81/1.01      (![X24 : $i]: ((l1_struct_0 @ X24) | ~ (l1_pre_topc @ X24))),
% 0.81/1.01      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.81/1.01  thf('34', plain,
% 0.81/1.01      (((l1_struct_0 @ (sk_C_3 @ sk_B_1 @ sk_A)))
% 0.81/1.01         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.81/1.01      inference('sup-', [status(thm)], ['32', '33'])).
% 0.81/1.01  thf('35', plain,
% 0.81/1.01      ((((v1_zfmisc_1 @ sk_B_1) | ~ (v7_struct_0 @ (sk_C_3 @ sk_B_1 @ sk_A))))
% 0.81/1.01         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.81/1.01      inference('demod', [status(thm)], ['16', '34'])).
% 0.81/1.01  thf('36', plain,
% 0.81/1.01      (((l1_pre_topc @ (sk_C_3 @ sk_B_1 @ sk_A)))
% 0.81/1.01         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.81/1.01      inference('demod', [status(thm)], ['30', '31'])).
% 0.81/1.01  thf(cc2_tex_1, axiom,
% 0.81/1.01    (![A:$i]:
% 0.81/1.01     ( ( l1_pre_topc @ A ) =>
% 0.81/1.01       ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.81/1.01           ( v1_tdlat_3 @ A ) & ( v2_tdlat_3 @ A ) ) =>
% 0.81/1.01         ( ( ~( v2_struct_0 @ A ) ) & ( v7_struct_0 @ A ) & ( v2_pre_topc @ A ) ) ) ))).
% 0.81/1.01  thf('37', plain,
% 0.81/1.01      (![X34 : $i]:
% 0.81/1.01         ((v2_struct_0 @ X34)
% 0.81/1.01          | ~ (v2_pre_topc @ X34)
% 0.81/1.01          | ~ (v1_tdlat_3 @ X34)
% 0.81/1.01          | ~ (v2_tdlat_3 @ X34)
% 0.81/1.01          | (v7_struct_0 @ X34)
% 0.81/1.01          | ~ (l1_pre_topc @ X34))),
% 0.81/1.01      inference('cnf', [status(esa)], [cc2_tex_1])).
% 0.81/1.01  thf('38', plain,
% 0.81/1.01      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('39', plain,
% 0.81/1.01      (![X41 : $i, X42 : $i]:
% 0.81/1.01         ((v1_xboole_0 @ X41)
% 0.81/1.01          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.81/1.01          | ~ (v2_tex_2 @ X41 @ X42)
% 0.81/1.01          | ~ (v2_struct_0 @ (sk_C_3 @ X41 @ X42))
% 0.81/1.01          | ~ (l1_pre_topc @ X42)
% 0.81/1.01          | ~ (v2_pre_topc @ X42)
% 0.81/1.01          | (v2_struct_0 @ X42))),
% 0.81/1.01      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.81/1.01  thf('40', plain,
% 0.81/1.01      (((v2_struct_0 @ sk_A)
% 0.81/1.01        | ~ (v2_pre_topc @ sk_A)
% 0.81/1.01        | ~ (l1_pre_topc @ sk_A)
% 0.81/1.01        | ~ (v2_struct_0 @ (sk_C_3 @ sk_B_1 @ sk_A))
% 0.81/1.01        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.81/1.01        | (v1_xboole_0 @ sk_B_1))),
% 0.81/1.01      inference('sup-', [status(thm)], ['38', '39'])).
% 0.81/1.01  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('43', plain,
% 0.81/1.01      (((v2_struct_0 @ sk_A)
% 0.81/1.01        | ~ (v2_struct_0 @ (sk_C_3 @ sk_B_1 @ sk_A))
% 0.81/1.01        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.81/1.01        | (v1_xboole_0 @ sk_B_1))),
% 0.81/1.01      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.81/1.01  thf('44', plain,
% 0.81/1.01      ((~ (l1_pre_topc @ (sk_C_3 @ sk_B_1 @ sk_A))
% 0.81/1.01        | (v7_struct_0 @ (sk_C_3 @ sk_B_1 @ sk_A))
% 0.81/1.01        | ~ (v2_tdlat_3 @ (sk_C_3 @ sk_B_1 @ sk_A))
% 0.81/1.01        | ~ (v1_tdlat_3 @ (sk_C_3 @ sk_B_1 @ sk_A))
% 0.81/1.01        | ~ (v2_pre_topc @ (sk_C_3 @ sk_B_1 @ sk_A))
% 0.81/1.01        | (v1_xboole_0 @ sk_B_1)
% 0.81/1.01        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.81/1.01        | (v2_struct_0 @ sk_A))),
% 0.81/1.01      inference('sup-', [status(thm)], ['37', '43'])).
% 0.81/1.01  thf('45', plain,
% 0.81/1.01      ((((v2_struct_0 @ sk_A)
% 0.81/1.01         | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.81/1.01         | (v1_xboole_0 @ sk_B_1)
% 0.81/1.01         | ~ (v2_pre_topc @ (sk_C_3 @ sk_B_1 @ sk_A))
% 0.81/1.01         | ~ (v1_tdlat_3 @ (sk_C_3 @ sk_B_1 @ sk_A))
% 0.81/1.01         | ~ (v2_tdlat_3 @ (sk_C_3 @ sk_B_1 @ sk_A))
% 0.81/1.01         | (v7_struct_0 @ (sk_C_3 @ sk_B_1 @ sk_A))))
% 0.81/1.01         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.81/1.01      inference('sup-', [status(thm)], ['36', '44'])).
% 0.81/1.01  thf('46', plain,
% 0.81/1.01      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.81/1.01      inference('split', [status(esa)], ['2'])).
% 0.81/1.01  thf('47', plain,
% 0.81/1.01      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.81/1.01      inference('split', [status(esa)], ['2'])).
% 0.81/1.01  thf('48', plain,
% 0.81/1.01      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('49', plain,
% 0.81/1.01      (![X41 : $i, X42 : $i]:
% 0.81/1.01         ((v1_xboole_0 @ X41)
% 0.81/1.01          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.81/1.01          | ~ (v2_tex_2 @ X41 @ X42)
% 0.81/1.01          | (v1_tdlat_3 @ (sk_C_3 @ X41 @ X42))
% 0.81/1.01          | ~ (l1_pre_topc @ X42)
% 0.81/1.01          | ~ (v2_pre_topc @ X42)
% 0.81/1.01          | (v2_struct_0 @ X42))),
% 0.81/1.01      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.81/1.01  thf('50', plain,
% 0.81/1.01      (((v2_struct_0 @ sk_A)
% 0.81/1.01        | ~ (v2_pre_topc @ sk_A)
% 0.81/1.01        | ~ (l1_pre_topc @ sk_A)
% 0.81/1.01        | (v1_tdlat_3 @ (sk_C_3 @ sk_B_1 @ sk_A))
% 0.81/1.01        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.81/1.01        | (v1_xboole_0 @ sk_B_1))),
% 0.81/1.01      inference('sup-', [status(thm)], ['48', '49'])).
% 0.81/1.01  thf('51', plain, ((v2_pre_topc @ sk_A)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('53', plain,
% 0.81/1.01      (((v2_struct_0 @ sk_A)
% 0.81/1.01        | (v1_tdlat_3 @ (sk_C_3 @ sk_B_1 @ sk_A))
% 0.81/1.01        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.81/1.01        | (v1_xboole_0 @ sk_B_1))),
% 0.81/1.01      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.81/1.01  thf('54', plain,
% 0.81/1.01      ((((v1_xboole_0 @ sk_B_1)
% 0.81/1.01         | (v1_tdlat_3 @ (sk_C_3 @ sk_B_1 @ sk_A))
% 0.81/1.01         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.81/1.01      inference('sup-', [status(thm)], ['47', '53'])).
% 0.81/1.01  thf('55', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('56', plain,
% 0.81/1.01      ((((v2_struct_0 @ sk_A) | (v1_tdlat_3 @ (sk_C_3 @ sk_B_1 @ sk_A))))
% 0.81/1.01         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.81/1.01      inference('clc', [status(thm)], ['54', '55'])).
% 0.81/1.01  thf('57', plain, (~ (v2_struct_0 @ sk_A)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('58', plain,
% 0.81/1.01      (((v1_tdlat_3 @ (sk_C_3 @ sk_B_1 @ sk_A)))
% 0.81/1.01         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.81/1.01      inference('clc', [status(thm)], ['56', '57'])).
% 0.81/1.01  thf('59', plain,
% 0.81/1.01      ((((v2_struct_0 @ sk_A)
% 0.81/1.01         | (v1_xboole_0 @ sk_B_1)
% 0.81/1.01         | ~ (v2_pre_topc @ (sk_C_3 @ sk_B_1 @ sk_A))
% 0.81/1.01         | ~ (v2_tdlat_3 @ (sk_C_3 @ sk_B_1 @ sk_A))
% 0.81/1.01         | (v7_struct_0 @ (sk_C_3 @ sk_B_1 @ sk_A))))
% 0.81/1.01         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.81/1.01      inference('demod', [status(thm)], ['45', '46', '58'])).
% 0.81/1.01  thf('60', plain,
% 0.81/1.01      (((l1_pre_topc @ (sk_C_3 @ sk_B_1 @ sk_A)))
% 0.81/1.01         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.81/1.01      inference('demod', [status(thm)], ['30', '31'])).
% 0.81/1.01  thf(cc2_tdlat_3, axiom,
% 0.81/1.01    (![A:$i]:
% 0.81/1.01     ( ( l1_pre_topc @ A ) => ( ( v2_tdlat_3 @ A ) => ( v2_pre_topc @ A ) ) ))).
% 0.81/1.01  thf('61', plain,
% 0.81/1.01      (![X33 : $i]:
% 0.81/1.01         (~ (v2_tdlat_3 @ X33) | (v2_pre_topc @ X33) | ~ (l1_pre_topc @ X33))),
% 0.81/1.01      inference('cnf', [status(esa)], [cc2_tdlat_3])).
% 0.81/1.01  thf('62', plain,
% 0.81/1.01      ((((v2_pre_topc @ (sk_C_3 @ sk_B_1 @ sk_A))
% 0.81/1.01         | ~ (v2_tdlat_3 @ (sk_C_3 @ sk_B_1 @ sk_A))))
% 0.81/1.01         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.81/1.01      inference('sup-', [status(thm)], ['60', '61'])).
% 0.81/1.01  thf('63', plain,
% 0.81/1.01      (((m1_pre_topc @ (sk_C_3 @ sk_B_1 @ sk_A) @ sk_A))
% 0.81/1.01         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.81/1.01      inference('clc', [status(thm)], ['26', '27'])).
% 0.81/1.01  thf(cc6_tdlat_3, axiom,
% 0.81/1.01    (![A:$i]:
% 0.81/1.01     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.81/1.01         ( l1_pre_topc @ A ) ) =>
% 0.81/1.01       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_tdlat_3 @ B ) ) ) ))).
% 0.81/1.01  thf('64', plain,
% 0.81/1.01      (![X35 : $i, X36 : $i]:
% 0.81/1.01         (~ (m1_pre_topc @ X35 @ X36)
% 0.81/1.01          | (v2_tdlat_3 @ X35)
% 0.81/1.01          | ~ (l1_pre_topc @ X36)
% 0.81/1.01          | ~ (v2_tdlat_3 @ X36)
% 0.81/1.01          | ~ (v2_pre_topc @ X36)
% 0.81/1.01          | (v2_struct_0 @ X36))),
% 0.81/1.01      inference('cnf', [status(esa)], [cc6_tdlat_3])).
% 0.81/1.01  thf('65', plain,
% 0.81/1.01      ((((v2_struct_0 @ sk_A)
% 0.81/1.01         | ~ (v2_pre_topc @ sk_A)
% 0.81/1.01         | ~ (v2_tdlat_3 @ sk_A)
% 0.81/1.01         | ~ (l1_pre_topc @ sk_A)
% 0.81/1.01         | (v2_tdlat_3 @ (sk_C_3 @ sk_B_1 @ sk_A))))
% 0.81/1.01         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.81/1.01      inference('sup-', [status(thm)], ['63', '64'])).
% 0.81/1.01  thf('66', plain, ((v2_pre_topc @ sk_A)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('67', plain, ((v2_tdlat_3 @ sk_A)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('69', plain,
% 0.81/1.01      ((((v2_struct_0 @ sk_A) | (v2_tdlat_3 @ (sk_C_3 @ sk_B_1 @ sk_A))))
% 0.81/1.01         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.81/1.01      inference('demod', [status(thm)], ['65', '66', '67', '68'])).
% 0.81/1.01  thf('70', plain, (~ (v2_struct_0 @ sk_A)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('71', plain,
% 0.81/1.01      (((v2_tdlat_3 @ (sk_C_3 @ sk_B_1 @ sk_A)))
% 0.81/1.01         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.81/1.01      inference('clc', [status(thm)], ['69', '70'])).
% 0.81/1.01  thf('72', plain,
% 0.81/1.01      (((v2_pre_topc @ (sk_C_3 @ sk_B_1 @ sk_A)))
% 0.81/1.01         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.81/1.01      inference('demod', [status(thm)], ['62', '71'])).
% 0.81/1.01  thf('73', plain,
% 0.81/1.01      (((v2_tdlat_3 @ (sk_C_3 @ sk_B_1 @ sk_A)))
% 0.81/1.01         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.81/1.01      inference('clc', [status(thm)], ['69', '70'])).
% 0.81/1.01  thf('74', plain,
% 0.81/1.01      ((((v2_struct_0 @ sk_A)
% 0.81/1.01         | (v1_xboole_0 @ sk_B_1)
% 0.81/1.01         | (v7_struct_0 @ (sk_C_3 @ sk_B_1 @ sk_A))))
% 0.81/1.01         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.81/1.01      inference('demod', [status(thm)], ['59', '72', '73'])).
% 0.81/1.01  thf('75', plain, (~ (v2_struct_0 @ sk_A)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('76', plain,
% 0.81/1.01      ((((v7_struct_0 @ (sk_C_3 @ sk_B_1 @ sk_A)) | (v1_xboole_0 @ sk_B_1)))
% 0.81/1.01         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.81/1.01      inference('clc', [status(thm)], ['74', '75'])).
% 0.81/1.01  thf('77', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('78', plain,
% 0.81/1.01      (((v7_struct_0 @ (sk_C_3 @ sk_B_1 @ sk_A)))
% 0.81/1.01         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.81/1.01      inference('clc', [status(thm)], ['76', '77'])).
% 0.81/1.01  thf('79', plain,
% 0.81/1.01      (((v1_zfmisc_1 @ sk_B_1)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.81/1.01      inference('demod', [status(thm)], ['35', '78'])).
% 0.81/1.01  thf('80', plain,
% 0.81/1.01      ((~ (v1_zfmisc_1 @ sk_B_1)) <= (~ ((v1_zfmisc_1 @ sk_B_1)))),
% 0.81/1.01      inference('split', [status(esa)], ['0'])).
% 0.81/1.01  thf('81', plain, (((v1_zfmisc_1 @ sk_B_1)) | ~ ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.81/1.01      inference('sup-', [status(thm)], ['79', '80'])).
% 0.81/1.01  thf('82', plain, (((v1_zfmisc_1 @ sk_B_1)) | ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.81/1.01      inference('split', [status(esa)], ['2'])).
% 0.81/1.01  thf(d1_xboole_0, axiom,
% 0.81/1.01    (![A:$i]:
% 0.81/1.01     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.81/1.01  thf('83', plain,
% 0.81/1.01      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.81/1.01      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.81/1.01  thf(t1_subset, axiom,
% 0.81/1.01    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.81/1.01  thf('84', plain,
% 0.81/1.01      (![X14 : $i, X15 : $i]:
% 0.81/1.01         ((m1_subset_1 @ X14 @ X15) | ~ (r2_hidden @ X14 @ X15))),
% 0.81/1.01      inference('cnf', [status(esa)], [t1_subset])).
% 0.81/1.01  thf('85', plain,
% 0.81/1.01      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.81/1.01      inference('sup-', [status(thm)], ['83', '84'])).
% 0.81/1.01  thf(redefinition_k6_domain_1, axiom,
% 0.81/1.01    (![A:$i,B:$i]:
% 0.81/1.01     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.81/1.01       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.81/1.01  thf('86', plain,
% 0.81/1.01      (![X31 : $i, X32 : $i]:
% 0.81/1.01         ((v1_xboole_0 @ X31)
% 0.81/1.01          | ~ (m1_subset_1 @ X32 @ X31)
% 0.81/1.01          | ((k6_domain_1 @ X31 @ X32) = (k1_tarski @ X32)))),
% 0.81/1.01      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.81/1.01  thf('87', plain,
% 0.81/1.01      (![X0 : $i]:
% 0.81/1.01         ((v1_xboole_0 @ X0)
% 0.81/1.01          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.81/1.01          | (v1_xboole_0 @ X0))),
% 0.81/1.01      inference('sup-', [status(thm)], ['85', '86'])).
% 0.81/1.01  thf('88', plain,
% 0.81/1.01      (![X0 : $i]:
% 0.81/1.01         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.81/1.01          | (v1_xboole_0 @ X0))),
% 0.81/1.01      inference('simplify', [status(thm)], ['87'])).
% 0.81/1.01  thf('89', plain,
% 0.81/1.01      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.81/1.01      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.81/1.01  thf(l1_zfmisc_1, axiom,
% 0.81/1.01    (![A:$i,B:$i]:
% 0.81/1.01     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.81/1.01  thf('90', plain,
% 0.81/1.01      (![X9 : $i, X11 : $i]:
% 0.81/1.01         ((r1_tarski @ (k1_tarski @ X9) @ X11) | ~ (r2_hidden @ X9 @ X11))),
% 0.81/1.01      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.81/1.01  thf('91', plain,
% 0.81/1.01      (![X0 : $i]:
% 0.81/1.01         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.81/1.01      inference('sup-', [status(thm)], ['89', '90'])).
% 0.81/1.01  thf(t1_tex_2, axiom,
% 0.81/1.01    (![A:$i]:
% 0.81/1.01     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.81/1.01       ( ![B:$i]:
% 0.81/1.01         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.81/1.01           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.81/1.01  thf('92', plain,
% 0.81/1.01      (![X39 : $i, X40 : $i]:
% 0.81/1.01         ((v1_xboole_0 @ X39)
% 0.81/1.01          | ~ (v1_zfmisc_1 @ X39)
% 0.81/1.01          | ((X40) = (X39))
% 0.81/1.01          | ~ (r1_tarski @ X40 @ X39)
% 0.81/1.01          | (v1_xboole_0 @ X40))),
% 0.81/1.01      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.81/1.01  thf('93', plain,
% 0.81/1.01      (![X0 : $i]:
% 0.81/1.01         ((v1_xboole_0 @ X0)
% 0.81/1.01          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.81/1.01          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.81/1.01          | ~ (v1_zfmisc_1 @ X0)
% 0.81/1.01          | (v1_xboole_0 @ X0))),
% 0.81/1.01      inference('sup-', [status(thm)], ['91', '92'])).
% 0.81/1.01  thf('94', plain,
% 0.81/1.01      (![X0 : $i]:
% 0.81/1.01         (~ (v1_zfmisc_1 @ X0)
% 0.81/1.01          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.81/1.01          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.81/1.01          | (v1_xboole_0 @ X0))),
% 0.81/1.01      inference('simplify', [status(thm)], ['93'])).
% 0.81/1.01  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.81/1.01  thf('95', plain, (![X8 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X8))),
% 0.81/1.01      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.81/1.01  thf('96', plain,
% 0.81/1.01      (![X0 : $i]:
% 0.81/1.01         ((v1_xboole_0 @ X0)
% 0.81/1.01          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.81/1.01          | ~ (v1_zfmisc_1 @ X0))),
% 0.81/1.01      inference('sup-', [status(thm)], ['94', '95'])).
% 0.81/1.01  thf('97', plain,
% 0.81/1.01      (![X0 : $i]:
% 0.81/1.01         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (X0))
% 0.81/1.01          | (v1_xboole_0 @ X0)
% 0.81/1.01          | ~ (v1_zfmisc_1 @ X0)
% 0.81/1.01          | (v1_xboole_0 @ X0))),
% 0.81/1.01      inference('sup+', [status(thm)], ['88', '96'])).
% 0.81/1.01  thf('98', plain,
% 0.81/1.01      (![X0 : $i]:
% 0.81/1.01         (~ (v1_zfmisc_1 @ X0)
% 0.81/1.01          | (v1_xboole_0 @ X0)
% 0.81/1.01          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (X0)))),
% 0.81/1.01      inference('simplify', [status(thm)], ['97'])).
% 0.81/1.01  thf('99', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.81/1.01      inference('split', [status(esa)], ['2'])).
% 0.81/1.01  thf('100', plain,
% 0.81/1.01      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf(existence_m2_subset_1, axiom,
% 0.81/1.01    (![A:$i,B:$i]:
% 0.81/1.01     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.81/1.01         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.81/1.01       ( ?[C:$i]: ( m2_subset_1 @ C @ A @ B ) ) ))).
% 0.81/1.01  thf('101', plain,
% 0.81/1.01      (![X18 : $i, X19 : $i]:
% 0.81/1.01         ((v1_xboole_0 @ X18)
% 0.81/1.01          | (v1_xboole_0 @ X19)
% 0.81/1.01          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18))
% 0.81/1.01          | (m2_subset_1 @ (sk_C_1 @ X19 @ X18) @ X18 @ X19))),
% 0.81/1.01      inference('cnf', [status(esa)], [existence_m2_subset_1])).
% 0.81/1.01  thf('102', plain,
% 0.81/1.01      (((m2_subset_1 @ (sk_C_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.81/1.01         (u1_struct_0 @ sk_A) @ sk_B_1)
% 0.81/1.01        | (v1_xboole_0 @ sk_B_1)
% 0.81/1.01        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.01      inference('sup-', [status(thm)], ['100', '101'])).
% 0.81/1.01  thf('103', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('104', plain,
% 0.81/1.01      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.81/1.01        | (m2_subset_1 @ (sk_C_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.81/1.01           (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.81/1.01      inference('clc', [status(thm)], ['102', '103'])).
% 0.81/1.01  thf('105', plain,
% 0.81/1.01      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf(cc1_subset_1, axiom,
% 0.81/1.01    (![A:$i]:
% 0.81/1.01     ( ( v1_xboole_0 @ A ) =>
% 0.81/1.01       ( ![B:$i]:
% 0.81/1.01         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.81/1.01  thf('106', plain,
% 0.81/1.01      (![X12 : $i, X13 : $i]:
% 0.81/1.01         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.81/1.01          | (v1_xboole_0 @ X12)
% 0.81/1.01          | ~ (v1_xboole_0 @ X13))),
% 0.81/1.01      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.81/1.01  thf('107', plain,
% 0.81/1.01      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_B_1))),
% 0.81/1.01      inference('sup-', [status(thm)], ['105', '106'])).
% 0.81/1.01  thf('108', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('109', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.81/1.01      inference('clc', [status(thm)], ['107', '108'])).
% 0.81/1.01  thf('110', plain,
% 0.81/1.01      ((m2_subset_1 @ (sk_C_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.81/1.01        (u1_struct_0 @ sk_A) @ sk_B_1)),
% 0.81/1.01      inference('clc', [status(thm)], ['104', '109'])).
% 0.81/1.01  thf('111', plain,
% 0.81/1.01      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf(redefinition_m2_subset_1, axiom,
% 0.81/1.01    (![A:$i,B:$i]:
% 0.81/1.01     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.81/1.01         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.81/1.01       ( ![C:$i]: ( ( m2_subset_1 @ C @ A @ B ) <=> ( m1_subset_1 @ C @ B ) ) ) ))).
% 0.81/1.01  thf('112', plain,
% 0.81/1.01      (![X20 : $i, X21 : $i, X23 : $i]:
% 0.81/1.01         ((v1_xboole_0 @ X20)
% 0.81/1.01          | (v1_xboole_0 @ X21)
% 0.81/1.01          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20))
% 0.81/1.01          | (m1_subset_1 @ X23 @ X21)
% 0.81/1.01          | ~ (m2_subset_1 @ X23 @ X20 @ X21))),
% 0.81/1.01      inference('cnf', [status(esa)], [redefinition_m2_subset_1])).
% 0.81/1.01  thf('113', plain,
% 0.81/1.01      (![X0 : $i]:
% 0.81/1.01         (~ (m2_subset_1 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 0.81/1.01          | (m1_subset_1 @ X0 @ sk_B_1)
% 0.81/1.01          | (v1_xboole_0 @ sk_B_1)
% 0.81/1.01          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.01      inference('sup-', [status(thm)], ['111', '112'])).
% 0.81/1.01  thf('114', plain,
% 0.81/1.01      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.81/1.01        | (v1_xboole_0 @ sk_B_1)
% 0.81/1.01        | (m1_subset_1 @ (sk_C_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ sk_B_1))),
% 0.81/1.01      inference('sup-', [status(thm)], ['110', '113'])).
% 0.81/1.01  thf('115', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.81/1.01      inference('clc', [status(thm)], ['107', '108'])).
% 0.81/1.01  thf('116', plain,
% 0.81/1.01      (((m1_subset_1 @ (sk_C_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ sk_B_1)
% 0.81/1.01        | (v1_xboole_0 @ sk_B_1))),
% 0.81/1.01      inference('clc', [status(thm)], ['114', '115'])).
% 0.81/1.01  thf('117', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('118', plain,
% 0.81/1.01      ((m1_subset_1 @ (sk_C_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ sk_B_1)),
% 0.81/1.01      inference('clc', [status(thm)], ['116', '117'])).
% 0.81/1.01  thf(t2_subset, axiom,
% 0.81/1.01    (![A:$i,B:$i]:
% 0.81/1.01     ( ( m1_subset_1 @ A @ B ) =>
% 0.81/1.01       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.81/1.01  thf('119', plain,
% 0.81/1.01      (![X16 : $i, X17 : $i]:
% 0.81/1.01         ((r2_hidden @ X16 @ X17)
% 0.81/1.01          | (v1_xboole_0 @ X17)
% 0.81/1.01          | ~ (m1_subset_1 @ X16 @ X17))),
% 0.81/1.01      inference('cnf', [status(esa)], [t2_subset])).
% 0.81/1.01  thf('120', plain,
% 0.81/1.01      (((v1_xboole_0 @ sk_B_1)
% 0.81/1.01        | (r2_hidden @ (sk_C_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ sk_B_1))),
% 0.81/1.01      inference('sup-', [status(thm)], ['118', '119'])).
% 0.81/1.01  thf('121', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('122', plain,
% 0.81/1.01      ((r2_hidden @ (sk_C_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ sk_B_1)),
% 0.81/1.01      inference('clc', [status(thm)], ['120', '121'])).
% 0.81/1.01  thf('123', plain,
% 0.81/1.01      (![X0 : $i]:
% 0.81/1.01         ((v1_xboole_0 @ X0)
% 0.81/1.01          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.81/1.01          | ~ (v1_zfmisc_1 @ X0))),
% 0.81/1.01      inference('sup-', [status(thm)], ['94', '95'])).
% 0.81/1.01  thf(d1_tarski, axiom,
% 0.81/1.01    (![A:$i,B:$i]:
% 0.81/1.01     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.81/1.01       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.81/1.01  thf('124', plain,
% 0.81/1.01      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.81/1.01         (~ (r2_hidden @ X6 @ X5) | ((X6) = (X3)) | ((X5) != (k1_tarski @ X3)))),
% 0.81/1.01      inference('cnf', [status(esa)], [d1_tarski])).
% 0.81/1.01  thf('125', plain,
% 0.81/1.01      (![X3 : $i, X6 : $i]:
% 0.81/1.01         (((X6) = (X3)) | ~ (r2_hidden @ X6 @ (k1_tarski @ X3)))),
% 0.81/1.01      inference('simplify', [status(thm)], ['124'])).
% 0.81/1.01  thf('126', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i]:
% 0.81/1.01         (~ (r2_hidden @ X1 @ X0)
% 0.81/1.01          | ~ (v1_zfmisc_1 @ X0)
% 0.81/1.01          | (v1_xboole_0 @ X0)
% 0.81/1.01          | ((X1) = (sk_B @ X0)))),
% 0.81/1.01      inference('sup-', [status(thm)], ['123', '125'])).
% 0.81/1.01  thf('127', plain,
% 0.81/1.01      ((((sk_C_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)) = (sk_B @ sk_B_1))
% 0.81/1.01        | (v1_xboole_0 @ sk_B_1)
% 0.81/1.01        | ~ (v1_zfmisc_1 @ sk_B_1))),
% 0.81/1.01      inference('sup-', [status(thm)], ['122', '126'])).
% 0.81/1.01  thf('128', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('129', plain,
% 0.81/1.01      ((~ (v1_zfmisc_1 @ sk_B_1)
% 0.81/1.01        | ((sk_C_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)) = (sk_B @ sk_B_1)))),
% 0.81/1.01      inference('clc', [status(thm)], ['127', '128'])).
% 0.81/1.01  thf('130', plain,
% 0.81/1.01      ((((sk_C_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)) = (sk_B @ sk_B_1)))
% 0.81/1.01         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.81/1.01      inference('sup-', [status(thm)], ['99', '129'])).
% 0.81/1.01  thf('131', plain,
% 0.81/1.01      ((m1_subset_1 @ (sk_C_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ sk_B_1)),
% 0.81/1.01      inference('clc', [status(thm)], ['116', '117'])).
% 0.81/1.01  thf('132', plain,
% 0.81/1.01      (((m1_subset_1 @ (sk_B @ sk_B_1) @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.81/1.01      inference('sup+', [status(thm)], ['130', '131'])).
% 0.81/1.01  thf('133', plain,
% 0.81/1.01      (![X31 : $i, X32 : $i]:
% 0.81/1.01         ((v1_xboole_0 @ X31)
% 0.81/1.01          | ~ (m1_subset_1 @ X32 @ X31)
% 0.81/1.01          | ((k6_domain_1 @ X31 @ X32) = (k1_tarski @ X32)))),
% 0.81/1.01      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.81/1.01  thf('134', plain,
% 0.81/1.01      (((((k6_domain_1 @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.81/1.01           = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.81/1.01         | (v1_xboole_0 @ sk_B_1))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.81/1.02      inference('sup-', [status(thm)], ['132', '133'])).
% 0.81/1.02  thf('135', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('136', plain,
% 0.81/1.02      ((((k6_domain_1 @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.81/1.02          = (k1_tarski @ (sk_B @ sk_B_1))))
% 0.81/1.02         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.81/1.02      inference('clc', [status(thm)], ['134', '135'])).
% 0.81/1.02  thf('137', plain,
% 0.81/1.02      (((((sk_B_1) = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.81/1.02         | (v1_xboole_0 @ sk_B_1)
% 0.81/1.02         | ~ (v1_zfmisc_1 @ sk_B_1))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.81/1.02      inference('sup+', [status(thm)], ['98', '136'])).
% 0.81/1.02  thf('138', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.81/1.02      inference('split', [status(esa)], ['2'])).
% 0.81/1.02  thf('139', plain,
% 0.81/1.02      (((((sk_B_1) = (k1_tarski @ (sk_B @ sk_B_1))) | (v1_xboole_0 @ sk_B_1)))
% 0.81/1.02         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.81/1.02      inference('demod', [status(thm)], ['137', '138'])).
% 0.81/1.02  thf('140', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('141', plain,
% 0.81/1.02      ((((sk_B_1) = (k1_tarski @ (sk_B @ sk_B_1))))
% 0.81/1.02         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.81/1.02      inference('clc', [status(thm)], ['139', '140'])).
% 0.81/1.02  thf('142', plain,
% 0.81/1.02      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf(t10_tsep_1, axiom,
% 0.81/1.02    (![A:$i]:
% 0.81/1.02     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.81/1.02       ( ![B:$i]:
% 0.81/1.02         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.81/1.02             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.81/1.02           ( ?[C:$i]:
% 0.81/1.02             ( ( ( B ) = ( u1_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) & 
% 0.81/1.02               ( v1_pre_topc @ C ) & ( ~( v2_struct_0 @ C ) ) ) ) ) ) ))).
% 0.81/1.02  thf('143', plain,
% 0.81/1.02      (![X37 : $i, X38 : $i]:
% 0.81/1.02         ((v1_xboole_0 @ X37)
% 0.81/1.02          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.81/1.02          | (m1_pre_topc @ (sk_C_2 @ X37 @ X38) @ X38)
% 0.81/1.02          | ~ (l1_pre_topc @ X38)
% 0.81/1.02          | (v2_struct_0 @ X38))),
% 0.81/1.02      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.81/1.02  thf('144', plain,
% 0.81/1.02      (((v2_struct_0 @ sk_A)
% 0.81/1.02        | ~ (l1_pre_topc @ sk_A)
% 0.81/1.02        | (m1_pre_topc @ (sk_C_2 @ sk_B_1 @ sk_A) @ sk_A)
% 0.81/1.02        | (v1_xboole_0 @ sk_B_1))),
% 0.81/1.02      inference('sup-', [status(thm)], ['142', '143'])).
% 0.81/1.02  thf('145', plain, ((l1_pre_topc @ sk_A)),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('146', plain,
% 0.81/1.02      (((v2_struct_0 @ sk_A)
% 0.81/1.02        | (m1_pre_topc @ (sk_C_2 @ sk_B_1 @ sk_A) @ sk_A)
% 0.81/1.02        | (v1_xboole_0 @ sk_B_1))),
% 0.81/1.02      inference('demod', [status(thm)], ['144', '145'])).
% 0.81/1.02  thf('147', plain, (~ (v2_struct_0 @ sk_A)),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('148', plain,
% 0.81/1.02      (((v1_xboole_0 @ sk_B_1)
% 0.81/1.02        | (m1_pre_topc @ (sk_C_2 @ sk_B_1 @ sk_A) @ sk_A))),
% 0.81/1.02      inference('clc', [status(thm)], ['146', '147'])).
% 0.81/1.02  thf('149', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('150', plain, ((m1_pre_topc @ (sk_C_2 @ sk_B_1 @ sk_A) @ sk_A)),
% 0.81/1.02      inference('clc', [status(thm)], ['148', '149'])).
% 0.81/1.02  thf('151', plain,
% 0.81/1.02      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.81/1.02      inference('sup-', [status(thm)], ['83', '84'])).
% 0.81/1.02  thf(t55_pre_topc, axiom,
% 0.81/1.02    (![A:$i]:
% 0.81/1.02     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.81/1.02       ( ![B:$i]:
% 0.81/1.02         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.81/1.02           ( ![C:$i]:
% 0.81/1.02             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.81/1.02               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.81/1.02  thf('152', plain,
% 0.81/1.02      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.81/1.02         ((v2_struct_0 @ X28)
% 0.81/1.02          | ~ (m1_pre_topc @ X28 @ X29)
% 0.81/1.02          | (m1_subset_1 @ X30 @ (u1_struct_0 @ X29))
% 0.81/1.02          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 0.81/1.02          | ~ (l1_pre_topc @ X29)
% 0.81/1.02          | (v2_struct_0 @ X29))),
% 0.81/1.02      inference('cnf', [status(esa)], [t55_pre_topc])).
% 0.81/1.02  thf('153', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]:
% 0.81/1.02         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.81/1.02          | (v2_struct_0 @ X1)
% 0.81/1.02          | ~ (l1_pre_topc @ X1)
% 0.81/1.02          | (m1_subset_1 @ (sk_B @ (u1_struct_0 @ X0)) @ (u1_struct_0 @ X1))
% 0.81/1.02          | ~ (m1_pre_topc @ X0 @ X1)
% 0.81/1.02          | (v2_struct_0 @ X0))),
% 0.81/1.02      inference('sup-', [status(thm)], ['151', '152'])).
% 0.81/1.02  thf('154', plain,
% 0.81/1.02      (((v2_struct_0 @ (sk_C_2 @ sk_B_1 @ sk_A))
% 0.81/1.02        | (m1_subset_1 @ (sk_B @ (u1_struct_0 @ (sk_C_2 @ sk_B_1 @ sk_A))) @ 
% 0.81/1.02           (u1_struct_0 @ sk_A))
% 0.81/1.02        | ~ (l1_pre_topc @ sk_A)
% 0.81/1.02        | (v2_struct_0 @ sk_A)
% 0.81/1.02        | (v1_xboole_0 @ (u1_struct_0 @ (sk_C_2 @ sk_B_1 @ sk_A))))),
% 0.81/1.02      inference('sup-', [status(thm)], ['150', '153'])).
% 0.81/1.02  thf('155', plain,
% 0.81/1.02      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('156', plain,
% 0.81/1.02      (![X37 : $i, X38 : $i]:
% 0.81/1.02         ((v1_xboole_0 @ X37)
% 0.81/1.02          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.81/1.02          | ((X37) = (u1_struct_0 @ (sk_C_2 @ X37 @ X38)))
% 0.81/1.02          | ~ (l1_pre_topc @ X38)
% 0.81/1.02          | (v2_struct_0 @ X38))),
% 0.81/1.02      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.81/1.02  thf('157', plain,
% 0.81/1.02      (((v2_struct_0 @ sk_A)
% 0.81/1.02        | ~ (l1_pre_topc @ sk_A)
% 0.81/1.02        | ((sk_B_1) = (u1_struct_0 @ (sk_C_2 @ sk_B_1 @ sk_A)))
% 0.81/1.02        | (v1_xboole_0 @ sk_B_1))),
% 0.81/1.02      inference('sup-', [status(thm)], ['155', '156'])).
% 0.81/1.02  thf('158', plain, ((l1_pre_topc @ sk_A)),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('159', plain,
% 0.81/1.02      (((v2_struct_0 @ sk_A)
% 0.81/1.02        | ((sk_B_1) = (u1_struct_0 @ (sk_C_2 @ sk_B_1 @ sk_A)))
% 0.81/1.02        | (v1_xboole_0 @ sk_B_1))),
% 0.81/1.02      inference('demod', [status(thm)], ['157', '158'])).
% 0.81/1.02  thf('160', plain, (~ (v2_struct_0 @ sk_A)),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('161', plain,
% 0.81/1.02      (((v1_xboole_0 @ sk_B_1)
% 0.81/1.02        | ((sk_B_1) = (u1_struct_0 @ (sk_C_2 @ sk_B_1 @ sk_A))))),
% 0.81/1.02      inference('clc', [status(thm)], ['159', '160'])).
% 0.81/1.02  thf('162', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('163', plain, (((sk_B_1) = (u1_struct_0 @ (sk_C_2 @ sk_B_1 @ sk_A)))),
% 0.81/1.02      inference('clc', [status(thm)], ['161', '162'])).
% 0.81/1.02  thf('164', plain, ((l1_pre_topc @ sk_A)),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('165', plain, (((sk_B_1) = (u1_struct_0 @ (sk_C_2 @ sk_B_1 @ sk_A)))),
% 0.81/1.02      inference('clc', [status(thm)], ['161', '162'])).
% 0.81/1.02  thf('166', plain,
% 0.81/1.02      (((v2_struct_0 @ (sk_C_2 @ sk_B_1 @ sk_A))
% 0.81/1.02        | (m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.81/1.02        | (v2_struct_0 @ sk_A)
% 0.81/1.02        | (v1_xboole_0 @ sk_B_1))),
% 0.81/1.02      inference('demod', [status(thm)], ['154', '163', '164', '165'])).
% 0.81/1.02  thf('167', plain,
% 0.81/1.02      (![X16 : $i, X17 : $i]:
% 0.81/1.02         ((r2_hidden @ X16 @ X17)
% 0.81/1.02          | (v1_xboole_0 @ X17)
% 0.81/1.02          | ~ (m1_subset_1 @ X16 @ X17))),
% 0.81/1.02      inference('cnf', [status(esa)], [t2_subset])).
% 0.81/1.02  thf('168', plain,
% 0.81/1.02      (((v1_xboole_0 @ sk_B_1)
% 0.81/1.02        | (v2_struct_0 @ sk_A)
% 0.81/1.02        | (v2_struct_0 @ (sk_C_2 @ sk_B_1 @ sk_A))
% 0.81/1.02        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.81/1.02        | (r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 0.81/1.02      inference('sup-', [status(thm)], ['166', '167'])).
% 0.81/1.02  thf('169', plain,
% 0.81/1.02      (![X9 : $i, X11 : $i]:
% 0.81/1.02         ((r1_tarski @ (k1_tarski @ X9) @ X11) | ~ (r2_hidden @ X9 @ X11))),
% 0.81/1.02      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.81/1.02  thf('170', plain,
% 0.81/1.02      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.81/1.02        | (v2_struct_0 @ (sk_C_2 @ sk_B_1 @ sk_A))
% 0.81/1.02        | (v2_struct_0 @ sk_A)
% 0.81/1.02        | (v1_xboole_0 @ sk_B_1)
% 0.81/1.02        | (r1_tarski @ (k1_tarski @ (sk_B @ sk_B_1)) @ (u1_struct_0 @ sk_A)))),
% 0.81/1.02      inference('sup-', [status(thm)], ['168', '169'])).
% 0.81/1.02  thf('171', plain,
% 0.81/1.02      ((((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.81/1.02         | (v1_xboole_0 @ sk_B_1)
% 0.81/1.02         | (v2_struct_0 @ sk_A)
% 0.81/1.02         | (v2_struct_0 @ (sk_C_2 @ sk_B_1 @ sk_A))
% 0.81/1.02         | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.81/1.02      inference('sup+', [status(thm)], ['141', '170'])).
% 0.81/1.02  thf('172', plain,
% 0.81/1.02      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('173', plain,
% 0.81/1.02      (![X37 : $i, X38 : $i]:
% 0.81/1.02         ((v1_xboole_0 @ X37)
% 0.81/1.02          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.81/1.02          | ~ (v2_struct_0 @ (sk_C_2 @ X37 @ X38))
% 0.81/1.02          | ~ (l1_pre_topc @ X38)
% 0.81/1.02          | (v2_struct_0 @ X38))),
% 0.81/1.02      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.81/1.02  thf('174', plain,
% 0.81/1.02      (((v2_struct_0 @ sk_A)
% 0.81/1.02        | ~ (l1_pre_topc @ sk_A)
% 0.81/1.02        | ~ (v2_struct_0 @ (sk_C_2 @ sk_B_1 @ sk_A))
% 0.81/1.02        | (v1_xboole_0 @ sk_B_1))),
% 0.81/1.02      inference('sup-', [status(thm)], ['172', '173'])).
% 0.81/1.02  thf('175', plain, ((l1_pre_topc @ sk_A)),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('176', plain,
% 0.81/1.02      (((v2_struct_0 @ sk_A)
% 0.81/1.02        | ~ (v2_struct_0 @ (sk_C_2 @ sk_B_1 @ sk_A))
% 0.81/1.02        | (v1_xboole_0 @ sk_B_1))),
% 0.81/1.02      inference('demod', [status(thm)], ['174', '175'])).
% 0.81/1.02  thf('177', plain, (~ (v2_struct_0 @ sk_A)),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('178', plain,
% 0.81/1.02      (((v1_xboole_0 @ sk_B_1) | ~ (v2_struct_0 @ (sk_C_2 @ sk_B_1 @ sk_A)))),
% 0.81/1.02      inference('clc', [status(thm)], ['176', '177'])).
% 0.81/1.02  thf('179', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('180', plain, (~ (v2_struct_0 @ (sk_C_2 @ sk_B_1 @ sk_A))),
% 0.81/1.02      inference('clc', [status(thm)], ['178', '179'])).
% 0.81/1.02  thf('181', plain,
% 0.81/1.02      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.81/1.02         | (v2_struct_0 @ sk_A)
% 0.81/1.02         | (v1_xboole_0 @ sk_B_1)
% 0.81/1.02         | (r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))))
% 0.81/1.02         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.81/1.02      inference('sup-', [status(thm)], ['171', '180'])).
% 0.81/1.02  thf('182', plain,
% 0.81/1.02      ((((sk_B_1) = (k1_tarski @ (sk_B @ sk_B_1))))
% 0.81/1.02         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.81/1.02      inference('clc', [status(thm)], ['139', '140'])).
% 0.81/1.02  thf('183', plain,
% 0.81/1.02      (![X9 : $i, X10 : $i]:
% 0.81/1.02         ((r2_hidden @ X9 @ X10) | ~ (r1_tarski @ (k1_tarski @ X9) @ X10))),
% 0.81/1.02      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.81/1.02  thf('184', plain,
% 0.81/1.02      ((![X0 : $i]:
% 0.81/1.02          (~ (r1_tarski @ sk_B_1 @ X0) | (r2_hidden @ (sk_B @ sk_B_1) @ X0)))
% 0.81/1.02         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.81/1.02      inference('sup-', [status(thm)], ['182', '183'])).
% 0.81/1.02  thf('185', plain,
% 0.81/1.02      ((((v1_xboole_0 @ sk_B_1)
% 0.81/1.02         | (v2_struct_0 @ sk_A)
% 0.81/1.02         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.81/1.02         | (r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))))
% 0.81/1.02         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.81/1.02      inference('sup-', [status(thm)], ['181', '184'])).
% 0.81/1.02  thf('186', plain,
% 0.81/1.02      (![X14 : $i, X15 : $i]:
% 0.81/1.02         ((m1_subset_1 @ X14 @ X15) | ~ (r2_hidden @ X14 @ X15))),
% 0.81/1.02      inference('cnf', [status(esa)], [t1_subset])).
% 0.81/1.02  thf('187', plain,
% 0.81/1.02      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.81/1.02         | (v2_struct_0 @ sk_A)
% 0.81/1.02         | (v1_xboole_0 @ sk_B_1)
% 0.81/1.02         | (m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))))
% 0.81/1.02         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.81/1.02      inference('sup-', [status(thm)], ['185', '186'])).
% 0.81/1.02  thf('188', plain,
% 0.81/1.02      (![X31 : $i, X32 : $i]:
% 0.81/1.02         ((v1_xboole_0 @ X31)
% 0.81/1.02          | ~ (m1_subset_1 @ X32 @ X31)
% 0.81/1.02          | ((k6_domain_1 @ X31 @ X32) = (k1_tarski @ X32)))),
% 0.81/1.02      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.81/1.02  thf('189', plain,
% 0.81/1.02      ((((v1_xboole_0 @ sk_B_1)
% 0.81/1.02         | (v2_struct_0 @ sk_A)
% 0.81/1.02         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.81/1.02         | ((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.81/1.02             = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.81/1.02         | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.81/1.02      inference('sup-', [status(thm)], ['187', '188'])).
% 0.81/1.02  thf('190', plain,
% 0.81/1.02      ((((sk_B_1) = (k1_tarski @ (sk_B @ sk_B_1))))
% 0.81/1.02         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.81/1.02      inference('clc', [status(thm)], ['139', '140'])).
% 0.81/1.02  thf('191', plain,
% 0.81/1.02      ((((v1_xboole_0 @ sk_B_1)
% 0.81/1.02         | (v2_struct_0 @ sk_A)
% 0.81/1.02         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.81/1.02         | ((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) = (sk_B_1))
% 0.81/1.02         | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.81/1.02      inference('demod', [status(thm)], ['189', '190'])).
% 0.81/1.02  thf('192', plain,
% 0.81/1.02      (((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) = (sk_B_1))
% 0.81/1.02         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.81/1.02         | (v2_struct_0 @ sk_A)
% 0.81/1.02         | (v1_xboole_0 @ sk_B_1))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.81/1.02      inference('simplify', [status(thm)], ['191'])).
% 0.81/1.02  thf('193', plain,
% 0.81/1.02      (((v2_struct_0 @ (sk_C_2 @ sk_B_1 @ sk_A))
% 0.81/1.02        | (m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.81/1.02        | (v2_struct_0 @ sk_A)
% 0.81/1.02        | (v1_xboole_0 @ sk_B_1))),
% 0.81/1.02      inference('demod', [status(thm)], ['154', '163', '164', '165'])).
% 0.81/1.02  thf(t36_tex_2, axiom,
% 0.81/1.02    (![A:$i]:
% 0.81/1.02     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.81/1.02       ( ![B:$i]:
% 0.81/1.02         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.81/1.02           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.81/1.02  thf('194', plain,
% 0.81/1.02      (![X43 : $i, X44 : $i]:
% 0.81/1.02         (~ (m1_subset_1 @ X43 @ (u1_struct_0 @ X44))
% 0.81/1.02          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X44) @ X43) @ X44)
% 0.81/1.02          | ~ (l1_pre_topc @ X44)
% 0.81/1.02          | ~ (v2_pre_topc @ X44)
% 0.81/1.02          | (v2_struct_0 @ X44))),
% 0.81/1.02      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.81/1.02  thf('195', plain,
% 0.81/1.02      (((v1_xboole_0 @ sk_B_1)
% 0.81/1.02        | (v2_struct_0 @ sk_A)
% 0.81/1.02        | (v2_struct_0 @ (sk_C_2 @ sk_B_1 @ sk_A))
% 0.81/1.02        | (v2_struct_0 @ sk_A)
% 0.81/1.02        | ~ (v2_pre_topc @ sk_A)
% 0.81/1.02        | ~ (l1_pre_topc @ sk_A)
% 0.81/1.02        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.81/1.02           sk_A))),
% 0.81/1.02      inference('sup-', [status(thm)], ['193', '194'])).
% 0.81/1.02  thf('196', plain, ((v2_pre_topc @ sk_A)),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('197', plain, ((l1_pre_topc @ sk_A)),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('198', plain,
% 0.81/1.02      (((v1_xboole_0 @ sk_B_1)
% 0.81/1.02        | (v2_struct_0 @ sk_A)
% 0.81/1.02        | (v2_struct_0 @ (sk_C_2 @ sk_B_1 @ sk_A))
% 0.81/1.02        | (v2_struct_0 @ sk_A)
% 0.81/1.02        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.81/1.02           sk_A))),
% 0.81/1.02      inference('demod', [status(thm)], ['195', '196', '197'])).
% 0.81/1.02  thf('199', plain,
% 0.81/1.02      (((v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.81/1.02         sk_A)
% 0.81/1.02        | (v2_struct_0 @ (sk_C_2 @ sk_B_1 @ sk_A))
% 0.81/1.02        | (v2_struct_0 @ sk_A)
% 0.81/1.02        | (v1_xboole_0 @ sk_B_1))),
% 0.81/1.02      inference('simplify', [status(thm)], ['198'])).
% 0.81/1.02  thf('200', plain,
% 0.81/1.02      ((((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.81/1.02         | (v1_xboole_0 @ sk_B_1)
% 0.81/1.02         | (v2_struct_0 @ sk_A)
% 0.81/1.02         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.81/1.02         | (v1_xboole_0 @ sk_B_1)
% 0.81/1.02         | (v2_struct_0 @ sk_A)
% 0.81/1.02         | (v2_struct_0 @ (sk_C_2 @ sk_B_1 @ sk_A))))
% 0.81/1.02         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.81/1.02      inference('sup+', [status(thm)], ['192', '199'])).
% 0.81/1.02  thf('201', plain,
% 0.81/1.02      ((((v2_struct_0 @ (sk_C_2 @ sk_B_1 @ sk_A))
% 0.81/1.02         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.81/1.02         | (v2_struct_0 @ sk_A)
% 0.81/1.02         | (v1_xboole_0 @ sk_B_1)
% 0.81/1.02         | (v2_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.81/1.02      inference('simplify', [status(thm)], ['200'])).
% 0.81/1.02  thf('202', plain, (~ (v2_struct_0 @ (sk_C_2 @ sk_B_1 @ sk_A))),
% 0.81/1.02      inference('clc', [status(thm)], ['178', '179'])).
% 0.81/1.02  thf('203', plain,
% 0.81/1.02      ((((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.81/1.02         | (v1_xboole_0 @ sk_B_1)
% 0.81/1.02         | (v2_struct_0 @ sk_A)
% 0.81/1.02         | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.81/1.02      inference('sup-', [status(thm)], ['201', '202'])).
% 0.81/1.02  thf('204', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.81/1.02      inference('clc', [status(thm)], ['107', '108'])).
% 0.81/1.02  thf('205', plain,
% 0.81/1.02      ((((v2_struct_0 @ sk_A)
% 0.81/1.02         | (v1_xboole_0 @ sk_B_1)
% 0.81/1.02         | (v2_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.81/1.02      inference('sup-', [status(thm)], ['203', '204'])).
% 0.81/1.02  thf('206', plain, (~ (v2_struct_0 @ sk_A)),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('207', plain,
% 0.81/1.02      ((((v2_tex_2 @ sk_B_1 @ sk_A) | (v1_xboole_0 @ sk_B_1)))
% 0.81/1.02         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.81/1.02      inference('clc', [status(thm)], ['205', '206'])).
% 0.81/1.02  thf('208', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('209', plain,
% 0.81/1.02      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.81/1.02      inference('clc', [status(thm)], ['207', '208'])).
% 0.81/1.02  thf('210', plain,
% 0.81/1.02      ((~ (v2_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.81/1.02      inference('split', [status(esa)], ['0'])).
% 0.81/1.02  thf('211', plain,
% 0.81/1.02      (~ ((v1_zfmisc_1 @ sk_B_1)) | ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.81/1.02      inference('sup-', [status(thm)], ['209', '210'])).
% 0.81/1.02  thf('212', plain, ($false),
% 0.81/1.02      inference('sat_resolution*', [status(thm)], ['1', '81', '82', '211'])).
% 0.81/1.02  
% 0.81/1.02  % SZS output end Refutation
% 0.81/1.02  
% 0.81/1.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
